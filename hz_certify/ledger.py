"""Write results straight into proof_factgraph/ledger.toml.

The tools in this package are only worth having if using them is cheaper than
not using them, and the expensive part was never the solver call: it was
hand-writing a ledger entry afterwards and getting the layer name right.  So
every entry point here takes a result object from `rigorous`, `certificates`
or `decide` and appends a correctly-tagged, append-only ledger record.

Layer assignment is not a free choice, and this module makes it automatically
so that it stays consistent between sessions and between agents:

    exact   a finite certificate re-verified in exact arithmetic.  Trusts
            nothing beyond sympy, which is already trusted.  SOS and Farkas
            certificates, exact finite enumerations, rational witnesses.
    arb     a proved enclosure from interval arithmetic.  Trusts the Arb
            implementation.  Strictly stronger than any float computation and
            strictly weaker than `exact`.
    z3      a decision by z3 alone.
    cvc5    a decision by cvc5 alone.  Both names appear when both agreed;
            that is the point of running two, and a reader can see at a glance
            whether a claim rests on one solver or two.

A refutation is recorded as a credential too.  A counterexample that replays
exactly in sympy is the strongest cheap result available, and it belongs in
the ledger next to the claim it kills.
"""

from __future__ import annotations

import datetime as _dt
import io
import os
import re
from pathlib import Path

__all__ = ["LEDGER", "record", "record_verdict", "record_certificate",
           "record_decision", "already_recorded"]

LEDGER = Path(__file__).resolve().parents[1] / "proof_factgraph" / "ledger.toml"

_VALID = {"exact", "arb", "z3", "cvc5", "sympy", "lean", "rethlas", "litcheck",
          "float", "audit", "latex", "bookkeeping", "author-decision"}


def _today() -> str:
    return _dt.date.today().isoformat()


def _slug(s: str) -> str:
    s = re.sub(r"[^a-zA-Z0-9]+", "_", s.strip().lower()).strip("_")
    return s[:64] or "claim"


def already_recorded(key: str, path: Path = None) -> bool:
    """Check the ledger before running anything.

    The standing rule is to consult the ledger first and re-use an existing
    credential rather than re-running a layer, so this is the call that should
    come before the solver, not after.
    """
    path = Path(path or LEDGER)
    if not path.exists():
        return False
    return f"[claims.{key}]" in io.open(path, encoding="utf-8").read()


def record(key: str, statement: str, verified, evidence: str,
           paper: str = "", note: str = "", path: Path = None) -> str:
    """Append one entry.  Never rewrites or removes an existing one."""
    path = Path(path or LEDGER)
    layers = [verified] if isinstance(verified, str) else list(verified)
    bad = [l for l in layers if l not in _VALID]
    if bad:
        raise ValueError(f"unknown verification layer(s) {bad}; "
                         f"valid layers are {sorted(_VALID)}")
    key = _slug(key)
    if already_recorded(key, path):
        raise ValueError(f"claims.{key} already exists; the ledger is "
                         f"append-only, so pick a new key or supersede the old one")

    def esc(s):
        return str(s).replace("\\", "\\\\").replace('"', '\\"').replace("\n", " ")

    lines = [f"\n[claims.{key}]",
             f'statement = "{esc(statement)}"',
             "verified = [" + ", ".join(f'"{l}"' for l in layers) + "]",
             f'evidence = "{esc(evidence)}"',
             f'date = "{_today()}"']
    if paper:
        lines.append(f'paper = "{esc(paper)}"')
    if note:
        lines.append(f'note = "{esc(note)}"')
    with io.open(path, "a", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    return key


def record_verdict(verdict, key: str, statement: str = "", paper: str = "",
                   script: str = "", path: Path = None) -> str:
    """Record a `rigorous.Verdict` on the `arb` layer.

    An `unknown` verdict is recorded too, with no credential, because a budget
    exhaustion is information: it says where the difficulty is and stops the
    next session from re-running the same search.
    """
    st = statement or verdict.claim
    src = f"hz_certify.rigorous, {verdict.prec}-bit, {verdict.boxes_used} boxes"
    if script:
        src += f"; {script}"
    if verdict.status == "proved":
        return record(key, st, ["arb"],
                      f"proved on the whole domain by interval enclosure ({src})",
                      paper, path=path)
    if verdict.status == "refuted":
        pt = ", ".join(f"{k}={v}" for k, v in (verdict.witness or {}).items())
        return record(key, st, ["arb", "exact"],
                      f"REFUTED at the exact rational point {pt}, "
                      f"value {verdict.witness_value} ({src})", paper, path=path)
    return record(key, st, [],
                  f"UNKNOWN: subdivision budget exhausted, "
                  f"{len(verdict.unresolved)} sign-indefinite region(s) remain, "
                  f"first {verdict.unresolved[:1]} ({src})", paper, path=path)


def record_certificate(cert, key: str, statement: str = "", paper: str = "",
                       script: str = "", path: Path = None) -> str:
    """Record a verified certificate on the `exact` layer.

    An unverified certificate is not recorded at all: there is nothing to cite.
    """
    if not cert.verified:
        raise ValueError(f"refusing to record an unverified certificate: {cert.note}")
    st = statement or cert.claim
    body = cert.data.get("pretty", "").replace("\n", "; ").strip()
    src = f"hz_certify.certificates.{cert.kind}" + (f"; {script}" if script else "")
    return record(key, st, ["exact"],
                  f"{cert.kind} certificate, sympy residual identically {cert.residual}: "
                  f"{body} ({src})", paper, path=path)


def record_decision(dec, key: str, statement: str = "", paper: str = "",
                    script: str = "", path: Path = None) -> str:
    """Record a `decide.Decision`, tagged with the solvers that actually closed it.

    A `conflict` raises rather than recording.  Two solvers disagreeing means
    one of them is wrong, and filing that as a credential would be worse than
    filing nothing.
    """
    st = statement or dec.claim
    votes = ", ".join(f"{k}={v}" for k, v in dec.solvers.items())
    src = f"hz_certify.decide" + (f"; {script}" if script else "")
    if dec.status == "conflict":
        raise ValueError(f"solvers disagree ({votes}); resolve before recording")
    if dec.status == "proved":
        agreed = [k for k, v in dec.solvers.items() if v == "unsat"]
        return record(key, st, agreed or ["z3"],
                      f"negation unsat ({votes}) ({src})", paper, path=path)
    if dec.status == "refuted":
        pt = ", ".join(f"{k}={v}" for k, v in (dec.witness or {}).items())
        return record(key, st, ["exact"],
                      f"REFUTED by a model at {pt}; {dec.replay} ({votes}) ({src})",
                      paper, path=path)
    if dec.status == "bracket":
        return record(key, st, ["z3", "cvc5"],
                      f"certified bracket; {dec.note}; {dec.replay} ({votes}) ({src})",
                      paper, path=path)
    return record(key, st, [],
                  f"UNDECIDED ({votes}); {dec.note} ({src})", paper, path=path)
