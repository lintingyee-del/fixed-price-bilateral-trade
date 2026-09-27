#!/usr/bin/env python3
"""Proof fact-graph tool.

Manages a paper's proof appendix as a dependency graph with per-node
verification states. Zero dependencies (Python >= 3.11, stdlib tomllib).

Usage:
    python factgraph.py <manifest.toml> check
    python factgraph.py <manifest.toml> status
    python factgraph.py <manifest.toml> blast <NODE>   # who falls if NODE falls
    python factgraph.py <manifest.toml> audit <NODE>   # ancestors + verification gaps
    python factgraph.py <manifest.toml> stamp          # refresh fingerprints on credentialed nodes

A credential is issued against a specific (statement, premise set) pair, so each
credentialed node stores a fingerprint of that pair. `check` recomputes it and
refuses any node whose statement or dependency list has moved since. That catches
a model upgrade, where a node keeps its wording but comes to rest on different
premises and is therefore a different theorem.

Manifest schema (TOML):
    [nodes.<ID>]
    kind       = "assumption" | "lemma" | "proposition" | "theorem" | "corollary"
    statement  = "one-line statement"
    depends_on = ["A1", "L2"]          # cited assumptions / lemmas
    verified   = ["exact", "arb", "sympy", "z3", "cvc5", "lean", "rethlas", "litcheck"]
                                       # subset; only what actually ran.
                                       # "axle" and "human" remain readable legacy layers.
                                       #
                                       # The machine layers differ in what they ask you to
                                       # trust, which is the reason they are separate names:
                                       #   exact  a finite certificate re-expanded to zero in
                                       #          sympy: an SOS or Farkas decomposition, an
                                       #          exact finite enumeration, a counterexample
                                       #          replayed exactly. Adds nothing to the
                                       #          trusted base and any reader can recheck it.
                                       #   lean   kernel-checked.
                                       #   arb    a proved interval enclosure. Trusts Arb.
                                       #          Covers a whole domain, unlike a grid scan,
                                       #          which is not a credential at all.
                                       #   sympy  an exact symbolic computation.
                                       #   z3     a decision by z3 alone.
                                       #   cvc5   a decision by cvc5 alone. Both names present
                                       #          means both agreed; one name means one solver
                                       #          closed it, which is the weaker result and
                                       #          should look weaker on the page.
    divergent  = ["rethlas"]           # layers that PASSED, but on text that differs from the
                                       # paper. A rethlas credential certifies a blueprint; if
                                       # that blueprint was repaired and the paper was not, the
                                       # credential is real and is not a credential for the paper.
    failed     = ["rethlas"]           # layers that returned a NEGATIVE verdict on this node.
                                       # A node can carry both: sympy may certify the algebra
                                       # while rethlas rejects the argument around it. audit
                                       # surfaces these separately and never treats a node as
                                       # covered while a failure stands against it.
    location   = "App B, p.34"         # optional
    notes      = "lean: project/toolchain/file/theorem ..." # optional, log evidence here
"""
import hashlib
import re
import sys
import tomllib
from collections import deque

MACHINE = {"exact", "arb", "sympy", "z3", "cvc5", "lean", "axle"}  # axle: historical only
AUDIT = {"rethlas", "litcheck", "human"}   # "human" kept as a legacy alias
LAYERS = ["exact", "arb", "sympy", "z3", "cvc5", "lean", "axle",
          "rethlas", "litcheck", "human"]

# Layers whose output a reader can recheck without trusting the tool that
# produced it. A certificate expands to zero in sympy and the kernel checks a
# Lean proof, so neither asks the reader to take a solver's word for anything.
# Everything else in MACHINE does. `audit` reports the difference, because a
# result that rests on a single solver's unsat is worth flagging even though
# it is a genuine machine credential.
SELF_CHECKING = {"exact", "lean"}
KINDS = {"assumption", "definition", "lemma", "proposition", "theorem", "corollary"}


def fingerprint(node):
    """A credential is valid only against the (statement, premise set) it was issued for."""
    payload = node["statement"].strip() + "|" + ",".join(sorted(node["depends_on"]))
    return "sha256:" + hashlib.sha256(payload.encode("utf-8")).hexdigest()[:12]


def load(path):
    with open(path, "rb") as f:
        data = tomllib.load(f)
    nodes = data.get("nodes", {})
    for name, n in nodes.items():
        n.setdefault("kind", "lemma")
        n.setdefault("statement", "")
        n.setdefault("depends_on", [])
        n.setdefault("verified", [])
        n.setdefault("fingerprint", "")
        n.setdefault("failed", [])
        n.setdefault("divergent", [])
    return nodes


def check(nodes):
    errs = []
    for name, n in nodes.items():
        if n["kind"] not in KINDS:
            errs.append(f"{name}: unknown kind '{n['kind']}'")
        for lay in n["verified"]:
            if lay not in LAYERS:
                errs.append(f"{name}: unknown verification layer '{lay}'")
        for lay in n["failed"] + n["divergent"]:
            if lay not in LAYERS:
                errs.append(f"{name}: unknown layer '{lay}' in failed/divergent")
        for lay in n["failed"]:
            if lay in n["verified"]:
                errs.append(f"{name}: '{lay}' is in both verified and failed")
        for lay in n["divergent"]:
            if lay not in n["verified"]:
                errs.append(f"{name}: '{lay}' marked divergent but not verified")
        for d in n["depends_on"]:
            if d not in nodes:
                errs.append(f"{name}: depends on undeclared node '{d}'")
        if n["kind"] == "assumption" and n["depends_on"]:
            errs.append(f"{name}: assumptions must not have dependencies")
        if n["verified"]:
            want = fingerprint(n)
            if not n["fingerprint"]:
                errs.append(f"{name}: carries {n['verified']} with no fingerprint; "
                            f"run stamp to record it as {want}")
            elif n["fingerprint"] != want:
                errs.append(f"{name}: credential {n['verified']} was issued against a "
                            f"different statement or premise set "
                            f"({n['fingerprint']} != {want}); clear verified and re-run, "
                            f"or restore the wording it was issued for")
    color = {k: 0 for k in nodes}  # 0 white, 1 gray, 2 black

    def dfs(u, stack):
        color[u] = 1
        stack.append(u)
        for v in nodes[u]["depends_on"]:
            if v in nodes:
                if color[v] == 1:
                    cyc = stack[stack.index(v):] + [v]
                    errs.append("dependency cycle: " + " -> ".join(cyc))
                elif color[v] == 0:
                    dfs(v, stack)
        color[u] = 2
        stack.pop()

    for k in nodes:
        if color[k] == 0:
            dfs(k, [])
    return errs


def reverse_edges(nodes):
    rev = {k: [] for k in nodes}
    for name, n in nodes.items():
        for d in n["depends_on"]:
            if d in rev:
                rev[d].append(name)
    return rev


def descendants(nodes, start):
    rev = reverse_edges(nodes)
    seen, q = set(), deque([start])
    while q:
        for v in rev[q.popleft()]:
            if v not in seen:
                seen.add(v)
                q.append(v)
    return seen


def ancestors(nodes, start):
    seen, q = set(), deque([start])
    while q:
        for v in nodes[q.popleft()]["depends_on"]:
            if v in nodes and v not in seen:
                seen.add(v)
                q.append(v)
    return seen


def fmt(nodes, name):
    n = nodes[name]
    ver = ",".join(n["verified"]) if n["verified"] else "UNVERIFIED"
    if n["failed"]:
        ver += " !FAILED:" + ",".join(n["failed"])
    if n["divergent"]:
        ver += " ~REPAIRED-TEXT:" + ",".join(n["divergent"])
    return f"{name:<5} [{n['kind'][:4]}] ({ver})  {n['statement']}"


def main():
    if sys.platform == "win32":
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    path, cmd = sys.argv[1], sys.argv[2]
    nodes = load(path)

    if cmd == "check":
        errs = check(nodes)
        if errs:
            print("MANIFEST ERRORS:")
            for e in errs:
                print("  -", e)
            sys.exit(1)
        print(f"ok: {len(nodes)} nodes, no dangling refs, no cycles")

    elif cmd == "status":
        print(f"{'node':<5} {'kind':<12} {'verified':<24} {'#dn':>3}  statement")
        for name in nodes:
            n = nodes[name]
            ver = ",".join(n["verified"]) if n["verified"] else "-"
            dn = len(descendants(nodes, name))
            print(f"{name:<5} {n['kind']:<12} {ver:<24} {dn:>3}  {n['statement']}")
        unv = [k for k, n in nodes.items()
               if n["kind"] not in ("assumption", "definition") and not n["verified"]]
        if unv:
            print()
            print("unverified non-assumption nodes:", ", ".join(unv))
        bad = sorted(k for k, n in nodes.items() if n["failed"])
        if bad:
            print("standing failure:", ", ".join(bad))
        dft = sorted(k for k, n in nodes.items() if n["divergent"])
        if dft:
            print("credentialed on repaired text, paper not updated:", ", ".join(dft))
        idle = sorted(k for k, n in nodes.items()
                      if n["kind"] not in ("assumption", "definition")
                      and not descendants(nodes, k) and len(ancestors(nodes, k)) >= 4)
        if idle:
            print()
            print("costly but load-bearing for nothing (no descendants, 4+ ancestors):")
            print("  " + ", ".join(idle))
            print("  A proportionality reading, not a correctness one.")

    elif cmd == "blast":
        target = sys.argv[3]
        hit = descendants(nodes, target)
        print(f"if {target} falls, it takes down {len(hit)} node(s):")
        for k in nodes:
            if k in hit:
                print("  ", fmt(nodes, k))

    elif cmd == "audit":
        target = sys.argv[3]
        anc = ancestors(nodes, target) | {target}
        print(f"{target} rests on {len(anc) - 1} ancestor(s); the target itself is included below:")
        bare, audited, broken, drift, single = [], [], [], [], []
        for k in nodes:
            if k in anc:
                print("  ", fmt(nodes, k))
                n = nodes[k]
                if n["failed"]:
                    broken.append(k)          # a standing failure outranks any credential
                    continue
                if n["divergent"]:
                    drift.append(k)           # passed, but not on the paper's own text
                if n["kind"] in ("assumption", "definition"):
                    continue
                ver = set(n["verified"])
                if ver & MACHINE:
                    # A machine credential that no reader can recheck, and that
                    # rests on exactly one solver, is the weakest of them. Worth
                    # naming so it can be strengthened cheaply rather than found
                    # by a referee.
                    if not (ver & SELF_CHECKING) and len(ver & {"z3", "cvc5"}) == 1:
                        single.append(k)
                    continue
                (audited if ver & AUDIT else bare).append(k)
        if broken:
            print()
            print(f"KNOWN FAILURE on: {', '.join(broken)}  <- a layer rejected this node")
            print("  A machine credential on the same node covers its algebra only; it does")
            print("  not answer the layer that rejected it. Read the ledger before shipping.")
        if drift:
            print()
            print(f"PASSED ON REPAIRED TEXT: {', '.join(drift)}")
            print("  The credential certifies a corrected argument. Until the paper is")
            print("  updated to match, it is not a credential for the paper.")
        if bare:
            print()
            print(f"NO EVIDENCE on: {', '.join(bare)}  <- must verify")
        if audited:
            print()
            print(f"AUDIT ONLY, no machine layer, on: {', '.join(audited)}"
                  "  <- must disclose in the paper")
        if single:
            print()
            print(f"ONE SOLVER, NOTHING RECHECKABLE, on: {', '.join(single)}")
            print("  These rest on a single solver's verdict with no certificate and no")
            print("  Lean proof behind them. Running the other solver, or turning the")
            print("  claim into an 'exact' certificate, is usually a few minutes' work.")
        if not bare and not audited and not broken and not drift:
            print()
            print("all non-assumption ancestors carry at least one machine layer")

    elif cmd == "stamp":
        text = open(path, encoding="utf-8").read()
        lines, out, cur, changed = text.splitlines(), [], None, 0
        for line in lines:
            m = re.match(r"\[nodes\.([A-Za-z0-9_]+)\]\s*$", line)
            if m:
                cur = m.group(1)
            if re.match(r"\s*fingerprint\s*=", line) and cur in nodes:
                continue                       # drop, reinserted below
            out.append(line)
            if m and cur in nodes and nodes[cur]["verified"]:
                out.append(f'fingerprint = "{fingerprint(nodes[cur])}"')
                changed += 1
        open(path, "w", encoding="utf-8").write(chr(10).join(out) + chr(10))
        print(f"stamped {changed} credentialed node(s)")

    else:
        print(f"unknown command '{cmd}'")
        sys.exit(1)


if __name__ == "__main__":
    main()
