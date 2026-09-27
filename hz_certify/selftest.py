"""Self-test.  Run after any change:  python -m hz_certify.selftest

Every case has a known answer, and the negative cases matter as much as the
positive ones: a layer that proves everything is not proving anything.  So the
suite checks that false claims are refuted, that non-strict bounds attained at
a point report `unknown` instead of success, that an unverified certificate is
never recorded, and that a feasible system yields no infeasibility certificate.
"""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

import sympy as sp

from . import certificates as C
from . import decide as D
from . import ledger as L
from . import rigorous as R

FAILED = []


def check(label, got, want):
    ok = got == want
    print(f"  {'ok  ' if ok else 'FAIL'}  {label}: {got!r}" +
          ("" if ok else f"  (expected {want!r})"))
    if not ok:
        FAILED.append(label)


def main() -> int:
    x, y = sp.symbols("x y")

    print("rigorous (Arb)")
    check("strict bound on a box",
          R.prove_positive(x ** 2 - x + sp.Rational(1, 3), {x: (0, 1)}).status, "proved")
    check("false bound is refuted",
          R.prove_positive(x ** 2 - x + sp.Rational(1, 5), {x: (0, 1)}).status, "refuted")
    check("no interior max, refuted on the whole interval",
          R.prove_positive(sp.diff(x * sp.exp(-x), x), {x: (0, 10)}).status, "refuted")
    check("transcendental, two variables",
          R.prove_positive(sp.exp(x) - 1 - x + y ** 2,
                           {x: (sp.Rational(1, 10), 2), y: (-1, 1)}).status, "proved")
    check("attained non-strict bound stays unknown",
          R.prove_nonneg((x - sp.Rational(1, 2)) ** 2, {x: (0, 1)}, max_boxes=200).status,
          "unknown")
    check("same bound with slack is decidable",
          R.prove_nonneg((x - sp.Rational(1, 2)) ** 2, {x: (0, 1)},
                         slack=sp.Rational(1, 1000)).status, "proved")
    I = R.integral(sp.exp(-x ** 2), x, 0, 3)
    check("rigorous integral bound",
          bool(I < R.as_interval(sp.Rational(8863, 10000), sp.Rational(8863, 10000))), True)

    print("certificates (SOS, Farkas)")
    c1 = C.sos(x ** 4 - x ** 2 + sp.Rational(1, 2), [x])
    check("unconstrained SOS", c1.verified, True)
    check("  residual identically zero", c1.residual, 0)
    check("  independent re-verification", C.verify(c1), True)
    c2 = C.sos(x ** 4 + y ** 4 - x * y + sp.Rational(1, 4), [x, y])
    check("two-variable SOS", c2.verified and C.verify(c2), True)
    c3 = C.sos_on_box(x - x ** 2 + sp.Rational(1, 100), {x: (0, 1)})
    check("constrained SOS on a box", c3.verified and C.verify(c3), True)
    c4 = C.sos(x ** 3 + (1 - x) ** 3 - sp.Rational(1, 4), [x])
    check("AM-GM style", c4.verified, True)
    check("  Lean hint mentions the square",
          "sq_nonneg (x - 1/2)" in C.to_lean_hint(c4), True)

    A, b = [[-1, 0], [0, -1], [1, 1]], [0, 0, 1]
    check("Farkas implication", C.farkas(A, b, [2, 3], 3).verified, True)
    check("Farkas rejects a false bound", C.farkas(A, b, [2, 3], 1).verified, False)
    check("Farkas infeasibility",
          C.farkas_infeasible([[1], [-1]], [-1, -1]).verified, True)
    check("Farkas finds nothing on a feasible system",
          C.farkas_infeasible([[1], [-1]], [1, 1]).verified, False)

    print("decide (z3 + cvc5)")
    d1 = D.prove_forall(x ** 3 + (1 - x) ** 3 >= sp.Rational(1, 4), [x >= 0, x <= 1])
    check("both solvers close a true claim", d1.status, "proved")
    check("  and both are recorded", sorted(d1.solvers.values()), ["unsat", "unsat"])
    d2 = D.prove_forall(x ** 2 >= x, [x > 0])
    check("false claim refuted", d2.status, "refuted")
    check("  witness replays exactly in sympy",
          d2.replay.startswith("all negation clauses confirmed"), True)
    check("exact optimum, min", D.worst_case(x ** 2 - x, [x >= 0, x <= 1]).claim,
          "min x**2 - x = -1/4")
    check("exact optimum, max",
          D.worst_case(x * (1 - x), [x >= 0, x <= 1], sense="max").claim,
          "max x*(1 - x) = 1/4")

    def assoc(n, S):
        return [S.op(S.op(i, j), k) == S.op(i, S.op(j, k))
                for i in range(n) for j in range(n) for k in range(n)]

    def comm(n, S):
        return [S.op(i, j) == S.op(j, i) for i in range(n) for j in range(n)]

    def idem(n, S):
        return [S.op(i, i) == i for i in range(n)]

    ind = D.independent_axioms({"assoc": assoc, "comm": comm, "idem": idem},
                               domain_sizes=range(1, 5), signature={"op": 2})
    for name in ("assoc", "comm", "idem"):
        check(f"independence of {name}", ind[name].status, "refuted")
        check(f"  {name} model confirmed without a solver",
              ind[name].witness["recheck"], "confirmed")

    print("ledger")
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "ledger.toml"
        p.write_text("# test\n", encoding="utf-8")
        check("nothing recorded yet", L.already_recorded("k1", p), False)
        L.record_certificate(c4, "k1", paper="selftest", path=p)
        check("recorded", L.already_recorded("k1", p), True)
        text = p.read_text(encoding="utf-8")
        check("  tagged exact", 'verified = ["exact"]' in text, True)
        L.record_decision(d1, "k2", paper="selftest", path=p)
        check("  dual solver tagged with both",
              'verified = ["z3", "cvc5"]' in p.read_text(encoding="utf-8"), True)
        v = R.prove_positive(sp.diff(x * sp.exp(-x), x), {x: (0, 10)})
        L.record_verdict(v, "k3", paper="selftest", path=p)
        check("  refutation tagged arb+exact",
              'verified = ["arb", "exact"]' in p.read_text(encoding="utf-8"), True)
        try:
            L.record("k1", "dup", ["exact"], "e", path=p)
            check("append-only guard", "no error", "ValueError")
        except ValueError:
            check("append-only guard", "raised", "raised")
        try:
            L.record("k9", "s", ["nosuch"], "e", path=p)
            check("layer guard", "no error", "ValueError")
        except ValueError:
            check("layer guard", "raised", "raised")
        bad = C.sos(x ** 2 - 1, [x])          # false: negative at x = 0
        check("false claim yields no certificate", bad.verified, False)
        try:
            L.record_certificate(bad, "k8", path=p)
            check("unverified certificate refused", "no error", "ValueError")
        except ValueError:
            check("unverified certificate refused", "raised", "raised")

    print()
    if FAILED:
        print(f"{len(FAILED)} FAILED: {', '.join(FAILED)}")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
