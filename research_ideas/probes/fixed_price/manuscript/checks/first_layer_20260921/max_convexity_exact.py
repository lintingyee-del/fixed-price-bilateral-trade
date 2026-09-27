"""Exact finite branch certificate for the max-convexity SMT timeout.

No solver is run here.  Every triple of active indices for the two endpoint
maxima and the mixed maximum is covered.  The checked residual for each
triple is zero, and the displayed decomposition is a sum of products of
the branch's explicitly nonnegative factors.
"""

import itertools
import json
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
a = sp.symbols("a", real=True)
x = sp.symbols("x0:3", real=True)
y = sp.symbols("y0:3", real=True)
z = tuple(a*x[k] + (1-a)*y[k] for k in range(3))
rows = []
for i, j, k in itertools.product(range(3), repeat=3):
    target = a*x[i] + (1-a)*y[j] - z[k]
    decomposition = a*(x[i]-x[k]) + (1-a)*(y[j]-y[k])
    residual = sp.expand(target-decomposition)
    rows.append({
        "active_indices": [i,j,k],
        "hypotheses": ["0<=a<=1"]
            + [f"x{i}-x{ell}>=0" for ell in range(3)]
            + [f"y{j}-y{ell}>=0" for ell in range(3)]
            + [f"z{k}-z{ell}>=0" for ell in range(3)],
        "target": str(target),
        "nonnegative_product_terms": [str(a*(x[i]-x[k])),
                                      str((1-a)*(y[j]-y[k]))],
        "decomposition": str(decomposition),
        "residual": str(residual),
        "passed": residual == 0,
    })

all_passed = len(rows)==27 and all(row["passed"] for row in rows)
statement = (
    "For all real x0,x1,x2,y0,y1,y2 and 0<=a<=1, "
    "max_k(a*xk+(1-a)*yk) <= a*max_k(xk)+(1-a)*max_k(yk). "
    "All 27 triples of active endpoint/mixed maxima have the exact "
    "nonnegative decomposition a*(xi-xk)+(1-a)*(yj-yk), with zero "
    "polynomial residual. Ties belong to one or more covered branches."
)
receipt = {
    "date": "2026-09-21", "statement": statement,
    "scope": "Universal scalar max-convexity component of eq:two-backward; "
             "the induction in the number of nodes remains analytic.",
    "previous_run": "results.json:three_way_max_convexity (Z3 unsat, cvc5 unknown)",
    "branches": rows, "branches_covered": len(rows),
    "all_passed": all_passed,
}
path = HERE/"max_convexity_exact.json"
path.write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf-8")
record = {
    "key": "fpm_20260921_finite_node_max_convexity_exact",
    "statement": statement,
    "verified": ["exact"] if all_passed else [],
    "evidence": path.relative_to(ROOT).as_posix(),
    "date": "2026-09-21", "paper": "fixed-price bilateral trade manuscript (current included TeX)",
    "note": "Exact certificate for the scalar max convexity step in "
            "two_unit_pricing_proofs.tex, eq:two-backward. The 27 branch "
            "certificates cover all endpoint and mixed max active indices. "
            "This resolves the preceding dual-solver timeout without rerunning "
            "or changing that receipt. No continuum or arbitrary-node-count "
            "proof is claimed.",
    "manifest_node_for_scoped_notes": "P_two_finite_nodes",
}
(HERE/"pending_max_convexity_record.json").write_text(
    json.dumps(record,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"branches":len(rows),"all_passed":all_passed}))
