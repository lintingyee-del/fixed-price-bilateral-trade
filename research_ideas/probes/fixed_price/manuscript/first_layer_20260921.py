"""New first-layer checks for components of the current included TeX.

Run from Documents with the shared Python interpreter.  This script does not
write the shared ledger or a fact graph.  Its pending_records.json is a run
receipt for the coordinator to record once, not a separate state database.

The scalar/finite max and rounding checks below are universal over their
displayed real variables.  They are not an audit of the infinite-dimensional
fixed-point, compactness, Stieltjes, or limit arguments in Theorem E.
"""

from __future__ import annotations

import json
import sys
import tomllib
from dataclasses import asdict
from pathlib import Path

import sympy as sp


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE / "checks" / "first_layer_20260921"
sys.path.insert(0, str(ROOT))
from hz_certify import decide as D  # noqa: E402; no ledger writes

DATE = "2026-09-21"
PAPER = "fixed-price bilateral trade manuscript (current included TeX)"
SCOPE = (
    "Only paper.tex and its four included TeX files. New scalar algebra and "
    "universal semialgebraic components of Theorem E and finite-node evaluation. "
    "No theorem-level certificate for existence, compactness, continuum order, "
    "measure identities, limiting arguments, or the conjectural matching bound."
)

REUSE = {
    "fp_ext_k2_prefix_obstacle_components_20260914": {
        "use": [
            "four cumulative-price Fubini identities with common buyer/price atoms",
            "contraction_weight_bound_identity",
            "pricing_scale_relation",
        ],
        "tex": ["two_units.tex:eq:two-potential", "two_units.tex:eq:two-operator"],
    },
    "fp_ext_k2_buyer_adaptive_prefix_components_20260914": {
        "use": [
            "seller_price_atom_jump",
            "interior_seller_potential_slope",
            "nonnegative_interval_slope_decomposition",
            "node_increment_combines_affine_piece_and_downward_jump",
        ],
        "tex": ["two_unit_pricing_proofs.tex:app:two-recurrence"],
    },
    "fp_ext_k2_buyer_adaptive_continuous_components_20260914": {
        "use": ["future-price kernel derivative", "coincident atom traces"],
        "tex": ["two_unit_pricing_proofs.tex:app:two-pricing"],
    },
    "fp_ext_k2_continuous_switching_components_20260914": {
        "use": ["tail_seller_constant_piece", "tail_seller_outside_piece"],
        "tex": ["two_unit_pricing_proofs.tex:app:two-pricing"],
    },
    "fp_ext_k2_tail_active_components_20260913": {
        "use": ["tail balance algebra", "clipping-loss decomposition"],
        "tex": ["two_unit_pricing_proofs.tex:app:two-tail"],
    },
}


def at(filename: str, anchor: str) -> dict:
    """Record a current TeX location without adding a source fingerprint."""
    lines = (HERE / filename).read_text(encoding="utf-8").splitlines()
    matches = [i + 1 for i, line in enumerate(lines) if anchor in line]
    return {"file": filename, "anchor": anchor, "lines": matches}


GROUPS = {
    "pricing_algebra": {
        "key": "fpm_20260921_pricing_obstacle_new_exact",
        "locations": [at("two_units.tex", "eq:two-potential"),
                      at("two_units.tex", "eq:two-operator")],
        "node": "T_two_pricing",
        "limitation": "Affine and Farkas components only; no continuum prefix or attainment theorem.",
    },
    "pricing_scalar": {
        "key": "fpm_20260921_pricing_scalar_new_smt",
        "locations": [at("two_unit_pricing_proofs.tex", "app:two-pricing")],
        "node": "T_two_pricing",
        "limitation": "Scalar consequences conditional on the displayed integral bounds; no Banach-space or right-continuity argument is machine-proved.",
    },
    "recurrence": {
        "key": "fpm_20260921_finite_node_max_steps_smt",
        "locations": [at("two_unit_pricing_proofs.tex", "eq:two-backward"),
                      at("two_unit_pricing_proofs.tex", "app:two-recurrence")],
        "node": "P_two_finite_nodes",
        "limitation": "Universal scalar steps used by the backwards induction, not a machine-formalized induction over arbitrary node counts or continuum extension.",
    },
    "rounding": {
        "key": "fpm_20260921_buyer_rounding_pointwise_smt",
        "locations": [at("two_unit_pricing_proofs.tex", "Rounding the buyer bodies.")],
        "node": "T_two_pricing",
        "limitation": "Pointwise real-variable implications only; expectation passage, floor measurability, optimal-price existence, and the supremum limit remain analytic.",
    },
}

ITEMS: list[dict] = []


def exact(group, name, statement, target, decomposition, nonnegative_terms=()):
    """Replay a rational identity or a Farkas certificate with explicit slacks."""
    residual = sp.cancel(sp.together(target - decomposition))
    ITEMS.append({
        "group": group, "name": name, "statement": statement,
        "kind": "exact", "status": "proved" if residual == 0 else "failed",
        "target": str(target), "decomposition": str(decomposition),
        "residual": str(residual),
        "nonnegative_terms_under_statement_premises": list(nonnegative_terms),
    })
    print(f"{name}: exact residual {residual}", flush=True)


def smt(group, name, statement, claim, assumptions):
    """Run both installed solvers on the negation, preserving every verdict."""
    decision = D.prove_forall(claim, assumptions, timeout_ms=15000)
    row = asdict(decision)
    ITEMS.append({
        "group": group, "name": name, "statement": statement,
        "kind": "smt", "hypotheses": [str(x) for x in assumptions],
        "goal": str(claim), **row,
    })
    print(f"{name}: {decision.status} {decision.solvers}", flush=True)


def check_exact_components():
    d, s, L, u, I, e, theta = sp.symbols("d s L u I epsilon theta", real=True)
    potential = d * s - L + L * u - I
    obstacle = 1 - d * s / L + e * theta / L + I / L
    exact(
        "pricing_algebra", "potential_minus_compensation_obstacle_identity",
        "For L != 0, L*(u-[1-d*s/L+epsilon*theta/L+I/L]) "
        "= (d*s-L+L*u-I)-epsilon*theta.",
        L * (u - obstacle), potential - e * theta,
    )

    a, d0, d1, u0, u1, I0, I1, th0, th1 = sp.symbols(
        "a d0 d1 u0 u1 I0 I1 theta0 theta1", real=True
    )
    def slack(dd, uu, ii, tt):
        return dd * s - L + L * uu - ii - e * tt
    exact(
        "pricing_algebra", "feasible_triple_affine_slack",
        "For every a, the potential-compensation slack of the a-weighted "
        "combination of (d,u,I,theta) equals the a-weighted combination of the "
        "two slacks, with buyer L and seller s fixed.",
        slack(a*d0+(1-a)*d1, a*u0+(1-a)*u1,
              a*I0+(1-a)*I1, a*th0+(1-a)*th1),
        a*slack(d0,u0,I0,th0)+(1-a)*slack(d1,u1,I1,th1),
    )

    x, y, t1, t2 = sp.symbols("psi1 psi2 theta1 theta2", real=True)
    exact(
        "pricing_algebra", "ordered_compensation_farkas_certificate",
        "If psi1+theta1 >= 0, psi2-theta2 >= 0, and theta2-theta1 >= 0, "
        "then psi1+psi2 >= 0. The three Farkas multipliers are exactly 1.",
        x+y, (x+t1)+(y-t2)+(t2-t1),
        ["psi1+theta1", "psi2-theta2", "theta2-theta1"],
    )

    delta, dl, dg = sp.symbols("delta DeltaL DeltaG", real=True)
    exact(
        "pricing_algebra", "rounding_tail_repair_farkas_certificate",
        "If 0 <= DeltaL <= delta and DeltaG >= 0, adding ideal-tail mass "
        "delta changes each potential by -DeltaL+DeltaG+delta >= 0. "
        "The two slack multipliers are exactly 1.",
        -dl+dg+delta, (delta-dl)+dg,
        ["delta-DeltaL", "DeltaG"],
    )


def check_pricing_scalar():
    b, L, E, q = sp.symbols("b L E kernel_difference", real=True)
    smt(
        "pricing_scalar", "scalar_kernel_contraction_after_common_denominator",
        "For b>=0, 1<=L<=1+b, E>=0 and |kernel_difference|<=(L-1)*E, "
        "|kernel_difference|*(1+b)<=b*L*E. Dividing by positive L*(1+b) "
        "gives the obstacle difference bound b/(1+b)*E.",
        sp.Abs(q)*(1+b) <= b*L*E,
        [b>=0, L>=1, L<=1+b, E>=0, sp.Abs(q)<=(L-1)*E],
    )

    x1, x2, y1, y2 = sp.symbols("x1 x2 y1 y2", real=True)
    smt(
        "pricing_scalar", "two_obstacle_max_is_nonexpansive",
        "If E>=0, |x1-y1|<=E and |x2-y2|<=E, then "
        "|max(0,x1,x2)-max(0,y1,y2)|<=E.",
        sp.Abs(sp.Max(0,x1,x2)-sp.Max(0,y1,y2)) <= E,
        [E>=0, sp.Abs(x1-y1)<=E, sp.Abs(x2-y2)<=E],
    )

    d, s = sp.symbols("d s", real=True)
    smt(
        "pricing_scalar", "constant_cumulative_mass_feasible_scalar",
        "For d>0, 0<=s<=b and 1<=L<=1+b, the potential at constant "
        "cumulative mass 1+b and zero compensation equals d*s+1+b-L >= 0 "
        "after using the existing kernel mass identity.",
        d*s+1+b-L >= 0,
        [d>0, s>=0, s<=b, L>=1, L<=1+b],
    )

    old, p1, p2 = sp.symbols("old_prefix psi1 psi2", real=True)
    new = sp.Max(old, -p1)
    smt(
        "pricing_scalar", "finite_canonical_prefix_extension",
        "If old_prefix<=psi2 and psi1+psi2>=0, the updated prefix "
        "max(old_prefix,-psi1) is >=old_prefix, >=-psi1 and <=psi2.",
        sp.And(new>=old, new>=-p1, new<=p2),
        [old<=p2, p1+p2>=0],
    )


def check_recurrence():
    r, A, B, u = sp.symbols("next_mass obstacle1 obstacle2 competitor", real=True)
    m = sp.Max(r,A,B)
    smt(
        "recurrence", "one_backward_step_is_least_feasible",
        "For next_mass>=0, m=max(next_mass,obstacle1,obstacle2) is "
        "nonnegative and satisfies all three bounds; every competitor "
        "satisfying those bounds is at least m.",
        sp.And(m>=0, m>=r, m>=A, m>=B, m<=u),
        [r>=0, u>=r, u>=A, u>=B],
    )

    r1, A1, B1 = sp.symbols("next_mass_upper obstacle1_upper obstacle2_upper", real=True)
    smt(
        "recurrence", "one_backward_step_is_order_preserving",
        "If next_mass<=next_mass_upper and each obstacle is at most its "
        "upper counterpart, their three-way maximum has the same order.",
        m <= sp.Max(r1,A1,B1), [r<=r1, A<=A1, B<=B1],
    )

    a = sp.symbols("a", real=True)
    smt(
        "recurrence", "three_way_max_convexity",
        "For 0<=a<=1, max(a*r+(1-a)*r1,a*A+(1-a)*A1,a*B+(1-a)*B1) "
        "<= a*max(r,A,B)+(1-a)*max(r1,A1,B1).",
        sp.Max(a*r+(1-a)*r1,a*A+(1-a)*A1,a*B+(1-a)*B1)
        <= a*m+(1-a)*sp.Max(r1,A1,B1), [a>=0, a<=1],
    )

    w, x, y = sp.symbols("weight future_lower future_upper", real=True)
    smt(
        "recurrence", "positive_kernel_summand_preserves_future_bounds",
        "For weight>=0 and future_lower<=future_upper, "
        "weight*future_lower<=weight*future_upper. "
        "This is the termwise comparison in the positive finite kernel.",
        w*x<=w*y, [w>=0, x<=y],
    )


def check_rounding():
    x, y, s, z, delta = sp.symbols("buyer rounded_buyer seller price delta", real=True)
    loss = sp.Max(x-s,0)-sp.Max(y-s,0)
    smt(
        "rounding", "rounded_stoploss_loss_all_real_regions",
        "For 0<=rounded_buyer<=buyer<rounded_buyer+delta, delta>0 and "
        "seller>=0, 0<=(buyer-seller)_+-(rounded_buyer-seller)_+<=delta.",
        sp.And(loss>=0,loss<=delta),
        [y>=0, x>=y, x<y+delta, delta>0, s>=0],
    )

    # For s<z, both gains contain the same constant 1.  For s>=z,
    # both kernels are zero.  Keeping all equality cases explicit retains
    # the manuscript's strict-seller / inclusive-buyer convention.
    def component(buyer):
        return sp.Piecewise((buyer-s,z<=buyer),(0,True))

    # hz_certify accepts boolean formulas rather than Piecewise.  The three
    # exhaustive branches below are written separately so equality at x=z
    # and y=z is unambiguous and the actual encoded premises are saved.
    smt(
        "rounding", "rounded_gain_both_buyers_accept",
        "For 0<=seller<price<=rounded_buyer<=buyer, "
        "[1+buyer-seller]-[1+rounded_buyer-seller]>=0.",
        (1+x-s)-(1+y-s)>=0,
        [s>=0, s<z, z<=y, y<=x],
    )
    smt(
        "rounding", "rounded_gain_only_original_buyer_accepts",
        "For 0<=rounded_buyer<price<=buyer and 0<=seller<price, "
        "the strict-seller/inclusive-buyer kernels differ by buyer-seller>=0.",
        x-s>=0, [y>=0,y<z,z<=x,s>=0,s<z],
    )
    smt(
        "rounding", "rounded_gain_acceptance_branches_are_exhaustive",
        "For rounded_buyer<=buyer, every real seller and price lies in "
        "one of: seller>=price; seller<price<=rounded_buyer; "
        "seller<price, rounded_buyer<price<=buyer; "
        "seller<price and buyer<price. The first and last branches have "
        "equal pointwise gain kernels.",
        sp.Or(s>=z, sp.And(s<z,z<=y), sp.And(s<z,y<z,z<=x),
              sp.And(s<z,x<z)), [y<=x],
    )


def save_receipt():
    OUT.mkdir(parents=True, exist_ok=True)
    ledger = tomllib.loads((ROOT/"proof_factgraph"/"ledger.toml").read_text(encoding="utf-8"))["claims"]
    reuse = {}
    for key, value in REUSE.items():
        source = ledger[key]
        reuse[key] = {**value, "original_statement": source["statement"],
                      "verified": source["verified"], "evidence": source["evidence"],
                      "rerun": False}
    data = {"date":DATE,"scope":SCOPE,"groups":GROUPS,"checks":ITEMS,
            "reused_existing_credentials":reuse,
            "summary":{
                "new_exact_checks":sum(x["kind"]=="exact" for x in ITEMS),
                "new_dual_solver_checks":sum(x["kind"]=="smt" for x in ITEMS),
                "passed":sum(x["status"]=="proved" for x in ITEMS),
                "nonpassing":[x["name"] for x in ITEMS if x["status"]!="proved"],
            }}
    (OUT/"results.json").write_text(json.dumps(data,indent=2,ensure_ascii=True)+"\n",encoding="utf-8")
    records=[]
    evidence=(OUT/"results.json").relative_to(ROOT).as_posix()
    for group,info in GROUPS.items():
        rows=[x for x in ITEMS if x["group"]==group]
        passed=[x for x in rows if x["status"]=="proved"]
        if passed:
            layers=["exact"] if all(x["kind"]=="exact" for x in passed) else ["z3","cvc5"]
            records.append({
                "key":info["key"],"statement":" ".join(x["statement"] for x in passed),
                "verified":layers,"evidence":evidence,"date":DATE,"paper":PAPER,
                "note":f"{len(passed)} new checks: "+", ".join(x["name"] for x in passed)+". "+info["limitation"],
                "manifest_node_for_scoped_notes":info["node"],"locations":info["locations"],
            })
        for x in rows:
            if x["status"]=="proved":continue
            records.append({
                "key":info["key"]+"_"+x["name"],"statement":x["statement"],
                "verified":[],"evidence":evidence,"date":DATE,"paper":PAPER,
                "note":f"Actual status {x['status']}; no credential. Raw result preserved in results.json. "+info["limitation"],
            })
    (OUT/"pending_records.json").write_text(json.dumps(records,indent=2,ensure_ascii=True)+"\n",encoding="utf-8")
    print(json.dumps(data["summary"]),flush=True)


def main():
    # Lookup happened before these new checks were designed.  Retain the
    # original credentials and reuse map in the actual run output.
    check_exact_components()
    check_pricing_scalar()
    check_recurrence()
    check_rounding()
    save_receipt()


if __name__=="__main__":
    main()
