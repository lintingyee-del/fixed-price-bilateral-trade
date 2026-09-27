"""Prepare/replay local first-layer checks after the authorized D.1/D.4 repairs.

Default invocation prints the plan only.  The coordinator calls --run after
writing the TeX.  No TeX, old receipt, ledger, graph, or Rethlas input is written.
The old functions/calculation blocks are reused without their ledger/writer
wrappers.  Unaffected Arb covers are explicitly reused, not executed here.

This is a local algebra/SMT receipt, not a whole-theorem proof credential.
"""

from __future__ import annotations

import argparse
import ast
import contextlib
import io
import json
from pathlib import Path
import sys
import tomllib
import traceback
from types import SimpleNamespace

import sympy as sp


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXT = HERE.parent / "extension_screen_20260913"
CONT = EXT / "continuation"
OUT = HERE / "checks" / "first_layer_repair_20260921"
sys.path.insert(0, str(ROOT))
from hz_certify import decide  # noqa: E402; this module does not write the ledger

DATE = "2026-09-21"
PREFIX = "fpm_repair_20260921_"
PAPER = "fixed-price bilateral trade manuscript: repaired included TeX"

PLAN = {
    "mode": "plan_only_unless_run_is_explicitly_selected",
    "scope": "Current paper.tex and four included TeX files; local checks only.",
    "replay_symbolic": [
        {"group":"single_unit_algebra", "count":46,
         "source":"first_layer.py:algebra", "old_key":"fpm2_20260913_algebra"},
        {"group":"displayed_steps", "count":6,
         "source":"first_layer_register_20260913.py:displayed_steps",
         "old_key":"fpm3_20260913_displayed_steps"},
        {"group":"granularity", "count":22,
         "source":"verify_granularity_hard_20260918.py: symbolic prefix only",
         "old_key":"fp_manuscript_granularity_intermediate_identities_20260918"},
        {"group":"shifted", "count":12,
         "source":"extension_screen_20260913/shifted_algebra.py:main calculation block",
         "old_key":"fp_ext_k2_shifted_clock_algebra_20260913"},
        {"group":"endpoint", "count":13,
         "source":"continuation/endpoint_algebra.py:main calculation block",
         "old_key":"fp_ext_k2_inverse_endpoint_algebra_20260913"},
        {"group":"outer_boundary", "count":4,
         "source":"continuation/outer_boundary_algebra.py: pre-Arb calculation block",
         "old_key":"fp_ext_k2_outer_boundary_algebra_20260913"},
        {"group":"branch_elimination", "count":4,
         "source":"continuation/branch_reduction.py:algebra calculation block",
         "old_key":"fp_ext_k2_branch_elimination_algebra_20260913"},
        {"group":"second_body_kernel", "count":10,
         "source":"continuation/general_dual/second_body_kernel.py:symbolic",
         "old_key":"fp_ext_k2_second_body_kernel_algebra_20260913"},
        {"group":"stationary_reconstruction_replay", "count":9,
         "source":"checks/first_layer_repair_20260921/physical_conditions.py:exact_components",
         "old_key":"fpm_repair_20260921_stationary_reverse_construction_algebra"},
    ],
    "replay_smt": [
        {"group":"single_unit_signs", "count":10,
         "source":"first_layer.py:sign_claims"},
        {"group":"pricing_scalar", "count":4,
         "source":"first_layer_20260921.py:check_pricing_scalar"},
        {"group":"node_steps", "count":3,
         "source":"first_layer_20260921.py:check_recurrence, excluding the prior unknown"},
        {"group":"buyer_rounding", "count":4,
         "source":"first_layer_20260921.py:check_rounding"},
    ],
    "new_repair_checks": {
        "D1":"Four disjoint/exhaustive price regions, terminal atom routing, and scalar tail bounds.",
        "D4":"K=(M+G)/D*(1-R/beta), R>=beta iff K<=0, equality at beta=R_min, and derivative identities.",
    },
    "incidental_original_helper_replay": (
        "The original calibration_probe.symbolic helper also replays its "
        "finite rational Jensen witness. That actual exact calculation is "
        "reported separately; it is not omitted from the run record."
    ),
    "reused_without_execution": [
        "All unaffected Arb covers, including stationary branch and kernel sign covers",
        "Specified finite-instance and polygon exact receipts",
        "The 27-branch exact max-convexity certificate from this session",
        "Other unchanged exact component receipts not invoked by the listed functions",
    ],
    "not_run": [
        "Unpublished Markdown branches", "Lean", "Rethlas", "Floating discovery",
        "Granularity script's four floating quadratures", "Original script main/writer wrappers",
    ],
    "writes": ["checks/first_layer_repair_20260921/results.json",
               "checks/first_layer_repair_20260921/pending_records.json"],
}

GROUPS: list[dict] = []
LEDGER: dict = {}


def parse_source(path):
    return ast.parse(path.read_text(encoding="utf-8-sig"), filename=str(path))


def original_function(path, name, extra=None):
    """Load only a named function definition; imports and main are not run."""
    tree = parse_source(path)
    node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name)
    namespace = {"s":sp, "sp":sp, "__doc__":ast.get_docstring(tree), **(extra or {})}
    exec(compile(ast.Module(body=[node], type_ignores=[]), str(path), "exec"), namespace)
    return namespace[name]


def original_calculation_block(path, function, result_name, stop):
    """Extract the existing calculation block, excluding persistence wrappers.

    The boundaries are ordinary Python statements in an old combined
    calculation/writer function. No algebraic expression is replaced.
    """
    tree = parse_source(path)
    fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == function)
    start = next(i for i,n in enumerate(fn.body)
                 if isinstance(n, ast.Assign) and "s.symbols(" in ast.unparse(n))
    end = next(i for i,n in enumerate(fn.body) if i > start and stop(n))
    # A nonzero residual is persisted and does not prevent remaining groups.
    body = [n for n in fn.body[start:end] if not isinstance(n, ast.Assert)]
    body.append(ast.Return(value=ast.Name(id=result_name, ctx=ast.Load())))
    isolated = ast.FunctionDef(name="calculate", args=ast.arguments(
        posonlyargs=[], args=[], kwonlyargs=[], kw_defaults=[], defaults=[]),
        body=body, decorator_list=[])
    module = ast.fix_missing_locations(ast.Module(body=[isolated], type_ignores=[]))
    namespace = {"s":sp}
    exec(compile(module, str(path), "exec"), namespace)
    return namespace["calculate"]


def assigning(name):
    return lambda node: isinstance(node, ast.Assign) and any(
        isinstance(t, ast.Name) and t.id == name for t in node.targets)


def symbolic_result(value):
    if "residuals" in value:
        result = dict(value)
    else:
        result = {"residuals":{k:str(v) for k,v in value.items()}}
    result["all_zero"] = all(str(v) == "0" for v in result["residuals"].values())
    return result


def receipt_record(group):
    good = group["status"] == "passed"
    return {
        "key": PREFIX+group["name"], "statement":group["statement"],
        "verified":group["layers"] if good else [],
        "evidence":(OUT/"results.json").relative_to(ROOT).as_posix()+" group "+group["name"],
        "date":DATE, "paper":PAPER,
        "note":group["scope"]+" "
            +(f"Replays original component(s): {group.get('old_keys', [])}. "
              if group.get("old_keys") else "")
            +("Actual status "+group["status"]+"; no pass credential. " if not good else "")
            +"No complete analytic theorem is machine-certified.",
    }


def save():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/"results.json").write_text(json.dumps({
        "date":DATE, "plan":PLAN, "groups":GROUPS,
        "source_locations": ["two_unit_family.tex:lem:2fam-realization",
                             "two_unit_family.tex:lem:2fam-boundary"],
        "summary":{"groups":len(GROUPS),
                   "passed":sum(g["status"]=="passed" for g in GROUPS),
                   "nonpassing":[g["name"] for g in GROUPS if g["status"]!="passed"]},
    },indent=2,default=str)+"\n",encoding="utf-8")
    (OUT/"pending_records.json").write_text(
        json.dumps([receipt_record(g) for g in GROUPS],indent=2,default=str)+"\n",encoding="utf-8")


def run_group(name, statement, layers, scope, calculation, old_keys=()):
    row = {"name":name,"statement":statement,"layers":layers,"scope":scope,
           "old_keys":list(old_keys)}
    try:
        value = calculation()
        row["result"] = value
        row["status"] = "passed" if value.get("all_zero",value.get("all_passed",False)) else "failed_or_unknown"
    except Exception as exc:
        row.update(status="error",error=repr(exc),traceback=traceback.format_exc())
    GROUPS.append(row)
    save()
    print(name+": "+row["status"],flush=True)
    return row


def smt_result(name, claim, assumptions, statement):
    result = decide.prove_forall(claim, assumptions, timeout_ms=15000)
    return {"name":name,"statement":statement,"goal":str(claim),
            "assumptions":[str(v) for v in assumptions],"status":result.status,
            "solvers":result.solvers,"witness":result.witness,"replay":result.replay,
            "note":result.note}


def smt_bundle(items):
    rows=[]
    for name,claim,assumptions,statement in items:
        try:
            rows.append(smt_result(name,claim,assumptions,statement))
        except Exception as exc:
            rows.append({"name":name,"statement":statement,"status":"error","error":repr(exc)})
    return {"checks":rows,"all_passed":all(r["status"]=="proved" for r in rows)}


def run_old_symbolic():
    calibration = original_function(HERE.parent/"calibration_probe.py", "symbolic")
    algebra = original_function(HERE/"first_layer.py", "algebra",
                                {"calibration_probe":SimpleNamespace(symbolic=calibration)})
    row = run_group("single_unit_algebra", LEDGER["fpm2_20260913_algebra"]["statement"],
        ["sympy"],"46 local identities from the current included single-unit proof.",
        algebra,["fpm2_20260913_algebra"])
    if row["status"]=="passed":
        witness=row["result"]["Jensen_witness"]
        run_group("single_unit_jensen_helper", LEDGER["fpm2_20260913_jensen_exact"]["statement"],
            ["exact"],"Incidental exact calculation actually performed by the reused original helper; fixed rational witness only.",
            lambda:{"witness":witness,"all_passed":sp.Rational(witness["average_minus_midpoint"])>0},
            ["fpm2_20260913_jensen_exact"])

    fn=original_function(HERE/"first_layer_register_20260913.py","displayed_steps")
    run_group("displayed_steps",LEDGER["fpm3_20260913_displayed_steps"]["statement"],
        ["sympy"],"Six local derivatives and first-variation identities.",fn,
        ["fpm3_20260913_displayed_steps"])

    def granularity():
        path=HERE/"verify_granularity_hard_20260918.py"
        tree=parse_source(path)
        end=next(i for i,n in enumerate(tree.body) if ast.unparse(n).startswith("mp.mp.dps ="))
        body=[n for n in tree.body[:end] if not isinstance(n,(ast.Import,ast.ImportFrom))]
        namespace={"sp":sp}
        with contextlib.redirect_stdout(io.StringIO()):
            exec(compile(ast.Module(body=body,type_ignores=[]),str(path),"exec"),namespace)
        return {"zero_residual_tests":namespace["results"],
                "all_passed":all(namespace["results"].values())}
    run_group("granularity_symbolic_only",
        "The 22 exact symbolic intermediate formulas in the recorded Lemma 6.1, Lemma 7.1 and Corollary B' expansion again have zero residual.",
        ["exact"],"Only the old script's symbolic prefix is executed; four floating quadratures are excluded.",
        granularity,["fp_manuscript_granularity_intermediate_identities_20260918"])

    specs=[
        ("shifted",EXT/"shifted_algebra.py","main","checks",assigning("receipt"),
         "fp_ext_k2_shifted_clock_algebra_20260913"),
        ("endpoint",CONT/"endpoint_algebra.py","main","checks",assigning("failures"),
         "fp_ext_k2_inverse_endpoint_algebra_20260913"),
        ("outer_boundary",CONT/"outer_boundary_algebra.py","main","residuals",
         lambda n:ast.unparse(n).startswith("ctx.prec ="),
         "fp_ext_k2_outer_boundary_algebra_20260913"),
        ("branch_elimination",CONT/"branch_reduction.py","algebra","checks",
         lambda n:isinstance(n,ast.Assign) and isinstance(n.value,ast.Call)
             and isinstance(n.value.func,ast.Name) and n.value.func.id=="expressions",
         "fp_ext_k2_branch_elimination_algebra_20260913"),
    ]
    for name,path,fn,result_name,stop,old in specs:
        calculation=original_calculation_block(path,fn,result_name,stop)
        statement=LEDGER[old]["statement"]
        if name=="outer_boundary":
            statement="The four recorded zero-left-contact, zero-right-contact, p=1 gap and buyer-mean identities have zero symbolic residual."
        run_group(name,statement,["sympy"],
            "Original local symbolic calculation block only; all writers and unrelated interval/search code are excluded.",
            lambda calculation=calculation:symbolic_result(calculation()),[old])
    second=original_function(CONT/"general_dual"/"second_body_kernel.py","symbolic")
    run_group("second_body_kernel",LEDGER["fp_ext_k2_second_body_kernel_algebra_20260913"]["statement"],
        ["sympy"],"Ten conditional local kernel identities; the unchanged Arb sign cover is reused.",
        lambda:symbolic_result(second()),["fp_ext_k2_second_body_kernel_algebra_20260913"])
    reconstruction=original_function(OUT/"physical_conditions.py","exact_components")
    old="fpm_repair_20260921_stationary_reverse_construction_algebra"
    run_group("stationary_reconstruction_replay",LEDGER[old]["statement"],
        ["sympy"],"Nine local D.6 identities replayed after insertion of the reverse construction into TeX; the existing physical-domain Arb box is not rerun.",
        reconstruction,[old])


def run_old_smt():
    builder=original_function(HERE/"first_layer.py","sign_claims")
    for name,claim,assumptions in builder():
        old="fpm2_20260913_"+name
        statement=LEDGER[old]["statement"]
        run_group("single_unit_"+name,statement,["z3","cvc5"],
            "Original semialgebraic component, both solvers rerun after the authorized TeX repairs.",
            lambda name=name,claim=claim,assumptions=assumptions,statement=statement:
                smt_bundle([(name,claim,assumptions,statement)]),[old])

    specs=[("pricing_scalar","check_pricing_scalar","fpm_20260921_pricing_scalar_new_smt"),
           ("node_steps","check_recurrence","fpm_20260921_finite_node_max_steps_smt"),
           ("buyer_rounding","check_rounding","fpm_20260921_buyer_rounding_pointwise_smt")]
    for group,fn,old in specs:
        def compute(fn=fn):
            items=[]
            def collect(_group,name,statement,claim,assumptions):
                if name!="three_way_max_convexity":
                    items.append((name,claim,assumptions,statement))
            original_function(HERE/"first_layer_20260921.py",fn,{"smt":collect})()
            return smt_bundle(items)
        run_group(group,LEDGER[old]["statement"],["z3","cvc5"],
            "Replays only previously passing scalar/pointwise components. The existing 27-branch exact max-convexity certificate is reused.",
            compute,[old])


def new_d1():
    a,b,eps,s,z=sp.symbols("a b epsilon price body_value",real=True)
    hyps=[a>=0,b>=a,eps>0]
    regions=[s<=a,sp.And(s>a,s<a+eps),sp.And(s>=a+eps,s<b+eps),s>=b+eps]
    pairwise=[sp.Not(sp.And(regions[i],regions[j])) for i in range(4) for j in range(i+1,4)]
    items=[
        ("price_partition",sp.And(sp.Or(*regions),*pairwise),hyps,
         "For 0<=a<=b and epsilon>0, price<=a; a<price<a+epsilon; a+epsilon<=price<b+epsilon; price>=b+epsilon form a disjoint exhaustive partition."),
        ("terminal_atom_excluded_from_middle",sp.And(sp.Not(regions[2].subs(s,b+eps)),regions[3].subs(s,b+eps)),hyps,
         "The shifted terminal price b+epsilon belongs to the common-tail region and is excluded from the middle bound."),
        ("middle_trace_is_half_open",sp.And(s-eps>=a,s-eps<b),hyps+[regions[2]],
         "In the middle region, the shifted trace belongs to [a,b), retaining the corrected half-open terminal convention."),
        ("only_tail_buys_in_terminal_region",s>z,hyps+[regions[3],z<=b],
         "If the buyer body is bounded by b, every price>=b+epsilon strictly exceeds every body value."),
    ]
    m,eta,M1,M2=sp.symbols("m eta seller_mean1 seller_mean2",real=True)
    items.extend([
        ("second_seller_terminal_rejects_before_tail",s<b+eps,
         hyps+[sp.Or(regions[1],regions[2])],
         "Throughout the two middle price regions, the shifted high second-seller atom b+epsilon rejects."),
        ("second_buyer_body_rejects_middle",s>a,
         hyps+[sp.Or(regions[1],regions[2])],
         "Throughout the two middle price regions, the second-buyer body a rejects."),
        ("second_unit_tail_only_low_mass_bound",sp.And(m*(1-eta*eps)<=m,m*(1-eta*eps)>=0),
         [m>=0,m<=1,eta>=0,eps>0,eta*eps<=1],
         "When only the low second-seller atom trades with the escaping tail, its gain m*(1-eta*epsilon) lies between zero and m; rejection gives zero."),
        ("combined_tail_bound",2-eta*(M1+M2)<=2,
         [eta>=0,M1>=0,M2>=0],
         "When both shifted seller marginals accept a common escaping tail, their total gain 2-eta*(M1+M2) is at most 2; above the tail the gain is zero."),
    ])
    return smt_bundle(items)


def new_d1_endpoint_replay():
    m=sp.Rational(2,3);b=sp.Rational(5,6);eps=eta=sp.Rational(1,100)
    gain=1-eta*((1-m)*b+eps)
    return {"m":str(m),"b":str(b),"epsilon":str(eps),"eta":str(eta),
            "terminal_second_unit_gain":str(gain),
            "residual_to_reported_fraction":str(gain-sp.Rational(89741,90000)),
            "gain_minus_m":str(gain-m),
            "terminal_region":True,
            "all_passed":gain==sp.Rational(89741,90000) and gain>m and gain<=1}


def new_d4_algebra():
    M,G,D,beta=sp.symbols("M G D beta",real=True)
    R=(M+2)/(M+G)
    K=(beta*G-(1-beta)*M-2)/(beta*D)
    O,Op,Dp,r,rp=sp.symbols("O O_prime D_prime R R_prime",real=True)
    expression=O/D*(1-r/beta)
    derivative=sp.diff(expression,O)*Op+sp.diff(expression,D)*Dp+sp.diff(expression,r)*rp
    formula=(Op*D-O*Dp)/D**2*(1-r/beta)-O*rp/(beta*D)
    residuals={
        "normalized_comparison_ratio_identity":sp.cancel(K-(M+G)/D*(1-R/beta)),
        "comparison_coordinate_derivative":sp.cancel(derivative-formula),
        "stationarity_at_identified_trial_ratio":sp.cancel(derivative.subs({r:beta,rp:0})),
    }
    return {"residuals":{k:str(v) for k,v in residuals.items()},
            "general_derivative":str(formula),
            "premises":"Denominators are nonzero; derivative is at fixed beta. The stationarity substitution assumes R=beta and R_prime=0.",
            "all_zero":all(v==0 for v in residuals.values())}


def new_d4_smt():
    beta,D,O,R,K,E1,E2,C=sp.symbols("beta D O R K E1 E2 fixed_endpoint_constant",real=True)
    equality=sp.Eq(beta*D*K,O*(beta-R))
    positive=[beta>0,D>0,O>0,equality]
    equivalence=sp.And(sp.Implies(sp.Eq(K,0),sp.Eq(R,beta)),
                       sp.Implies(sp.Eq(R,beta),sp.Eq(K,0)))
    return smt_bundle([
        ("global_ratio_lower_bound_gives_comparison_upper_zero",K<=0,
         positive+[R>=beta],
         "Under beta>0,D>0,O>0 and beta*D*K=O*(beta-R), R>=beta implies K<=0."),
        ("attainment_at_identified_trial_ratio",equivalence,positive,
         "Under the same positive-denominator premises, K=0 iff R=beta. Thus an attained global minimum beta of R is an attained global maximum zero of K."),
        ("fixed_endpoint_energy_order",C-E1>=C-E2,[E1<=E2],
         "At fixed endpoints and fixed beta, K=constant-E reverses energy order: E1<=E2 implies K1>=K2."),
    ])


def run():
    global LEDGER
    LEDGER=tomllib.loads((ROOT/"proof_factgraph"/"ledger.toml").read_text(encoding="utf-8"))["claims"]
    # Loading the current graph here is a lookup, not a re-verification.
    graph=tomllib.loads((HERE/"factgraph.toml").read_text(encoding="utf-8"))["nodes"]
    PLAN["current_graph_nodes_read"]=len(graph)
    PLAN["tex_files_read"]=[p.name for p in [HERE/"paper.tex",HERE/"two_units.tex",
        HERE/"two_unit_pricing_proofs.tex",HERE/"two_unit_family.tex",HERE/"two_unit_computation.tex"]
        if p.is_file()]
    run_old_symbolic()
    run_old_smt()
    run_group("D1_price_regions", "The corrected four price regions are exhaustive and disjoint; the shifted terminal seller atom is assigned to the common-tail bound. The eight saved scalar implications hold.",
        ["z3","cvc5"],"D.1 price-domain and conditional gain algebra only; no measure convergence or entire realization lemma.",new_d1)
    run_group("D1_terminal_example", "For the previously reported endpoint example m=2/3,b=5/6,eta=epsilon=1/100, the second-unit terminal-tail gain is exactly 89741/90000, greater than m and at most one; this endpoint belongs to the common-tail region after the correction.",
        ["exact"],"Exact endpoint regression calculation; the old false m bound is not reasserted.",new_d1_endpoint_replay)
    run_group("D4_ratio_comparison_algebra", "For R=(M+2)/(M+G), K=(beta*G-(1-beta)*M-2)/(beta*D) equals (M+G)/D*(1-R/beta). Its coordinate derivative at fixed beta has the saved product-rule form and vanishes when R=beta and R_prime=0.",
        ["sympy"],"D.4 local identities only. Differentiability, Fermat's condition and feasible variations remain analytic premises.",new_d4_algebra)
    run_group("D4_ratio_minimum_comparison", "With positive beta,D,O and beta*D*K=O*(beta-R), R>=beta implies K<=0 and equality is equivalent to R=beta. At fixed endpoints, K=constant-E reverses energy order.",
        ["z3","cvc5"],"Scalar implication for the explicitly authorized beta=R_min branch. It does not establish existence, interiority or global uniqueness.",new_d4_smt)
    print(json.dumps({"groups":len(GROUPS),"nonpassing":[g["name"] for g in GROUPS if g["status"]!="passed"]}))


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run",action="store_true",help="Execute after the coordinator has written the TeX repairs.")
    args=parser.parse_args()
    if args.run:
        run()
    else:
        print(json.dumps(PLAN,indent=2))
