"""New physical-domain and reverse-substitution checks for Lemma D.6.

The pre-existing stationary root cover is an input and is not rerun. Arb
evaluates its entire rational Cartesian root hull. Exact local identities
support the coordinator's reverse construction but do not prove it globally.
"""

from fractions import Fraction
import json
from pathlib import Path
import sys
import tomllib

import sympy as sp
from flint import arb, ctx


HERE=Path(__file__).resolve().parent
MANUSCRIPT=HERE.parents[1]
ROOT=MANUSCRIPT.parents[3]
sys.path.insert(0,str(ROOT))
from hz_certify.rigorous import as_interval, interval_str

SOURCE=MANUSCRIPT/"supplement"/"stationary_uniform_cover.json"
OUTPUT=HERE/"physical_conditions.json"
DATE="2026-09-21"


def exact_components():
    q,u,C,d,xi,P=sp.symbols("q u C d xi P",real=True)
    D=q*q-q+C
    xi_q=-xi/D
    P_log_q=(xi_q/xi-sp.diff(D,q)/D)/2
    P_q=-q*P/D
    P_xi=q*P/xi
    dP_xi_q=sp.diff(P_xi,q)+sp.diff(P_xi,P)*P_q+sp.diff(P_xi,xi)*xi_q
    delta,Pl,e,v,h,p,t=sp.symbols("delta Pl e v h p t",real=True)
    ql=(Pl-delta)/Pl
    Cleft=(delta+d)*(Pl-delta)/Pl**2
    Pr=e/(1-q)
    hr=d*q*(1-q)/(e*D)
    xir=q*Pr/hr
    J=1/Pr-1+e*(1-1/Pr**2)/2
    Kh_numerator=-v*v*h+2*(h*e+d)*J
    h_target=d*(v*v*D-C*q*q)/(e*D)
    # The e+v=1 relation is imposed on both sides before cancellation.
    h_residual=sp.cancel((Kh_numerator.subs(h,hr)-h_target).subs(e,1-v))
    A=-d/t**2+2*d+1/p+(t+d)/p**2
    two_Kt=-A-v+(h*e+d)/h*(1/Pr**2-1)
    A_reduced=-A+v*(v-q)/(e*(v+q))
    difference=sp.cancel((two_Kt-A_reduced).subs(h,hr).subs(e,1-v))
    numerator,denominator=sp.fraction(difference)
    quadratic=v*v*D-C*q*q
    quotient,remainder=sp.div(sp.Poly(numerator,C),sp.Poly(quadratic,C))
    Pl_squared=p*p*(delta+d)/(t+d)
    checks={
        "quadratic_complete_square":sp.expand(u*u-u+C-((u-sp.Rational(1,2))**2+C-sp.Rational(1,4))),
        "reconstructed_logP_q":sp.cancel(P_log_q+q/D),
        "reconstructed_P_xi":sp.cancel(P_q/xi_q-P_xi),
        "reconstructed_P_xixi":sp.cancel(dP_xi_q/xi_q+C*P/xi**2),
        "left_endpoint_D_identity":sp.cancel(ql*ql-ql+Cleft-d*(Pl-delta)/Pl**2),
        "right_endpoint_xi_identity":sp.cancel(xir-Pr**2*D/d),
        "h_stationarity_numerator_factor":h_residual,
        "t_stationarity_mod_quadratic":sp.cancel(remainder.as_expr()),
        "p_stationarity_from_Pl_definition":sp.cancel((t+d)/p**2-(delta+d)/Pl_squared),
    }
    return {
        "residuals":{k:str(val) for k,val in checks.items()},
        "all_zero":all(val==0 for val in checks.values()),
        "t_stationarity_difference_factor":str(sp.cancel(quotient.as_expr()/denominator)),
        "t_stationarity_quadratic_factor":str(quadratic),
        "t_stationarity_difference_denominator":str(denominator),
        "hypotheses":[
            "D(q)=q^2-q+C; xi_q=-xi/D(q); P^2=d*xi/D(q), using the positive branch",
            "All displayed denominators are nonzero; physical signs are checked separately by Arb",
            "Left endpoint: xi_l=Pl-delta and C=(delta+d)*xi_l/Pl^2",
            "Right endpoint: Pr=e/(1-q), h=d*q*(1-q)/(e*D(q)), e+v=1",
            "h stationarity uses v^2*D(q)=C*q^2",
            "t stationarity additionally uses (delta+d)/Pl^2=(t+d)/p^2",
        ],
        "scope":"Nine new local reverse-construction and stationarity identities only; no global curve existence or boundary exhaustion.",
    }


def evaluate_box(box):
    t,p,beta=(as_interval(*box[k]) for k in ("t","p","beta"))
    d=(1-beta)/beta
    c=(p-t)/2
    delta=(p+t)/2
    e=(1+t)/2
    v=(1-t)/2
    Pl=p*((delta+d)/(t+d)).sqrt()
    xl=Pl-delta
    C=(delta+d)*xl/Pl**2
    disc=v*v-4*(v*v-C)*C
    qr=2*v*C/(v+disc.sqrt())
    ql=xl/Pl
    Dq=qr*qr-qr+C
    h=d*qr*(1-qr)/(e*Dq)
    Pr=e/(1-qr)
    xr=qr*Pr/h
    x0=v/h
    values={"t":t,"p":p,"beta":beta,"d":d,"c":c,"delta":delta,
            "e":e,"v":v,"P_l":Pl,"xi_l":xl,"C":C,
            "discriminant":disc,"q_r":qr,"q_l":ql,"D(q_r)":Dq,
            "h":h,"P_r":Pr,"xi_r":xr,"xi_0":x0}
    margins={
        "t_positive":t,"p_minus_t":p-t,"one_minus_p":1-p,
        "C_minus_one_quarter":C-arb(1)/4,
        "xi_l_minus_c":xl-c,"xi_r_minus_xi_l":xr-xl,"xi_0_minus_xi_r":x0-xr,
        "q_r_positive":qr,"q_l_minus_q_r":ql-qr,"one_minus_q_l":1-ql,
        "h_positive":h,"one_minus_h":1-h,
        "discriminant_positive":disc,"v_minus_q_r":v-qr,
    }
    return values,margins


def main():
    ledger=tomllib.loads((ROOT/"proof_factgraph"/"ledger.toml").read_text(encoding="utf-8"))["claims"]
    source=json.loads(SOURCE.read_text(encoding="utf-8"))
    exact_input={"t":source["root_t_interval"],"p":source["root_p_interval"],"beta":source["beta_interval"]}
    box={k:tuple(map(Fraction,value)) for k,value in exact_input.items()}
    ctx.prec=256
    values,margins=evaluate_box(box)
    failed=[k for k,value in margins.items() if not value>0]
    receipt={
        "date":DATE,"precision_bits":ctx.prec,
        "scope":"New physical inequalities on the entire Cartesian product of the existing exact rational root_t_interval, root_p_interval and beta_interval. Existing root isolation is reused, not rerun.",
        "input_source":SOURCE.relative_to(ROOT).as_posix(),
        "input_exact_rational_intervals":exact_input,
        "cover":{"type":"one full Cartesian box","boxes_evaluated":1,"uncovered_boxes":[] if not failed else [exact_input]},
        "formulas":{
            "d":"(1-beta)/beta","c":"(p-t)/2","delta":"(p+t)/2","e":"(1+t)/2","v":"(1-t)/2",
            "P_l":"p*sqrt((delta+d)/(t+d))","xi_l":"P_l-delta","C":"(delta+d)*xi_l/P_l^2",
            "q_r":"2*v*C/(v+sqrt(v^2-4*(v^2-C)*C))","q_l":"xi_l/P_l",
            "h":"d*q_r*(1-q_r)/(e*(q_r^2-q_r+C))","P_r":"e/(1-q_r)",
            "xi_r":"q_r*P_r/h","xi_0":"v/h",
        },
        "interval_bounds":{k:interval_str(value,40) for k,value in values.items()},
        "strict_positive_margins":{k:interval_str(value,40) for k,value in margins.items()},
        "arb_status":"proved" if not failed else "unknown",
        "failed_or_indefinite_margins":failed,
        "reused_credential":{
            "key":"fp_ext_k2_stationary_branch_uniform_arb_20260913",
            "statement":ledger["fp_ext_k2_stationary_branch_uniform_arb_20260913"]["statement"],
            "rerun":False,
        },
        "exact":exact_components(),
        "not_certified":["The old root-isolation result is not reverified", "The analytic reverse construction and gluing", "Global minimization over curves", "The general two-unit matching lower bound"],
    }
    HERE.mkdir(parents=True,exist_ok=True)
    OUTPUT.write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf-8")
    evidence=OUTPUT.relative_to(ROOT).as_posix()
    records=[{
        "key":"fpm_repair_20260921_stationary_physical_cartesian_arb",
        "statement":"On the entire exact rational Cartesian root hull saved in manuscript/supplement/stationary_uniform_cover.json, the recovery formulas satisfy 0<t<p<1, C>1/4, c<xi_l<xi_r<xi_0, 0<q_r<q_l<1, 0<h<1 and 0<q_r<v. Hence D(u)=(u-1/2)^2+C-1/4 is positive for every real u.",
        "verified":["arb"] if not failed else [],"evidence":evidence,
        "date":DATE,"paper":"fixed-price bilateral trade manuscript",
        "note":"One full Cartesian box at 256-bit Arb, not point samples. The inherited stationary root cover is not rerun. Formula-to-curve realization remains an analytic argument. Actual status "+receipt["arb_status"]+".",
    },{
        "key":"fpm_repair_20260921_stationary_reverse_construction_algebra",
        "statement":"The nine saved local identities have zero exact symbolic residual: D complete square; reconstructed (log P)_q, P_xi and P_xixi; D(q_l)=d*xi_l/P_l^2; xi_r=P_r^2*D(q_r)/d; the h-stationarity factor; the t-stationarity reduction modulo v^2*D(q_r)-C*q_r^2; and p-stationarity from the definition of P_l.",
        "verified":["sympy"] if receipt["exact"]["all_zero"] else [],
        "evidence":evidence,"date":DATE,"paper":"fixed-price bilateral trade manuscript",
        "note":"Conditional local algebra, with all denominator and stationary premises retained in the receipt. Does not certify global existence, gluing, or optimization.",
    }]
    (HERE/"pending_physical_records.json").write_text(json.dumps(records,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"arb_status":receipt["arb_status"],"failed_margins":failed,
                      "exact_all_zero":receipt["exact"]["all_zero"],
                      "margins":receipt["strict_positive_margins"]},indent=2))


if __name__=="__main__":
    main()
