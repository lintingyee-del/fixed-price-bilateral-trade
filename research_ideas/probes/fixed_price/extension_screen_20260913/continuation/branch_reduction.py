"""Rational elimination of the three algebraic endpoint stationarity conditions."""
import json
from pathlib import Path
import sys
import sympy as s

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
sys.path.insert(0,str(ROOT))
from hz_certify import ledger,decide


def expressions():
    t,p=s.symbols('t p',real=True)
    lam=s.Rational(6773,18227)
    d=(p+t)/2;e=(1+t)/2;v=(1-t)/2
    A=-lam/t**2+2*lam+1/p+(t+lam)/p**2
    q=v*(v-A*e)/(v+A*e)
    C=(v-A*e)*(v+A*(1+v))/(4*A)
    B=d*(t+lam)/p**2
    Pl=(lam+d)/(C+B)
    equation=s.factor(s.together(p**2*(C+B)**2-(d+lam)*(t+lam))).as_numer_denom()[0]
    positive=lambda z:s.factor(s.together(z)).as_numer_denom()[0]*s.factor(s.together(z)).as_numer_denom()[1]>0
    # Numerator*denominator has the sign of a rational expression wherever
    # the denominator is nonzero; t,p,A and v+A e are explicitly positive.
    hypotheses=[t>0,t<1,p>t,p<1,positive(A),positive(v/e-A),
                s.Eq(equation,0),positive(Pl-p),positive(1-Pl),positive(Pl*(1-q)-d)]
    return t,p,lam,A,q,C,Pl,equation,hypotheses


def algebra():
    key='fp_ext_k2_branch_elimination_algebra_20260913'
    if ledger.already_recorded(key):
        print('Reusing '+key);return
    v,A,e,q,C=s.symbols('v A e q C',positive=True)
    qr=v*(v-A*e)/(v+A*e)
    Cr=(v-A*e)*(v+A*(1+v))/(4*A)
    checks={
        'natural_t_condition_solved_for_q':s.factor((v*(v-q)/(e*(v+q))-A).subs(q,qr)),
        'contact_condition_solved_for_C':s.factor((v*v*(q*q-q+C)-C*q*q).subs({q:qr,C:Cr}).subs(e,1-v)),
    }
    d,t,p,z,lam,B=s.symbols('d t p z lam B',positive=True)
    leftC=(lam+d)*(z-d)/z**2
    # The following two residuals are conditional on the positive left
    # natural condition z^2(t+lambda)=p^2(d+lambda).
    left_res=s.together(leftC+d*(t+lam)/p**2-(lam+d)/z).as_numer_denom()[0]
    relation=z*z*(t+lam)-p*p*(d+lam)
    checks['left_C_rewrite_mod_natural_condition']=s.rem(s.Poly(left_res,z),s.Poly(relation,z)).as_expr()
    elimination=p*p*((lam+d)/z)**2-(d+lam)*(t+lam)
    residual=s.together(elimination).as_numer_denom()[0]
    checks['squared_elimination_mod_natural_condition']=s.rem(s.Poly(residual,z),s.Poly(relation,z)).as_expr()
    assert all(s.factor(value)==0 for value in checks.values()),checks
    t,p,lam,A,q,C,Pl,poly,hyps=expressions()
    receipt={'scope':__doc__.strip()+' The physical sign conditions remain part of the branch definition; this is not global root isolation.',
             'residuals':{name:str(s.factor(value)) for name,value in checks.items()},
             'trial_beta':'18227/25000','lambda':str(lam),'A':str(A),'q':str(q),'C':str(C),'Pl':str(Pl),
             'branch_polynomial':str(poly),'polynomial_degrees':list(s.Poly(poly,t,p).degree_list()),
             'polynomial_terms':len(s.Poly(poly,t,p).terms())}
    path=HERE/'results/branch_elimination_algebra.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record(key,'The four rational identities reducing the interior algebraic endpoint stationarity conditions to the two-variable branch in continuation/branch_reduction.py have zero symbolic residual.',
                  ['sympy'],str(path.relative_to(ROOT)),paper='fixed-price extension screen',note=receipt['scope'])
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['branch_polynomial','A','q','C','Pl']},indent=2))


def box_probe():
    key='fp_ext_k2_branch_box_probe_20260913'
    if ledger.already_recorded(key):
        print('Reusing '+key);return
    t,p,lam,A,q,C,Pl,poly,hyps=expressions()
    claim=s.And(t>s.Rational(6,25),t<s.Rational(37,100),p>s.Rational(2,5),p<s.Rational(9,10))
    result=decide.prove_forall(claim,hyps,timeout_ms=20000)
    receipt={'scope':'First-layer box exclusion for the algebraic stationary branch, with beta fixed at .72908. No Euler connection or full-family boundary proof.',
             'status':result.status,'solvers':result.solvers,'note':result.note,
             'witness':None if result.witness is None else {str(k):str(v) for k,v in result.witness.items()},
             'hypotheses':[str(x) for x in hyps],'claim':str(claim)}
    path=HERE/'results/branch_box_probe.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record_decision(result,key,statement='Every physical algebraic stationary branch point specified in continuation/branch_reduction.py at beta=.72908 satisfies .24<t<.37 and .4<p0<.9.',
                           paper='fixed-price extension screen',script=str(path.relative_to(ROOT)))
    print(json.dumps({k:v for k,v in receipt.items() if k!='hypotheses'},indent=2))


if __name__=='__main__':
    algebra()
    if '--box' in sys.argv:box_probe()
