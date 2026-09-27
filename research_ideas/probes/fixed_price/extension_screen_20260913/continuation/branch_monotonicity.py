"""Positive-factor certificates for algebraic branch monotonicity and compact bounds.

These algebraic bounds concern interior stationary points. They do not prove
that every restricted-family optimum is such a point.
"""
import json
from pathlib import Path
import sys
import sympy as s

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
sys.path.insert(0,str(ROOT))
from hz_certify import ledger


def main():
    key='fp_ext_k2_branch_positive_factors_20260913'
    if ledger.already_recorded(key):
        print('Reusing '+key);return
    t,p,z,lam,v,q,e,cp,fc,slack,increment,r=s.symbols(
        't p z lam v q e cp fc slack increment r',positive=True)
    delta=(p+t)/2
    zprime=z/p+z/(4*(lam+delta))
    cc=(lam+delta)*(z-delta)/z**2
    derivative=s.diff(cc,p)+s.diff(cc,z)*zprime
    cp_form=(lam+t)/p**3*(t+p/2-z+z*p/(4*(lam+delta)))
    relation=z*z*(lam+t)-p*p*(lam+delta)
    numerator=s.together(derivative-cp_form).as_numer_denom()[0]
    checks={
        'C_p_mod_left_stationarity':s.factor(s.rem(s.Poly(numerator,z),s.Poly(relation,z)).as_expr()),
        'C_p_upper_positive_gap':s.factor(t-(t+p/2-z+z*p/(4*(lam+delta)))
                              -(z-p)/2-z*(2*lam+t)/(4*(lam+delta))),
    }
    mass=v*v*(q*q-q+s.Symbol('C'))-s.Symbol('C')*q*q
    Cq=v*v*q*(1-q)/(v*v-q*q)
    f=v*(v-q)/(e*(v+q))
    fC=s.factor(s.diff(f,q)/s.diff(Cq,q))
    den=v*v*(1-2*q)+q*q
    fCform=-2*(v-q)**2/(e*den)
    checks['f_C_derivative']=s.factor(fC-fCform)
    checks['f_C_lower_positive_gap']=s.factor(fCform+2/e-4*v*q*(1-v)/(e*den))
    checks['f_C_positive_denominator']=s.factor(den-(v-q)**2-2*v*q*(1-v))
    Rp=1/p**2+2*(lam+t)/p**3+fc*cp
    lower=1/p**2+2*(lam+t)*(e-t)/(e*p**3)
    # For cp>=0, slack=t(lam+t)/p^3-cp>0 and increment=fc+2/e>0.
    checks['R_p_positive_decomposition']=s.factor((Rp-lower-2*slack/e-increment*cp)
                      .subs({slack:t*(lam+t)/p**3-cp,increment:fc+2/e}))
    # For cp<0, fc<=0 makes its contribution nonnegative directly.
    A=-lam/t**2+2*lam+1/p+(t+lam)/p**2
    expanded=s.factor((-A*p*p*t*t).subs(p,7*t/4+r))
    decomposition=lam*(1-2*t*t)*r*r+t*((s.Rational(7,2))*lam*(1-2*t*t)-t)*r
    decomposition+=t*t*((33-98*t*t)*lam/16-11*t/4)
    checks['small_t_large_p_exclusion']=s.factor(expanded-decomposition)
    checks['Pl_ratio_bound']=s.factor(43*(lam+t)-38*(lam+11*t/8)
                              -5*(lam-s.Rational(37,100))-s.Rational(37,4)*(s.Rational(1,5)-t))
    d=s.symbols('d',positive=True)
    checks['lambda_delta_ratio_bound']=s.factor(129*lam-74*(lam+d)
                              -55*(lam-s.Rational(37,100))-74*(s.Rational(11,40)-d))
    k=s.symbols('k',positive=True)
    checks['ordered_phase_mass_sign']=s.factor((v*v*(k*k-k+s.Symbol('C'))-s.Symbol('C')*k*k)
                  .subs(s.Symbol('C'),(lam+d)*k*(1-k)/d)
                  -k*(1-k)/d*(lam*v*v-(lam+d)*k*k))
    b0=s.Rational(421,1000)
    bound=lambda t:-s.Rational(3,8)/t**2+3*s.Rational(37,100)+1+t-(1-t)/(1+t)
    checks['large_t_bound_increasing']=s.factor(bound(t)-bound(b0)-(t-b0)*(
        1+s.Rational(3,8)*(t+b0)/(t*t*b0*b0)+2/((1+t)*(1+b0))))
    # Exact constants used with monotone factors on 0<t<=1/5,
    # 37/100<=lambda<=3/8. All three coefficients of the r-polynomial
    # above are positive (the middle coefficient has a positive factor t).
    constants={
        'r_squared_coefficient_lower':s.Rational(37,100)*(1-2*s.Rational(1,5)**2),
        'r_times_t_coefficient_lower':s.Rational(7,2)*s.Rational(37,100)*(1-2*s.Rational(1,5)**2)-s.Rational(1,5),
        't_squared_coefficient_lower':(33-98*s.Rational(1,5)**2)*s.Rational(37,100)/16-11*s.Rational(1,5)/4,
        'square_root_comparison_gap':s.Rational(256,225)-s.Rational(43,38),
        'k_upper_gap_below_three_tenths':s.Rational(3,10)-s.Rational(59,224),
        'phase_threshold_square_gap':s.Rational(74,129)-s.Rational(9,16),
        'large_t_exclusion_margin':bound(b0),
    }
    assert all(x==0 for x in checks.values()),checks
    assert all(x>0 for x in constants.values()),constants
    receipt={'scope':__doc__.strip(),
             'monotonicity_premises':'0<t<p<1, lambda>0, Pl>p, Pl^2(t+lambda)=p^2(delta+lambda), delta=(p+t)/2, e=(1+t)/2, v=1-e, 0<q<v, v^2(q^2-q+C)=Cq^2, C=(lambda+delta)(Pl-delta)/Pl^2.',
             'compactness_additional_premises':'37/100<=lambda<=3/8; natural t condition A=v(v-q)/(e(v+q)); q<k=(Pl-delta)/Pl.',
             'residuals':{key:str(value) for key,value in checks.items()},
             'positive_constants':{key:str(value) for key,value in constants.items()},
             'conclusions':'R_p>0 for the algebraic residual R=-A+v(v-q)/(e(v+q)). Physical stationary points satisfy 1/5<t<421/1000.',
             'R_p_positive_case':'1/p^2+2(lambda+t)(e-t)/(e p^3)+2 slack/e+increment C_p',
             'R_p_nonpositive_C_p_case':'1/p^2+2(lambda+t)/p^3+(-f_C)(-C_p)'}
    path=HERE/'results/branch_positive_factors.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record(key,'The explicit positive-factor decompositions and rational constants in continuation/branch_monotonicity.py replay exactly; under the stated stationary-state premises they prove strict p0 monotonicity of the algebraic residual and 1/5<t<421/1000 for 37/100<=lambda<=3/8.',
                  ['exact'],str(path.relative_to(ROOT)),paper='fixed-price extension screen',note=receipt['scope'])
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
