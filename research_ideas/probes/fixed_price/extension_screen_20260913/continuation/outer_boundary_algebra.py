"""Local boundary variations and compactness constants; not a proof audit."""
import hashlib
import json
from pathlib import Path
import sys
import sympy as s
from flint import arb, ctx

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
sys.path.insert(0,str(ROOT))
from hz_certify import ledger


def main():
    key='fp_ext_k2_outer_boundary_algebra_20260913'
    if ledger.already_recorded(key):
        print('Reusing '+key);return
    t,p,lam,H,x0=s.symbols('t p lam H x0',positive=True)
    c=(p-t)/2
    a=c/(t*p)
    constant=1-t/p-s.log(p)-lam*a-lam*(1+t)+lam*x0
    energy_p=-(c*H**2+lam)/(2*p**2)-2*c*H/p**2*(1-H/2)
    energy_x0=(x0*H**2+lam)-2*x0*H**2
    p1ratio=(1+3*t*t)/(1+t)**2
    residuals={
        'zero_left_contact':s.diff(constant,p)-energy_p+c*(H-2)**2/(2*p**2),
        'zero_right_contact':s.diff(constant,x0)-energy_x0-x0*H**2,
        'p_equals_one_gap':p1ratio-s.Rational(3,4)-(3*t-1)**2/(4*(1+t)**2),
        'buyer_mean_identity':2*a+1/p-1-(1/t-1),
    }
    residuals={name:str(s.simplify(value)) for name,value in residuals.items()}
    assert set(residuals.values())=={'0'}
    derivative_numerator=s.Rational(1,4)-s.Rational(3,2)/32-s.Rational(1,32)**2
    assert derivative_numerator==s.Rational(207,1024)>0
    ctx.prec=160
    m=arb(1)/32
    compact_upper=arb(3)/4*(4+2*(2/m).log())-(1-m)**2/(4*m)-2
    assert compact_upper<0
    receipt=dict(scope=__doc__,residuals=residuals,
        small_m_domain='0<m<=1/32, 0<beta<=3/4',
        positive_derivative_numerator_lower=str(derivative_numerator),
        compact_upper_at_one_over_32=str(compact_upper),
        precision_bits=ctx.prec,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    path=HERE/'results/outer_boundary_algebra.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record(key,
        'The four local boundary/mean identities in continuation/outer_boundary_algebra.py have zero symbolic residual, the stated small-m bound is increasing on (0,1/32], and its endpoint upper enclosure is strictly negative for beta<=3/4.',
        ['sympy','arb'],str(path.relative_to(ROOT)),paper='fixed-price extension screen',
        note='Boundary derivative algebra and scalar enclosure only; feasible perturbations and compactness require the mathematical argument.')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
