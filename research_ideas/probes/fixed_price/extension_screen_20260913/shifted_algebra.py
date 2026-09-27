"""Local symbolic checks for the restricted k=2 shifted-clock derivation."""
import hashlib
import json
from pathlib import Path
import sys

import sympy as s

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sys.path.insert(0,str(ROOT))
from hz_certify import ledger


def main():
    key='fp_ext_k2_shifted_clock_algebra_20260913'
    if ledger.already_recorded(key):
        print('Reusing '+key);return
    x,P,H,Hx,D,m,p0,C,lam,delta,h=s.symbols('x P H Hx D m p0 C lam delta h',positive=True)
    a=((2-m)/m-1/p0)/2
    c=p0/2-m/(2*(2-m))
    F=D*(P-x*H)
    area=D*x/P
    dx=lambda v:s.diff(v,x)+s.diff(v,P)*H+s.diff(v,H)*Hx
    checks={
        'area_derivative_in_price':s.factor(dx(area)*P**2-F),
        'first_unit_equalizer':s.factor(F/P+H*area-D),
        'seller_cdf_derivative':s.factor(dx(F)+D*x*Hx),
        'low_price_balance':s.factor(m*(1+1/p0+2*a)-2),
        'initial_seller_atom':s.factor((2-m)*(p0-c)-m-m*a*p0),
        'gain_density':s.factor(F*H/P**2-D*H/P+D*x*H**2/P**2),
    }
    beta,T,Q,x0,ell=s.symbols('beta T Q x0 ell',real=True)
    MM=(2-m)*(a+T-x0)
    GG=2+2*m*a-(2-m)*ell-(2-m)*Q
    K=beta*GG-(1-beta)*MM-2
    const=beta*(2+2*m*a-(2-m)*ell)-(1-beta)*(2-m)*a-2+(1-beta)*(2-m)*x0
    checks['ratio_energy_reduction']=s.factor(K-(const-beta*(2-m)*(Q+(1-beta)/beta*T)))
    r,rp,zp=s.symbols('r rp zp',real=True)
    difference=x*((zp+rp)**2-zp**2)+lam/P**2*(s.exp(-2*r)-1)
    gap=x*rp**2+lam/P**2*(s.exp(-2*r)-1+2*r)+2*x*zp*rp-2*lam/P**2*r
    checks['gap_density_identity']=s.factor(difference-gap)
    first=x*H**2-P*H+C*P**2/x
    checks['Euler_first_integral']=s.factor(dx(first).subs(Hx,-C*P/x**2))
    el=P*H+x*(P*Hx-H**2)+first
    checks['Euler_equation_from_first_integral']=s.factor(el.subs(Hx,-C*P/x**2))
    q=(H/P+x*(Hx/P-H**2/P**2)+lam/P**2)
    checks['left_contact_density']=s.factor(q.subs({P:x+delta,H:1,Hx:0})-(delta+lam)/(x+delta)**2)
    checks['right_contact_density']=s.factor(q.subs({P:h*x+1/D,H:h,Hx:0})-(h/D+lam)/(h*x+1/D)**2)
    assert all(v==0 for v in checks.values()),checks
    receipt={'scope':'Twelve local symbolic identities for the explicitly restricted family and its energy comparison. No all-instance reduction, free-endpoint optimality, or full proof audit.',
             'residuals':{k:str(v) for k,v in checks.items()},
             'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    dest=HERE/'results/shifted_clock_algebra.json'
    dest.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record(key,'The twelve local identities in shifted_algebra.py, including the restricted two-unit objective reduction to positive shifted-clock log energy, have zero symbolic residual.',
                  ['sympy'],str(dest.relative_to(ROOT)),paper='fixed-price extension screen',note=receipt['scope'])
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
