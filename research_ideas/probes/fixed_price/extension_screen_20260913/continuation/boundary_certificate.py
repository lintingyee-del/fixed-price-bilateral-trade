"""Exact Bernstein certificates for two straight-line degenerations.

Certifies R >= 73/100 for each whole two-parameter boundary. This does not
exhaust the boundary of the full k=2 problem or of every Euler parametrization.
"""
import hashlib
import json
from pathlib import Path
import sys
import sympy as s

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
sys.path.insert(0,str(ROOT))
from hz_certify import ledger

t,u=s.symbols('t u')


def bernstein(poly):
    poly=s.Poly(poly,t,u)
    n,m=poly.degree(t),poly.degree(u)
    out=[]
    for i in range(n+1):
        row=[]
        for j in range(m+1):
            row.append(sum(a*s.binomial(i,k)*s.binomial(j,l)
                           /(s.binomial(n,k)*s.binomial(m,l))
                           for (k,l),a in poly.terms() if k<=i and l<=j))
        out.append(row)
    return out


def certify(poly, depth=0):
    coeffs=bernstein(poly)
    if all(a>=0 for row in coeffs for a in row):
        n,m=len(coeffs)-1,len(coeffs[0])-1
        replay=sum(coeffs[i][j]*s.binomial(n,i)*t**i*(1-t)**(n-i)
                   *s.binomial(m,j)*u**j*(1-u)**(m-j)
                   for i in range(n+1) for j in range(m+1))
        assert s.Poly(poly-replay,t,u).is_zero
        return {'coefficients':[[str(a) for a in row] for row in coeffs]}
    if depth>=16:
        raise RuntimeError('Unresolved exact Bernstein box at depth '+str(depth))
    var=t if depth%2==0 else u
    return {'split':str(var),'left':certify(s.expand(poly.subs(var,var/2)),depth+1),
            'right':certify(s.expand(poly.subs(var,(1+var)/2)),depth+1)}


def leaves(tree):
    if 'coefficients' in tree:return 1
    return leaves(tree['left'])+leaves(tree['right'])


def main():
    key='fp_ext_k2_straight_boundaries_073_20260913'
    if ledger.already_recorded(key):
        print('Reusing '+key);return
    p=s.symbols('p',positive=True)
    m=2*t/(1+t);D=2/(1+t);c=(p-t)/2;d=(p+t)/2;e=(1+t)/2
    a=c/(t*p)
    records=[]
    for name in ['left','right']:
        if name=='left':
            x0=1-d;T=1/p-1;Q=d*(1-1/p)
            substitution=t+(1-t)*u
            denominator=p*t*(1+t)
        else:
            h=(p-e)/c;x0=(1-e)/h;T=(1/p-1)/h;Q=e*(1-1/p)
            substitution=e+(1-e)*u
            denominator=p*t*(1+t)*(2*p-t-1)
        M=D*(a+T-x0);G=2+2*m*a-D*Q
        expression=(M+2)-s.Rational(73,100)*(M+G)
        numerator=s.factor(expression*denominator)
        assert s.denom(numerator)==1 or s.denom(numerator).is_Integer
        polynomial=s.factor(numerator.subs(p,substitution))
        # Remove only nonnegative factors that are strictly positive in the
        # open physical domain; their exact exponents are stored for replay.
        reduced=polynomial
        factors={}
        for factor,label in [(t,'t'),(1-t,'1-t'),(u,'u'),(1-u,'1-u')]:
            count=0
            while s.rem(s.Poly(reduced,t,u),s.Poly(factor,t,u))==0:
                reduced=s.cancel(reduced/factor);count+=1
            if count:factors[label]=count
        tree=certify(s.expand(reduced))
        rec={'boundary':name,'domain':'0<t<1, 0<u<1',
             'p0_substitution':str(substitution),'M':str(s.factor(M)),
             'G':str(s.factor(G)),'positive_multiplier':str(denominator),
             'polynomial':str(polynomial),'removed_positive_factors':factors,
             'reduced_polynomial':str(reduced),'certificate':tree,'leaf_count':leaves(tree)}
        records.append(rec)
        print(json.dumps({k:v for k,v in rec.items() if k!='certificate'}),flush=True)
    receipt={'scope':__doc__.strip(),'bound':'73/100','boundaries':records,
             'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=HERE/'results/boundary_certificate.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record(key,'Both rational straight-line boundary functionals defined in continuation/boundary_certificate.py satisfy R >= 73/100 over their entire physical two-parameter domains.',
                  ['exact'],str(path.relative_to(ROOT)),paper='fixed-price extension screen',note=receipt['scope'])


if __name__=='__main__':main()
