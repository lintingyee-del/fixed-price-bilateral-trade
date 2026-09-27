"""Exact local checks for inverse-clock calibration and endpoint equations.

The credential covers these identities, not existence of a stationary root or
a reduction from the full ordered-marginal problem.
"""
import hashlib
import json
from pathlib import Path
import sys

import sympy as s

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(ROOT))
from hz_certify import ledger


def main():
    key = 'fp_ext_k2_inverse_endpoint_algebra_20260913'
    if ledger.already_recorded(key):
        print('Reusing ' + key)
        return
    x, P, H, C, lam = s.symbols('x P H C lam', positive=True)
    first = x*H**2-P*H+C*P**2/x
    dx = lambda f: s.diff(f,x)+s.diff(f,P)*H-s.diff(f,H)*C*P/x**2
    q = x*H/P
    checks = {
        'q_derivative_quadrature': s.factor(dx(q)+first/P**2),
        'gradient_quadrature': s.factor(x*H**2/P**2-first/P**2-H/P+C/x),
    }
    d,e,h,p,pl,pr,xl,xr = s.symbols('delta e h p0 Pl Pr xl xr', positive=True)
    midtime, Y = s.symbols('Tmid Y', real=True)
    leftgrad = s.log(pl/p)+d*(1/pl-1/p)
    rightgrad = -s.log(pr)+e*(1-1/pr)
    midgrad = midtime*lam+s.log(pr/pl)-C*Y
    fullgrad = leftgrad+midgrad+rightgrad
    fullgrad = s.expand_log(fullgrad, force=True).subs(midtime*lam, xl/pl-h*xr/pr)
    checks['total_gradient_endpoint_formula'] = s.factor(
        (fullgrad+s.log(p)+C*Y+d/p-e).subs({xl:pl-d,xr:(pr-e)/h}))
    y,z,zp,zpp = s.symbols('y z zp zpp', positive=True)
    X,Xp = s.symbols('X Xp', positive=True)
    # T=[X/y^2]+2 int X/y^3, with X=exp(z).
    checks['inverse_time_integration_by_parts'] = s.factor(
        Xp/y**2-(Xp/y**2-2*X/y**3)-2*X/y**3)
    u,v = s.symbols('u v', positive=True)
    checks['inverse_derivative_Bregman_gap'] = s.factor(
        1/u-1/v+(u-v)/v**2-(u-v)**2/(u*v**2))
    # mu=f_z-(f_z')' for f=1/(y^2 z')+2 lambda exp(z)/y^3.
    mu=2*lam*s.exp(z)/y**3-2/(y**3*zp**2)-2*zpp/(y**2*zp**3)
    checks['inverse_left_contact_density'] = s.factor(mu.subs({
        z:s.log(y-d),zp:1/(y-d),zpp:-1/(y-d)**2})
        -2*(d+lam)*(y-d)/y**3)
    checks['inverse_right_contact_density'] = s.factor(mu.subs({
        z:s.log((y-e)/h),zp:1/(y-e),zpp:-1/(y-e)**2})
        -2*(h*e+lam)*(y-e)/(h*y**3))
    # z'=1/(x H), z''=-(H+x H')/(x^2 H^3).
    checks['inverse_interior_density'] = s.factor(mu.subs({
        z:s.log(x),zp:1/(x*H),zpp:-(H-C*P/x)/(x**2*H**3),y:P,
        lam:first}))
    primitive=2*(h*e+lam)/h*(-1/y+e/(2*y**2))
    checks['right_contact_mass_primitive'] = s.factor(
        s.diff(primitive,y)-2*(h*e+lam)*(y-e)/(h*y**3))
    t=s.symbols('t',positive=True)
    x0=(1-e)/h
    J=(1/pr-1)+e*(1-1/pr**2)/2
    Kh=-x0**2*h+2*(h*e+lam)*J/h**2
    checks['right_transversality_equals_contact_mass'] = s.factor(
        h*Kh+(1-e)**2-2*(h*e+lam)*J/h)
    # Envelope derivative of E at a fixed-lambda Euler minimizer.
    dc,dd,de,dh,dp,dt=s.symbols('dc dd de dh dp dt',real=True)
    c=(p-t)/2
    delta=(p+t)/2
    ep=(1+t)/2
    I0=(pr**-2-1)/(2*h)
    Ix=J/h**2
    dx0=-(x0*dh+de)/h
    dE=-(c+lam)/p**2*dc+(-(2*c+d+lam)/p**2+(d+lam)/pl**2)*dd
    dE+=(lam-x0*h*h)*dx0-2*(h*e+lam)*(Ix*dh+I0*de)
    pref=1-t/p-s.log(p)-lam*(p-t)/(2*t*p)-lam*(1+t)
    dK=s.diff(pref,p)*dp+s.diff(pref,t)*dt+lam*dx0-dE
    dK=s.expand(dK.subs({dc:(dp-dt)/2,dd:(dp+dt)/2,de:dt/2}))
    targetp=((t+lam)/p**2-(d+lam)/pl**2)/2
    targett=-1/(2*p)+lam/(2*t*t)-lam-(d+lam)/(2*pl**2)
    targett+=-x0*h/2+(h*e+lam)*(pr**-2-1)/(2*h)
    for name,coefficient,target in [('p0',dp,targetp),('t',dt,targett),('h',dh,Kh)]:
        checks['envelope_'+name]=s.factor((dK.coeff(coefficient)-target).subs({d:delta,e:ep}))
    failures={k:str(v) for k,v in checks.items() if v!=0}
    receipt={'scope':__doc__.strip(),'residuals':{k:str(v) for k,v in checks.items()},
             'failures':failures,
             'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=HERE/'results/endpoint_algebra.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record(key,
        'The endpoint quadrature, inverse-clock convex-gap and contact-density identities, and the three envelope derivatives in continuation/endpoint_algebra.py have zero symbolic residual.',
        ['sympy'] if not failures else [], str(path.relative_to(ROOT)),
        paper='fixed-price extension screen',note=receipt['scope']+(' FAILED: '+str(failures) if failures else ''))
    assert not failures, failures
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    main()
