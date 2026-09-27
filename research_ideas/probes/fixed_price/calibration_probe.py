"""Discovery and local algebra for an obstacle-energy calibration.

This script does not certify the global variational optimum.  The coordinating
thread records actual checks in the shared ledger after inspecting this output.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path

import numpy as np
import sympy as s
from scipy.integrate import quad
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0,str(ROOT))


def symbolic():
    d, x, y, a = s.symbols("d x y a", positive=True)
    gs = d + a*x
    gt = gs + (1-a)*y
    two = a*(d+x)/gs + (1-a)*(d*d+d*y+a*x*(y-x))/(gs*gt)
    two = s.factor(two)
    hess = s.hessian(two, (x, y))
    point = {d: s.Rational(1, 2), a: s.Rational(1, 2),
             x: s.Rational(1, 2), y: s.Rational(1, 2)}
    hv = hess.subs(point)

    A, P, Pp, Ppp, p0 = s.symbols("A P Pp Ppp p0", positive=True)
    C = s.symbols("C", positive=True)
    riccati = Pp/P + A*(Ppp/P-Pp*Pp/(P*P))
    checks = {
        "two_step_formula": s.factor(two - 1 - a*(1-a)*(d+x)*(y-x)/(gs*gt)),
        "energy_Euler_singular": s.factor(
            (riccati+1/P**2).subs(Ppp, -C*P/A**2)
            - (1+P*Pp-A*Pp**2-C*P**2/A)/P**2),
        "energy_Euler_terminal": s.factor(
            (riccati+1/P**2).subs({P:p0+A, Pp:1, Ppp:0})
            -(1+p0)/(p0+A)**2),
    }
    r, rp, up, pstar = s.symbols("r rp up pstar", real=True)
    bregman = (s.exp(-2*r)-1+2*r)/pstar**2
    L_diff = (s.exp(-2*r)-1)/pstar**2+A*((up+rp)**2-up**2)
    checks["energy_gap_before_parts"] = s.expand(
        L_diff - (A*rp**2+bregman+2*A*up*rp-2*r/pstar**2))

    # Endpoint and envelope identities; the named integrals are kept symbolic.
    yy, ii, jj = s.symbols("yy ii jj", real=True)
    DD = 1-yy+C*yy**2
    dydC = (yy**3+yy*DD*jj)/2
    partial_y = lambda f: s.factor(s.diff(f,yy)+s.diff(f,ii)/DD
                                 +s.diff(f,jj)*yy**2/DD**2)
    total_C = lambda f: s.factor(s.diff(f,C)+s.diff(f,yy)*dydC
                                +s.diff(f,ii)*(-jj+dydC/DD))
    log_d = s.log(DD)/2-s.log(yy)-ii/2
    checks["endpoint_d_y"] = s.factor(partial_y(log_d)+1/(yy*DD))
    checks["endpoint_d_C_fixed_d"] = s.factor(total_C(log_d))
    integral_relation = 2*ii+yy*(yy-2)/DD-(4*C-1)*jj
    checks["integral_relation_derivative"] = partial_y(integral_relation)
    checks["integral_relation_initial"] = integral_relation.subs({yy:0,ii:0,jj:0})
    ww = (yy**2/DD+(-1+2*C*yy)*jj)/2
    jzero = yy/DD+C*jj
    checks["positive_kernel_integral_derivative"] = s.factor(partial_y(ww)-jzero)
    checks["positive_kernel_second_derivative"] = s.factor(partial_y(jzero)-1/DD**2)
    checks["D_total_positive_kernel"] = s.factor(total_C(DD)-yy*DD*(yy+ww))
    endpoint = (1-DD)/DD
    pend = yy/DD
    phi = C*ii-C**2*yy/(1-C*yy)
    phi_endpoint = 1/endpoint**2-(1+endpoint)/pend**2
    relation_i = ((4*C-1)*jj-yy*(yy-2)/DD)/2
    checks["envelope_derivative"] = s.factor(
        (total_C(phi)-phi_endpoint*total_C(endpoint)).subs(ii,relation_i))
    checks["envelope_sign_numerator"] = s.factor(
        phi_endpoint-DD*((2*C-1)+C*(1-C)*yy)/(yy*(1-C*yy)**2))
    checks["critical_curve_derivative"] = s.factor(
        s.diff((1-2*C)/(C*(1-C)),C)+1/C**2+1/(1-C)**2)
    yc = (1-2*C)/(C*(1-C))
    checks["critical_total_active_time"] = s.factor(
        (C*yy+C*DD/(1-C*yy)).subs(yy,yc)-(1-C))
    checks["critical_value"] = s.factor(
        phi.subs(yy,yc)-(C*(2+ii)-1))
    checks["endpoint_matching"] = s.factor(pend-C*pend**2*DD-endpoint)

    # An exact Jensen witness, with every control strictly inside the box.
    eps = s.Rational(1, 10)
    midpoint = two.subs(point)
    attempts = []
    for i in range(-3,4):
        for j in range(-3,4):
            left = two.subs({**point,x:s.Rational(1,2)+i*eps,y:s.Rational(1,2)+j*eps})
            right = two.subs({**point,x:s.Rational(1,2)-i*eps,y:s.Rational(1,2)-j*eps})
            attempts.append((s.factor((left+right)/2-midpoint),i,j,left,right))
    witness_gap,i,j,left,right = max(attempts)
    v = s.Matrix([i,j])
    assert all(z == 0 for z in checks.values()), checks
    assert witness_gap > 0
    return {
        "scope":"Local symbolic identities and an exact counterexample to global concavity in h. No global calibration credential.",
        "identities":{k:str(v) for k,v in checks.items()},
        "two_step_objective":str(two),
        "Hessian_at_d_half_constant_half":str(hv),
        "Hessian_determinant":str(s.factor(hv.det())),
        "Jensen_counterexample": {
            "d":"1/2", "switch_time":"1/2",
            "left_control":[str(s.Rational(1,2)+i*eps),str(s.Rational(1,2)+j*eps)],
            "right_control":[str(s.Rational(1,2)-i*eps),str(s.Rational(1,2)-j*eps)],
            "midpoint_control":["1/2","1/2"],
            "left_objective":str(left),"right_objective":str(right),
            "midpoint_objective":str(midpoint),
            "average_minus_midpoint":str(witness_gap),
            "directional_second_derivative":str((v.T*hv*v)[0])
        }
    }


def integral_I(C, y):
    if C == 0:
        return -np.log1p(-y)
    if abs(C-.25) < 1e-10:
        return y/(1-y/2)
    if C > .25:
        w = np.sqrt(C-.25)
        return (np.arctan((C*y-.5)/w)+np.arctan(.5/w))/w
    w = np.sqrt(.25-C)
    first_reciprocal = .5+w
    second_reciprocal = C/first_reciprocal
    return (np.log1p(-y*second_reciprocal)-np.log1p(-y*first_reciprocal))/(2*w)


def log_d_of(C, y):
    D = 1-y+C*y*y
    return .5*np.log(D)-np.log(y)-.5*integral_I(C,y)


def C_bar(d):
    f = lambda C: np.log(C)-.5*integral_I(C,1/C)-np.log(d)
    hi = max(1.,2*d+1)
    return brentq(f,.2500000001,hi,xtol=2e-14)


def y_for(C,d):
    if C == 0:
        return 1/(1+d)
    hi = (2/(1+np.sqrt(1-4*C)) if C <= .25 else 1/C)
    return brentq(lambda y:log_d_of(C,y)-np.log(d),
                  1e-13,hi*(1-1e-12),xtol=2e-14)


def reference_from_endpoint(d, endpoint):
    if abs(endpoint-1/d) < 1e-11:
        return {"C":0.,"y":1/(1+d),"D":d/(1+d),"I":np.log1p(1/d),
                "Ae":0.,"Aa":0.,"endpoint":endpoint,"d":d,"Phi":0.}
    cb = C_bar(d)
    def residual(C):
        y = y_for(C,d)
        D = 1-y+C*y*y
        return 1/D-1-endpoint
    C = brentq(residual,1e-10,cb*(1-1e-10),xtol=2e-13)
    y = y_for(C,d)
    D = 1-y+C*y*y
    I = integral_I(C,y)
    return {"C":C,"y":y,"D":D,"I":I,"Ae":C*y*y/D,"Aa":C/(d*d),
            "endpoint":endpoint,"d":d,"Phi":C*I-C*C*y/(1-C*y)}


def eval_reference(ref,A):
    d,C,endpoint = ref["d"],ref["C"],ref["endpoint"]
    if A <= ref["Ae"]:
        P = endpoint+A
        return P,1.,(1+endpoint)/(P*P)
    if A >= ref["Aa"]:
        return 1/d,0.,d*d
    z = A/ref["Aa"]
    logz = np.log(z)
    if C > .2500000001:
        w = np.sqrt(C-.25)
        P = np.sqrt(z)*(np.cos(w*logz)-np.sin(w*logz)/(2*w))/d
        slope = -d*np.sin(w*logz)/(w*np.sqrt(z))
    elif C < .2499999999:
        w = np.sqrt(.25-C)
        P = np.sqrt(z)*(np.cosh(w*logz)-np.sinh(w*logz)/(2*w))/d
        slope = -d*np.sinh(w*logz)/(w*np.sqrt(z))
    else:
        P = np.sqrt(z)*(1-logz/2)/d
        slope = -d*logz/np.sqrt(z)
    return P,slope,0.


def numeric():
    d = (1-.738025)/.738025
    cb = C_bar(d)
    def critical_eq(C):
        y = (1-2*C)/(C*(1-C))
        return log_d_of(C,y)-np.log(d)
    Cstar = brentq(critical_eq,.2500000001,.4999999999,xtol=2e-14)
    ystar = (1-2*Cstar)/(Cstar*(1-Cstar))
    phistar = Cstar*(2+integral_I(Cstar,ystar))-1
    rng = np.random.default_rng(20260912)
    controls = {
        "zero": np.zeros(12),
        "one": np.ones(12),
        "random": rng.uniform(0,1,12),
        "reverse_ramp": np.linspace(.95,.05,12),
        "increasing_ramp":np.linspace(.05,.95,12),
        "bang_alternating":np.array([0,1]*6,dtype=float),
        "late_spike": np.array([0]*10+[1]*2,dtype=float),
    }
    rows = []
    for label,h in controls.items():
        dt = 1/len(h)
        g = d+np.r_[0,np.cumsum(h)*dt]
        k = np.r_[0,np.cumsum(h*h)*dt]
        segA = dt/(g[:-1]*g[1:])
        A_nodes = np.r_[np.cumsum(segA[::-1])[::-1],0.]
        nval = d*d+h*g[:-1]-k[:-1]
        J = float(nval@segA)
        ep = 1/g[-1]
        ref = reference_from_endpoint(d,ep)
        AA = A_nodes[::-1]
        pp = (1/g)[::-1]
        hs = h[::-1]
        cap = max(ref["Aa"],AA[-1])
        breaks = sorted(set([0.,cap,ref["Ae"],ref["Aa"],*AA]))
        def pieces(A):
            if A >= AA[-1]:
                p,ps=1/d,0.
            else:
                ix = min(np.searchsorted(AA,A,side="right")-1,len(h)-1)
                p=pp[ix]+hs[ix]*(A-AA[ix])
                ps=hs[ix]
            P,Ps,Q=eval_reference(ref,A)
            r=np.log(p/P)
            rp=ps/p-Ps/P
            return np.array([A*rp*rp,(np.expm1(-2*r)+2*r)/(P*P),-2*Q*r])
        terms=[]
        for j in range(3):
            val=0.
            for aa,bb in zip(breaks[:-1],breaks[1:]):
                if bb>aa:
                    val += quad(lambda a:pieces(a)[j],aa,bb,epsabs=1e-11,epsrel=1e-10)[0]
            terms.append(val)
        scalar_gap=phistar-ref["Phi"]
        residual=(1+phistar-J)-(scalar_gap+sum(terms))
        rows.append({"label":label,"control":h.tolist(),"J":J,
                     "endpoint":ep,"reference_C":ref["C"],
                     "scalar_gap":scalar_gap,"energy_square":terms[0],
                     "exponential_Bregman":terms[1],"obstacle_slack":terms[2],
                     "gap_identity_residual":residual})
    return {"scope":"Floating-point discovery replay of the candidate nonnegative gap decomposition; no universal credential.",
            "d":d,"C_bar":cb,"C_star":Cstar,"J_star":1+phistar,"rows":rows}


def signs():
    from hz_certify import decide
    C,y,A,z,E,p,Q,r = s.symbols("C y A z E p Q r",real=True)
    B = 2*C-1+C*(1-C)*y
    questions = [
        ("upper_C_envelope_sign",B>0,[C>=s.Rational(1,2),y>0,C*y<1]),
        ("lower_C_envelope_sign",B<0,[C>0,C<=s.Rational(1,4),y>0,2*C*y<1]),
        ("local_gap_integrand_nonnegative",A*z*z+E/(p*p)-2*Q*r>=0,
         [A>=0,E>=0,p>0,Q>=0,r<=0]),
    ]
    rows=[]
    for name,claim,hyps in questions:
        result=decide.prove_forall(claim,hyps,timeout_ms=15000)
        rows.append({"name":name,"claim":str(claim),"assumptions":[str(h) for h in hyps],
                     "status":result.status,"votes":result.solvers})
    return {"scope":"Three scalar algebraic implications only. E>=0 must be supplied analytically for the exponential remainder.",
            "decisions":rows}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["symbolic","numeric","signs"])
    args = ap.parse_args()
    ans = {"symbolic":symbolic,"numeric":numeric,"signs":signs}[args.mode]()
    ans["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    out = HERE / ("results/calibration_"+args.mode+"_20260912.json")
    out.write_text(json.dumps(ans, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(ans, indent=2))


if __name__ == "__main__":
    main()
