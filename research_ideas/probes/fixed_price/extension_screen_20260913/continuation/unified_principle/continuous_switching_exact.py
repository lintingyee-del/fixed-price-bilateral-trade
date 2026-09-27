"""New components for the finite-support common-price switching construction.

Exact scope: the named rational identities only. Arb scope: the new strict
scalar sign hypotheses on the already credentialed stationary root hull.
Neither layer audits the complete measure/PMP argument or issues a universal
simultaneous-buyer-and-seller guarantee. Old root isolation and kernel sign
checks are inputs and are not rerun.
"""
from pathlib import Path
from fractions import Fraction as Q
import sys,json,hashlib
import sympy as s
from flint import arb,ctx

HERE=Path(__file__).resolve().parent;CONT=HERE.parent
sys.path.insert(0,str(CONT/'general_dual'))
from second_body_kernel import interval_values,as_interval,interval_str


def identities():
    a,z,r,p,m,B,k0,k1,k,pt,A1,A2,alpha1,alpha2,Jb,t=s.symbols(
        'a z r p m beta k0 k1 kappa pt A1 A2 alpha1 alpha2 Jb t',real=True)
    rhoa=k0+k1*a;pa=k0*a+k1*a*a/2;beta=pa+a*rhoa
    checks={}
    def check(name,expr):
        value=s.factor(s.together(expr));assert value==0,(name,value)
        checks[name]=str(value)
    check('linear_low_price_mass',a*(2*pa/a-rhoa)+a*a/2*(2*(rhoa-pa/a)/a)-pa)
    check('linear_low_price_endpoint',2*pa/a-rhoa+a*(2*(rhoa-pa/a)/a)-rhoa)
    gb=m*(2*k0*z+s.Rational(3,2)*k1*z*z-beta)
    low_b=m*(z-a)**2*(k0+k1*(z+2*a)/2)
    check('low_buyer_potential_derivative',s.diff(low_b,z)-gb)
    g1=r*(2*rhoa-k1/p-s.Rational(3,2)*k1*r)
    low_s=r*r*(rhoa-k1/(2*p)-k1*r/2)
    check('low_first_seller_potential_derivative',s.diff(low_s,r)-g1)
    g2=rhoa-1+(2*rhoa-k1)*r-s.Rational(3,2)*k1*r*r
    E=4*rhoa-k1*(1+1/p)
    Delta=12*k1*(1-rhoa)-E*E
    check('low_joint_seller_gradient',g1+g2-(rhoa-1+E*r-3*k1*r*r))
    check('low_joint_seller_negative_square',
          -(g1+g2)-(3*k1*(r-E/(6*k1))**2+Delta/(12*k1)))
    check('low_first_seller_origin_value',
          low_s.subs(r,a)-(a*pa+(pa-a*rhoa)/p))
    d2=alpha2+k*A2-B
    # alpha1=B-k*A1 is the first-buyer terminal flatness condition.
    check('tail_first_buyer_derivative',
          (alpha1+k*t+k*(A1+t)-B).subs(alpha1,B-k*A1)-2*k*t)
    check('tail_second_buyer_derivative',alpha2+k*t+k*(A2+t)-B-(d2+2*k*t))
    check('tail_joint_buyer_square',
          Jb+d2*t+2*k*t*t-(Jb-d2*d2/(8*k)+2*k*(t+d2/(4*k))**2))
    final1=alpha1+pt-B;final2=alpha2+pt-B
    check('tail_joint_final_balance',
          (final1+final2).subs(alpha2,2*B-2*pt-alpha1))
    check('tail_seller_constant_piece',k*t-k*t)
    check('tail_seller_outside_piece',k*t-pt-k*(t-pt/k))
    # Left first-buyer endpoint flatness, modulo the two saved left relations.
    tt,pp,C,xl,lam=s.symbols('t p C xl lambda',positive=True)
    delta=(pp+tt)/2;c=(pp-tt)/2;Pl=xl+delta;aa=c/(tt*pp)
    D=2/(1+tt);mm=D*tt
    pa1=1-aa*C*pp*pp/xl
    left_kernel=mm*pa1+D*delta*C*(1-c/xl)+C*D*Pl-D*delta
    check('left_buyer_endpoint_boundary_factors',
          left_kernel-D*((C*Pl*Pl/xl-lam-delta)-(C*pp*pp/xl-lam-tt)))
    # Right outer-stationary parameterization reused from branch_interval.py.
    ee,q=s.symbols('e q',positive=True);vv=1-ee
    CC=vv*vv*q*(1-q)/(vv*vv-q*q)
    hh=lam*q*(1-q)/(ee*(q*q-q+CC))
    Pr=ee/(1-q);xr=q*Pr/hh;x0=vv/hh
    check('right_terminal_price_density',CC*xr/x0**2-lam)
    check('right_seller_gradient_at_contact',
          CC*(2*hh+ee/xr-xr*hh/x0)-hh-lam)
    check('right_clock_mass_identity',
          CC*(1-xr/x0)-q+lam/hh*(1/Pr-1))
    # The saved left equations give this analogous clock identity.
    l1,l2=s.symbols('left_relation_1 left_relation_2')
    left_clock=C*(Pl-pp)/xl+lam*(1/pp-1/Pl)+xl/Pl-(1-tt/pp)
    check('left_clock_mass_boundary_factors',
          left_clock-((C*Pl*Pl/xl-lam-delta)/Pl-(C*pp*pp/xl-lam-tt)/pp))
    # Combine the clock identities to obtain exact tail-slope balance at K=0.
    TL,TR,ql,qr,Y,X0=s.symbols('TL TR ql qr Y X0',real=True)
    CL=1-tt/pp-lam*TL-ql;CR=qr-lam*TR
    T=TL+(ql-qr)/lam+TR;bb=aa+T
    bet=1/(1+lam);pa0=bet*(1-aa*(lam+tt))
    tail=1-pa0-bet*(CL+CR+C*Y)
    KK=(1-tt)/2+(tt-lam)*aa+C*Y-lam*T+lam*X0-lam*(1+tt)
    alpha1b=bet-(1-bet)*D*X0;alpha2b=mm*(1-tail)
    check('joint_tail_slope_is_minus_normalized_comparison',
          alpha1b+alpha2b+2*tail-2*bet+bet*D*KK)
    # Only the normalization algebra in the common-zero-mass envelope step.
    kval,kprime=s.symbols('K Kprime')
    Dprime=s.diff(D,tt);mprime=s.diff(mm,tt)
    check('common_zero_mass_envelope_normalization',
          -(D*kprime+Dprime*kval)/mprime-(kval-(1+tt)*kprime))
    return dict(actual_layer='exact',scope='Only the twenty named identities below.',
                identities=checks,count=len(checks),
                not_certified=['Measure-level potential inequalities and support complementarity',
                               'The envelope argument identifying the common mass derivative',
                               'PMP/Kelley necessity or sufficiency',
                               'A universal simultaneous two-side price guarantee'])


def new_signs(subdivisions=8):
    source=CONT/'results/stationary_branch_uniform_arb.json'
    raw=source.read_bytes();old=json.loads(raw)
    tl,th=map(Q,old['root_t_interval']);pl,ph=map(Q,old['root_p_interval'])
    beta=as_interval(*map(Q,old['beta_interval']));ctx.prec=192
    vals={}
    for i in range(subdivisions):
        ti=as_interval(tl+(th-tl)*i/subdivisions,tl+(th-tl)*(i+1)/subdivisions)
        for j in range(subdivisions):
            pi=as_interval(pl+(ph-pl)*j/subdivisions,pl+(ph-pl)*(j+1)/subdivisions)
            v=interval_values(ti,pi,beta)
            a,b,m,pa,pt,C,xl,x0=[v[n] for n in ['a','b','m','pi_a','pi_tail','C','xl','x0']]
            kappa=1-beta;rhoa=beta*C*pi*pi/xl
            k0=2*pa/a-rhoa;k1=2*(rhoa-pa/a)/a
            B1=2*rhoa-k1/pi
            E=4*rhoa-k1*(1+1/pi)
            phi2b=m*(b*(1-pt-beta)+a*(beta-pa))
            A1=(2-m)*x0;A2=m*b
            d2=m*(1-pt)+kappa*A2-beta
            cell=dict(low_density_intercept=k0,low_density_slope=k1,
                      low_first_seller_monotonicity_margin=B1-arb(3)*k1*a/2,
                      low_joint_seller_square_margin=12*k1*(1-rhoa)-E*E,
                      tail_buyer_first_final_slope=pt-kappa*A1,
                      tail_joint_buyer_global_quadratic_margin=phi2b-d2*d2/(8*kappa),
                      tail_density=kappa,finite_price_ceiling=b+pt/kappa,
                      second_buyer_value_at_b=phi2b)
            for name,value in cell.items():vals[name]=value if name not in vals else vals[name].union(value)
    failures=[n for n,v in vals.items() if not v>0]
    return dict(actual_layer='arb',scope='New strict scalar sign hypotheses for the low-density and finite-tail extensions, over the saved stationary root hull. Old root isolation and old kernel signs are not rerun.',
                source=str(source),source_sha256=hashlib.sha256(raw).hexdigest(),
                input_t=old['root_t_interval'],input_p=old['root_p_interval'],input_beta=old['beta_interval'],
                precision_bits=ctx.prec,cells=subdivisions**2,
                bounds={n:interval_str(v,25) for n,v in vals.items()},failures=failures)


if __name__=='__main__':
    exact=identities();signs=new_signs()
    out=dict(scope=__doc__,exact=exact,new_signs=signs,
             reused_credentials=['fp_ext_k2_second_body_kernel_arb_20260913',
                                 'fp_ext_k2_second_body_kernel_algebra_20260913',
                                 'saved stationary_branch_uniform_arb.json root hull'])
    dest=HERE/'continuous_switching_exact.json'
    if signs['failures']:dest=HERE/'continuous_switching_exact_signs_unresolved.json'
    dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(identities=exact['count'],failures=signs['failures'],bounds=signs['bounds'],receipt=str(dest)),indent=2))
    assert not signs['failures'],signs['failures']
