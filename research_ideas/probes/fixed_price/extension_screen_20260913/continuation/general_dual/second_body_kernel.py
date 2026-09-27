"""Conditional second-body reduced-cost kernel at the stationary reference.

SymPy checks local identities. Arb checks explicit kernel sign hypotheses
on the already recorded uniform stationary root hull; it does not repeat
root isolation or certify a general k=2 reduction. Buyer and seller states
are fixed to the reference when the second buyer body is varied.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import sys
import sympy as sp
from flint import arb, ctx, fmpq

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parents[5]))
from hz_certify.rigorous import as_interval, interval_str


def symbolic():
    p, t, lam, beta, C, xl, a, P, x, h, e, s, xr = sp.symbols(
        'p t lambda beta C xl a P x h e s xr', positive=True)
    d = (p+t)/2
    c = (p-t)/2
    aa = c/(t*p)
    D = 2/(1+t)
    m = 2*t/(1+t)
    # The two p-stationarity relations imply C/xl=(lambda+t)/p^2.
    pi_a_raw = beta*D/m*(d*(1-C+C*c/xl)-C*(xl+d))
    pi_a_simple = beta*(1-aa*(lam+t))
    pi_a_residual = sp.factor(pi_a_raw-pi_a_simple)
    # Multiplying out leaves exactly the p-stationarity factor.
    arc_first_integral = C*(xl+d)**2/xl-d-lam
    p_stationarity = C*p*p/xl-lam-t
    pi_a_factor = beta/t*(-arc_first_integral+d*p_stationarity/p)
    checks = {'left_price_atom_factor': sp.factor(pi_a_residual-pi_a_factor)}

    rho = beta*C*P**2/xl
    ss = a+1/p-1/P
    pi_a = beta-a*beta*C*p*p/xl
    Kleft = pi_a+beta*C*(P-p)/xl+ss*rho-beta
    checks['left_kernel_positive_factor'] = sp.factor(
        Kleft-beta*C*(a+1/p)*(P**2-p**2)/xl)

    def total_dx(expr, pprime):
        return sp.diff(expr, x)+sp.diff(expr, P)*pprime

    rho_mid = beta*C*P**2/x
    rho_mid_s = total_dx(rho_mid, h)*P**2
    checks['middle_density_derivative'] = sp.factor(
        rho_mid_s-rho_mid*(2*x*h/P-1)*P**2/x)
    rho_right = beta*C*xr*P**2/x**2
    checks['right_density_derivative'] = sp.factor(
        total_dx(rho_right, h)*P**2+2*e*P*rho_right/x)
    checks['right_density_derivative'] = sp.factor(
        checks['right_density_derivative'].subs(P,h*x+e))
    # A1=D*x/P and D*e=1 on the right contact.
    checks['right_kernel_derivative'] = sp.factor(
        (2*rho_right-2*s*e*P*rho_right/x)
        -2*rho_right*(1-s/(x/(e*P))))

    # For a general fixed seller state, the buyer-body kernel is
    # alpha + A rho - beta F. Its reference q=2 form is m K.
    mass, Pi, r = sp.symbols('mass Pi r')
    checks['second_body_kernel'] = sp.expand(
        mass*Pi+mass*s*r-beta*mass-mass*(Pi+s*r-beta))

    # Price-density stationarity for the first body on the Euler arc.
    H = sp.symbols('H')
    FF = D*(P-x*H)
    AA = D*x/P
    F_x = D*C*P/x
    rho_x = beta*C*(2*P*H/x-P**2/x**2)
    checks['first_body_kernel_derivative_middle'] = sp.factor(
        2*FF*rho_mid+AA*rho_x*P**2-beta*F_x*P**2)

    # Endpoint-mass variation at S2=(0,b), buyer body a and tail moment 1.
    b, pa, pt = sp.symbols('b pa pt')
    loss0 = (1-beta)+(pa-beta)*a
    lossb = (1-beta)*b+pt-beta
    checks['second_seller_mass_derivative'] = sp.expand(
        loss0-lossb-(1-pt+a*(pa-beta)-(1-beta)*b))
    m2, bb, z, Iz = sp.symbols('m2 bb z Iz')
    low_new=1+pa*z+z*Iz-beta*(1+z)
    high_new=(1-beta)*bb+pt-beta
    new=m2*low_new+(1-m2)*high_new
    old=m*loss0+(1-m)*lossb
    J=(pa-beta)*(z-a)+z*Iz
    checks['joint_second_body_and_seller_change'] = sp.factor(
        new-old-((m2-m)*(loss0-lossb)+(1-m2)*(1-beta)*(bb-b)+m2*J))
    checks['below_floor_price_atom_gap'] = sp.expand(
        -m*a*pa-beta*m*(z-a)-m*(beta*(a-z)-a*pa))
    bad = {k:str(v) for k,v in checks.items() if v != 0}
    return {'scope':__doc__.strip(), 'residuals':{k:str(v) for k,v in checks.items()},
            'failures':bad,
            'factor_premises':['C*p^2=xl*(lambda+t)',
                               'C*(xl+delta)^2=xl*(lambda+delta)'],
            'body_variation_identity':
            'Delta(W_pi-beta O)=m E[integral_a^Z (Pi([a,s])+s rho(s)-beta) ds], a<=Z<=b',
            'below_floor_exact_difference':
            'm*(beta*(a-Z)-a*pi_a), 0<=Z<a; negative near a from below',
            'above_ceiling_linear_slope':
            'm*(1-pi_tail)-beta <= m-beta < 0 when m<beta; this direction requires changing B1 too'}


def interval_values(t,p,beta):
    lam = (1-beta)/beta
    delta=(p+t)/2; ee=(1+t)/2; v=1-ee
    Pl=p*((delta+lam)/(t+lam)).sqrt(); xl=Pl-delta
    C=(lam+delta)*xl/Pl**2
    q=2*v*v*C/(v*v+(v**4-4*(v*v-C)*v*v*C).sqrt())
    ql=xl/Pl
    h=lam*q*(1-q)/(ee*(q*q-q+C));Pr=ee/(1-q)
    xr=q*Pr/h; x0=v/h
    a=(p-t)/(2*t*p);c=(p-t)/2;m=2*t/(1+t)
    u=a+1/p-1/Pl
    w=u+(ql-q)/lam
    b=w+(1/Pr-1)/h
    pa=beta*(1-a*(lam+t))
    mass_left=beta*C*(1-c/xl)
    mass_mid=beta*C*(xr/xl).log()
    mass_right=beta*C*(1-xr/x0)
    pt=1-pa-mass_left-mass_mid-mass_right
    rhob=beta*C*xr/x0**2
    kb=1-pt+b*rhob-beta
    middle_margin=2-w*(1-2*q)*Pl**2/xl
    dm=1-pt+a*(pa-beta)-(1-beta)*b
    values=dict(a=a,u=u,w=w,b=b,m=m,Pl=Pl,Pr=Pr,xl=xl,xr=xr,x0=x0,C=C,
                ql=ql,qr=q,pi_a=pa,pi_tail=pt,
                mass_left=mass_left,mass_middle=mass_mid,mass_right=mass_right,
                left_half_margin=arb(fmpq(1,2))-ql,middle_derivative_margin=middle_margin,
                K_at_b=kb,second_seller_mass_derivative=dm,
                beta_minus_m=beta-m)
    return values


def interval_signs(subdivisions=8):
    ctx.prec = 192
    source = HERE.parent/'results/stationary_branch_uniform_arb.json'
    raw = source.read_bytes()
    old = json.loads(raw)
    tl,th = map(F, old['root_t_interval'])
    pl,ph = map(F, old['root_p_interval'])
    beta = as_interval(*map(F, old['beta_interval']))
    values={}
    for i in range(subdivisions):
        t=as_interval(tl+(th-tl)*i/subdivisions,tl+(th-tl)*(i+1)/subdivisions)
        for j in range(subdivisions):
            p=as_interval(pl+(ph-pl)*j/subdivisions,pl+(ph-pl)*(j+1)/subdivisions)
            cell=interval_values(t,p,beta)
            for name,value in cell.items():
                values[name]=value if name not in values else values[name].union(value)
    positive=['a','pi_a','pi_tail','mass_left','mass_middle','mass_right',
              'left_half_margin','middle_derivative_margin','K_at_b','beta_minus_m']
    failures=[name for name in positive if not values[name]>0]
    if not values['second_seller_mass_derivative']<0:
        failures.append('second_seller_mass_derivative_not_negative')
    return {'scope':'New explicit kernel sign inequalities on the saved stationary root hull. '
                    'The existing root-isolation result is an input, not re-run. '
                    'Only reference-state buyer variations are covered.',
            'source':str(source.relative_to(HERE.parents[5])),
            'source_sha256':hashlib.sha256(raw).hexdigest(),
            'precision_bits':ctx.prec,
            'rectangular_cells':subdivisions**2,
            'input_t':old['root_t_interval'],'input_p':old['root_p_interval'],
            'input_beta':old['beta_interval'],
            'bounds':{k:interval_str(v,25) for k,v in values.items()},
            'strict_positive':positive,'strict_negative':['second_seller_mass_derivative'],
            'failures':failures}


if __name__=='__main__':
    algebra=symbolic()
    (HERE/'results/second_body_kernel_algebra.json').write_text(json.dumps(algebra,indent=2)+'\n')
    assert not algebra['failures'],algebra['failures']
    signs=interval_signs()
    (HERE/'results/second_body_kernel_arb.json').write_text(json.dumps(signs,indent=2)+'\n')
    print(json.dumps({'algebra_failures':algebra['failures'], 'arb_failures':signs['failures'],
                      'sign_bounds':{k:signs['bounds'][k] for k in ['pi_a','pi_tail','left_half_margin',
                         'middle_derivative_margin','K_at_b','second_seller_mass_derivative']}},indent=2))
    assert not signs['failures'],signs['failures']
