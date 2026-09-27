"""Replay the manuscript's local mathematics, with separate evidence per layer.

This does not certify the measure-theoretic or global variational arguments.
Existing research credentials are read first; this new replay is required by the
changed manuscript and the user's explicit first/second-layer review request.
"""
from pathlib import Path
import hashlib,json,sys,traceback,tomllib
import sympy as s

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sys.path[:0]=[str(ROOT),str(HERE.parent)]
from hz_certify import decide,ledger
import calibration_probe

REVISION='v2'
OUT=HERE/'checks'/('first_layer_'+REVISION+'.json')
PAPER='fixed-price bilateral trade manuscript'
PREFIX='fpm2_20260913_'


def algebra():
    checks={}
    old=calibration_probe.symbolic()
    checks.update({'calibration_'+k:s.sympify(v) for k,v in old['identities'].items()})
    C,y,I,d,S,sigma,beta,J,T,eta=s.symbols('C y I d S sigma beta J T eta',real=True)
    D=1-y+C*y*y;u=1-2*C
    Ip=-2*(C*I+2)/(C*(4*C-1));Sp=((2*C-1)*I+8*C-6)/(4*C-1)
    checks['S_derivative']=s.factor(2+I+C*Ip-Sp)
    checks['d_log_derivative']=s.factor(2/C+2/u-Ip/2-Sp/(2*C-1))
    w=s.sqrt(C-s.Rational(1,4))
    Iy=(s.atan((C*y-s.Rational(1,2))/w)+s.atan(1/(2*w)))/w
    checks['arctan_primitive_y']=s.simplify(s.diff(Iy,y)-1/D)
    ye=u/(C*(1-C));Iclosed=Iy.subs(y,ye)
    checks['arctan_full_derivative']=s.simplify(s.diff(Iclosed,C)+2*(C*Iclosed+2)/(C*(4*C-1)))
    a,P,Pp=s.symbols('a P Pp',positive=True)
    Ppp=Pp*Pp/P-Pp/a-1/(a*P)
    first=a/P**2+a*Pp/P-a*a*(Pp/P)**2
    checks['EL_first_integral']=s.factor(s.diff(first,a)+s.diff(first,P)*Pp+s.diff(first,Pp)*Ppp)
    checks['EL_power_equation']=s.factor(Ppp+first*P/a**2)
    L,K,H,Hp,TT=s.symbols('L K H Hp TT',real=True)
    diff=lambda f:s.factor(-H*s.diff(f,L)-H*H*s.diff(f,K)+Hp*s.diff(f,H)+s.diff(f,TT)/L**2)
    q=beta*(H/L+(d*d-K)/L**2);Fs=d*(1/L-H*TT)
    checks['pricing_primitive']=s.factor(diff((d*d-K)/L)-H*q/beta)
    checks['seller_CDF_derivative']=s.factor(diff(Fs)+d*TT*Hp)
    checks['seller_CDF_primitive']=s.factor(diff(d*L*TT)-Fs)
    checks['constant_price_GFT']=s.factor(Fs*L+H*d*L*TT-d)
    checks['LRW_density_attribution']=s.factor((q-(beta*(H/L-K/L**2)+(1-beta)*d/L**2)).subs(d,(1-beta)/beta))
    M=1-d*d*T;gm=d+eta*d*d*T;G=d+d*J-d**3*T
    checks['finite_affine_gap']=s.factor(gm-beta*G+beta*d*M-(d*(1-beta*J)+eta*d*d*T))
    checks['finite_welfare_gap']=s.factor((M+gm-beta*(M+G)-(d*(1-beta*J)+eta*d*d*T)).subs(beta,1/(1+d)))
    dC=-d*sigma/u;bC=-sigma/S**2
    deltaC=(dC*S-d*sigma)/S**2;slope=d*(1+S/u)
    slopeC=s.diff(slope,C)+s.diff(slope,S)*sigma+s.diff(slope,d)*dC
    checks['frontier_slope']=s.factor(deltaC/bC-slope)
    checks['frontier_slope_C']=s.factor(slopeC-d*S*(2-sigma)/u**2)
    checks['limiting_mean']=s.factor(M.subs(T,2*C/d**2)-u)
    checks['limiting_GFT']=s.factor(G.subs({T:2*C/d**2,J:S})-d*(S+u))
    kap=d*(S+u)/u
    checks['Legendre_profile']=s.factor(1/S-(d/S)/kap-1/(S+u))
    checks['profile_denominator']=s.factor((S+u-(1+C*I)).subs(S,C*(2+I)))
    g=s.symbols('g',positive=True);gy=C*y*g/D;hh=y*g/D
    checks['explicit_h_y']=s.factor(s.diff(hh,y)+s.diff(hh,g)*gy-g/D**2)
    rate=(2-3*C*y)/(C*D);num=2-3*C-4*C*y+3*C*C*y*y
    checks['nonexponential_log_rate']=s.factor((C*y/D-2*s.diff(D,y)/D)/C-rate)
    checks['nonexponential_rate_derivative']=s.factor(s.diff(rate,y)/C-num/(C*C*D*D))
    checks['nonexponential_nonzero_coefficient']=s.Poly(num,y).coeff_monomial(y*y)-3*C*C
    v=s.symbols('v',positive=True);Lerr=3/d+3/d**2+2/d**3
    checks['reciprocal_remainder']=s.factor(v/g**2-(1/g-1/(g+v))-v**2/(g**2*(g+v)))
    checks['square_reciprocal_remainder']=s.factor(2*v/g**3-(1/g**2-1/(g+v)**2)-v**2*(3*g+2*v)/(g**3*(g+v)**2))
    checks['Lipschitz_coefficient']=s.factor(1/d+3/d**2+2*(d*d+1)/d**3-Lerr)
    checks['Lipschitz_decreasing']=s.factor(s.diff(Lerr,d)+3/d**2+6/d**3+6/d**4)
    ss,bb=s.symbols('ss bb');phi=s.Function('phi')(ss,bb)
    checks['weak_mixed_product']=s.simplify(s.diff((bb-ss)*phi,ss,bb)-s.diff(phi,ss)+s.diff(phi,bb)-(bb-ss)*s.diff(phi,ss,bb))
    alpha,GM,MM,GG=s.symbols('alpha GM MM GG')
    checks['strict_gap_decomposition']=s.expand(MM+GM-beta*(MM+GG)-((1-alpha)*GM+alpha*GM-beta*GG+(1-beta)*MM))
    result={'residuals':{k:str(s.simplify(v)) for k,v in checks.items()},'Jensen_witness':old['Jensen_counterexample']}
    result['all_zero']=all(v=='0' for v in result['residuals'].values())
    return result


def sign_claims():
    C,I,y,S,d,sigma,H,L,K,a,v,Q,E,p,vp,alpha,GM,MM,GG,eta,T,beta,eps,X,Z,Lambda=s.symbols('C I y S d sigma H L K a v Q E p vp alpha GM MM GG eta T beta eps X Z Lambda',real=True)
    Sp=((2*C-1)*I+8*C-6)/(4*C-1);B=2*C-1+C*(1-C)*y
    common=[C>s.Rational(1,4),C<s.Rational(1,2),S>1,d>0,sigma<0]
    return [
      ('scalar_signs',s.And(Sp<0,Sp/(2*C-1)>0),[C>s.Rational(1,4),C<s.Rational(1,2),I>0]),
      ('envelope_lower',B<0,[C>0,C<=s.Rational(1,4),y>0,2*C*y<1]),
      ('envelope_upper',B>0,[C>=s.Rational(1,2),y>0,C*y<1]),
      ('gap_terms',a*vp*vp+E/p**2-2*Q*v>=0,[a>=0,p>0,E>=0,Q>=0,v<=0]),
      ('density_positive',H*L+d*d-K>0,[d>0,L>=d,H>=0,K<=H*(L-d)]),
      ('frontier_increasing',d*(1+S/(1-2*C))>0,common),
      ('frontier_convex',(d*S*(2-sigma)/(1-2*C)**2)/(-sigma/S**2)>0,common),
      ('seller_atom',s.And(d*eta*T>=0,d*eta*T<1),[d>0,eta>0,T>=0,T<=1/(d*(d+eta))]),
      ('strict_welfare',MM+GM-beta*(MM+GG)>0,[beta>0,beta<1,alpha>=0,alpha<1,GM>0,MM>=0,GG>=0,alpha*GM>=beta*GG-(1-beta)*MM]),
      ('smoothing_support',s.And((1-2*eps)*X+eps*Lambda+eps*Lambda*Z>0,(1-2*eps)*X+eps*Lambda+eps*Lambda*Z<Lambda),[Lambda>0,X>=0,X<=Lambda,eps>0,eps<s.Rational(1,2),Z>=-s.Rational(1,2),Z<=s.Rational(1,2)]),
    ]


def interval_and_rational():
    from flint import arb,ctx
    ctx.prec=256
    def vals(c):
        w=(c-arb(1)/4).sqrt()
        I=(((1-3*c)/(2*(1-c)*w)).atan()+(1/(2*w)).atan())/w
        S=c*(2+I);d=c*c/(1-2*c)*(-I/2).exp()
        return S-1-d,1/(1+d),d,I
    lo=arb('0.39375716251478');hi=arb('0.39375716251479')
    assert vals(lo)[0]>0 and vals(hi)[0]<0
    for _ in range(65):
        mid=(lo+hi)/2;f=vals(mid)[0]
        if f>0:lo=mid
        elif f<0:hi=mid
        else:raise ArithmeticError('undecided Arb point sign')
    center=(lo+hi)/2
    box=center+arb(0,str(float((hi-lo)/2)*1.0000001))
    assert box.contains(lo) and box.contains(hi)
    residual,beta,d,I=vals(box)
    assert beta>arb('0.73802433573445') and beta<arb('0.73802433573455')
    assert beta>arb('0.7380243357344945') and beta<arb('0.7380243357344946')
    q=s.Rational
    lower=q('0.73802433573445');upper=q('0.73802433573455')
    dlo=q(7,20);dhi=q(9,25);eta=q(1,10**12)
    assert 1/upper-1>dlo and 1/lower-1<dhi
    Lerr=3/dlo+3/dlo**2+2/dlo**3
    rbound=upper+eta*(q(37,50)*Lerr+1/dlo)
    assert rbound<q('0.738024335797')
    return {'bits':ctx.prec,'C_left':str(lo),'C_right':str(hi),'left_residual':str(vals(lo)[0]),'right_residual':str(vals(hi)[0]),'beta_enclosure':str(beta),'d_enclosure':str(d),'I_enclosure':str(I),'rational_ratio_bound':str(rbound),'remote_atom_bound':str(1+dhi/eta)}


def main():
    manifest=tomllib.loads((HERE.parent/'factgraph.toml').read_text(encoding='utf-8'))
    oldledger=tomllib.loads(ledger.LEDGER.read_text(encoding='utf-8'))['claims']
    lookup=[k for k in oldledger if k.startswith('fixed_price_') and any(t in k for t in ['calibration','frontier','profile','boundary','approximation','scalar','shape'])]
    report={'scope':'Local symbolic identities, semialgebraic implications, scalar interval and rational arithmetic only. Global and measure-theoretic arguments go to the separate second layer.','lookup_before_run':lookup,'research_nodes_read':len(manifest['nodes']),'tex_sha256':hashlib.sha256((HERE/'paper.tex').read_bytes()).hexdigest(),'groups':{},'decisions':[]}
    if OUT.exists():
        prior=json.loads(OUT.read_text())
    else:prior={}
    def run_group(name,fn,layers,statement):
        key=PREFIX+name
        if ledger.already_recorded(key):
            report['groups'][name]=prior.get('groups',{}).get(name,{'reused_ledger':key})
            return
        try:
            value=fn()
            good=value.get('all_zero',True)
            report['groups'][name]=value
            if not good:layers=[]
            evidence=str(OUT.relative_to(ROOT))+' group '+name
            ledger.record(key,statement,layers,evidence,paper=PAPER,note='Local claim only; no credential for a universal welfare theorem.')
        except Exception as e:
            report['groups'][name]={'error':repr(e),'traceback':traceback.format_exc()}
            ledger.record(key,statement,[],str(OUT.relative_to(ROOT)),paper=PAPER,note='Run returned an error; no pass credential: '+repr(e))
        OUT.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    run_group('algebra',algebra,['sympy'],'The local identities listed in manuscript/first_layer.py algebra() have zero residual, including the new EL first integral and strict-welfare decomposition.')
    for name,claim,hyps in sign_claims():
        key=PREFIX+name
        if ledger.already_recorded(key):
            old=next((v for v in prior.get('decisions',[]) if v['name']==name),{'name':name,'reused_ledger':key})
            report['decisions'].append(old);continue
        try:
            r=decide.prove_forall(claim,hyps,timeout_ms=15000)
            ledger.record_decision(r,key=key,statement=str(claim)+' under '+str(hyps),paper=PAPER,script=str(Path(__file__).relative_to(ROOT)))
            row={'name':name,'status':r.status,'solvers':r.solvers,'note':r.note,'claim':str(claim),'premises':[str(x) for x in hyps]}
        except Exception as e:
            row={'name':name,'error':repr(e)}
            ledger.record(key,str(claim)+' under '+str(hyps),[],str(OUT.relative_to(ROOT)),paper=PAPER,note='Error, no pass credential: '+repr(e))
        report['decisions'].append(row)
        OUT.write_text(json.dumps(report,indent=2,default=str)+'\n',encoding='utf-8')
    run_group('interval',interval_and_rational,['arb'],'The manuscript arctangent formula has the recorded sign bracket and beta image enclosure; this is a scalar enclosure only.')
    # Rational propagation and Jensen replay are separately identified as exact.
    for name,statement,evidence in [
      ('jensen_exact','At d=theta=1/2 the two stated rational two-step controls have Jensen gap 11/1728.','algebra.Jensen_witness'),
      ('finite_exact','Given the displayed rational beta bracket, rational propagation gives 7/20<d<9/25 and the stated finite-pair ratio and support bounds.','interval.rational_ratio_bound')]:
        key=PREFIX+name
        group='algebra' if name.startswith('jensen') else 'interval'
        if not ledger.already_recorded(key) and 'error' not in report['groups'].get(group,{}):
            ledger.record(key,statement,['exact'],str(OUT.relative_to(ROOT))+' '+evidence,paper=PAPER,note='Exact arithmetic conditional on the formulas, not their mechanism interpretation.')
    report['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    OUT.write_text(json.dumps(report,indent=2,default=str)+'\n',encoding='utf-8')
    print(json.dumps({'groups':{k:('ERROR' if 'error' in v else 'completed') for k,v in report['groups'].items()},'identities':len(report['groups'].get('algebra',{}).get('residuals',{})),'decisions':[{k:v for k,v in x.items() if k in ['name','status','solvers','error']} for x in report['decisions']],'output':str(OUT)},indent=2,default=str))


if __name__=='__main__':main()
