"""Uniform Arb enclosure of interior stationary points for .72908<=beta<=.729081.

Uses the exact algebraic residual monotonicity and t bounds recorded by
branch_monotonicity.py. This is not a boundary-exhaustion or general-k2 proof.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys

from flint import arb,ctx,fmpq
from scipy.optimize import brentq

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
sys.path.insert(0,str(ROOT))
from hz_certify import ledger
from hz_certify.rigorous import as_interval,interval_str
from stationary_branch_probe import algebraic


def Q(n,d=1):return arb(fmpq(n,d))


class Jet:
    """First partial derivatives in t,p, evaluated with Arb operations."""
    def __init__(self,v,dt=0,dp=0):
        self.v=v if isinstance(v,arb) else Q(v)
        self.dt=dt if isinstance(dt,arb) else Q(dt)
        self.dp=dp if isinstance(dp,arb) else Q(dp)
    @staticmethod
    def cast(x):return x if isinstance(x,Jet) else Jet(x)
    def __add__(self,b):
        b=self.cast(b);return Jet(self.v+b.v,self.dt+b.dt,self.dp+b.dp)
    __radd__=__add__
    def __neg__(self):return Jet(-self.v,-self.dt,-self.dp)
    def __sub__(self,b):return self+-self.cast(b)
    def __rsub__(self,b):return self.cast(b)+-self
    def __mul__(self,b):
        b=self.cast(b);return Jet(self.v*b.v,self.dt*b.v+self.v*b.dt,self.dp*b.v+self.v*b.dp)
    __rmul__=__mul__
    def reciprocal(self):return Jet(1/self.v,-self.dt/self.v**2,-self.dp/self.v**2)
    def __truediv__(self,b):return self*self.cast(b).reciprocal()
    def __rtruediv__(self,b):return self.cast(b)*self.reciprocal()
    def __pow__(self,n):
        if n==0:return Jet(1)
        if n<0:return (self**(-n)).reciprocal()
        return Jet(self.v**n,n*self.v**(n-1)*self.dt,n*self.v**(n-1)*self.dp)
    def sqrt(self):
        z=self.v.sqrt();return Jet(z,self.dt/(2*z),self.dp/(2*z))
    def log(self):return Jet(self.v.log(),self.dt/self.v,self.dp/self.v)
    def atan(self):return Jet(self.v.atan(),self.dt/(1+self.v**2),self.dp/(1+self.v**2))


LAM=as_interval(F(270919,729081),F(6773,18227))
BETA=as_interval(F(18227,25000),F(729081,1000000))


def states(t,p,connection=True):
    t=Jet.cast(t);p=Jet.cast(p)
    delta=(p+t)/2;e=(1+t)/2;v=1-e
    Pl=p*((delta+LAM)/(t+LAM)).sqrt();xl=Pl-delta
    C=(LAM+delta)*xl/Pl**2
    q=2*v*v*C/(v*v+(v**4-4*(v*v-C)*v*v*C).sqrt())
    k=xl/Pl
    A=-LAM/t**2+2*LAM+1/p+(t+LAM)/p**2
    residual=-A+v*(v-q)/(e*(v+q))
    result=dict(t=t,p=p,delta=delta,e=e,v=v,Pl=Pl,xl=xl,C=C,q=q,k=k,R=residual)
    if connection and C.v>Q(1,4):
        w=(C-Q(1,4)).sqrt()
        J=(((k-Q(1,2))/w).atan()-((q-Q(1,2))/w).atan())/w
        Dk=k*k-k+C;Dq=q*q-q+C
        fun=((1-q)/(1-k)).log()+((Dk/Dq).log()+J)/2-(e/delta).log()
        h=LAM*q*(1-q)/(e*Dq);Pr=e/(1-q);xr=q*Pr/h;x0=v/h
        a=(p-t)/(2*t*p);DD=2/(1+t);m=2*t/(1+t)
        T=1/p-1/Pl+(k-q)/LAM+(1/Pr-1)/h
        M=DD*(a+T-x0);G=3-m+m*a+DD*C*J
        K=BETA*G-(1-BETA)*M-2
        result.update(connection=fun,J=J,h=h,Pr=Pr,xr=xr,x0=x0,M=M,G=G,K=K)
    return result


def residual(tb,p):
    return states(Jet(tb),Jet(as_interval(p,p)),False)['R'].v


def bracket(lo,hi,refine=False):
    tb=as_interval(lo,hi)
    if residual(tb,F(1))<0:return 'no_root',None
    mid=float((lo+hi)/2);lam=float((F(270919,729081)+F(6773,18227))/2)
    if algebraic(mid,1.,lam)['residual']>0:
        seed=brentq(lambda p:algebraic(mid,p,lam)['residual'],mid*(1+1e-9),1.)
    else:seed=1.
    middle=F(seed)
    radius=max(F(1,10**8),16*(hi-lo))
    for _ in range(14):
        pl=middle-radius;ph=min(F(1),middle+radius)
        if pl<=hi:return 'split',None
        low=residual(tb,pl);high=residual(tb,ph)
        if low<0 and (ph==1 or high>0):break
        radius*=2
    else:return 'split',None
    if refine:
        assert lo==hi
        if not high>0:return 'split',None
        for _ in range(100):
            if ph-pl<F(1,2**90):break
            pm=(pl+ph)/2;value=residual(tb,pm)
            if value>0:ph=pm
            elif value<0:pl=pm
            else:break
    return 'bracket',(pl,ph,low,high)


def box(lo,hi):
    if hi-lo>F(1,256):return None
    status,br=bracket(lo,hi)
    if status=='no_root':return {'reason':'no_algebraic_root'}
    if status!='bracket':return None
    pl,ph,low,high=br
    st=states(Jet(as_interval(lo,hi),1,0),Jet(as_interval(pl,ph),0,1))
    common={'p_bracket':[str(pl),str(ph)],'R_at_p_lower':interval_str(low),
            'R_at_p_upper':interval_str(high)}
    if st['Pl'].v>1:return {**common,'reason':'Pl_above_one','Pl':interval_str(st['Pl'].v)}
    if st['k'].v<st['q'].v:return {**common,'reason':'wrong_phase_order'}
    if 'connection' not in st:return None
    f=st['connection']
    if f.v>0 or f.v<0:
        return {**common,'reason':'connection_nonzero','connection':interval_str(f.v)}
    if hi-lo>F(1,10**7):return None
    if not high>0:return None
    Rp=st['R'].dp
    if not Rp>0:return None
    derivative=f.dt-f.dp*st['R'].dt/Rp
    if not derivative>0:return None
    return {**common,'reason':'root_candidate','connection':interval_str(f.v),
            'branch_derivative':interval_str(derivative)}


def point_connection(t):
    status,br=bracket(t,t,True)
    assert status=='bracket',(t,status)
    pl,ph,_,_=br
    st=states(Jet(as_interval(t,t),1,0),Jet(as_interval(pl,ph),0,1))
    return st['connection'].v


def main():
    key='fp_ext_k2_stationary_branch_uniform_arb_20260913'
    if ledger.already_recorded(key):
        print('Reusing '+key);return
    assert ledger.already_recorded('fp_ext_k2_branch_positive_factors_20260913')
    ctx.prec=192
    pending=[(F(1,5),F(421,1000),0)];leaves=[];unresolved=[]
    while pending:
        lo,hi,depth=pending.pop()
        result=box(lo,hi)
        if result is not None:
            leaves.append({'t_box':[str(lo),str(hi)],**result})
        elif depth>=55 or len(leaves)+len(pending)>50000:
            unresolved.append([str(lo),str(hi)])
        else:
            mid=(lo+hi)/2;pending.extend([(mid,hi,depth+1),(lo,mid,depth+1)])
        if len(leaves) and len(leaves)%2000==0:
            print(json.dumps({'finished_boxes':len(leaves),'pending':len(pending)}),flush=True)
    candidates=[row for row in leaves if row['reason']=='root_candidate']
    assert candidates and not unresolved,{'unresolved':unresolved,'candidate_count':len(candidates)}
    intervals=sorted((F(row['t_box'][0]),F(row['t_box'][1])) for row in candidates)
    assert all(a[1]==b[0] for a,b in zip(intervals[:-1],intervals[1:])),intervals
    rootlo,roothi=intervals[0][0],intervals[-1][1]
    fleft=point_connection(rootlo);fright=point_connection(roothi)
    assert fleft<0 and fright>0,(fleft,fright)
    status,br=bracket(rootlo,roothi)
    assert status=='bracket'
    pl,ph,low,high=br
    assert low<0 and high>0
    st=states(Jet(as_interval(rootlo,roothi),1,0),Jet(as_interval(pl,ph),0,1))
    df=st['connection'].dt-st['connection'].dp*st['R'].dt/st['R'].dp
    # The root cells are contiguous and each already has a positive branch
    # derivative enclosure for the whole lambda interval. Preserve that
    # covering proof instead of replacing it by a much larger hull box.
    assert all(row['reason']=='root_candidate' for row in candidates)
    assert st['Pl'].v<st['Pr'].v and st['Pr'].v<1 and st['h'].v>0 and st['h'].v<1
    # Exact coverage bookkeeping: leaves must partition the entire t interval.
    all_intervals=sorted((F(row['t_box'][0]),F(row['t_box'][1])) for row in leaves)
    assert all_intervals[0][0]==F(1,5) and all_intervals[-1][1]==F(421,1000)
    assert all(a[1]==b[0] for a,b in zip(all_intervals[:-1],all_intervals[1:]))
    receipt={'scope':__doc__.strip(),'precision_bits':192,'beta_interval':['18227/25000','729081/1000000'],
             'domain':['1/5','421/1000'],'leaf_count':len(leaves),'unresolved':unresolved,
             'root_t_interval':[str(rootlo),str(roothi)],'root_p_interval':[str(pl),str(ph)],
             'connection_left':interval_str(fleft,25),'connection_right':interval_str(fright,25),
             'root_branch_derivative_hull_diagnostic':interval_str(df,25),
             'monotonicity_certificate':'Positive branch_derivative in every contiguous retained root cell; see boxes.',
             'root_comparison_K':interval_str(st['K'].v,25),
             'root_ratio':interval_str((st['M'].v+2)/(st['M'].v+st['G'].v),25),
             'boxes':leaves,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    path=HERE/'results/stationary_branch_uniform_arb.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record(key,'For every beta in [18227/25000,729081/1000000], conditional on the recorded stationary-state identities, p0 monotonicity and 1/5<t<421/1000 bounds, the Arb cover in continuation/branch_interval_uniform.py encloses exactly one physical interior stationary point in a common admissible root strip.',
                  ['arb'],str(path.relative_to(ROOT)),paper='fixed-price extension screen',note=receipt['scope'])
    print(json.dumps({k:v for k,v in receipt.items() if k!='boxes'},indent=2),flush=True)


if __name__=='__main__':main()
