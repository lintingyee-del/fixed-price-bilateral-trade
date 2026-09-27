"""Four marginal switching potentials at the saved continuous candidate.

Reuses the stationary candidate in outer_screen.json and the existing body
price density of second_body_kernel.py. The old low-price atom is spread into
a linear density on (0,a), and the old tail atom into a uniform finite interval.
Both masses are preserved, and the densities match at a and b.
No LP, root search, or old Arb verification is rerun. New numerical values are
discovery, not a global PMP sufficiency or a universal lower-bound credential.
"""
from pathlib import Path
import json,hashlib
import numpy as np
from scipy.integrate import quad,solve_ivp
from scipy.optimize import brentq

HERE=Path(__file__).resolve().parent
CONT=HERE.parent


class Reference:
    def __init__(self):
        source=CONT/'results/outer_screen.json'
        self.source=source;self.source_sha256=hashlib.sha256(source.read_bytes()).hexdigest()
        row=json.loads(source.read_text())['root'];self.row=row
        for name,value in row.items():
            if isinstance(value,(int,float)):setattr(self,name,float(value))
        self.beta=self.ratio;self.D=2-self.m;self.p=self.p0
        self.u=self.a+1/self.p-1/self.Pl
        self.v=self.u+self.Tmid;self.b=self.a+self.T
        self.pa=self.beta*(1-self.a*((1-self.beta)/self.beta+self.t))
        self.body_masses=[self.beta*self.C*(1-self.c/self.xl),
                          self.beta*self.C*np.log(self.xr/self.xl),
                          self.beta*self.C*(1-self.xr/self.x0)]
        self.pt=1-self.pa-sum(self.body_masses)
        self.rhoa=self.beta*self.C*self.p*self.p/self.xl
        self.low_intercept=2*self.pa/self.a-self.rhoa
        self.low_slope=2*(self.rhoa-self.pa/self.a)/self.a
        self.kappa=1-self.beta
        self.tail_length=self.pt/self.kappa
        self.price_ceiling=self.b+self.tail_length
        self.seller_means=np.array([self.b-self.D*self.x0,(1-self.m)*self.b])
        self.bounds=[0.,self.a,self.u,self.v,self.b]

    def price_density(self,s):
        """Actual finite-support common price density, including both extensions."""
        if s<0 or s>self.price_ceiling:return 0.
        if s>self.b:return self.kappa
        j=min(3,max(0,int(np.searchsorted(self.bounds,s,side='right')-1)))
        return self.state(s,j)['rho']

    def euler(self,y):
        w=np.sqrt(self.C-.25);ey=np.exp(y/2)
        U=self.Pl*np.cos(w*y)+(self.xl-self.Pl/2)*np.sin(w*y)/w
        Uy=-self.Pl*w*np.sin(w*y)+(self.xl-self.Pl/2)*np.cos(w*y)
        P=ey*U;Py=ey*(U/2+Uy);x=self.xl*np.exp(y)
        return x,P,Py/x,Py/P

    def state(self,s,segment):
        if segment==0:
            return dict(A=np.array([self.m*s,self.m*s]),
                        L=np.array([self.a+1/self.p-s,1+self.a-s]),
                        F=np.array([self.m,self.m]),H=np.array([1.,1.]),
                        u=np.zeros(2),v=np.zeros(2),
                        rho=self.low_intercept+self.low_slope*s,
                        rho_prime=self.low_slope)
        if segment==1:
            P=1/(self.a+1/self.p-s);x=P-self.delta;H=1.
            u=v=0.;rho=self.beta*self.C*P*P/self.xl
            rho_prime=2*rho*P
        elif segment==2:
            target=self.ql-self.lam*(s-self.u)
            y=brentq(lambda yy:self.euler(yy)[3]-target,0,self.yr,
                     xtol=2e-14) if self.u<s<self.v else (0 if s<=self.u else self.yr)
            x,P,H,q=self.euler(y)
            u=self.D*self.C*P**3/x;v=self.C*P**3/x**2
            rho=self.beta*self.C*P*P/x
            rho_prime=rho*(2*q-1)*P*P/x
        else:
            P=1/(1/self.Pr-self.h*(s-self.v));x=(P-self.e)/self.h;H=self.h
            u=v=0.;rho=self.beta*self.C*self.xr*P*P/x**2
            rho_prime=-2*rho/(self.D*x/P)
        return dict(A=np.array([self.D*x/P,self.m*s]),L=np.array([1/P,1.]),
                    F=np.array([self.D*(P-x*H),self.m]),H=np.array([H,0.]),
                    u=np.array([u,0.]),v=np.array([v,0.]),rho=rho,rho_prime=rho_prime,
                    x=x,P=P)

    def integrals(self):
        total=np.zeros(2)
        for j,(lo,hi) in enumerate(zip(self.bounds,self.bounds[1:])):
            for i in range(2):
                total[i]+=quad(lambda s:self.state(s,j)['rho']*self.state(s,j)['H'][i],
                               lo,hi,epsabs=3e-12,epsrel=3e-12)[0]
        self.total_H=total
        sols=[];initial=np.zeros(8)
        for j,(lo,hi) in enumerate(zip(self.bounds,self.bounds[1:])):
            def ode(s,y):
                st=self.state(s,j);rho=st['rho']
                gb=y[:2]+rho*st['A']-self.beta*st['F']
                gs=rho*st['L']+total-y[2:4]-self.beta*st['H']-(1-self.beta)
                return np.r_[rho*st['F'],rho*st['H'],gb,-gs]
            sol=solve_ivp(ode,(lo,hi),initial,method='DOP853',
                          rtol=2e-12,atol=2e-13,dense_output=True,max_step=(hi-lo)/15)
            assert sol.success,sol.message
            sols.append(sol);initial=sol.y[:,-1]
        self.sols=sols
        self.buyer_anchor=sols[1].sol(self.u)[4:6].copy()
        self.buyer_anchor[1]=sols[0].sol(self.a)[5]
        self.seller_anchor=sols[1].sol(self.u)[6:8].copy()
        self.seller_anchor[1]=sols[3].sol(self.b)[7]

    def diagnostics(self,s,j):
        st=self.state(s,j);y=self.sols[j].sol(s);rho=st['rho'];rp=st['rho_prime']
        gb=y[:2]+rho*st['A']-self.beta*st['F']
        gs=rho*st['L']+self.total_H-y[2:4]-self.beta*st['H']-(1-self.beta)
        gbp=2*rho*st['F']+rp*st['A']-self.beta*st['u']
        gsp=rp*st['L']-2*rho*st['H']+self.beta*st['v']
        seller_cost=y[6:8]-self.seller_anchor
        buyer_cost=y[4:6]-self.buyer_anchor
        return dict(s=float(s),segment=j,F=st['F'].tolist(),H=st['H'].tolist(),
                    A=st['A'].tolist(),L=st['L'].tolist(),rho=float(rho),rho_prime=float(rp),
                    seller_state_gradient=gs.tolist(),buyer_state_gradient=gb.tolist(),
                    seller_gradient_derivative=gsp.tolist(),buyer_gradient_derivative=gbp.tolist(),
                    seller_atom_cost=seller_cost.tolist(),buyer_atom_cost=buyer_cost.tolist(),
                    # Global_structure's normalized max-problem switching signs.
                    xi=(-seller_cost/self.beta).tolist(),eta=(buyer_cost/self.beta).tolist(),
                    gain=float(st['F']@st['L']+st['H']@st['A']))

    def tail_diagnostics(self,t,side='right'):
        s=self.b+t;rho=self.kappa if t<self.tail_length or (t==self.tail_length and side=='left') else 0.
        cum=min(self.kappa*t,self.pt)
        alpha_b=self.sols[-1].y[:2,-1]
        A=s-self.seller_means
        gb=alpha_b+cum+rho*A-self.beta
        at_b=self.diagnostics(self.b,3)
        cb=np.array(at_b['buyer_atom_cost'])
        cs=np.array(at_b['seller_atom_cost'])
        d0=alpha_b+self.kappa*(self.b-self.seller_means)-self.beta
        active=min(t,self.tail_length)
        buyer=cb+d0*active+self.kappa*active*active
        final_slopes=alpha_b+self.pt-self.beta
        if t>self.tail_length:buyer+=final_slopes*(t-self.tail_length)
        seller=cs+self.kappa*t-cum
        return dict(s=float(s),segment=4 if t<=self.tail_length else 5,
                    rho=float(rho),rho_prime=0.,A=A.tolist(),L=[1.,1.],F=[1.,1.],H=[0.,0.],
                    seller_state_gradient=[rho-self.kappa]*2,buyer_state_gradient=gb.tolist(),
                    seller_atom_cost=seller.tolist(),buyer_atom_cost=buyer.tolist(),
                    xi=(-seller/self.beta).tolist(),eta=(buyer/self.beta).tolist(),
                    seller_ordered_pair_lower=float(seller[1]),
                    buyer_ordered_pair_lower=float(sum(buyer)),gain=2.)


def main():
    ref=Reference();ref.integrals();segments=[]
    for j,(lo,hi) in enumerate(zip(ref.bounds,ref.bounds[1:])):
        rows=[ref.diagnostics(float(s),j) for s in np.linspace(lo,hi,101)]
        bounds={}
        for key in ['seller_atom_cost','buyer_atom_cost','seller_state_gradient',
                    'buyer_state_gradient','seller_gradient_derivative','buyer_gradient_derivative']:
            v=np.array([r[key] for r in rows])
            bounds[key]=dict(min=v.min(axis=0).tolist(),max=v.max(axis=0).tolist())
        for row in rows:
            row['seller_ordered_pair_lower']=float(sum(row['seller_atom_cost']) if j==0
                                                    else row['seller_atom_cost'][1])
            row['buyer_ordered_pair_lower']=float(row['buyer_atom_cost'][1])
        segments.append(dict(segment=j,interval=[lo,hi],bounds=bounds,
                             samples=rows))
    zero=ref.diagnostics(0,0)
    rho_mass=ref.low_intercept*ref.a+ref.low_slope*ref.a**2/2
    alpha_b=ref.sols[-1].y[:2,-1]
    slopes=alpha_b+ref.pt-ref.beta
    at_b=ref.diagnostics(ref.b,3)
    d2=alpha_b[1]+ref.kappa*ref.m*ref.b-ref.beta
    minimum_t=max(0.,min(ref.tail_length,-d2/(4*ref.kappa)))
    pair_minimum=sum(at_b['buyer_atom_cost'])+d2*minimum_t+2*ref.kappa*minimum_t**2
    tail_rows=[ref.tail_diagnostics(float(t)) for t in np.linspace(0,ref.tail_length,101)]
    tail_rows += [ref.tail_diagnostics(float(t)) for t in
                  np.linspace(ref.tail_length,ref.tail_length+2*ref.b,51)[1:]]
    out=dict(scope=__doc__,actual_layer='floating discovery',
             reused_source=str(ref.source),reused_source_sha256=ref.source_sha256,
             ratio=ref.beta,parameters={key:getattr(ref,key) for key in
                 ['m','p','C','xl','xr','x0','a','u','v','b','pa','pt','rhoa',
                  'low_intercept','low_slope']},
             finite_price_support=[0.,ref.price_ceiling],
             tail_extension=dict(density=ref.kappa,length=ref.tail_length,
                 ceiling=ref.price_ceiling,alpha_at_b=alpha_b.tolist(),
                 final_buyer_slopes=slopes.tolist(),joint_final_slope=float(sum(slopes)),
                 joint_buyer_value_at_b=float(sum(at_b['buyer_atom_cost'])),
                 initial_joint_derivative=float(d2),
                 joint_buyer_minimum_t=minimum_t,joint_buyer_minimum=pair_minimum,
                 samples=tail_rows,left_at_ceiling=ref.tail_diagnostics(ref.tail_length,'left'),
                 right_at_ceiling=ref.tail_diagnostics(ref.tail_length,'right')),
             low_price_mass=rho_mass,body_price_masses=ref.body_masses,
             total_price_mass=rho_mass+sum(ref.body_masses)+ref.pt,
             joint_zero_mass_cost=sum(zero['seller_atom_cost']),
             seller_zero_mass_costs=zero['seller_atom_cost'],segments=segments,
             boundary_traces=[dict(point=ref.bounds[j],
                 left=ref.diagnostics(ref.bounds[j],j-1),
                 right=ref.diagnostics(ref.bounds[j],j)) for j in range(1,4)],
             limitations=['Finite sampled sign diagnostics only; ODE integration is floating.',
                          'No universal lower bound or second-order sufficiency.',
                          'Separate normalized atom-cost constants are coupled on the low seller-order interval and above b for ordered buyers.',
                          'The old density/Arb/root statements are reused rather than recertified.'])
    dest=HERE/'continuous_switching.json'
    dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:out[k] for k in ['ratio','parameters','finite_price_support','joint_zero_mass_cost','seller_zero_mass_costs']}))
    print(json.dumps({k:v for k,v in out['tail_extension'].items() if k not in ['samples','left_at_ceiling','right_at_ceiling']}))
    print(json.dumps([dict(segment=s['segment'],bounds=s['bounds']) for s in segments]))


if __name__=='__main__':main()
