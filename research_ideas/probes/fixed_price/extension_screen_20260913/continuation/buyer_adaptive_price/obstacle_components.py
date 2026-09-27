"""New exact components for the cumulative-price and energy interfaces.

Finite symbolic identities and one local coordinate-domain obstruction only;
not an audit of the contraction/compactness theorem or a calibration proof.
"""
from pathlib import Path
import hashlib
import json
import sympy as s

HERE=Path(__file__).resolve().parent


def main():
    identities={}
    def zero(name,expression):
        value=s.factor(expression)
        assert value==0,(name,value)
        identities[name]=str(value)
    # Independent expansion of the new cumulative kernel, retaining a buyer
    # and a price at the same positive event. Buyer masses are formal symbols.
    nodes=[s.Rational(0),s.Rational(2,5),s.Rational(7,5),s.Rational(3)]
    p=s.symbols('p0:4');q=s.symbols('q1:4');tau=s.symbols('tau')
    for j, seller in enumerate(nodes):
        C=1+sum(max(z-seller,0)*w for z,w in zip(nodes,p))
        m=tau+sum(q[k-1] for k in range(j+1,4))
        integral=sum((nodes[k]-seller)*p[k]*(tau+sum(q[l-1] for l in range(k+1,4))) for k in range(j+1,4))
        direct=tau+sum(q[k-1]*(1+sum((nodes[l]-seller)*p[l] for l in range(k,4))) for k in range(j+1,4))
        zero(f'cumulative_kernel_node_{j}',C*m-integral-direct)
    b,L=s.symbols('b L',nonnegative=True)
    zero('contraction_weight_bound_identity',b/(1+b)-L/(1+L)-(b-L)/((1+b)*(1+L)))
    beta,d,v,C,k,I=s.symbols('beta d v C k I',nonzero=True)
    zero('pricing_scale_relation',beta*(1-d*v/C+k/C+I/C)-(beta-(beta*d)*v/C+beta*k/C+beta*I/C))
    H,g,rho,Hp,Eprime=s.symbols('H g rho Hp Eprime')
    zero('aggregate_energy_derivative',-H*g+C*(Hp+H*rho)-(C*Hp-H*(g-C*rho)))
    t=s.symbols('t');y=s.Function('y')(t)
    zero('energy_integration_by_parts',s.diff(s.diff(y,t)/y,t)+(s.diff(y,t)/y)**2-s.diff(y,t,2)/y)
    x,z,xd,zd,xdd,zdd=s.symbols('x z xd zd xdd zdd',nonzero=True)
    H1=z*xd-x*zd;H2=(1-z)*xd+x*zd
    zero('common_clock_total_survival',H1+H2-xd)
    zero('common_clock_first_curvature',s.diff(H1,x)*xd+s.diff(H1,z)*zd+s.diff(H1,xd)*xdd+s.diff(H1,zd)*zdd-(z*xdd-x*zdd))
    zero('common_clock_second_curvature',s.diff(H2,x)*xd+s.diff(H2,z)*zd+s.diff(H2,xd)*xdd+s.diff(H2,zd)*zdd-((1-z)*xdd+x*zdd))
    zero('single_clock_energy_weight',(z*(z*xd/x-zd))**2/z**2-(z*xd/x-zd)**2)
    share,speed=s.symbols('share speed',positive=True)
    zero('reciprocal_total_coordinate_order',share/speed-(1-share)/speed-(2*share-1)/speed)
    zero('reciprocal_total_coordinate_box',1-share/speed-(speed-share)/speed)
    eps=s.symbols('eps')
    speeds=[1+2*eps,2+eps,20-14*eps]
    energy=speeds[0]/(6*speeds[1])+(speeds[0]+speeds[1])/(12*speeds[2])
    energy_curvature=s.diff(energy,eps,2).subs(eps,0)
    assert energy_curvature==s.Rational(-381,4000)
    zero('reciprocal_total_clock_length_preserved',4*speeds[0]+s.Rational(4,3)*speeds[1]+s.Rational(2,3)*speeds[2]-20)
    # One explicit equalizing probability measure; all body event prices
    # and the ideal tail column have conditional gain exactly one.
    buyer=[s.Rational(0),s.Rational(1,4),s.Rational(1,2),s.Rational(1,4)]
    cvalues=[1+sum(max(z-v,0)*p for z,p in zip(nodes,buyer)) for v in nodes]
    clock=[s.Rational(0)]
    for j in range(1,len(nodes)):
        h=sum(buyer[j:])
        clock.append(clock[-1]+(1/cvalues[j]-1/cvalues[j-1])/h)
    cdf=[1/c-clock[j]*sum(buyer[j+1:]) for j,c in enumerate(cvalues)]
    omega=[cdf[0]]+[cdf[j]-cdf[j-1] for j in range(1,len(nodes))]
    assert all(v>=0 for v in omega)
    zero('equalizer_total_mass',sum(omega)-1)
    for j,price in enumerate(nodes[1:],start=1):
        value=sum(omega[k]*(1+sum((nodes[l]-nodes[k])*buyer[l] for l in range(j,len(nodes)))) for k in range(j))
        zero(f'equalizer_body_price_{j}',value-1)
    jets=[dict(x=s.Rational(1,4),z=s.Rational(7,10),xd=1,zd=s.Rational(2,5),xdd=-2,zdd=s.Rational(-28,5)),
          dict(x=s.Rational(1,4),z=s.Rational(3,5),xd=1,zd=0,xdd=-1,zdd=s.Rational(-12,5))]
    jets.append({key:(s.sympify(jets[0][key])+s.sympify(jets[1][key]))/2 for key in jets[0]})
    jet_receipts=[]
    for jet in jets:
        values={name:s.sympify(value) for name,value in jet.items()}
        xx,zz,dx,dz,ddx,ddz=[values[key] for key in ('x','z','xd','zd','xdd','zdd')]
        h1=zz*dx-xx*dz;h2=(1-zz)*dx+xx*dz
        h1dot=zz*ddx-xx*ddz;h2dot=(1-zz)*ddx+xx*ddz
        jet_receipts.append(dict(jet={a:str(v) for a,v in values.items()},H1=str(h1),H2=str(h2),
            dot_H1=str(h1dot),dot_H2=str(h2dot),
            box_and_order=bool(0<=h2<=h1<=1),state_box=bool(0<xx<=s.Rational(1,2)<=zz<=1-xx)))
    assert all(row['box_and_order'] and row['state_box'] for row in jet_receipts)
    assert all(s.Rational(row['dot_H1'])<=0 and s.Rational(row['dot_H2'])<=0 for row in jet_receipts[:2])
    assert s.Rational(jet_receipts[2]['dot_H1'])==s.Rational(1,40)
    out=dict(scope=__doc__,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        identities=identities,local_common_clock_nonconvexity=jet_receipts,
        reciprocal_total_energy_curvature=str(energy_curvature),
        equalizer_example=dict(nodes=[str(v) for v in nodes],buyer=[str(v) for v in buyer],
                               seller=[str(v) for v in omega]),second_layer_run=False,
        development_note='The initial run stopped at the midpoint equality because Python integer division produced a float in one jet component. Explicit symbolic division corrected the checker; no mathematical identity changed.')
    (HERE/'obstacle_components.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(identities=len(identities),all_zero=True,local_midpoint_dot_H1='1/40',energy_curvature=str(energy_curvature))))


if __name__=='__main__':main()
