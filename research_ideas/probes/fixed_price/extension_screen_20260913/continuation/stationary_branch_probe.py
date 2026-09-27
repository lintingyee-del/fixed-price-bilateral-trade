"""Reduce the interior endpoint stationarity equations to a branch in t.

Only numerical discovery. Completeness of boundary exclusion, branch uniqueness
and the sign of the remaining transcendental connection are not certified here.
"""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import brentq

HERE=Path(__file__).resolve().parent


def algebraic(t,p,lam):
    delta=(p+t)/2;e=(1+t)/2;v=1-e
    Pl=p*np.sqrt((delta+lam)/(t+lam));xl=Pl-delta
    C=(lam+delta)*xl/Pl**2
    if C<=0:return None
    # Unique q in (0,v): f(0)>0, f(v)<0 and f'<0 on this interval.
    # Stable positive root of (v^2-C)q^2-v^2 q+v^2 C=0.
    q=2*v*v*C/(v*v+np.sqrt(v**4-4*(v*v-C)*v*v*C))
    k=xl/Pl
    A=-lam/t**2+2*lam+1/p+(t+lam)/p**2
    residual=-A+v*(v-q)/(e*(v+q))
    return dict(t=t,p0=p,delta=delta,e=e,v=v,Pl=Pl,xl=xl,C=C,q=q,k=k,
                residual=residual)


def connection(row,lam):
    C,q,k,delta,e=[row[key] for key in ['C','q','k','delta','e']]
    if not(0<q<k<1):return None
    D=lambda u:u*u-u+C
    if C>.25:
        w=np.sqrt(C-.25)
        J=(np.arctan((k-.5)/w)-np.arctan((q-.5)/w))/w
    elif C<.25:
        w=np.sqrt(.25-C)
        if not k<.5-w:return None
        primitive=lambda u:np.log(abs((u-.5-w)/(u-.5+w)))/(2*w)
        J=primitive(k)-primitive(q)
    else:
        if k>=.5:return None
        J=1/(q-.5)-1/(k-.5)
    I=np.log((1-q)/(1-k))+.5*np.log(D(k)/D(q))+.5*J
    h=lam*q*(1-q)/(e*D(q))
    Pr=e/(1-q);xr=q*Pr/h;x0=(1-e)/h
    if not(0<h<1 and row['Pl']<1 and Pr<1 and xr<x0):return None
    return dict(connection=I-np.log(e/delta),h=h,Pr=Pr,xr=xr,x0=x0,clock_length=J)


def rows_at(t,lam):
    pmax=brentq(lambda p:p*p*((p+t)/2+lam)-t-lam,t,1.)
    # Examine the whole p interval before solving sign changes, preserving
    # the number found rather than presupposing one algebraic branch.
    grid=np.linspace(t+1e-8*(pmax-t),pmax-1e-8*(pmax-t),100)
    values=[algebraic(t,p,lam)['residual'] for p in grid]
    roots=[]
    for p,q,a,b in zip(grid[:-1],grid[1:],values[:-1],values[1:]):
        if a*b<0:
            root=brentq(lambda z:algebraic(t,z,lam)['residual'],p,q,xtol=1e-14)
            row=algebraic(t,root,lam)
            conn=connection(row,lam)
            roots.append({**row,'admissible_connection_states':conn is not None,
                          **({} if conn is None else conn)})
    return roots


def main():
    lam=(1-.72908)/.72908
    ts=np.unique(np.r_[np.geomspace(.001,.15,180),np.linspace(.15,.65,700),
                        np.linspace(.65,.999,100)])
    rows=[];counts=[]
    for t in ts:
        found=rows_at(t,lam);counts.append({'t':float(t),'roots':len(found)})
        rows.extend(found)
    valid=[row for row in rows if row['admissible_connection_states']]
    crossings=[]
    for left,right in zip(valid[:-1],valid[1:]):
        if left['connection']*right['connection']<0:
            t=brentq(lambda t:rows_at(t,lam)[0]['connection'],left['t'],right['t'],xtol=1e-14)
            crossings.append(rows_at(t,lam)[0])
    receipt={'scope':__doc__.strip(),'lambda':lam,'trial_beta':.72908,
             't_samples':len(ts),'root_count_samples':counts,'algebraic_roots':rows,
             'valid_connection_states':len(valid),'connection_roots':crossings}
    (HERE/'results/stationary_branch_probe.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'t_samples':len(ts),'total_algebraic_roots':len(rows),
                      'max_algebraic_roots_per_sample':max(x['roots'] for x in counts),
                      'valid_connection_states':len(valid),'connection_roots':crossings},indent=2))


if __name__=='__main__':main()
