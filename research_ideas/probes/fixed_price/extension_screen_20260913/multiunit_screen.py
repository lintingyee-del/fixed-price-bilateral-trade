"""Finite discovery for GdK26 (6.1) and exact finite seller-response LPs.

Nothing returned by the floating-point solvers is a universal credential.
The program's strict seller support shift is accounted for in the later replay.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path
import sys

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
OUT = HERE / 'results'
OUT.mkdir(exist_ok=True)


def dump(path, data):
    path.write_text(json.dumps(data, indent=2, default=lambda x: x.tolist()
                    if isinstance(x, np.ndarray) else float(x)) + '\n', encoding='utf-8')


def published_points(n=30, alpha=5, beta=98, tail=2500):
    return np.r_[0., (np.arange(2, n) + alpha) / beta, tail]


def order_matrix(n, k=2, seller=True):
    rows = []
    for q in range(k-1):
        for t in range(n-1):
            row = np.zeros(k*n)
            row[q*n:q*n+t+1] = -1 if seller else 1
            row[(q+1)*n:(q+1)*n+t+1] = 1 if seller else -1
            rows.append(row)
    return np.asarray(rows)


def source_arrays(points, fixed, seller=True):
    """Linear coefficients in one side of (6.1), other side fixed."""
    k, n = fixed.shape
    delta = np.maximum(points[None, :] - points[:, None], 0)
    maximum = np.maximum(points[:, None], points[None, :])
    W = np.zeros((n, k*n))
    O = np.zeros((k, n))
    for q in range(k):
        for t in range(n):
            mask = (np.arange(n)[:, None] <= t) & (np.arange(n)[None, :] > t)
            kernel = delta * mask
            W[t, q*n:(q+1)*n] = (points + kernel @ fixed[q]) if seller else (
                points @ fixed[q] + fixed[q] @ kernel)
        O[q] = maximum @ fixed[q]
    return W, O.ravel()


def source_response(points, fixed, seller=True):
    k, n = fixed.shape
    W, O = source_arrays(points, fixed, seller)
    order = order_matrix(n, k, seller)
    aub = np.r_[np.c_[W, -np.ones(n)], np.c_[-O[None, :], [0]],
                 np.c_[order, np.zeros(len(order))]]
    bub = np.r_[np.zeros(n), -1., np.zeros(len(order))]
    aeq = np.zeros((k, k*n+1))
    for q in range(k):
        aeq[q, q*n:(q+1)*n] = 1
    result = linprog(np.r_[np.zeros(k*n), 1.], A_ub=aub, b_ub=bub,
                     A_eq=aeq, b_eq=np.ones(k), bounds=[(0, None)]*(k*n)+[(0, 1)],
                     method='highs', options={'dual_feasibility_tolerance':1e-9,
                                               'primal_feasibility_tolerance':1e-9})
    if not result.success:
        source_response.last_failure = result.message
        return None
    return result.x[:-1].reshape(k, n), result.fun


def source_value(points, seller, buyer):
    W, O = source_arrays(points, buyer)
    w = W @ seller.ravel()
    opt = O @ seller.ravel()
    return float(w.max()), float(opt), w


def seed_buyer(points, seed, k=2):
    rng = np.random.default_rng(seed)
    n = len(points)
    rows = rng.dirichlet(np.full(n-1, .7), size=k)
    cdfs = np.sort(np.cumsum(rows, axis=1), axis=0)
    probs = np.diff(np.c_[np.zeros(k), cdfs], axis=1)
    tails = np.sort(rng.uniform(.12, .32, k) / points[-1])[::-1]
    return np.c_[probs * (1-tails[:, None]), tails]


def alternate(points, seeds=24, steps=100):
    records, best = [], None
    for seed in range(seeds):
        buyer = seed_buyer(points, 260913+seed)
        last = np.inf
        for it in range(steps):
            sr = source_response(points, buyer, True)
            if sr is None:
                break
            seller, _ = sr
            br = source_response(points, seller, False)
            if br is None:
                break
            buyer, value = br
            if abs(last-value) < 2e-11:
                break
            last = value
        if sr is None or br is None:
            records.append({'seed': seed, 'status': source_response.last_failure})
            print(json.dumps(records[-1]), flush=True)
            continue
        value, opt, w = source_value(points, seller, buyer)
        row = {'seed': seed, 'iterations': it+1, 'objective': value, 'OPT': opt,
               'ratio': value/opt}
        records.append(row)
        if best is None or value < best['objective']:
            best = dict(row, seller=seller, buyer=buyer, welfare=w)
            dump(OUT/'source_best.json', dict(points=points, **best,
                 scope='Alternating-LP discovery for the published (6.1), not a global minimum.'))
        print(json.dumps(row), flush=True)
    dump(OUT/'source_alternating.json', {'points':points, 'runs':records,
         'best':best, 'scope':'Floating-point discovery only'})
    return best


def gurobi_source(seconds=180, symmetric=False):
    sys.path.insert(0, str(HERE/'.deps'))
    import gurobipy as gp
    p = published_points()
    n, k = len(p), 2
    m = gp.Model('GdK26_equation_6_1')
    m.Params.NonConvex = 2
    m.Params.Threads = 4
    m.Params.TimeLimit = seconds
    m.Params.MIPGap = 1e-5
    m.Params.FeasibilityTol = 1e-8
    m.Params.OptimalityTol = 1e-8
    m.Params.Seed = 260913
    m.Params.LogFile = str(OUT/('gurobi_symmetric.log' if symmetric else 'gurobi_source.log'))
    s = m.addVars(k, n, lb=0, ub=1, name='s')
    b = {(q,j):s[k-1-q,j] for q in range(k) for j in range(n)} if symmetric else (
        m.addVars(k, n, lb=0, ub=1, name='b'))
    r = m.addVar(lb=0, ub=1, name='ratio_bound')
    initial = gp.quicksum(s[q,i]*p[i] for q in range(k) for i in range(n))
    for t in range(n):
        m.addQConstr(initial + gp.quicksum(s[q,i]*b[q,j]*(p[j]-p[i])
            for q in range(k) for i in range(t+1)
            for j in range(t if symmetric else t+1, n)) <= r, name=f'price_{t}')
    m.addQConstr(gp.quicksum(s[q,i]*b[q,j]*max(p[i],p[j]) for q in range(k)
                            for i in range(n) for j in range(n)) >= 1, name='OPT')
    for q in range(k):
        m.addConstr(gp.quicksum(s[q,i] for i in range(n)) == 1)
        if not symmetric:
            m.addConstr(gp.quicksum(b[q,i] for i in range(n)) == 1)
    for t in range(n-1):
        m.addConstr(gp.quicksum(s[0,i]-s[1,i] for i in range(t+1)) >= 0)
        if not symmetric:
            m.addConstr(gp.quicksum(b[0,i]-b[1,i] for i in range(t+1)) <= 0)
    m.setObjective(r)
    if not symmetric and (OUT/'source_best.json').exists():
        start = best_source()
        for q in range(k):
            for i in range(n):
                s[q,i].Start = start['seller'][q][i]
                b[q,i].Start = start['buyer'][q][i]
        r.Start = start['objective']
    m.optimize()
    rec = {'gurobi_version':gp.gurobi.version(), 'status':m.Status,
           'sol_count':m.SolCount, 'runtime':m.Runtime, 'symmetric':symmetric,
           'scope':'Published finite QCQP, floating-point discovery only'}
    if m.SolCount:
        rec.update(points=p, seller=np.array([[s[q,i].X for i in range(n)] for q in range(k)]),
                   buyer=np.array([[b[q,i].X for i in range(n)] for q in range(k)]),
                   objective=r.X, solver_bound=m.ObjBound)
    dump(OUT/('source_gurobi_symmetric.json' if symmetric else 'source_gurobi.json'), rec)
    return rec


def best_source():
    candidates=[]
    for name in ['source_best.json','source_slsqp.json','source_gurobi.json']:
        if (OUT/name).exists():
            item=json.loads((OUT/name).read_text())
            if 'seller' in item and 'objective' in item:
                candidates.append(item)
    return min(candidates,key=lambda v:v['objective'])


def slsqp_source(starts=6):
    from scipy.optimize import minimize
    from threadpoolctl import threadpool_limits
    p=published_points();n=len(p);k=2;dim=k*n
    scale=np.ones((k,n));scale[:,-1]=p[-1];scale=scale.ravel()
    mm=np.maximum(p[:,None],p[None,:])
    kernels=np.array([np.maximum(p[None,:]-p[:,None],0)*
        ((np.arange(n)[:,None]<=t)&(np.arange(n)[None,:]>t)) for t in range(n)])
    order_s=order_matrix(n);order_b=order_matrix(n,seller=False)
    records=[];best=best_source()
    for start in range(starts):
        rng=np.random.default_rng(9113+start)
        seller=np.asarray(best['seller']);buyer=np.asarray(best['buyer'])
        if start:
            rb=seed_buyer(p,99000+start)
            ss=source_response(p,rb)
            if ss is not None:
                seller=ss[0];buyer=rb
        r0,_,_=source_value(p,seller,buyer)
        x0=np.r_[seller.ravel()*scale,buyer.ravel()*scale,r0]
        def unpack(x):return (x[:dim]/scale).reshape(k,n),(x[dim:2*dim]/scale).reshape(k,n)
        def eq(x):
            s,b=unpack(x)
            return np.r_[s.sum(axis=1)-1,b.sum(axis=1)-1]
        jeq=np.zeros((4,2*dim+1))
        for q in range(k):
            jeq[q,q*n:(q+1)*n]=1/scale[q*n:(q+1)*n]
            jeq[q+k,dim+q*n:dim+(q+1)*n]=1/scale[q*n:(q+1)*n]
        def iq(x):
            s,b=unpack(x)
            w=(s@p).sum()+np.einsum('qi,tij,qj->t',s,kernels,b)
            opt=np.einsum('qi,ij,qj->',s,mm,b)
            return np.r_[x[-1]-w,opt-1,-order_s@s.ravel(),-order_b@b.ravel()]
        def jiq(x):
            s,b=unpack(x)
            dw_s=(p[None,None,:]+np.einsum('tij,qj->tqi',kernels,b)).reshape(n,dim)/scale
            dw_b=np.einsum('qi,tij->tqj',s,kernels).reshape(n,dim)/scale
            opt_s=(b@mm.T).ravel()/scale;opt_b=(s@mm).ravel()/scale
            return np.r_[np.c_[-dw_s,-dw_b,np.ones(n)],
                np.r_[opt_s,opt_b,0][None,:],
                np.c_[-order_s/scale,np.zeros((len(order_s),dim+1))],
                np.c_[np.zeros((len(order_b),dim)),-order_b/scale,np.zeros(len(order_b))]]
        with threadpool_limits(limits=1):
            result=minimize(lambda x:x[-1],x0,jac=lambda x:np.r_[np.zeros(2*dim),1.],
                constraints=[{'type':'eq','fun':eq,'jac':lambda x:jeq},
                             {'type':'ineq','fun':iq,'jac':jiq}],
                bounds=[(0,float(v)) for v in np.r_[scale,scale]]+[(0,1)],method='SLSQP',
                options={'maxiter':600,'ftol':1e-11})
        s,b=unpack(result.x);value,opt,w=source_value(p,s,b)
        record={'start':start,'objective':value,'OPT':opt,'success':bool(result.success),
                'message':result.message,'iterations':result.nit,
                'minimum_slack':float(min(iq(result.x))),
                'max_equality_residual':float(max(abs(eq(result.x))))}
        records.append(record);print(json.dumps(record),flush=True)
        if record['minimum_slack']>-1e-7 and value<best['objective']:
            best=dict(record,points=p,seller=s,buyer=b,welfare=w)
            dump(OUT/'source_slsqp.json',dict(best,scope='Joint SLSQP discovery, not a global optimum'))
    dump(OUT/'source_slsqp_runs.json',records)
    return best


def slsqp_symmetric(starts=8):
    from scipy.optimize import minimize
    from threadpoolctl import threadpool_limits
    p=published_points();n=len(p);k=2;dim=k*n
    scale=np.ones((k,n));scale[:,-1]=p[-1];scale=scale.ravel()
    mm=np.maximum(p[:,None],p[None,:])
    kernels=np.array([np.maximum(p[None,:]-p[:,None],0)*
        ((np.arange(n)[:,None]<=t)&(np.arange(n)[None,:]>=t)) for t in range(n)])
    order=order_matrix(n)
    records=[];best=None
    def evaluate(x):
        s=(x[:-1]/scale).reshape(k,n);b=s[::-1]
        w=(s@p).sum()+np.einsum('qi,tij,qj->t',s,kernels,b)
        opt=np.einsum('qi,ij,qj->',s,mm,b)
        return s,b,w,opt
    def eq(x):return evaluate(x)[0].sum(axis=1)-1
    jeq=np.zeros((k,dim+1))
    for q in range(k):jeq[q,q*n:(q+1)*n]=1/scale[q*n:(q+1)*n]
    def iq(x):
        s,b,w,opt=evaluate(x)
        return np.r_[x[-1]-w,opt-1,-order@s.ravel()]
    def jiq(x):
        s,b,w,opt=evaluate(x)
        dw=(p[None,None,:]+np.einsum('tij,qj->tqi',kernels,b)
             +np.einsum('qj,tji->tqi',b,kernels)).reshape(n,dim)/scale
        do=(2*b@mm).ravel()/scale
        return np.r_[np.c_[-dw,np.ones(n)],np.r_[do,0][None,:],
                     np.c_[-order/scale,np.zeros(len(order))]]
    for start in range(starts):
        s=seed_buyer(p,89100+start)[::-1]
        x0=np.r_[s.ravel()*scale,.9]
        with threadpool_limits(limits=1):
            res=minimize(lambda x:x[-1],x0,jac=lambda x:np.r_[np.zeros(dim),1.],
                constraints=[{'type':'eq','fun':eq,'jac':lambda x:jeq},
                             {'type':'ineq','fun':iq,'jac':jiq}],
                bounds=[(0,float(v)) for v in scale]+[(0,1)],method='SLSQP',
                options={'maxiter':600,'ftol':1e-11})
        s,b,w,opt=evaluate(res.x)
        record={'start':start,'objective':float(max(w)),'OPT':float(opt),
                'success':bool(res.success),'message':res.message,'iterations':res.nit,
                'minimum_slack':float(min(iq(res.x)))}
        records.append(record);print(json.dumps(record),flush=True)
        if record['minimum_slack']>-1e-7 and (best is None or max(w)<best['objective']):
            best=dict(record,points=p,seller=s,buyer=b,welfare=w,
                      scope='Symmetric finite QCQP with inclusive prices; numerical discovery')
            dump(OUT/'source_symmetric_slsqp.json',best)
    dump(OUT/'source_symmetric_slsqp_runs.json',records)
    return best


def actual_coefficients(support_s, support_b, buyer):
    k, nb = buyer.shape
    ns = len(support_s)
    prices = np.unique(np.r_[support_s, support_b])
    W = np.zeros((len(prices), k*ns))
    O = np.zeros((k, ns))
    D = np.maximum(support_b[None,:]-support_s[:,None], 0)
    for q in range(k):
        O[q] = np.maximum(support_s[:,None], support_b[None,:]) @ buyer[q]
        for t, z in enumerate(prices):
            eligible = (support_s[:,None] <= z) & (z <= support_b[None,:])
            W[t,q*ns:(q+1)*ns] = support_s + (D*eligible) @ buyer[q]
    return prices, W, O.ravel()


def seller_ratio_lp(support_s, support_b, buyer, ordered=True):
    """Charnes-Cooper minimax ratio LP; z rescales two probability marginals."""
    k, _ = buyer.shape
    ns = len(support_s)
    prices, W, O = actual_coefficients(support_s, support_b, buyer)
    order = order_matrix(ns, k) if ordered else np.empty((0,k*ns))
    # Variables y_{q,i}, z, R; sum_i y_{q,i}=z and O.y=1.
    aub = np.r_[np.c_[W,np.zeros(len(prices)),-np.ones(len(prices))],
                 np.c_[order,np.zeros((len(order),2))]]
    aeq = np.zeros((k+1,k*ns+2))
    for q in range(k):
        aeq[q,q*ns:(q+1)*ns] = 1
        aeq[q,-2] = -1
    aeq[-1,:-2] = O
    beq = np.r_[np.zeros(k),1.]
    res = linprog(np.r_[np.zeros(k*ns+1),1.], A_ub=aub,b_ub=np.zeros(len(aub)),
                  A_eq=aeq,b_eq=beq,bounds=(0,None),method='highs',
                  options={'primal_feasibility_tolerance':1e-9,
                           'dual_feasibility_tolerance':1e-9})
    if not res.success:
        return {'status':res.message}
    z = res.x[-2]
    pmf = (res.x[:-2]/z).reshape(k,ns)
    welfare_ratio = W @ res.x[:-2]
    price_dual = -res.ineqlin.marginals[:len(prices)]
    order_dual = -res.ineqlin.marginals[len(prices):]
    return {'status':'optimal finite LP', 'ratio':res.fun,'seller':pmf,
            'support_s':support_s,'support_b':support_b,'buyer':buyer,
            'prices':prices,'price_ratios':welfare_ratio,
            'active_price_indices':np.flatnonzero(res.fun-welfare_ratio < 1e-7),
            'dual_price_indices':np.flatnonzero(price_dual > 1e-8),
            'price_dual':price_dual,'order_dual':order_dual,
            'active_order_dual_indices':np.flatnonzero(order_dual > 1e-8),
            'cdf_order_gap':np.cumsum(pmf[0]-pmf[1]),
            'normalization_z':z,'OPT':1/z,
            'minimum_primal_slack':float(np.min(aub@res.x)*-1) if False else
                float(np.min(res.ineqlin.residual)),
            'scope':'Exact formulation on the specified finite supports; floating solve only'}


def seller_joint_lp(support_s, support_b, buyer):
    """Independent formulation with mass on pairs s1<=s2, same finite supports."""
    prices,W,O = actual_coefficients(support_s,support_b,buyer)
    n = len(support_s)
    pairs = [(i,j) for i in range(n) for j in range(i,n)]
    jointW = np.array([W[:,i]+W[:,n+j] for i,j in pairs]).T
    jointO = np.array([O[i]+O[n+j] for i,j in pairs])
    res = linprog(np.r_[np.zeros(len(pairs)),1.],
                  A_ub=np.c_[jointW,-np.ones(len(prices))],b_ub=np.zeros(len(prices)),
                  A_eq=np.r_[jointO,0][None,:],b_eq=[1.],bounds=(0,None),method='highs')
    return {'status':res.message,'ratio':res.fun if res.success else None,
            'joint_variables':len(pairs)}


def shape_statistics(points, seller, buyer):
    maxmat = np.maximum(points[:,None],points[None,:])
    rows=[]
    _,_,totalW=source_value(points,seller,buyer)
    for q in range(2):
        value,opt,w=source_value(points,seller[q:q+1],buyer[q:q+1])
        def describe(pmf):
            cdf=np.cumsum(pmf)
            return {'mean':float(pmf@points),'tail_mass':float(pmf[-1]),
                    'tail_mean':float(pmf[-1]*points[-1]),
                    'quantiles':{str(a):float(points[min(np.searchsorted(cdf,a),len(points)-1)])
                                 for a in [.1,.25,.5,.75,.9,.99]},
                    'positive_atoms':int(np.sum(pmf>1e-8))}
        rows.append({'unit':q+1,'seller':describe(seller[q]),'buyer':describe(buyer[q]),
                     'OPT':opt,'best_separate_welfare':value,'separate_ratio':value/opt,
                     'best_price':float(points[int(np.argmax(w))]),'welfare':w})
    return {'units':rows,'common_welfare':float(max(totalW)),
            'separate_welfare':sum(v['best_separate_welfare'] for v in rows),
            'common_price_cost':sum(v['best_separate_welfare'] for v in rows)-max(totalW),
            'seller_cdf_gap':np.cumsum(seller[0]-seller[1]),
            'buyer_cdf_gap':np.cumsum(buyer[1]-buyer[0])}


def responses():
    best=best_source()
    p=np.asarray(best['points']);s=np.asarray(best['seller']);b=np.asarray(best['buyer'])
    dump(OUT/'source_shapes.json',shape_statistics(p,s,b))
    cases=[]
    # Refine the seller support throughout the buyer support's bounded body.
    # Beyond the largest buyer value there is no reason to search for a hard seller:
    # such atoms yield ratio one and only dilute the loss.
    for subdivisions in [1,2,4,8]:
        body=np.linspace(p[1],p[-2],(len(p)-3)*subdivisions+1)
        ss=np.unique(np.r_[1e-8,p[1:-1]+1e-8,body+1e-8,p[-1]+1e-8])
        row=seller_ratio_lp(ss,p,b,True)
        row['name']=f'published_grid_buyer_seller_refinement_{subdivisions}'
        if subdivisions==1:
            row['joint_crosscheck']=seller_joint_lp(ss,p,b)
            row['unordered']=seller_ratio_lp(ss,p,b,False)
        cases.append(row)
        dump(OUT/f'seller_response_refine_{subdivisions}.json',row)
        print(json.dumps({'name':row['name'],'ratio':row.get('ratio'),
              'active_prices':len(row.get('active_price_indices',[])),
              'positive_price_duals':len(row.get('dual_price_indices',[])),
              'positive_order_duals':len(row.get('active_order_dual_indices',[]))}),flush=True)
    # Distinct ordered buyers prevent an active-set picture from being seed-specific.
    for seed in range(4):
        rb=seed_buyer(p,10913+seed)
        row=seller_ratio_lp(p+1e-8,p,rb,True)
        row['name']=f'random_ordered_buyer_{seed}'
        cases.append(row)
        dump(OUT/f'seller_response_random_{seed}.json',row)
    summary=[{'name':v['name'],'ratio':v.get('ratio'),
              'active_prices':len(v.get('active_price_indices',[])),
              'positive_price_duals':len(v.get('dual_price_indices',[])),
              'positive_order_duals':len(v.get('active_order_dual_indices',[]))} for v in cases]
    dump(OUT/'seller_response_summary.json',summary)
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('mode',choices=['alternating','slsqp','slsqp-symmetric','gurobi','symmetric','responses'])
    parser.add_argument('--seconds',type=int,default=180)
    parser.add_argument('--seeds',type=int,default=24)
    args=parser.parse_args()
    if args.mode=='alternating': alternate(published_points(),args.seeds)
    elif args.mode=='slsqp': slsqp_source(args.seeds)
    elif args.mode=='slsqp-symmetric': slsqp_symmetric(args.seeds)
    elif args.mode in ['gurobi','symmetric']:gurobi_source(args.seconds,args.mode=='symmetric')
    else:responses()
