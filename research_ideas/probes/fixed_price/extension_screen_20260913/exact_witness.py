"""Construct and replay one positive, ordered rational k=2 hard instance."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
import argparse

import numpy as np

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sys.path.insert(0,str(ROOT))
from hz_certify import ledger
from multiunit_screen import best_source


def rounded_probabilities(rows, denominator, seller):
    cdf=np.rint(np.cumsum(np.asarray(rows),axis=1)*denominator).astype(np.int64)
    cdf=np.clip(np.maximum.accumulate(cdf,axis=1),0,denominator)
    cdf[:,-1]=denominator
    if seller:
        cdf[0]=np.maximum(cdf[0],cdf[1])
    else:
        cdf[1]=np.maximum(cdf[0],cdf[1])
    return [[F(int(v),denominator) for v in row]
            for row in np.diff(np.c_[np.zeros(2,dtype=np.int64),cdf],axis=1)]


def quantile_joint(points,rows):
    cdfs=[]
    for row in rows:
        total=F(0);cdf=[]
        for v in row:total+=v;cdf.append(total)
        assert total==1
        cdfs.append(cdf)
    breaks=sorted(set([F(0)]+cdfs[0]+cdfs[1]))
    out=[]
    for left,right in zip(breaks,breaks[1:]):
        if left==right:continue
        u=(left+right)/2
        ix=[next(i for i,v in enumerate(cdf) if v>=u) for cdf in cdfs]
        out.append((right-left,(points[ix[0]],points[ix[1]])))
    return out


def main(symmetric=False, free_support=False, euler=False):
    if sum([symmetric,free_support,euler])>1:
        raise ValueError('Select exactly one source variant.')
    key=('fp_ext_k2_euler_rational_witness_v3_20260913' if euler else
         'fp_ext_k2_free_rational_witness_v2_20260913' if free_support else
         'fp_ext_k2_sym_rational_witness_v1_20260913' if symmetric else 'fp_ext_k2_rational_witness_v1_20260913')
    dest=HERE/('results/k2_euler_exact_witness_v3.json' if euler else
               'results/k2_free_exact_witness_v2.json' if free_support else
               'results/k2_sym_exact_witness_v1.json' if symmetric else 'results/k2_exact_witness_v1.json')
    if ledger.already_recorded(key):
        print('Reusing ledger credential '+key);return
    raw=(json.loads((HERE/'results/euler_finite_64.json').read_text()) if euler else
         json.loads((HERE/'results/free_support_refine_2.json').read_text()) if free_support else
         json.loads((HERE/'results/source_symmetric_slsqp.json').read_text()) if symmetric else best_source())
    n=len(raw['points']);denom=10**15 if euler else 10**12
    eps=F(1,10**10 if (free_support or euler) else 10**8)
    points=([F(round(p*denom),denom) for p in raw['points']] if (free_support or euler) else
            [F(0)]+[F(i+5,98) for i in range(2,n)]+[F(2500)])
    assert all(x+eps<y for x,y in zip(points,points[1:]))
    s_points=[p+eps for p in points]
    b_points=s_points.copy() if symmetric else points.copy()
    if not symmetric:b_points[0]=eps/2
    s=rounded_probabilities(raw['seller'],denom,True)
    b=s[::-1] if symmetric else rounded_probabilities(raw['buyer'],denom,False)
    sj=quantile_joint(s_points,s);bj=quantile_joint(b_points,b)
    assert all(0<v[0]<=v[1] for _,v in sj)
    assert all(v[0]>=v[1]>0 for _,v in bj)
    assert sum(w for w,_ in sj)==sum(w for w,_ in bj)==1
    if symmetric:
        assert sj==[(w,v[::-1]) for w,v in bj]
    initial=sum(s[q][i]*s_points[i] for q in range(2) for i in range(n))
    opt=sum(s[q][i]*b[q][j]*max(s_points[i],b_points[j])
            for q in range(2) for i in range(n) for j in range(n))
    prices=sorted(set(s_points+b_points))
    w_by_price=[];unit_profiles=[[],[]]
    for price in prices:
        gains=[sum(s[q][i]*b[q][j]*(b_points[j]-s_points[i])
                     for i in range(n) for j in range(n)
                     if s_points[i]<=price<=b_points[j]) for q in range(2)]
        w_by_price.append(initial+sum(gains))
        for q in range(2):
            unit_profiles[q].append(sum(s[q][i]*s_points[i] for i in range(n))+gains[q])
    opt_joint=sum(ws*wb*sum(max(sv[q],bv[q]) for q in range(2))
                  for ws,sv in sj for wb,bv in bj)
    assert opt_joint==opt
    # Independent sequential-mechanism replay on the joint value vectors.
    for price,wanted in zip(prices,w_by_price):
        actual=F(0)
        for ws,sv in sj:
            for wb,bv in bj:
                welfare=sum(sv)
                for q in range(2):
                    if sv[q]<=price<=bv[q]:welfare+=bv[q]-sv[q]
                    else:break
                actual+=ws*wb*welfare
        assert actual==wanted
    ratio=max(w_by_price)/opt
    bound=(F(182271,250000) if euler else F(91137,125000) if free_support else
           F(83693,100000) if symmetric else F(9114,12500))
    assert ratio<bound
    if symmetric:assert ratio<F(2093,2500)  # 0.8372, GdK26 symmetric k=2 upper bound
    else:assert ratio<F(1823,2500)  # 0.7292, published single-unit guarantee
    separate=sum(max(row) for row in unit_profiles)/opt
    receipt={'scope':'Specified rational finite instance, all real prices via finite support events; no claim of global k=2 optimality.',
             'source_objective':raw['objective'],'denominator':denom,'seller_shift':str(eps),'symmetric':symmetric,
             'free_support':free_support,'euler_discretization':euler,
             'seller_points':list(map(str,s_points)),'buyer_points':list(map(str,b_points)),
             'seller_pmf':[[str(v) for v in row] for row in s],
             'buyer_pmf':[[str(v) for v in row] for row in b],
             'seller_joint':[[str(w),list(map(str,v))] for w,v in sj],
             'buyer_joint':[[str(w),list(map(str,v))] for w,v in bj],
             'prices':list(map(str,prices)),
             'welfare_ratios':[str(w/opt) for w in w_by_price],
             'OPT':str(opt),'ratio':str(ratio),'ratio_decimal':float(ratio),
             'separate_price_ratio':str(separate),'separate_price_ratio_decimal':float(separate),
             'claimed_upper_bound':str(bound),'exact_margin':str(bound-ratio),
             'joint_replay_price_count':len(prices),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    dest.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    ledger.record(key,f'The explicitly stored positive ordered {"symmetric " if symmetric else ""}two-unit rational instance has optimal common-price welfare ratio < {bound}. Marginal and full joint sequential-trade enumeration agree at every finite support price.',
                  ['exact'],str(dest.relative_to(ROOT)),paper='fixed-price extension screen',
                  note='All distributions, order constraints and welfare values replayed with Fraction. Between support events allocations are constant. Above/below all supports there is no trade. This is an upper witness only, not the optimal k=2 ratio.')
    print(json.dumps({k:receipt[k] for k in ['ratio_decimal','separate_price_ratio_decimal','exact_margin','joint_replay_price_count']},indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--symmetric',action='store_true')
    parser.add_argument('--free-support',action='store_true')
    parser.add_argument('--euler',action='store_true')
    args=parser.parse_args();main(args.symmetric,args.free_support,args.euler)
