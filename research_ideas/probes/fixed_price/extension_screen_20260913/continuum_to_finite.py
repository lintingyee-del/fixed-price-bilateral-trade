"""Discretize the shifted-clock candidate; solve a full ordered seller LP.

The seller is unrestricted on the chosen grid. All outputs are discovery until
the separate rational replay script certifies a specified resulting instance.
"""
import json
from pathlib import Path
import numpy as np

from multiunit_screen import seller_ratio_lp,dump,source_value

HERE=Path(__file__).resolve().parent


def main():
    row=json.loads((HERE/'results/shifted_calibration_family.json').read_text())['best']
    prof=row['profile'];xs=np.array(prof['clock']);ps=np.array(prof['price'])
    hs=np.array(prof['buyer1_survival'])
    for count in [16,32,64]:
        inner=np.linspace(row['x_left'],row['x_right'],count+1)
        body_prices=np.interp(inner,xs,ps)
        body_h=np.interp(inner,xs,hs)
        tail=1000000.;eta=1/tail
        points=np.r_[0.,row['a'],body_prices,row['b'],tail]
        H1=np.r_[1.,1.,(1-eta)*body_h+eta,eta,0.]
        buyer=np.zeros((2,len(points)))
        buyer[0]=np.r_[1.,H1[:-1]]-H1
        buyer[0]=np.maximum(buyer[0],0);buyer[0]/=buyer[0].sum()
        buyer[1,1]=1-eta;buyer[1,-1]=eta
        result=seller_ratio_lp(points+1e-10,points,buyer)
        if 'seller' not in result:raise RuntimeError(result)
        seller=result['seller']
        value,opt,w=source_value(points,seller,buyer)
        raw={'points':points,'seller':seller,'buyer':buyer,'objective':value,
             'OPT':opt,'ratio':value/opt,'n':len(points),'body_subintervals':count,
             'seller_lp_ratio':result['ratio'],'welfare':w,
             'scope':'Discretized restricted Euler-family buyer, unrestricted ordered seller LP on this grid. Floating discovery.'}
        dump(HERE/f'results/euler_finite_{count}.json',raw)
        dump(HERE/f'results/euler_seller_response_{count}.json',result)
        print(json.dumps({k:raw[k] for k in ['body_subintervals','n','ratio','seller_lp_ratio']}),flush=True)


if __name__=='__main__':main()
