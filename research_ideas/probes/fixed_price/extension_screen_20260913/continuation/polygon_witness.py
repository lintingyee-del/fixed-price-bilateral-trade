"""Exact concave-polygon functional and positive finite k=2 witness.

Floating point is used only to propose polygon ordinates. Every subsequent
inequality, marginal coupling, and all-price sequential replay is rational
or integer arithmetic. This proves an upper bound, not a universal lower.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(ROOT))
from hz_certify import ledger

sys.set_int_max_str_digits(0)


def rounded(x, denominator):
    y = x * denominator
    return (2 * y.numerator + y.denominator) // (2 * y.denominator)


def counts(cdf, total):
    cumulative = [0] + [rounded(x, total) for x in cdf] + [total]
    assert all(a <= b for a, b in zip(cumulative, cumulative[1:]))
    return [b-a for a, b in zip(cumulative, cumulative[1:])]


def coupled(marginals, denominator, descending=False):
    """Common-quantile coupling with integer probability weights."""
    laws = [sorted([(v, w) for v, w in law if w], reverse=descending)
            for law in marginals]
    assert all(sum(w for _, w in law) == denominator for law in laws)
    i = j = 0
    w1, w2 = laws[0][0][1], laws[1][0][1]
    result = []
    while i < len(laws[0]) and j < len(laws[1]):
        mass = min(w1, w2)
        vals = (laws[0][i][0], laws[1][j][0])
        assert vals[0] >= vals[1] if descending else vals[0] <= vals[1]
        assert min(vals) > 0 and mass > 0
        result.append((vals, mass))
        w1 -= mass
        w2 -= mass
        if not w1:
            i += 1
            if i < len(laws[0]):
                w1 = laws[0][i][1]
        if not w2:
            j += 1
            if j < len(laws[1]):
                w2 = laws[1][j][1]
    assert sum(w for _, w in result) == denominator
    return result


def all_price_replay(buyers, sellers, denominator):
    events = sorted({v for law in [buyers, sellers] for vals, _ in law for v in vals})
    index = {v: i for i, v in enumerate(events)}
    difference = [0] * (len(events)+1)
    opt = 0
    initial = sum(w*sum(vals) for vals, w in sellers)*denominator
    for bv, bw in buyers:
        for sv, sw in sellers:
            mass = bw*sw
            opt += mass*sum(max(b, s) for b, s in zip(bv, sv))
            lo, hi = 0, len(events)-1
            for b, s in zip(bv, sv):
                lo, hi = max(lo, index[s]), min(hi, index[b])
                if lo > hi:
                    break
                gain = mass*(b-s)
                difference[lo] += gain
                difference[hi+1] -= gain
    running, best, best_index = 0, initial, None
    for i in range(len(events)):
        running += difference[i]
        if initial+running > best:
            best, best_index = initial+running, i
    assert running+difference[-1] == 0
    return dict(opt_integer=str(opt), best_welfare_integer=str(best),
                ratio=str(F(best, opt)), ratio_decimal=float(F(best, opt)),
                event_count=len(events), best_price_integer=events[best_index])


def main():
    key = 'fp_ext_k2_polygon_finite_upper_20260913'
    if ledger.already_recorded(key):
        print('Reusing '+key)
        return
    N = 128
    m, p = F('0.482350710205'), F('0.671601354876')
    xl, xr, x0 = map(F, ['0.258130642337', '0.429835670465', '0.675566875576'])
    D = 2-m
    t = m/D
    c, delta = (p-t)/2, (p+t)/2
    e, v = 1/D, 1-1/D
    h, a = v/x0, c/(t*p)
    Pl, Pr = xl+delta, h*xr+e
    C = 0.39454752717994257
    w = np.sqrt(C-.25)
    core_x = [xl+(xr-xl)*F(i, N) for i in range(N+1)]
    core_P = []
    for x in core_x:
        y = np.log(float(x/xl))
        value = np.exp(y/2)*(float(Pl)*np.cos(w*y)
                    +float(xl-Pl/2)*np.sin(w*y)/w)
        core_P.append(F(round(value*10**14), 10**14))
    core_P[0], core_P[-1] = Pl, Pr
    X, P = [c]+core_x+[x0], [p]+core_P+[F(1)]
    H = [(q2-q1)/(x2-x1) for x1,x2,q1,q2 in zip(X,X[1:],P,P[1:])]
    F1 = [D*(q-x*slope) for x,q,slope in zip(X,P,H)]
    assert H[0] == 1 and H[-1] == h
    assert all(0 < right <= left <= 1 for left,right in zip(H,H[1:]))
    assert m <= F1[0] and F1[-1] == 1
    assert all(left <= right for left,right in zip(F1,F1[1:]))
    ds = [(x2-x1)/(q1*q2) for x1,x2,q1,q2 in zip(X,X[1:],P,P[1:])]
    prices = [a]
    for length in ds:
        prices.append(prices[-1]+length)
    M = D*(a+sum(ds)-x0)
    G = 2+2*m*a+sum(f*slope*length for f,slope,length in zip(F1,H,ds))
    ratio = (M+2)/(M+G)
    assert ratio < F(729081, 10**6)

    # Common integer grids preserve exact positivity, order and normalization.
    value_den, prob_den, eta_den = 10**12, 10**15, 10**10
    body_values = [rounded(s,value_den) for s in prices]
    body_total = prob_den-prob_den//eta_den
    b1_weights = counts([1-slope for slope in H], body_total)
    b1 = list(zip(body_values,b1_weights))+[(value_den*eta_den,prob_den//eta_den)]
    b2 = [(body_values[0],body_total),(value_den*eta_den,prob_den//eta_den)]
    # A positive one-grid-step seller shift removes coincident buyer/seller atoms.
    seller_values = [1]+[s+1 for s in body_values]
    s1_weights = counts([m]+F1, prob_den)
    s1 = list(zip(seller_values,s1_weights))
    mass0 = rounded(m,prob_den)
    s2 = [(1,mass0),(body_values[-1]+1,prob_den-mass0)]
    assert len(b1_weights)==len(body_values) and len(s1_weights)==len(seller_values)
    buyers = coupled([b1,b2],prob_den,descending=True)
    sellers = coupled([s1,s2],prob_den)
    replay = all_price_replay(buyers,sellers,prob_den)
    assert F(replay['ratio']) < F(729081,10**6)
    receipt = dict(scope=__doc__.strip(), core_segments=N,
        m=str(m), p=str(p), X=list(map(str,X)), P=list(map(str,P)),
        polygon_ratio=str(ratio), polygon_ratio_decimal=float(ratio),
        value_denominator=value_den, probability_denominator=prob_den,
        buyers=buyers, sellers=sellers, replay=replay,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    path=HERE/'results/polygon_witness.json'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    ledger.record(key,
        'The explicit rational concave polygon and the positive finite ordered two-unit instance in continuation/results/polygon_witness.json each have common-price welfare ratio <729081/1000000. The finite ratio is replayed at every valuation event by exact sequential-trade integer arithmetic.',
        ['exact'],str(path.relative_to(ROOT)),paper='fixed-price extension screen',
        note='Finite upper witness and restricted polygon only. No universal lower bound.')
    print(json.dumps(dict(polygon_ratio=float(ratio), **replay,
        buyer_types=len(buyers),seller_types=len(sellers)),indent=2))


if __name__=='__main__':
    main()
