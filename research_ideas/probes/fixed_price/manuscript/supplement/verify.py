#!/usr/bin/env python3
"""Replay of the computer-assisted statements of the paper from the supplied data.

Usage:  python verify.py            (all checks, about a minute)
        python verify.py --fast     (skips the two interval covers)

Requires Python 3.9+, python-flint (Arb ball arithmetic) and sympy.
Every check either recomputes a statement from the data with exact rational or
ball arithmetic, or, where the file stores only enclosures of quantities whose
formulas live in the paper, confirms that the stored enclosures have the signs
the paper uses.  The README says which is which.  Nothing here searches: the
partitions, brackets and certificates are read from the files and re-evaluated.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re
import sys

import sympy as sp
from flint import arb, ctx, fmpq

HERE = Path(__file__).resolve().parent
RESULTS = []


def load(name):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def report(name, ok, detail=""):
    RESULTS.append(ok)
    print(("PASS  " if ok else "FAIL  ") + name + ("   " + detail if detail else ""), flush=True)


def Q(x):
    x = F(x)
    return arb(fmpq(x.numerator, x.denominator))


def hull(lo, hi):
    return Q(lo).union(Q(hi))


# ---------------------------------------------------------------- manifest
def check_manifest():
    files = load("manifest.json")["files"]
    bad = [n for n, rec in files.items()
           if hashlib.sha256((HERE / n).read_bytes()).hexdigest() != rec["sha256"]]
    report("manifest: sha256 of %d files" % len(files), not bad, ", ".join(bad))


# ---------------------------------------------------------------- single unit
def scalar_curve(C):
    """I(C), S(C), tau(C) of equations (3)-(5) of the paper, 1/4 < C < 1/2."""
    w = (C - Q(F(1, 4))).sqrt()
    I = (((1 - 3 * C) / (2 * (1 - C) * w)).atan() + (1 / (2 * w)).atan()) / w
    return I, C * (2 + I), C * C / (1 - 2 * C) * (-I / 2).exp()


def check_single_unit():
    ctx.prec = 256
    # S is strictly decreasing and tau strictly increasing (equation (7)), so
    # S - 1 - tau is strictly decreasing and a sign change brackets the root C_*.
    lo, hi = F(39, 100), F(2, 5)
    f = lambda c: (lambda I, S, tau: S - 1 - tau)(*scalar_curve(Q(c)))
    assert f(lo) > 0 and f(hi) < 0
    for _ in range(80):
        mid = (lo + hi) / 2
        v = f(mid)
        if v > 0:
            lo = mid
        elif v < 0:
            hi = mid
        else:
            break
    _, S_lo, tau_lo = scalar_curve(Q(lo))
    _, S_hi, tau_hi = scalar_curve(Q(hi))
    beta_lower, beta_upper = 1 / S_lo, 1 / S_hi          # beta_* = 1/S(C_*)
    report("beta_*: 0.73802433573 < beta_* < 0.73802433574",
           bool(beta_lower > Q(F(73802433573, 10**11)) and beta_upper < Q(F(73802433574, 10**11))),
           "beta_* in " + str(beta_lower.union(beta_upper)))
    report("C_* = 0.3937571625 to ten decimals",
           abs(lo - F(3937571625, 10**10)) < F(1, 10**10) and abs(hi - F(3937571625, 10**10)) < F(1, 10**10))
    report("7/20 < tau(C_*) < 9/25", bool(tau_lo > Q(F(7, 20)) and tau_hi < Q(F(9, 25))))
    # Proposition (finite-tail error): r_eta <= beta_* + eta*(beta_* L(d) + 1/d), L decreasing in d.
    eta, d = Q(F(1, 10**12)), tau_lo
    L = 3 / d + 3 / (d * d) + 2 / (d * d * d)
    r_upper = beta_upper + eta * (beta_upper * L + 1 / d)
    report("r_eta < 0.738024335797 at eta = 1e-12", bool(r_upper < Q(F(738024335797, 10**12))))
    report("R_eta = 1 + d/eta < 360000000001", bool(1 + tau_hi / eta < Q(360000000001)))


# ---------------------------------------------------------------- finite instances
def two_unit_ratio(buyers, sellers):
    """buyers, sellers: lists of ((v1, v2), probability). Independent vectors.
    Returns (OPT, best welfare, best price, all (price, welfare)). Inclusive rule S_i <= z <= B_i;
    the maximum over real prices is attained at a value of some coordinate."""
    for (b1, b2), _ in buyers:
        assert b1 >= b2 > 0
    for (s1, s2), _ in sellers:
        assert 0 < s1 <= s2
    assert sum(w for _, w in buyers) == 1 and sum(w for _, w in sellers) == 1
    M = sum(w * (s[0] + s[1]) for s, w in sellers)
    OPT = sum(wb * ws * (max(b[0], s[0]) + max(b[1], s[1]))
              for b, wb in buyers for s, ws in sellers)
    events = sorted({v for vec, _ in buyers + sellers for v in vec})
    table = []
    for z in events:
        gain = 0
        for i in (0, 1):
            pb = sum(w for b, w in buyers if b[i] >= z)
            eb = sum(w * b[i] for b, w in buyers if b[i] >= z)
            ps = sum(w for s, w in sellers if s[i] <= z)
            es = sum(w * s[i] for s, w in sellers if s[i] <= z)
            gain += eb * ps - pb * es          # E[(B_i - S_i) 1{S_i <= z <= B_i}] by independence
        table.append((z, M + gain))
    best = max(table, key=lambda r: r[1])
    return OPT, best[1], best[0], table


def check_general_instance():
    d = load("general_instance.json")
    vd, pd = d["value_denominator"], d["probability_denominator"]
    conv = lambda rows: [((F(v[0], vd), F(v[1], vd)), F(w, pd)) for v, w in rows]
    OPT, W, z, table = two_unit_ratio(conv(d["buyers"]), conv(d["sellers"]))
    scale = vd * pd * pd
    rep = d["replay"]
    report("general instance: 131 buyer and 131 seller types, %d price events" % len(table),
           len(d["buyers"]) == 131 and len(d["sellers"]) == 131 and len(table) == rep["event_count"])
    report("general instance: stored integers reproduced",
           OPT * scale == int(rep["opt_integer"]) and W * scale == int(rep["best_welfare_integer"])
           and z * vd == rep["best_price_integer"])
    report("general instance: ratio < 0.7290804", W / OPT < F(7290804, 10**7), "ratio = %.13f" % float(W / OPT))


def check_symmetric_instance():
    d = load("symmetric_instance.json")
    rows = lambda key: [((F(v[0]), F(v[1])), F(p)) for p, v in d[key]]
    buyers, sellers = rows("buyer_joint"), rows("seller_joint")
    mirrored = sorted(((s[1], s[0]), w) for s, w in sellers) == sorted(buyers)
    OPT, W, z, table = two_unit_ratio(buyers, sellers)
    report("symmetric instance: buyer law is the reversed seller law", mirrored)
    report("symmetric instance: stored OPT and ratio reproduced",
           OPT == F(d["OPT"]) and W / OPT == F(d["ratio"]))
    stored = dict(zip(map(F, d["prices"]), map(F, d["welfare_ratios"])))
    report("symmetric instance: ratio at each of %d events reproduced" % len(table),
           all(stored.get(p) == w / OPT for p, w in table))
    report("symmetric instance: ratio < 0.83693", W / OPT < F(83693, 10**5), "ratio = %.12f" % float(W / OPT))


# ---------------------------------------------------------------- Bernstein certificates
t, u, p = sp.symbols("t u p")


def bernstein_leaf(poly, coeffs):
    n, m = len(coeffs) - 1, len(coeffs[0]) - 1
    c = [[sp.Rational(x) for x in row] for row in coeffs]
    if any(x < 0 for row in c for x in row):
        return False
    rebuilt = sum(c[i][j] * sp.binomial(n, i) * t**i * (1 - t)**(n - i)
                  * sp.binomial(m, j) * u**j * (1 - u)**(m - j)
                  for i in range(n + 1) for j in range(m + 1))
    return sp.expand(poly - rebuilt) == 0


def bernstein_tree(poly, tree):
    """Nonnegativity of poly on [0,1]^2 from a bisection tree with nonnegative Bernstein leaves."""
    if "coefficients" in tree:
        return 1 if bernstein_leaf(poly, tree["coefficients"]) else None
    var = {"t": t, "u": u}[tree["split"]]
    a = bernstein_tree(sp.expand(poly.subs(var, var / 2)), tree["left"])
    b = bernstein_tree(sp.expand(poly.subs(var, (1 + var) / 2)), tree["right"])
    return None if a is None or b is None else a + b


def check_bernstein():
    d = load("affine_boundary_coefficients.json")
    bound = sp.Rational(d["bound"])
    for rec in d["boundaries"]:
        M, G = sp.sympify(rec["M"]), sp.sympify(rec["G"])
        target = ((M + 2) - bound * (M + G)) * sp.sympify(rec["positive_multiplier"])
        target = target.subs(p, sp.sympify(rec["p0_substitution"]))
        poly = sp.sympify(rec["polynomial"])
        reduced = sp.sympify(rec["reduced_polynomial"])
        removed = sp.Integer(1)
        for label, power in rec["removed_positive_factors"].items():
            removed *= sp.sympify(label) ** power
        linked = sp.simplify(target - poly) == 0 and sp.expand(poly - reduced * removed) == 0
        leaves = bernstein_tree(sp.expand(reduced), rec["certificate"])
        report("affine boundary '%s': (M+2) - %s (M+G) >= 0, %s Bernstein leaves"
               % (rec["boundary"], d["bound"], leaves), linked and leaves == rec["leaf_count"])


# ---------------------------------------------------------------- stationary covers
class Jet:
    """Value and first partial derivatives in (t, p), in ball arithmetic."""
    def __init__(self, v, dt=0, dp=0):
        self.v = v if isinstance(v, arb) else Q(v)
        self.dt = dt if isinstance(dt, arb) else Q(dt)
        self.dp = dp if isinstance(dp, arb) else Q(dp)

    @staticmethod
    def cast(x):
        return x if isinstance(x, Jet) else Jet(x)

    def __add__(self, b):
        b = self.cast(b)
        return Jet(self.v + b.v, self.dt + b.dt, self.dp + b.dp)
    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.dt, -self.dp)

    def __sub__(self, b):
        return self + (-self.cast(b))

    def __rsub__(self, b):
        return self.cast(b) + (-self)

    def __mul__(self, b):
        b = self.cast(b)
        return Jet(self.v * b.v, self.dt * b.v + self.v * b.dt, self.dp * b.v + self.v * b.dp)
    __rmul__ = __mul__

    def reciprocal(self):
        return Jet(1 / self.v, -self.dt / self.v**2, -self.dp / self.v**2)

    def __truediv__(self, b):
        return self * self.cast(b).reciprocal()

    def __rtruediv__(self, b):
        return self.cast(b) * self.reciprocal()

    def __pow__(self, n):
        return Jet(self.v**n, n * self.v**(n - 1) * self.dt, n * self.v**(n - 1) * self.dp)

    def sqrt(self):
        z = self.v.sqrt()
        return Jet(z, self.dt / (2 * z), self.dp / (2 * z))

    def log(self):
        return Jet(self.v.log(), self.dt / self.v, self.dp / self.v)

    def atan(self):
        return Jet(self.v.atan(), self.dt / (1 + self.v**2), self.dp / (1 + self.v**2))


def states(tj, pj, lam, beta, connection=True):
    """The eliminated stationary system of the structured family (Appendix on the family minimum).
    R is the algebraic residual, increasing in p; 'connection' is the connection equation."""
    delta = (pj + tj) / 2
    e = (1 + tj) / 2
    v = 1 - e
    Pl = pj * ((delta + lam) / (tj + lam)).sqrt()
    xl = Pl - delta
    C = (lam + delta) * xl / Pl**2
    q = 2 * v * v * C / (v * v + (v**4 - 4 * (v * v - C) * v * v * C).sqrt())
    k = xl / Pl
    A = -lam / tj**2 + 2 * lam + 1 / pj + (tj + lam) / pj**2
    out = dict(Pl=Pl, C=C, q=q, k=k, R=-A + v * (v - q) / (e * (v + q)))
    if connection and C.v > Q(F(1, 4)):
        w = (C - Q(F(1, 4))).sqrt()
        J = (((k - Q(F(1, 2))) / w).atan() - ((q - Q(F(1, 2))) / w).atan()) / w
        Dk, Dq = k * k - k + C, q * q - q + C
        out["connection"] = ((1 - q) / (1 - k)).log() + ((Dk / Dq).log() + J) / 2 - (e / delta).log()
        h = lam * q * (1 - q) / (e * Dq)
        Pr = e / (1 - q)
        a = (pj - tj) / (2 * tj * pj)
        DD, m = 2 / (1 + tj), 2 * tj / (1 + tj)
        T = 1 / pj - 1 / Pl + (k - q) / lam + (1 / Pr - 1) / h
        M = DD * (a + T - v / h)
        G = 3 - m + m * a + DD * C * J
        out.update(h=h, Pr=Pr, K=beta * G - (1 - beta) * M - 2)
    return out


def check_cover(name, lam, beta, candidate_needs_upper_sign, max_candidate_width, K_negative):
    ctx.prec = 192
    d = load(name)
    R = lambda tb, pv: states(Jet(tb), Jet(Q(pv)), lam, beta, False)["R"].v
    bad, candidates, reasons = [], [], {}
    for leaf in d["boxes"]:
        lo, hi = map(F, leaf["t_box"])
        tb, reason, ok = hull(lo, hi), leaf["reason"], False
        reasons[reason] = reasons.get(reason, 0) + 1
        if reason == "no_algebraic_root":
            ok = bool(R(tb, 1) < 0)                       # R increasing in p: no root with p <= 1
        else:
            pl, ph = map(F, leaf["p_bracket"])
            high = R(tb, ph)
            if pl > hi and ph <= 1 and R(tb, pl) < 0 and (ph == 1 or high > 0):
                st = states(Jet(tb, 1, 0), Jet(hull(pl, ph), 0, 1), lam, beta)
                if reason == "Pl_above_one":
                    ok = bool(st["Pl"].v > 1)
                elif reason == "wrong_phase_order":
                    ok = bool(st["k"].v < st["q"].v)
                elif reason == "connection_nonzero":
                    f = st["connection"].v
                    ok = bool(f > 0 or f < 0)
                elif reason == "root_candidate":
                    f, Rj = st["connection"], st["R"]
                    ok = bool(Rj.dp > 0) and bool(f.dt - f.dp * Rj.dt / Rj.dp > 0) \
                        and hi - lo <= max_candidate_width \
                        and (not candidate_needs_upper_sign or bool(high > 0))
                    candidates.append((lo, hi, pl, ph))
        if not ok:
            bad.append(leaf["t_box"])
    boxes = sorted(tuple(map(F, leaf["t_box"])) for leaf in d["boxes"])
    tiled = boxes[0][0] == F(d["domain"][0]) and boxes[-1][1] == F(d["domain"][1]) \
        and all(a[1] == b[0] for a, b in zip(boxes, boxes[1:]))
    report("%s: %d leaves re-evaluated %s" % (name, len(boxes), reasons),
           not bad and not d["unresolved"] and len(boxes) == d["leaf_count"], str(bad[:3]) if bad else "")
    report("%s: leaves tile t in [%s, %s]" % (name, *d["domain"]), tiled)
    candidates.sort()
    contiguous = all(a[1] == b[0] for a, b in zip(candidates, candidates[1:]))
    root = [str(candidates[0][0]), str(candidates[-1][1])]
    report("%s: retained cells are contiguous and equal the stored root interval" % name,
           contiguous and root == d["root_t_interval"])

    def connection_at(tval, pl, ph):
        tb = Q(tval)
        for _ in range(120):
            if ph - pl < F(1, 2**90):
                break
            pm = (pl + ph) / 2
            val = R(tb, pm)
            if val > 0:
                ph = pm
            elif val < 0:
                pl = pm
            else:
                break
        return states(Jet(tb, 1, 0), Jet(hull(pl, ph), 0, 1), lam, beta)["connection"].v

    left = connection_at(candidates[0][0], candidates[0][2], candidates[0][3])
    right = connection_at(candidates[-1][1], candidates[-1][2], candidates[-1][3])
    report("%s: connection equation changes sign across the root interval" % name,
           bool(left < 0 and right > 0))
    pl, ph = map(F, d["root_p_interval"])
    tb = hull(candidates[0][0], candidates[-1][1])
    st = states(Jet(tb, 1, 0), Jet(hull(pl, ph), 0, 1), lam, beta)
    physical = bool(R(tb, pl) < 0 and R(tb, ph) > 0 and st["Pl"].v < st["Pr"].v and st["Pr"].v < 1
                    and st["h"].v > 0 and st["h"].v < 1)
    if K_negative:
        physical = physical and bool(st["K"].v < 0)
    report("%s: root strip is physical%s" % (name, ", comparison K < 0" if K_negative else ""), physical)


# ---------------------------------------------------------------- stored enclosures
BALL = re.compile(r"\[?(-?\d+\.?\d*(?:e[+-]?\d+)?)(?:\s*\+/-\s*(\d+\.?\d*(?:e[+-]?\d+)?))?\]?")


def enclosure(text):
    """Lower and upper end of a stored '[a +/- r]', '[[a +/- r], [b +/- s]]' or '[a, b]'."""
    ends = []
    for mid, rad in BALL.findall(text):
        if mid:
            m, r = F(mid), F(rad) if rad else F(0)
            ends += [m - r, m + r]
    return min(ends), max(ends)


def check_stored_signs():
    d = load("stationary_physical_conditions.json")
    margins = d["strict_positive_margins"]
    report("stationary_physical_conditions: %d stored margins are positive" % len(margins),
           all(enclosure(v)[0] > 0 for v in margins.values()) and not d["failed_or_indefinite_margins"]
           and not d["cover"]["uncovered_boxes"])
    d = load("second_unit_kernel_bounds.json")
    b = d["bounds"]
    report("second_unit_kernel_bounds: stored signs",
           all(enclosure(b[k])[0] > 0 for k in d["strict_positive"])
           and all(enclosure(b[k])[1] < 0 for k in d["strict_negative"]))
    for name in ["endpoint_identities.json", "boundary_identities.json", "branch_elimination.json",
                 "branch_positive_factors.json", "second_unit_kernel_identities.json"]:
        res = load(name)["residuals"]
        report("%s: %d recorded residuals are zero" % (name, len(res)), all(v == "0" for v in res.values()))
    res = load("reference_price_coefficients.json")["exact"]["identities"]
    report("reference_price_coefficients.json: %d recorded residuals are zero" % len(res),
           all(v == "0" for v in res.values()))


# ---------------------------------------------------------------- obstructions
def check_obstructions():
    d = load("obstructions.json")
    c = d["coordinate_compression"]
    vec = lambda rows, probs: [((F(a), F(b)), F(w)) for (a, b), w in zip(rows, probs)]
    sellers = vec(c["seller_vectors"], c["seller_probabilities"])
    OPT, W, _, _ = two_unit_ratio(vec(c["buyer_vectors"], c["buyer_probabilities"]), sellers)
    OPT2, W2, _, _ = two_unit_ratio(vec(c["compressed_buyer_vectors"], c["compressed_buyer_probabilities"]), sellers)
    mean = sum(F(b[1]) * F(w) for b, w in zip(c["buyer_vectors"], c["buyer_probabilities"]))
    report("obstruction 1: ratio 67/70 rises to 1 when B2 is replaced by its mean",
           (OPT, W, W / OPT) == tuple(map(F, (c["expected"]["OPT"], c["expected"]["best_welfare"], "67/70")))
           and W2 / OPT2 == 1 and F(c["compressed_buyer_vectors"][0][1]) == mean)

    c = d["value_convexity"]
    s, z, lam, pp = sp.symbols("s z lambda p", positive=True)
    dens = sp.Rational(2, 3) / pp**2
    trade, tail = 1 + z - s, sp.Integer(1)
    rhs = {   # 1 + integral of g_p(s,z) against nu, by position of s
        "case_s_below_1": sp.Rational(1, 3) * trade + sp.integrate(dens * trade, (pp, 1, z)) + sp.integrate(dens * tail, (pp, z, 2)),
        "case_s_between_1_and_z": sp.integrate(dens * trade, (pp, s, z)) + sp.integrate(dens * tail, (pp, z, 2)),
        "case_s_at_least_z": sp.integrate(dens * tail, (pp, s, 2)),
    }
    lhs = {"case_s_below_1": z - s - lam * s, "case_s_between_1_and_z": z - s - lam * s,
           "case_s_at_least_z": -lam * s}
    ok = True
    for key, rec in c["remainders"].items():
        direct, form = (sp.sympify(rec[key2].replace("lambda", "lam"), locals={"lam": lam, "s": s, "z": z})
                        for key2 in ("direct", "nonnegative_form"))
        ok = ok and sp.simplify(rhs[key] - lhs[key] - direct) == 0 and sp.simplify(direct - form) == 0
    report("obstruction 2: the three pointwise remainders and their nonnegative forms", ok)

    S2 = [(F(a), F(w)) for a, w in c["second_seller"]]

    def gains_and_value(Z1, S1, Z2):
        g = lambda law_s, law_z, price, right_limit: sum(
            ws * wz * (1 + ((zv - sv) if (zv > price if right_limit else zv >= price) else 0))
            for sv, ws in law_s for zv, wz in law_z if (sv <= price if right_limit else sv < price))
        prices = sorted({v for law in (Z1, Z2, S1, S2) for v, _ in law})
        cap = max(g(S1, Z1, pr, lim) + g(S2, Z2, pr, lim) for pr in prices for lim in (False, True)
                  if pr < 2 or not lim)
        pos = lambda law_s, law_z: sum(ws * wz * max(zv - sv, 0) for sv, ws in law_s for zv, wz in law_z)
        return cap, 2 + pos(S1, Z1) + pos(S2, Z2), sum(v * w for v, w in S1) + sum(v * w for v, w in S2)

    law = lambda rows: [(F(a), F(w)) for a, w in rows]
    w2 = c["witness_at_delta_2"]
    cap2, G2, M2 = gains_and_value(law(w2["Z1"]), law(w2["S1"]), [(F(2), F(1))])
    wm = c["witness_at_mixture"]
    Zm = law(wm["Z1_equals_Z2"])
    capm, Gm, Mm = gains_and_value(Zm, law(wm["S1"]), Zm)
    report("obstruction 2: both witnesses respect the gain cap 2 and have the stated (G, M)",
           cap2 <= 2 and capm <= 2 and (G2, M2) == (F(w2["G"]), F(w2["M"])) and (Gm, Mm) == (F(wm["G"]), F(wm["M"])))
    # Upper bound at delta_1: 1 + (1/3)(2 - 1/5) + (1/3)(2 - 1/10) + G_2 - lambda M_2 with G_2 = 11/10, M_2 = 9/5.
    L = sp.Symbol("lam")
    parse = lambda text: sp.sympify(text.replace("lambda", "lam"), locals={"lam": L})
    up1 = 1 + sp.Rational(1, 3) * (2 - sp.Rational(1, 5)) + sp.Rational(1, 3) * (2 - sp.Rational(1, 10)) \
        + sp.Rational(11, 10) - L * sp.Rational(9, 5)
    val2 = sp.sympify(w2["G"]) - L * sp.sympify(w2["M"])
    mix = sp.sympify(wm["G"]) - L * sp.sympify(wm["M"])
    report("obstruction 2: endpoint bounds and the convexity gap lambda/10",
           sp.simplify(up1 - parse(c["upper_bound_at_delta_1"])) == 0
           and sp.simplify(val2 - parse(c["value_at_delta_2"])) == 0
           and sp.simplify(mix - (up1 + val2) / 2 - L / 10) == 0)


def main():
    fast = "--fast" in sys.argv
    check_manifest()
    check_single_unit()
    check_general_instance()
    check_symmetric_instance()
    check_bernstein()
    check_obstructions()
    check_stored_signs()
    if not fast:
        point = Q(F(6773, 18227))
        check_cover("stationary_lower_endpoint.json", point, Q(F(18227, 25000)), False, F(1, 10**12), True)
        check_cover("stationary_uniform_cover.json", hull(F(270919, 729081), F(6773, 18227)),
                    hull(F(18227, 25000), F(729081, 10**6)), True, F(1, 10**7), False)
    print("\n%d checks, %d failed" % (len(RESULTS), RESULTS.count(False)))
    sys.exit(0 if all(RESULTS) else 1)


if __name__ == "__main__":
    main()
