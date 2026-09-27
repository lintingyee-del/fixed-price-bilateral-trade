"""First-layer check of every intermediate formula added to Lemmas 6.1, 7.1 and Corollary B'.

Symbolic identities are checked exactly with SymPy; the three-piece energy integral is
checked numerically with mpmath at several parameter points.
"""
import sympy as sp
import mpmath as mp

C, Y, Z, I, r, y, x, a, beta = sp.symbols("C Y Z I r y x a beta", positive=True)
D = 1 - Y + C * Y**2
q = 1 - C * Y
results = {}


def check(name, expr):
    ok = sp.simplify(sp.together(expr)) == 0
    results[name] = ok
    print(("OK  " if ok else "FAIL"), name)


# Lemma 6.1: two exact derivatives and the U-Z relation
Dr = 1 - r + C * r**2
check("d/dr r/D", sp.diff(r / Dr, r) - (1 - C * r**2) / Dr**2)
check("d/dr r^2/D", sp.diff(r**2 / Dr, r) - (2 * r - r**2) / Dr**2)
A0 = Y / D + C * Z            # int D^-2
A1 = (Y**2 / D + Z) / 2       # int r D^-2
U = Y * A0 - A1
check("2U = Y^2/D + (2CY-1)Z", 2 * U - (Y**2 / D + (2 * C * Y - 1) * Z))
Yp = (Y**3 + Y * D * Z) / 2
common = Y**2 - Y**3 / 2 + C * Y**4 + (2 * C * Y - 1) * Y * D * Z / 2
check("total derivative of D equals common form", Y**2 + (2 * C * Y - 1) * Yp - common)
check("Y D (Y+U) equals common form", Y * D * (Y + U) - common)

# Lemma 7.1: contact identities
xC = (1 - D) / D
Pe = Y / D
check("1-D = Y(1-CY)", (1 - D) - Y * q)
check("x/Pe = 1-CY", xC / Pe - q)
check("line: 1/x - 1/Pe = CD/(1-CY)", 1 / xC - 1 / Pe - C * D / q)
check("Phi closed form", C * (1 + I) - C * Y - C * D / q - (C * I - C**2 * Y / q))
# identity (28): same y-derivative, both sides vanish at 0
Dy = 1 - y + C * y**2
check("(28) derivative", (4 * C - 1) * y**2 - (2 * y * Dy - y * (y - 2) * (2 * C * y - 1)))
# middle-arc energy algebra
check("C r^2 = D - 1 + r", C * r**2 - (Dr - 1 + r))
check("2C(1-r) = (2C-1) - D'", 2 * C * (1 - r) - ((2 * C - 1) - sp.diff(Dr, r)))

# derivative along the branch
dPhi = I - C * Z + C * Yp / D - (2 * C * Y - C**2 * Y**2 + C**2 * Yp) / q**2
I28 = ((4 * C - 1) * Z - Y * (Y - 2) / D) / 2
B = 2 * C - 1 + C * (1 - C) * Y
target = -(Y + U) * B / q**2
expr = sp.expand(sp.together(dPhi.subs(I, I28) - target))
check("dPhi/dC = -(Y+U)B/q^2 (as identity in C,Y,Z)", dPhi.subs(I, I28) - target)
lhs = sp.together(dPhi.subs(I, I28))
zc = sp.simplify(sp.diff(sp.expand(sp.simplify(lhs)), Z))
check("Z-coefficient, polynomial form", zc - ((2 * C - 1) + C * Y * (3 - 5 * C) - 2 * C**2 * (1 - C) * Y**2) / (2 * q**2))
check("Z-coefficient, product form", zc + (2 * C * Y - 1) * B / (2 * q**2))
rem = sp.simplify(lhs.subs(Z, 0))
check("remainder = -Y(2D+Y)B/(2Dq^2)", rem + Y * (2 * D + Y) * B / (2 * D * q**2))
check("D - (1-CY)^2 = Y B", D - q**2 - Y * B)
check("1/x^2 - (1+x)/Pe^2 = D B/(Y q^2)", 1 / xC**2 - (1 + xC) / Pe**2 - D * B / (Y * q**2))
xprime = -Y * (Y + U) / D
check("dPhi/dC = dPhi/dx * x'", target - (D * B / (Y * q**2)) * xprime)
# multiplier prediction
ae = sp.symbols("a_e", positive=True)
mult = -1 / x + sp.integrate(2 * (1 + x) / (x + a)**3, (a, 0, ae))
check("multiplier prediction", mult - (1 / x**2 - (1 + x) / (x + ae)**2))

# Corollary B': exponent algebra
Ihalf = 1 / (2 * beta * C) - 1
check("I/2 from S=1/beta", sp.simplify((1 / (beta * C) - 2) / 2 - Ihalf))
check("1/(2 beta C) split", 1 / (2 * beta * C) - (2 / beta - (4 * C - 1) / (2 * C * beta)))

# numeric check of the three-piece energy
mp.mp.dps = 30
for Cv, Yv in [(mp.mpf("0.3"), mp.mpf("0.8")), (mp.mpf("0.39"), mp.mpf("0.9")), (mp.mpf("0.2"), mp.mpf("0.6")), (mp.mpf("0.7"), mp.mpf("1.1"))]:
    Dc = lambda rr: 1 - rr + Cv * rr**2
    Ic = lambda yy: mp.quad(lambda s: 1 / Dc(s), [0, yy])
    Dv, Iv = Dc(Yv), Ic(Yv)
    d = mp.sqrt(Dv) / Yv * mp.e**(-Iv / 2)
    xv = (1 - Dv) / Dv
    aev = Cv * Yv**2 / Dv
    line = mp.quad(lambda t: d**2 - (1 + t) / (xv + t)**2, [0, aev])
    # middle arc in the parameter r: da = -a/D dr, P^-2 da = -C dr, a (logP)'^2 da = -C^2 r^2/D dr
    arc_a = lambda rr: Cv / d**2 * mp.e**(-Ic(rr))
    arc = mp.quad(lambda rr: (d**2 * arc_a(rr) / Dc(rr)) - Cv - Cv**2 * rr**2 / Dc(rr), [0, Yv])
    Phi_num = -mp.log(d * xv) + line + arc
    Phi_closed = Cv * Iv - Cv**2 * Yv / (1 - Cv * Yv)
    ok = abs(Phi_num - Phi_closed) < mp.mpf(10) ** (-20)
    results[f"numeric Phi C={Cv} Y={Yv}"] = bool(ok)
    print(("OK  " if ok else "FAIL"), f"numeric Phi at C={Cv}, Y={Yv}: diff={mp.nstr(Phi_num - Phi_closed, 5)}")

print("all ok:", all(results.values()), f"({sum(results.values())}/{len(results)})")

import json
from pathlib import Path
receipt = Path(__file__).resolve().parent / "checks" / "granularity_hard_first_layer_20260918.json"
receipt.write_text(json.dumps({"scope": "Intermediate formulas added to Lemmas 6.1, 7.1 and Corollary B' on 2026-09-18; SymPy exact identities plus mpmath 30-digit checks of the three-piece energy at four parameter points.", "results": results, "all_ok": all(results.values())}, indent=1), encoding="utf-8")
print("receipt:", receipt.name)
