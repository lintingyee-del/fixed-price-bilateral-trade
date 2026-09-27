"""Rigorous numerics over Arb (python-flint).

The point of this module is one distinction.  A grid scan that passes at
400/400 sample points says nothing about the 401st point; an Arb enclosure
covers an entire box.  So a claim of the form "f > 0 on [a,b]" can be *proved*
here, and a claim of the form "f has no interior maximum" can be *refuted*
here, neither of which a sampling loop can do.

Everything returns either an enclosure or a Verdict.  A Verdict is one of

    proved    the property holds on the whole domain, established by covering
              it with finitely many boxes on each of which the enclosure has
              a definite sign
    refuted   some box has an enclosure of the opposite definite sign, so the
              property fails on that whole box; `witness` is an exact rational
              point inside it
    unknown   the subdivision budget ran out; `unresolved` lists the boxes
              that stayed sign-indefinite, so you can see where the trouble is

`unknown` is never silently reported as success.  A budget exhaustion looks
different from a proof.

Interval arithmetic cannot prove a non-strict bound that is attained: if
f(x*) = 0 exactly for some x* in the domain, no enclosure around x* is ever
strictly positive.  `prove_nonneg` therefore reports `unknown` near the
contact point rather than pretending.  Push those cases to the SOS layer in
hz_certify.certificates, which handles equality contact exactly.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable, Iterable, Mapping, Sequence

import sympy as sp
from flint import acb, arb, ctx, fmpq

__all__ = [
    "Verdict",
    "DEFAULT_PREC",
    "enclose",
    "prove_positive",
    "prove_negative",
    "prove_nonneg",
    "prove_lt",
    "prove_gt",
    "prove_le",
    "prove_ge",
    "range_enclosure",
    "integral",
    "value",
    "as_interval",
    "interval_str",
]

DEFAULT_PREC = 128

Box = Mapping[sp.Symbol, "tuple[Fraction, Fraction]"]


class RigorousError(Exception):
    pass


# ---------------------------------------------------------------------------
# exact rational plumbing
# ---------------------------------------------------------------------------

def _frac(x) -> Fraction:
    """Exact rational from anything sympy or Python can hand us.

    Floats are accepted but converted through their exact binary value, so no
    silent widening happens.  A symbolic constant that is not rational is a
    hard error: the caller has to decide how to bound it.
    """
    if isinstance(x, Fraction):
        return x
    if isinstance(x, int):
        return Fraction(x)
    if isinstance(x, float):
        return Fraction(x)
    e = sp.nsimplify(sp.sympify(x), rational=True)
    if not e.is_Rational:
        raise RigorousError(f"domain endpoint {x!r} is not rational")
    return Fraction(int(e.p), int(e.q))


def _arb_of_frac(q: Fraction) -> arb:
    """A ball provably containing the rational q."""
    return arb(fmpq(int(q.numerator), int(q.denominator)))


def interval_str(a: arb, digits: int = 12) -> str:
    """Print a ball as the interval it encloses.

    arb's own `str(radius=True)` collapses to `[+/- r]` once the radius is
    large relative to the midpoint, which reads as if the midpoint were zero.
    For reporting a proved bound the endpoints are what the reader wants.
    """
    return f"[{a.lower().str(digits)}, {a.upper().str(digits)}]"


def as_interval(lo, hi) -> arb:
    """A ball provably containing every real in [lo, hi].

    Built as the union of two balls, each of which contains its endpoint, so
    the result is an enclosure regardless of how the endpoints round.
    """
    a, b = _frac(lo), _frac(hi)
    if a > b:
        a, b = b, a
    return _arb_of_frac(a).union(_arb_of_frac(b))


# ---------------------------------------------------------------------------
# sympy -> arb evaluation
# ---------------------------------------------------------------------------
# Deliberately a recursive walk rather than sympy.lambdify.  lambdify prints
# Rational(1,3) as the Python float 1/3, which silently drops the enclosure on
# the very first constant.  Everything below stays inside arb.

_UNARY = {
    sp.exp: lambda z: z.exp(),
    sp.log: lambda z: z.log(),
    sp.sin: lambda z: z.sin(),
    sp.cos: lambda z: z.cos(),
    sp.tan: lambda z: z.tan(),
    sp.atan: lambda z: z.atan(),
    sp.asin: lambda z: z.asin(),
    sp.acos: lambda z: z.acos(),
    sp.sinh: lambda z: z.sinh(),
    sp.cosh: lambda z: z.cosh(),
    sp.tanh: lambda z: z.tanh(),
}


def _span(*balls: arb) -> arb:
    out = balls[0]
    for b in balls[1:]:
        out = out.union(b)
    return out


def _minmax(op, args):
    """Conservative enclosure of min/max over several enclosures.

    min is enclosed by [min over the lower endpoints, min over the upper
    endpoints], and dually for max.  Spanning the two keeps the result an
    over-approximation, which is the safe direction: it can only report
    `unknown` where a tighter rule would have decided, never the reverse.
    """
    los = [a.lower() for a in args]
    his = [a.upper() for a in args]
    pick = (lambda p, q: p if (p < q) is True else q) if op is sp.Min \
        else (lambda p, q: p if (p > q) is True else q)
    return _span(_fold(los, pick), _fold(his, pick))


def _fold(xs, f):
    out = xs[0]
    for x in xs[1:]:
        out = f(out, x)
    return out


def _eval(expr, env: Mapping[sp.Symbol, arb]) -> arb:
    e = expr
    if e.is_Symbol:
        try:
            return env[e]
        except KeyError:
            raise RigorousError(f"free symbol {e} has no interval assigned")
    if e.is_Integer:
        return arb(int(e))
    if e.is_Rational:
        return arb(fmpq(int(e.p), int(e.q)))
    if e.is_Float:
        return arb(float(e))
    if e is sp.pi:
        return arb.pi()
    if e is sp.E:
        return arb(1).exp()
    if e is sp.S.Half:
        return arb(fmpq(1, 2))
    if e.is_Add:
        out = arb(0)
        for t in e.args:
            out = out + _eval(t, env)
        return out
    if e.is_Mul:
        out = arb(1)
        for t in e.args:
            out = out * _eval(t, env)
        return out
    if e.is_Pow:
        base, expo = e.args
        b = _eval(base, env)
        if expo.is_Integer:
            return b ** int(expo)
        return b ** _eval(expo, env)
    if isinstance(e, (sp.Min, sp.Max)):
        return _minmax(type(e), [_eval(a, env) for a in e.args])
    if isinstance(e, sp.Abs):
        return abs(_eval(e.args[0], env))
    for cls, fn in _UNARY.items():
        if isinstance(e, cls):
            if len(e.args) != 1:
                raise RigorousError(f"unsupported arity in {e}")
            return fn(_eval(e.args[0], env))
    raise RigorousError(
        f"no rigorous rule for {type(e).__name__} in {e}; extend _UNARY or "
        f"rewrite the expression"
    )


def enclose(expr, box: Box, prec: int = DEFAULT_PREC) -> arb:
    """Enclosure of `expr` over the whole box, not at a sample point."""
    old, ctx.prec = ctx.prec, prec
    try:
        env = {sp.sympify(k): as_interval(*v) for k, v in box.items()}
        return _eval(sp.sympify(expr), env)
    finally:
        ctx.prec = old


def value(expr, point: Mapping = None, prec: int = DEFAULT_PREC) -> arb:
    """Enclosure of `expr` at a single exact rational point."""
    point = point or {}
    box = {k: (v, v) for k, v in point.items()}
    return enclose(expr, box, prec)


# ---------------------------------------------------------------------------
# verdicts
# ---------------------------------------------------------------------------

@dataclass
class Verdict:
    status: str                      # "proved" | "refuted" | "unknown"
    claim: str = ""
    witness: dict | None = None      # exact rational point, on "refuted"
    witness_value: str = ""          # enclosure of the expression there
    unresolved: list = field(default_factory=list)   # boxes, on "unknown"
    boxes_used: int = 0
    prec: int = DEFAULT_PREC

    def __bool__(self) -> bool:
        return self.status == "proved"

    def __str__(self) -> str:
        head = f"[{self.status}] {self.claim}"
        if self.status == "refuted":
            pt = ", ".join(f"{k}={v}" for k, v in (self.witness or {}).items())
            return f"{head}\n  witness: {pt}\n  value:   {self.witness_value}"
        if self.status == "unknown":
            return (f"{head}\n  budget exhausted after {self.boxes_used} boxes; "
                    f"{len(self.unresolved)} sign-indefinite region(s) remain\n"
                    f"  first: {self.unresolved[0] if self.unresolved else '-'}")
        return f"{head}\n  covered by {self.boxes_used} box(es) at {self.prec}-bit precision"


def _widest(box):
    return max(box.items(), key=lambda kv: kv[1][1] - kv[1][0])


def _bisect(box, sym):
    lo, hi = box[sym]
    mid = (lo + hi) / 2
    left = dict(box); left[sym] = (lo, mid)
    right = dict(box); right[sym] = (mid, hi)
    return left, right


def _sign_search(expr, box: Box, want: int, prec: int, max_boxes: int,
                 min_width: Fraction, claim: str) -> Verdict:
    """Cover `box` by sub-boxes on which the enclosure has a definite sign.

    want = +1 asks for expr > 0 everywhere, want = -1 for expr < 0.  A box
    whose enclosure has the opposite definite sign refutes the claim outright,
    and its midpoint is returned as an exact witness.
    """
    expr = sp.sympify(expr)
    box = {sp.sympify(k): (_frac(v[0]), _frac(v[1])) for k, v in box.items()}
    zero = arb(0)
    queue = [box]
    used = 0
    stuck = []
    while queue:
        if used >= max_boxes:
            stuck.extend(queue)
            break
        cur = queue.pop()
        used += 1
        val = enclose(expr, cur, prec)
        good = (val > zero) if want > 0 else (val < zero)
        if good:
            continue
        bad = (val < zero) if want > 0 else (val > zero)
        if bad:
            pt = {k: (lo + hi) / 2 for k, (lo, hi) in cur.items()}
            return Verdict("refuted", claim, witness=pt,
                           witness_value=value(expr, pt, prec).str(15, radius=True),
                           boxes_used=used, prec=prec)
        sym, (lo, hi) = _widest(cur)
        if hi - lo <= min_width:
            stuck.append(cur)
            continue
        queue.extend(_bisect(cur, sym))
    if stuck:
        return Verdict("unknown", claim, unresolved=[_fmt(b) for b in stuck[:8]],
                       boxes_used=used, prec=prec)
    return Verdict("proved", claim, boxes_used=used, prec=prec)


def _fmt(box):
    return {str(k): (str(v[0]), str(v[1])) for k, v in box.items()}


def prove_positive(expr, box: Box, prec: int = DEFAULT_PREC,
                   max_boxes: int = 20000,
                   min_width: Fraction = Fraction(1, 10 ** 9)) -> Verdict:
    """Prove expr > 0 on the whole box, or refute it with an exact point."""
    return _sign_search(expr, box, +1, prec, max_boxes, min_width,
                        f"{sp.sympify(expr)} > 0 on {_fmt({sp.sympify(k): (_frac(v[0]), _frac(v[1])) for k, v in box.items()})}")


def prove_negative(expr, box: Box, **kw) -> Verdict:
    return prove_positive(-sp.sympify(expr), box, **kw)


def prove_gt(expr, rhs, box: Box, **kw) -> Verdict:
    return prove_positive(sp.sympify(expr) - sp.sympify(rhs), box, **kw)


def prove_lt(expr, rhs, box: Box, **kw) -> Verdict:
    return prove_positive(sp.sympify(rhs) - sp.sympify(expr), box, **kw)


def prove_nonneg(expr, box: Box, slack=None, **kw) -> Verdict:
    """Prove expr >= 0 on the box.

    Interval arithmetic cannot certify a non-strict bound that is attained.
    If the minimum is 0 at an interior point, every enclosure around it
    straddles 0 and the result is `unknown` there, which is the honest answer,
    not a failure of the caller.  Pass `slack` to instead prove the strictly
    weaker but decidable claim expr > -slack.
    """
    if slack is not None:
        return prove_positive(sp.sympify(expr) + sp.sympify(slack), box, **kw)
    return prove_positive(expr, box, **kw)


def prove_ge(expr, rhs, box: Box, **kw) -> Verdict:
    return prove_nonneg(sp.sympify(expr) - sp.sympify(rhs), box, **kw)


def prove_le(expr, rhs, box: Box, **kw) -> Verdict:
    return prove_nonneg(sp.sympify(rhs) - sp.sympify(expr), box, **kw)


# ---------------------------------------------------------------------------
# range and integral
# ---------------------------------------------------------------------------

def range_enclosure(expr, box: Box, prec: int = DEFAULT_PREC,
                    refine: int = 6) -> arb:
    """A ball provably containing every value expr takes on the box.

    `refine` bisections per variable tighten the naive enclosure; the result
    is always an over-approximation, so more refinement narrows it but never
    invalidates it.
    """
    expr = sp.sympify(expr)
    box = {sp.sympify(k): (_frac(v[0]), _frac(v[1])) for k, v in box.items()}
    boxes = [box]
    for _ in range(refine):
        nxt = []
        for b in boxes:
            sym, _ = _widest(b)
            nxt.extend(_bisect(b, sym))
        boxes = nxt
        if len(boxes) > 4096:
            break
    out = None
    for b in boxes:
        v = enclose(expr, b, prec)
        out = v if out is None else out.union(v)
    return out


def integral(expr, var, a, b, prec: int = DEFAULT_PREC) -> arb:
    """Rigorous definite integral: the result carries a proved error radius."""
    expr = sp.sympify(expr)
    var = sp.sympify(var)
    old, ctx.prec = ctx.prec, prec
    try:
        def f(z, _):
            return _eval_acb(expr, {var: z})
        return acb.integral(f, acb(_arb_of_frac(_frac(a))),
                            acb(_arb_of_frac(_frac(b)))).real
    finally:
        ctx.prec = old


_UNARY_ACB = {
    sp.exp: lambda z: z.exp(),
    sp.log: lambda z: z.log(),
    sp.sin: lambda z: z.sin(),
    sp.cos: lambda z: z.cos(),
    sp.tan: lambda z: z.tan(),
    sp.atan: lambda z: z.atan(),
    sp.sinh: lambda z: z.sinh(),
    sp.cosh: lambda z: z.cosh(),
    sp.tanh: lambda z: z.tanh(),
}


def _eval_acb(expr, env):
    """Same walk as _eval but over acb, which is what acb.integral hands us."""
    e = expr
    if e.is_Symbol:
        return env[e]
    if e.is_Integer:
        return acb(int(e))
    if e.is_Rational:
        return acb(arb(fmpq(int(e.p), int(e.q))))
    if e.is_Float:
        return acb(float(e))
    if e is sp.pi:
        return acb(arb.pi())
    if e is sp.E:
        return acb(1).exp()
    if e.is_Add:
        out = acb(0)
        for t in e.args:
            out = out + _eval_acb(t, env)
        return out
    if e.is_Mul:
        out = acb(1)
        for t in e.args:
            out = out * _eval_acb(t, env)
        return out
    if e.is_Pow:
        base, expo = e.args
        z = _eval_acb(base, env)
        if expo.is_Integer:
            return z ** int(expo)
        return z ** _eval_acb(expo, env)
    for cls, fn in _UNARY_ACB.items():
        if isinstance(e, cls):
            return fn(_eval_acb(e.args[0], env))
    raise RigorousError(f"no rigorous complex rule for {type(e).__name__} in {e}")
