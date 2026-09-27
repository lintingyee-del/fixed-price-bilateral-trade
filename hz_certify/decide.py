"""Decision and refutation, run through two independent SMT solvers.

Three things this module adds over calling z3 directly.

First, every decision runs on z3 *and* cvc5.  A `unsat` that only one of them
reports is recorded as a single-solver result, not as a proof.  The two
disagreeing is a bug in one of them and is reported as such rather than being
silently resolved in favour of whichever ran first.

Second, a `sat` answer is turned into an exact rational witness and replayed
through sympy.  A counterexample that survives that replay does not depend on
the solver at all, which makes refutation the cheapest credential available:
it costs one solver call and trusts nothing.

Third, two search modes that a plain `check()` does not give you: worst-case
optimisation over a parameter set, and finite counter-model search, which is
what an independence claim about a set of axioms actually needs.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Callable, Mapping, Sequence

import sympy as sp

__all__ = [
    "Decision",
    "prove_forall",
    "counterexample",
    "worst_case",
    "independent_axioms",
    "SOLVERS",
]

SOLVERS = ("z3", "cvc5")


class DecideError(Exception):
    pass


@dataclass
class Decision:
    status: str                      # "proved" | "refuted" | "unknown" | "conflict"
    claim: str = ""
    solvers: dict = field(default_factory=dict)     # name -> raw result
    witness: dict | None = None
    replay: str = ""                 # exact sympy replay of the witness
    note: str = ""

    def __bool__(self) -> bool:
        return self.status == "proved"

    def __str__(self) -> str:
        head = f"[{self.status}] {self.claim}"
        votes = "  ".join(f"{k}={v}" for k, v in self.solvers.items())
        out = f"{head}\n  solvers: {votes}"
        if self.witness:
            pt = ", ".join(f"{k}={v}" for k, v in self.witness.items())
            out += f"\n  witness: {pt}\n  replay:  {self.replay}"
        if self.note:
            out += f"\n  note:    {self.note}"
        return out


# ---------------------------------------------------------------------------
# backends
# ---------------------------------------------------------------------------
# cvc5.pythonic mirrors the z3 Python API closely enough that one builder
# serves both.  The two gaps are EnumSort and Abs, so finite sorts are encoded
# as bounded integers and Abs as a conditional, which keeps the encoding
# identical across backends instead of backend-specific.

def _backend(name):
    if name == "z3":
        import z3
        return z3
    if name == "cvc5":
        import cvc5.pythonic as c
        return c
    raise DecideError(f"unknown solver {name}")


def _build(expr, B, env):
    """sympy relational/boolean expression -> backend term."""
    e = sp.sympify(expr)
    if isinstance(e, sp.logic.boolalg.BooleanTrue):
        return B.BoolVal(True)
    if isinstance(e, sp.logic.boolalg.BooleanFalse):
        return B.BoolVal(False)
    if e.is_Symbol:
        return env[e]
    if e.is_Integer:
        return B.RealVal(int(e))
    if e.is_Rational:
        return B.RealVal(int(e.p)) / B.RealVal(int(e.q))
    if e.is_Float:
        r = sp.nsimplify(e, rational=True)
        return B.RealVal(int(r.p)) / B.RealVal(int(r.q))
    if isinstance(e, sp.And):
        return B.And(*[_build(a, B, env) for a in e.args])
    if isinstance(e, sp.Or):
        return B.Or(*[_build(a, B, env) for a in e.args])
    if isinstance(e, sp.Not):
        return B.Not(_build(e.args[0], B, env))
    if isinstance(e, sp.Implies):
        return B.Implies(_build(e.args[0], B, env), _build(e.args[1], B, env))
    if isinstance(e, sp.Equality):
        return _build(e.lhs, B, env) == _build(e.rhs, B, env)
    if isinstance(e, sp.Unequality):
        return _build(e.lhs, B, env) != _build(e.rhs, B, env)
    if isinstance(e, sp.StrictLessThan):
        return _build(e.lhs, B, env) < _build(e.rhs, B, env)
    if isinstance(e, sp.LessThan):
        return _build(e.lhs, B, env) <= _build(e.rhs, B, env)
    if isinstance(e, sp.StrictGreaterThan):
        return _build(e.lhs, B, env) > _build(e.rhs, B, env)
    if isinstance(e, sp.GreaterThan):
        return _build(e.lhs, B, env) >= _build(e.rhs, B, env)
    if e.is_Add:
        out = _build(e.args[0], B, env)
        for t in e.args[1:]:
            out = out + _build(t, B, env)
        return out
    if e.is_Mul:
        out = _build(e.args[0], B, env)
        for t in e.args[1:]:
            out = out * _build(t, B, env)
        return out
    if e.is_Pow:
        base, expo = e.args
        if not expo.is_Integer:
            raise DecideError(f"non-integer exponent in {e}; SMT has no rule for it")
        n = int(expo)
        b = _build(base, B, env)
        if n < 0:
            out = b
            for _ in range(-n - 1):
                out = out * b
            return B.RealVal(1) / out
        out = B.RealVal(1)
        for _ in range(n):
            out = out * b
        return out
    if isinstance(e, sp.Abs):
        a = _build(e.args[0], B, env)
        return B.If(a >= B.RealVal(0), a, -a)
    if isinstance(e, sp.Min):
        args = [_build(a, B, env) for a in e.args]
        out = args[0]
        for a in args[1:]:
            out = B.If(a < out, a, out)
        return out
    if isinstance(e, sp.Max):
        args = [_build(a, B, env) for a in e.args]
        out = args[0]
        for a in args[1:]:
            out = B.If(a > out, a, out)
        return out
    raise DecideError(f"no SMT rule for {type(e).__name__} in {e}; "
                      f"transcendental functions belong in hz_certify.rigorous")


# The two backends spell the time limit differently and cvc5 raises on an
# unknown option rather than ignoring it.  Getting this wrong once meant cvc5
# ran with no limit at all and hung on the first nonlinear query, so the
# option name is asserted here instead of being applied best-effort.
_TIMEOUT_OPTION = {"z3": "timeout", "cvc5": "tlimit-per"}

# cvc5 answers `unknown` on nonlinear real arithmetic under its default
# strategy, and slowly.  `nl-cov` switches on the cylindrical algebraic
# coverings procedure, which is a complete decision method for the theory and
# on polynomial goals is typically immediate.  Without it cvc5 contributes
# nothing to a nonlinear cross-check, so it is on by default.
_EXTRA_OPTIONS = {"z3": {}, "cvc5": {"nl-cov": "true"}}


def _configure(name, s, timeout_ms):
    s.set(_TIMEOUT_OPTION[name], timeout_ms)
    for k, v in _EXTRA_OPTIONS[name].items():
        s.set(k, v)


def _run(name, formulas, varlist, timeout_ms):
    B = _backend(name)
    s = B.Solver()
    _configure(name, s, timeout_ms)
    env = {v: B.Real(v.name) for v in varlist}
    for f in formulas:
        s.add(_build(f, B, env))
    r = s.check()
    if r == B.sat:
        m = s.model()
        pt = {}
        for v in varlist:
            try:
                pt[v] = _to_rational(m[env[v]])
            except Exception:
                pt[v] = None
        return "sat", pt
    if r == B.unsat:
        return "unsat", None
    return "unknown", None


def _to_rational(val):
    """Model value -> exact sympy Rational, for replay outside the solver."""
    if val is None:
        return None
    s = str(val)
    if hasattr(val, "numerator_as_long"):
        return sp.Rational(val.numerator_as_long(), val.denominator_as_long())
    if "/" in s:
        n, d = s.split("/")
        return sp.Rational(int(n.strip()), int(d.strip()))
    if s.endswith("?"):
        s = s[:-1]
    try:
        return sp.nsimplify(sp.Rational(s), rational=True)
    except Exception:
        return sp.nsimplify(sp.sympify(s), rational=True)


# ---------------------------------------------------------------------------
# the three entry points
# ---------------------------------------------------------------------------

def prove_forall(claim, assumptions=(), varlist=None, timeout_ms: int = 30000,
                 solvers: Sequence[str] = SOLVERS) -> Decision:
    """Prove that `assumptions` imply `claim` for all real values.

    Runs every solver in `solvers` on the negation.  A result is `proved` only
    when they all return unsat; one unsat and one unknown is reported as
    `unknown` with the split recorded, because a single solver's unsat is a
    weaker credential than two agreeing and the ledger should show which one
    you have.
    """
    claim = sp.sympify(claim)
    assumptions = [sp.sympify(a) for a in assumptions]
    if varlist is None:
        varlist = sorted(claim.free_symbols
                         | {s for a in assumptions for s in a.free_symbols},
                         key=lambda s: s.name)
    varlist = [sp.sympify(v) for v in varlist]
    negation = assumptions + [sp.Not(claim)]

    results, witness = {}, None
    for name in solvers:
        try:
            r, pt = _run(name, negation, varlist, timeout_ms)
        except Exception as exc:
            r, pt = f"error: {type(exc).__name__}", None
        results[name] = r
        if r == "sat" and witness is None:
            witness = pt

    text = f"forall {', '.join(str(v) for v in varlist)}: " + \
           (" and ".join(str(a) for a in assumptions) + " => " if assumptions else "") + \
           str(claim)

    vals = set(results.values())
    if vals == {"unsat"}:
        return Decision("proved", text, results)
    if "sat" in vals and "unsat" in vals:
        return Decision("conflict", text, results,
                        note="solvers disagree; one of them is wrong, do not record a credential")
    if "sat" in vals:
        replay = _replay(negation, witness)
        return Decision("refuted", text, results, witness=witness, replay=replay)
    if "unsat" in vals:
        return Decision("unknown", text, results,
                        note="only one solver closed it; record the solver that did, not both")
    return Decision("unknown", text, results, note="no solver decided it")


def _replay(formulas, witness):
    """Substitute an exact witness back into the formulas, outside the solver.

    This is what makes a refutation trustworthy: if sympy agrees that every
    formula in the negated claim holds at this exact rational point, the
    counterexample stands on its own.
    """
    if not witness or any(v is None for v in witness.values()):
        return "witness not fully rational; replay skipped"
    checks = []
    for f in formulas:
        val = sp.simplify(sp.sympify(f).subs(witness))
        checks.append(bool(val is sp.true or val == True))
    return ("all negation clauses confirmed exactly in sympy"
            if all(checks) else
            f"REPLAY FAILED on clause {checks.index(False)}; the model does not satisfy it")


def counterexample(claim, assumptions=(), varlist=None, **kw) -> Decision:
    """Search for a point where `assumptions` hold and `claim` fails.

    Same call as prove_forall, read from the other side.  The returned witness
    has already been replayed exactly in sympy.
    """
    d = prove_forall(claim, assumptions, varlist, **kw)
    if d.status == "proved":
        d.note = "no counterexample exists"
    return d


def worst_case(objective, constraints=(), varlist=None, sense: str = "min",
               timeout_ms: int = 30000, rounds: int = 40):
    """Bracket the optimum of `objective` over `constraints`, both ends certified.

    z3's Optimize is complete for linear arithmetic only.  On a nonlinear
    objective it returns a feasible point that need not be optimal: asked for
    the minimum of x^2 - x on [0,1] it answers -39/256 rather than -1/4.  So
    its answer is used only as a starting incumbent and never reported as the
    optimum.

    What comes back is a bracket [L, U] in which

        U   is attained at an exact rational point, so for a minimisation the
            true optimum is at most U, and the point is in `witness`
        L   is a bound proved by the dual-solver `prove_forall`, so the true
            optimum is at least L

    The status is `proved` only when the two ends meet, and `bracket`
    otherwise.  A bracket is still a usable result, and it is a truthful one,
    which the bare Optimize answer is not.
    """
    import z3
    objective = sp.sympify(objective)
    constraints = [sp.sympify(c) for c in constraints]
    if varlist is None:
        varlist = sorted(objective.free_symbols
                         | {s for c in constraints for s in c.free_symbols},
                         key=lambda s: s.name)
    varlist = [sp.sympify(v) for v in varlist]
    flip = (sense == "max")
    obj = -objective if flip else objective        # work with minimisation

    # incumbent from z3.Optimize: feasible, not necessarily optimal
    opt = z3.Optimize()
    opt.set("timeout", timeout_ms)
    env = {v: z3.Real(v.name) for v in varlist}
    for c in constraints:
        opt.add(_build(c, z3, env))
    zobj = _build(obj, z3, env)
    opt.minimize(zobj)
    if opt.check() != z3.sat:
        return Decision("unknown", f"{sense} {objective}", {"z3": "no model"},
                        note="infeasible, unbounded, or not decided")
    m = opt.model()
    best_pt = {v: _to_rational(m[env[v]]) for v in varlist}
    U = sp.nsimplify(sp.simplify(obj.subs(best_pt)), rational=True)

    def proves(level):
        return prove_forall(obj >= level, constraints, varlist,
                            timeout_ms=timeout_ms)

    def closed(u, pt):
        """Is the attained value already the optimum?

        Worth asking every time the incumbent improves, not just once at the
        start.  z3's first incumbent is rarely optimal, but the point that
        refutes a bound usually is, and without re-asking here the bisection
        only ever converges towards the answer and the bracket never closes.
        """
        if proves(u).status != "proved":
            return None
        lo = -u if flip else u
        return Decision("proved", f"{sense} {objective} = {lo}",
                        {"z3": "sat", "cvc5": "used for the bound proof"},
                        witness=pt,
                        replay=f"objective at the witness, recomputed in sympy: "
                               f"{sp.simplify(objective.subs(pt))}")

    done = closed(U, best_pt)
    if done:
        return done

    def improve(d):
        """Take the better incumbent out of a refutation, if it is better."""
        nonlocal U, best_pt
        if d.status != "refuted" or not d.witness:
            return None
        cand = sp.nsimplify(sp.simplify(obj.subs(d.witness)), rational=True)
        if cand < U:
            U, best_pt = cand, d.witness
            return closed(U, best_pt)
        return None

    # walk a certified lower bound down until it holds
    L, step, ok = U - 1, sp.Integer(1), False
    for _ in range(30):
        d = proves(L)
        if d.status == "proved":
            ok = True
            break
        done = improve(d)
        if done:
            return done
        step *= 2
        L = U - step
    if not ok:
        return Decision("unknown", f"{sense} {objective}", {"z3": "sat"},
                        witness=best_pt,
                        note=f"no certified lower bound found; best attained value {U}")

    # bisect the gap; both ends stay certified throughout
    for _ in range(rounds):
        if L == U:
            break
        M = sp.Rational(L + U, 2)
        d = proves(M)
        if d.status == "proved":
            L = M
            continue
        done = improve(d)
        if done:
            return done
        if d.status == "refuted":
            U = min(U, M)
        else:
            break

    lo, hi = (-U, -L) if flip else (L, U)
    exact = (L == U)
    val = sp.simplify(objective.subs(best_pt))
    return Decision(
        "proved" if exact else "bracket",
        f"{sense} {objective} " + (f"= {lo}" if exact else f"in [{lo}, {hi}]"),
        {"z3": "sat", "cvc5": "used for the bound proofs"},
        witness=best_pt,
        replay=f"objective at the witness, recomputed in sympy: {val}",
        note="" if exact else
             "lower end proved by both solvers, upper end attained at the witness")


class Structure:
    """A finite structure on {0, ..., n-1}, either symbolic or concrete.

    An axiom is written once against this interface and then used twice: with
    `symbolic=True` the operations are z3 integer variables and the axiom is a
    constraint to solve, with `symbolic=False` they are Python ints read off a
    found table and the axiom evaluates to a plain bool.  That second use is
    what makes an independence result self-checking, since confirming the
    counter-model then involves no solver at all.

    `op(i, j)` accepts ints or terms in either mode.  A term argument is
    resolved by an explicit case split over the finite domain, which is what
    lets a nested expression like op(op(i,j),k) stay quantifier-free.
    """

    def __init__(self, signature, n, backend=None, tables=None):
        from itertools import product
        self.n = n
        self.B = backend
        self.symbolic = backend is not None
        self.signature = signature
        self.tab = {}
        for f, ar in signature.items():
            self.tab[f] = {
                a: (backend.Int(f"{f}_" + "_".join(map(str, a))) if self.symbolic
                    else tables[f][a])
                for a in product(range(n), repeat=ar)}

    def __getattr__(self, name):
        if name.startswith("_") or name not in self.__dict__.get("signature", {}):
            raise AttributeError(name)
        return lambda *args: self.apply(name, *args)

    def apply(self, fname, *args):
        tbl = self.tab[fname]

        def rec(i, fixed):
            if i == len(args):
                return tbl[tuple(fixed)]
            a = args[i]
            if isinstance(a, int):
                return rec(i + 1, fixed + [a])
            if not self.symbolic:
                return rec(i + 1, fixed + [int(a)])
            e = rec(i + 1, fixed + [self.n - 1])
            for k in range(self.n - 2, -1, -1):
                e = self.B.If(a == k, rec(i + 1, fixed + [k]), e)
            return e

        return rec(0, [])

    # logical connectives that work in both modes
    def And(self, *xs):
        return self.B.And(*xs) if self.symbolic else all(xs)

    def Or(self, *xs):
        return self.B.Or(*xs) if self.symbolic else any(xs)

    def Not(self, x):
        return self.B.Not(x) if self.symbolic else (not x)

    def Implies(self, p, q):
        return self.B.Implies(p, q) if self.symbolic else ((not p) or q)

    def domain_constraints(self):
        return [self.B.And(v >= 0, v < self.n)
                for tbl in self.tab.values() for v in tbl.values()]

    def read(self, model):
        return {f: {a: int(str(model[v])) for a, v in tbl.items()}
                for f, tbl in self.tab.items()}


def independent_axioms(axioms: Mapping[str, Callable], domain_sizes=range(1, 5),
                       signature=None, timeout_ms: int = 30000):
    """For each axiom, look for a finite model of the others that violates it.

    Such a model is a complete proof that the axiom is not implied by the rest,
    which is what a referee asking "are these independent?" is asking for.
    Absence of a model up to the largest size tried proves nothing and is
    reported as `unknown`.

    Each axiom is a builder `f(n, S) -> list of constraints`, written against
    the `Structure` interface and expanded over the finite domain by the
    caller's own loops.  Everything is therefore quantifier-free.  That is not
    a stylistic choice: with quantifiers this search went through z3's MBQI,
    which is incomplete on this fragment and, in testing, returned `sat` or
    `unknown` for the same problem depending only on whether the range guard
    was written as a nested or a flattened conjunction.  Grounding removes
    that dependence and makes the search decide.

    Every model found is confirmed by evaluating all the axioms in plain
    Python against the extracted table, so the credential does not rest on the
    solver that found it.
    """
    import z3
    signature = signature or {}
    out = {}
    for target in axioms:
        found = None
        for n in domain_sizes:
            S = Structure(signature, n, backend=z3)
            s = z3.Solver()
            s.set("timeout", timeout_ms)
            for c in S.domain_constraints():
                s.add(c)
            for name, builder in axioms.items():
                cs = builder(n, S)
                cs = cs if isinstance(cs, (list, tuple)) else [cs]
                if name != target:
                    for c in cs:
                        s.add(c)
                else:
                    s.add(z3.Not(z3.And(*cs)) if len(cs) > 1 else z3.Not(cs[0]))
            if s.check() == z3.sat:
                tables = S.read(s.model())
                found = {"size": n, "tables": tables,
                         "recheck": _recheck_concrete(axioms, target, signature,
                                                      tables, n)}
                break
        ok = bool(found) and found["recheck"] == "confirmed"
        out[target] = Decision(
            "refuted" if ok else ("unknown" if not found else "conflict"),
            f"'{target}' is independent of the remaining axioms",
            {"z3": "sat" if found else "unsat/unknown"},
            witness=found,
            replay=(f"table re-evaluated in plain Python: {found['recheck']}"
                    if found else ""),
            note=("a finite counter-model exists, so the axiom is independent; "
                  "the table is small enough to check by hand"
                  if ok else
                  f"no counter-model up to size {max(domain_sizes)}; "
                  f"this is not a proof of dependence" if not found else
                  "a model was found but failed re-evaluation; treat the "
                  "encoding as suspect and do not record a credential"))
    return out


def _recheck_concrete(axioms, target, signature, tables, n):
    """Confirm the counter-model by evaluating every axiom in Python.

    No solver participates.  If this passes, the table plus these evaluations
    is the whole proof, and anyone can redo it.
    """
    for f, tbl in tables.items():
        if any(not (0 <= v < n) for v in tbl.values()):
            return "table leaves the domain; encoding is wrong"
    C = Structure(signature, n, backend=None, tables=tables)
    for name, builder in axioms.items():
        cs = builder(n, C)
        cs = cs if isinstance(cs, (list, tuple)) else [cs]
        holds = all(bool(c) for c in cs)
        if name == target and holds:
            return f"'{target}' actually holds in the model; not a counter-model"
        if name != target and not holds:
            return f"axiom '{name}' fails in the model; not a model of the others"
    return "confirmed"


def format_tables(witness) -> str:
    """Print a counter-model as operation tables, the form a reader can check."""
    if not witness or "tables" not in witness:
        return "(no model)"
    n = witness["size"]
    out = []
    for f, tbl in witness["tables"].items():
        ar = max(len(k) for k in tbl)
        if ar == 2:
            out.append(f"  {f}:  " + "  ".join(str(j) for j in range(n)))
            for i in range(n):
                out.append(f"    {i}   " + "  ".join(str(tbl[(i, j)]) for j in range(n)))
        else:
            out.append(f"  {f}: " + ", ".join(f"{k}->{v}" for k, v in sorted(tbl.items())))
    return "\n".join(out)
