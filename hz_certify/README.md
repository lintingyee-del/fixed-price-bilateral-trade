# hz_certify

The pre-Lean verification layer, organised by what a result asks the reader to
trust rather than by which tool produced it.

    python -m hz_certify.selftest      # 38 checks, all should pass

## Why the layers are separate names

| role | module | output | who you have to trust |
|---|---|---|---|
| certifier | `certificates` | SOS / Farkas decomposition | **nobody** — sympy expands it to zero |
| falsifier | `decide`, `rigorous` | a witness | **nobody** — replayed in exact arithmetic |
| bounder | `rigorous` | a proved enclosure | the Arb implementation |
| decider | `decide` | a verdict | the solver, so two are run |

A certificate and a counterexample can be rechecked by anyone; a verdict
cannot. Reaching for the first two rows first makes results cheaper to defend,
not just cheaper to obtain. This ordering is the whole design.

## Usage

```python
from hz_certify import rigorous as R, certificates as C, decide as D, ledger as L

L.already_recorded("my_claim")             # always first: the ledger may have it

cert = C.sos(x**3 + (1-x)**3 - Rational(1,4), [x])
#  sigma_0 = 3*(x - 1/2)^2      exact residual: 0
C.to_lean_hint(cert)                       # -> nlinarith [sq_nonneg (x - 1/2)]

R.prove_positive(sp.diff(x*sp.exp(-x), x), {x: (0, 10)})
#  [refuted] witness: x=75/8

D.prove_forall(claim, hyps)                # z3 and cvc5; proved only if both agree
D.worst_case(obj, cons)                    # both ends of the optimum certified
D.independent_axioms(axioms, signature={"op": 2})

L.record_certificate(cert, "my_claim")     # picks the layer, appends the entry
```

## Three traps this package exists to avoid

**A grid scan is not a credential.** Passing at 400 sample points says nothing
about the 401st, so no sampling loop can establish "there is no interior
maximum". `rigorous` encloses whole boxes instead. The ledger entry
`cp_sandwich_no_interior_bracket` was retracted for exactly this.

**`z3.Optimize` is wrong on nonlinear objectives, silently.** Asked for
`min x^2 - x` on `[0,1]` it returns `-39/256` when the answer is `-1/4`, and
reports `lower == upper`, so the one field that would tell you it is unsure
asserts the opposite. Its optimiser is simplex-based and complete only for
linear objectives; nonlinear goes to nlsat, a decision procedure with no
objective row. `decide.worst_case` certifies each end of a bracket separately
and closes it only when the ends meet.

**Quantifiers over a finite domain go through MBQI, which is incomplete.** In
testing, the same independence problem returned `sat` or `unknown` depending
only on whether the range guard was written `And(And(a,b), And(c,d))` or
`And(a,b,c,d)`. `independent_axioms` is fully ground, and every model it finds
is confirmed by re-evaluating the axioms in plain Python against the extracted
table, with no solver involved.

## Limits

`sos` handles polynomials only; transcendental bounds go to `rigorous`. A
failed `sos` is not evidence the claim is false, only that no decomposition
exists at that degree. `prove_nonneg` cannot certify a bound attained inside
the domain and reports `unknown` at the contact point, which is the honest
answer. `mpmath` is not rigorous and must not be used for a bound that goes
into a paper; use `rigorous.integral` or `rigorous.range_enclosure`.

## Dependencies

`sympy`, `z3-solver`, `cvc5`, `python-flint` (Arb), `cvxpy` with an SDP solver
(`SCS` or `CLARABEL`). All present in `AutoFigure-main/.venv`, which is the
interpreter these must be run under; the base Python 3.11 has none of them.
