# Supplementary material

These files accompany "The Exact Welfare Guarantee of Fixed-Price Bilateral
Trade". They contain the finite instances, certificates and interval data behind
the computer-assisted statements of the paper, and a script that replays them.

    python verify.py          # all checks, about a minute
    python verify.py --fast   # skips the two interval covers

The script needs Python 3.9 or later with `python-flint` (Arb ball arithmetic)
and `sympy`. It prints one PASS or FAIL line per check and exits with status 0
when every check passes. It performs no search: partitions, brackets and
certificates are read from the files and re-evaluated. Fractions are exact
rational numbers. In interval data, a center accompanied by a radius denotes an
enclosure, not a point estimate. Decimal display fields are provided for
convenience.

## What `verify.py` recomputes

| Statement in the paper | Data | Check |
|---|---|---|
| Numerical values after Theorem A: the enclosure of beta_*, the value of C_*, the bounds on tau(C_*), and the bounds on r_eta and R_eta at eta = 1e-12 | none needed | Ball arithmetic on the scalar curve (3)-(5). The root of S = 1 + tau is bracketed by a sign change, which suffices because S decreases and tau increases by (7). |
| Theorem D, general instance below 0.7290804 | `general_instance.json` | Exact rational welfare at every valuation event; the stored integers are reproduced. |
| Theorem D, symmetric instance below 0.83693 | `symmetric_instance.json` | Same replay; the ratio at each event is reproduced. |
| Lower bound 73/100 on the two affine boundary families | `affine_boundary_coefficients.json` | The polynomial is rebuilt from M and G, and every leaf of the bisection tree is expanded in the Bernstein basis with nonnegative coefficients. |
| Existence and uniqueness of the stationary point of the family, at beta = 18227/25000 and uniformly on [18227/25000, 729081/1000000] | `stationary_lower_endpoint.json`, `stationary_uniform_cover.json` | Every leaf is re-evaluated in 192-bit ball arithmetic: the bracket of the algebraic residual, then the stated exclusion (no algebraic root, P_l above one, wrong phase order, nonzero connection equation) or, on the retained cells, positivity of the branch derivative. The leaves tile the t-interval, the retained cells are contiguous, and the connection equation changes sign across them. |
| Open questions: two reductions of the second buyer that fail | `obstructions.json`, `obstructions.md` | Exact replay of both instances, symbolic integration of the three pointwise remainders, and the endpoint arithmetic. |

## What `verify.py` only reads

The following files store enclosures and records of symbolic identities whose
formulas are stated in the appendix on the family minimum. The script confirms
that the stored enclosures have the signs used there and that every recorded
residual is zero; it does not re-derive them.

- `endpoint_identities.json`, `boundary_identities.json`: endpoint derivative
  identities and compactness bounds.
- `branch_positive_factors.json`, `branch_elimination.json`: positive factors
  and polynomial elimination identities for the algebraic branch. The
  monotonicity of the algebraic residual in p, which the covers use, is proved
  from these factors in the appendix.
- `stationary_physical_conditions.json`: enclosures of every recovered contact
  parameter over the full rational root box, giving strict contact and slope
  orders and positivity of the quadratic on the whole integration interval.
- `reference_price_coefficients.json`, `second_unit_kernel_identities.json`,
  `second_unit_kernel_bounds.json`: identities and sign enclosures for the
  reference price and the second-unit kernel. These apply with one reference
  side fixed, as specified in the reference-price remark; they do not establish
  the conjectured comparison for arbitrary buyer and seller pairs.

## File formats

- `general_instance.json`: the rational polygon vertices `X, P`, their curve
  parameters, and 131 ordered buyer and seller types. Each type is stored as
  `[[first value, second value], weight]`, with integer entries. Divide weights
  by `probability_denominator` and values by `value_denominator`. The type
  vectors are drawn independently. The `replay` object contains efficient
  welfare, maximal posted price welfare, and the exact ratio in the common
  integer scale.
- `symmetric_instance.json`: rational marginal laws and their common-quantile
  couplings. Each joint-law row is `[probability, [first value, second value]]`.
  The buyer's vector has the law of the seller's reversed vector, independently
  drawn. `prices` and `welfare_ratios` give all valuation events and their ratios.
- In both instances, the inclusive event value dominates adjacent open
  intervals, so the finite maximum over valuation events covers every real
  posted price.
- The family data use the shorter symbols from the defining formulas:
  `t, p, C, lambda` mean the paper's family parameters t_f, p_f, C_f, d_f.
  `Pl`, `q`, `A`, and the connection equation refer to the eliminated
  stationary system.
- In the two covers, each leaf has a `t_box`, a `p_bracket` on whose ends the
  algebraic residual has opposite signs, and a `reason`. The `unresolved` lists
  are empty.

`manifest.json` lists the supplied files with their SHA-256 checksums.
