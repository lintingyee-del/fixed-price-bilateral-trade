import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Theorem E (two units): the pricing functional, definitions

Source: `manuscript/two_units.tex`, subsection "The pricing functional" (`sec:two-pricing`),
equations `eq:two-kernel`, `eq:two-potential`, `eq:two-operator`, `eq:two-functional`,
`eq:two-price-target`; proofs in `manuscript/two_unit_pricing_proofs.tex` (`app:two-pricing`).
The normalized model of `sec:two-tail` (`eq:two-body`) is used only by the welfare clause of
part (iii). The price constructed in the proof of part (iii) (`realizedPrice`) is built from
mathlib's `StieltjesFunction`.

Conventions.
* Units are indexed by `Fin 2`. Lean index `0` is the paper's unit 1, index `1` is unit 2.
* A buyer body `Z_i` is given by its law `law i : Measure ℝ`. The survival function is
  `H_i(s) = (law i).real (Ioi s)`, and the buyer Stieltjes measure `-dH_i` is `law i` itself
  (mathlib: `ProbabilityTheory.measure_cdf`).
* Functions on `[0, b̄]` are functions `ℝ → ℝ`; every property is stated on `Icc 0 bbar`, and
  values outside `[0, b̄]` never enter a statement about `[0, b̄]`.
* Right-continuity on `[0, b̄]` is `ContinuousWithinAt f (Icc s bbar) s` for `s ∈ Icc 0 bbar`.

The file also collects, in `PricingScalarCertificates`, the scalar facts that the verification
ledger already certifies by machine (exact / z3 / cvc5). By the user's standing rule these are
not re-proved in Lean; they enter every theorem that needs them as an explicit hypothesis.
Nothing in this file is proved, and no declaration here is a placeholder.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-! ### Kernel, gain and potential (`eq:two-kernel`, `eq:two-potential`) -/

/-- The compensation sign of `eq:two-operator`: `ε₁ = -1` for the first unit (Lean index `0`)
and `ε₂ = 1` for the second unit (Lean index `1`). -/
def compSign (i : Fin 2) : ℝ := if i = 0 then -1 else 1

/-- `L̄_i(s) = 1 + E (Z_i - s)_+` (`eq:two-kernel`). The integrand is the one of
`FixedPrice.tailIntegral` in `FixedPrice/BuyerTail.lean`. -/
def Lbar (μ : Measure ℝ) (s : ℝ) : ℝ := 1 + ∫ x, max (x - s) 0 ∂μ

/-- `g_i(s,z) = 1{s<z} [1 + E((Z_i - s) 1{z ≤ Z_i})]` (`eq:two-kernel`): strict seller
acceptance and inclusive buyer acceptance. -/
def gainKernel (μ : Measure ℝ) (s z : ℝ) : ℝ :=
  if s < z then 1 + ∫ x in Ici z, (x - s) ∂μ else 0

/-- The positive kernel `∫_{(s, b̄]} (t - s) ϖ(t) (-dH)(t)` of `eq:two-potential` and
`eq:two-operator`. -/
def kernelIntegral (bbar : ℝ) (μ : Measure ℝ) (ϖ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in Ioc s bbar, (t - s) * ϖ t ∂μ

/-- The gain `G^ϖ(s) = L̄(s) ϖ(s) - ∫_{(s,b̄]} (t - s) ϖ(t) (-dH)(t)` of `eq:two-potential`.
The atom at `s` is excluded from `ϖ(s)` (trace convention of the paper). -/
def gainFromMass (bbar : ℝ) (μ : Measure ℝ) (ϖ : ℝ → ℝ) (s : ℝ) : ℝ :=
  Lbar μ s * ϖ s - kernelIntegral bbar μ ϖ s

/-- The seller potential `ψ^ϖ(s) = d s - L̄(s) + G^ϖ(s)` of `eq:two-potential`. -/
def sellerPotential (bbar : ℝ) (μ : Measure ℝ) (d : ℝ) (ϖ : ℝ → ℝ) (s : ℝ) : ℝ :=
  d * s - Lbar μ s + gainFromMass bbar μ ϖ s

/-! ### Cumulative masses, compensations, feasibility -/

/-- `f` is bounded on `[0, b̄]`. -/
def IsBoundedOn (bbar : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ s ∈ Icc 0 bbar, |f s| ≤ C

/-- A cumulative mass on `[0, b̄]`: nonnegative, nonincreasing and right-continuous
(`sec:two-pricing`, the function `ϖ(s) = ϖ(b̄) + π̂₀((s, b̄])`). -/
structure IsCumulativeMass (bbar : ℝ) (ϖ : ℝ → ℝ) : Prop where
  nonneg : ∀ s ∈ Icc 0 bbar, 0 ≤ ϖ s
  antitoneOn : AntitoneOn ϖ (Icc 0 bbar)
  rightContinuous : ∀ s ∈ Icc 0 bbar, ContinuousWithinAt ϖ (Icc s bbar) s

/-- A compensation in `𝒱`: bounded, nondecreasing and right-continuous on `[0, b̄]`. -/
structure IsCompensation (bbar : ℝ) (ϑ : ℝ → ℝ) : Prop where
  bounded : IsBoundedOn bbar ϑ
  monotoneOn : MonotoneOn ϑ (Icc 0 bbar)
  rightContinuous : ∀ s ∈ Icc 0 bbar, ContinuousWithinAt ϑ (Icc s bbar) s

/-- The compensation class `𝒱`. -/
def compensationClass (bbar : ℝ) : Set (ℝ → ℝ) := {ϑ | IsCompensation bbar ϑ}

/-- `ϖ` is a feasible cumulative mass for `(d, ϑ)`: a cumulative mass with
`ψ₁^ϖ ≥ -ϑ` and `ψ₂^ϖ ≥ ϑ` on `[0, b̄]`, i.e. `ε_i ϑ ≤ ψ_i^ϖ`. -/
structure IsFeasibleMass (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d : ℝ) (ϑ ϖ : ℝ → ℝ) :
    Prop where
  cumulative : IsCumulativeMass bbar ϖ
  potential_ge : ∀ i : Fin 2, ∀ s ∈ Icc 0 bbar,
    compSign i * ϑ s ≤ sellerPotential bbar (law i) d ϖ s

/-! ### The operator, its least fixed point, and the functional
(`eq:two-operator`, `eq:two-functional`) -/

/-- The obstacle `A_{i,d,ϑ} ϖ (t)` of `eq:two-operator`. -/
def obstacle (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d : ℝ) (ϑ : ℝ → ℝ) (i : Fin 2)
    (ϖ : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - d * t / Lbar (law i) t + compSign i * ϑ t / Lbar (law i) t
    + kernelIntegral bbar (law i) ϖ t / Lbar (law i) t

/-- The operator `(𝒯_{d,ϑ} ϖ)(s) = sup_{s ≤ t ≤ b̄} max {0, A₁ϖ(t), A₂ϖ(t)}` of
`eq:two-operator`. For `s ∈ Icc 0 bbar` the set is nonempty; its boundedness is a lemma. -/
def pricingOperator (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d : ℝ) (ϑ : ℝ → ℝ)
    (ϖ : ℝ → ℝ) (s : ℝ) : ℝ :=
  sSup ((fun t => max 0 (max (obstacle bbar law d ϑ 0 ϖ t) (obstacle bbar law d ϑ 1 ϖ t)))
    '' Icc s bbar)

/-- `ϖ_{d,ϑ}`: the limit of the iteration from zero. The iterates increase, so the limit is
their supremum. Theorem E (i) asserts that this is the unique bounded fixed point of
`pricingOperator` and the pointwise least feasible cumulative mass. -/
def leastMass (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d : ℝ) (ϑ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ⨆ n : ℕ, (pricingOperator bbar law d ϑ)^[n] 0 s

/-- `𝒥_d^{(2)}(H₁,H₂) = inf_{ϑ ∈ 𝒱} ϖ_{d,ϑ}(0)` (`eq:two-functional`). Theorem E (ii) asserts
that the infimum is attained. -/
def pricingValue (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d : ℝ) : ℝ :=
  ⨅ ϑ : compensationClass bbar, leastMass bbar law d ϑ 0

/-- The canonical compensation `Θ_ϖ(s) = -inf_{0 ≤ t ≤ s} ψ₁^ϖ(t)`. -/
def canonicalCompensation (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d : ℝ) (ϖ : ℝ → ℝ)
    (s : ℝ) : ℝ :=
  -sInf (sellerPotential bbar (law 0) d ϖ '' Icc 0 s)

/-! ### Prices (`eq:two-price-target`) -/

/-- The price target `eq:two-price-target` for a price measure `π`, at every ordered pair of
seller costs `0 ≤ s₁ ≤ s₂` (including costs above `b̄`). A seller pair is `s : Fin 2 → ℝ`. -/
def PriceTarget (law : Fin 2 → Measure ℝ) (d β : ℝ) (π : Measure ℝ) : Prop :=
  ∀ s : Fin 2 → ℝ, 0 ≤ s 0 → s 0 ≤ s 1 →
    β * ∑ i, Lbar (law i) (s i) - β * d * (s 0 + s 1) ≤
      ∑ i, ∫ z, gainKernel (law i) (s i) z ∂π

/-- A price probability on `[0, ∞)` with bounded support. -/
structure IsBoundedPriceLaw (π : Measure ℝ) : Prop where
  isProbability : IsProbabilityMeasure π
  nonneg : π (Iio 0) = 0
  bounded : ∃ M : ℝ, π (Ioi M) = 0

/-! ### The price constructed in the proof of part (iii) -/

/-- The cumulative mass `ϖ_ext` (normalized by `β`) of the price constructed in the proof of
Theorem E (iii) (`two_unit_pricing_proofs.tex`, "A bounded price interval and the reverse
implication"): `ϖ(0)` below `0` (no negative prices), `ϖ` on `[0, b̄]`, and the realized tail
`(ϖ(b̄) - d (t - b̄))_+` above `b̄`, which is the cumulative mass of the density `d` on
`(b̄, b̄ + ϖ(b̄)/d)`. -/
def extendedMass (bbar d : ℝ) (ϖ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then ϖ 0 else if t ≤ bbar then ϖ t else max (ϖ bbar - d * (t - bbar)) 0

open Classical in
/-- The Stieltjes measure `-dϖ_ext` of the nondecreasing function `-extendedMass`: `-dϖ` on
`(0, b̄]` and the density `d` on `(b̄, b̄ + ϖ(b̄)/d)`, so that its mass on `(t, ∞)` is `ϖ_ext(t)`.
The construction needs `-extendedMass` to be a Stieltjes function (nondecreasing and
right-continuous). That holds for every cumulative mass `ϖ` on `[0, b̄]` (`IsCumulativeMass`)
with `d ≥ 0` and `b̄ ≥ 0`, in particular for `ϖ_{d,ϑ}` (an `OrderedBuyerPair` has `b̄ ≥ 0`); on
other inputs the value is the fallback `0`, which no statement reads. -/
def extendedMassMeasure (bbar d : ℝ) (ϖ : ℝ → ℝ) : Measure ℝ :=
  if h : Monotone (fun t => -extendedMass bbar d ϖ t) ∧
      ∀ x, ContinuousWithinAt (fun t => -extendedMass bbar d ϖ t) (Ici x) x then
    (StieltjesFunction.mk (fun t => -extendedMass bbar d ϖ t) h.1 h.2).measure
  else 0

/-- The price constructed in the proof of Theorem E (iii): "We put `-β dϖ` on `(0, b̄]` and
density `βd` on `(b̄, b̄ + ϖ(b̄)/d)`. Its mass is `βϖ(0) ≤ 1`, and the remainder is put at
zero." -/
def realizedPrice (bbar d β : ℝ) (ϖ : ℝ → ℝ) : Measure ℝ :=
  ENNReal.ofReal β • extendedMassMeasure bbar d ϖ +
    ENNReal.ofReal (1 - β * ϖ 0) • Measure.dirac 0

/-! ### Buyer bodies -/

/-- Laws of two buyer bodies supported on `[0, b̄]`. -/
structure IsBuyerBodies (bbar : ℝ) (law : Fin 2 → Measure ℝ) : Prop where
  isProbability : ∀ i, IsProbabilityMeasure (law i)
  supported : ∀ i, law i (Icc 0 bbar)ᶜ = 0

/-- An ordered buyer pair supported on `[0, b̄]`: `Z₁ ≥_st Z₂`, i.e. `H₁ ≥ H₂`. -/
structure OrderedBuyerPair where
  bbar : ℝ
  law : Fin 2 → Measure ℝ
  bodies : IsBuyerBodies bbar law
  ordered : ∀ s : ℝ, law 1 (Ioi s) ≤ law 0 (Ioi s)

namespace OrderedBuyerPair

/-- `𝒥_d^{(2)}(H₁,H₂)` of the pair, computed on its interval `[0, b̄]`. -/
def value (P : OrderedBuyerPair) (d : ℝ) : ℝ := pricingValue P.bbar P.law d

/-- Both buyer bodies have finite support. -/
def HasFiniteSupport (P : OrderedBuyerPair) : Prop :=
  ∃ S : Finset ℝ, ∀ i, P.law i (↑S)ᶜ = 0

end OrderedBuyerPair

/-- `δ ⌊x / δ⌋`. -/
def roundDown (δ x : ℝ) : ℝ := δ * (⌊x / δ⌋ : ℝ)

/-- The laws of the rounded bodies `δ ⌊Z_i / δ⌋`, whose survival functions are `H_i^δ`. -/
def roundedLaw (δ : ℝ) (law : Fin 2 → Measure ℝ) : Fin 2 → Measure ℝ :=
  fun i => (law i).map (roundDown δ)

/-! ### The normalized model of `sec:two-tail` (welfare clause of part (iii)) -/

/-- Expected normalized welfare at the price `z`: `E(Y₁ + Y₂) + Γ₀(z)` with
`Γ₀(z) = Σ_i E[1{Y_i < z} (1 + (Z_i - Y_i) 1{z ≤ Z_i})]` (`eq:two-body`), for independent buyer
bodies with marginal laws `law i` and a seller body vector with law `ν`. -/
def normalizedWelfare (law : Fin 2 → Measure ℝ) (ν : Measure (Fin 2 → ℝ)) (z : ℝ) : ℝ :=
  ∫ y, (y 0 + y 1) ∂ν +
    ∑ i, ∫ y, ∫ x, (if y i < z then 1 + (if z ≤ x then x - y i else 0) else 0) ∂(law i) ∂ν

/-- Normalized efficient welfare `2 + Σ_i E max {Z_i, Y_i}` (denominator of `eq:two-body`). -/
def normalizedEfficientWelfare (law : Fin 2 → Measure ℝ) (ν : Measure (Fin 2 → ℝ)) : ℝ :=
  2 + ∑ i, ∫ y, ∫ x, max x (y i) ∂(law i) ∂ν

/-! ### Machine-certified scalar facts (explicit hypotheses, not re-proved in Lean) -/

/-- Scalar facts that the verification ledger already certifies by machine. They are used by
the proof of Theorem E and must not be re-proved in Lean (standing user rule); each theorem that
needs them takes `cert : PricingScalarCertificates`. Every field is a closed, universally
quantified real-arithmetic statement copied from the certified formula.

Ledger `C:/Users/86131/Documents/proof_factgraph/ledger.toml`; formulas in
`research_ideas/probes/fixed_price/manuscript/checks/first_layer_20260921/results.json`
(replayed in `first_layer_repair_20260921/results.json`); paper graph nodes
`L_20260921_pricing_obstacle`, `L_20260921_pricing_scalar`, `L_20260921_buyer_rounding`. -/
structure PricingScalarCertificates : Prop where
  /-- `two_units.tex` `eq:two-operator` vs `eq:two-potential`: `ϖ ≥ A_i ϖ ⟺ ψ_i ≥ ε_i ϑ`.
  Ledger `fpm_20260921_pricing_obstacle_new_exact` (exact), check
  `potential_minus_compensation_obstacle_identity`. -/
  obstacle_identity : ∀ L u d s ε θ I : ℝ, L ≠ 0 →
    L * (u - (1 - d * s / L + ε * θ / L + I / L)) = (d * s - L + L * u - I) - ε * θ
  /-- `two_unit_pricing_proofs.tex`, "Convexity and attainment": the potential constraints are
  affine in `(ϖ, d, ϑ)`. Ledger `fpm_20260921_pricing_obstacle_new_exact` (exact), check
  `feasible_triple_affine_slack`. -/
  affine_slack : ∀ a L s d₀ d₁ u₀ u₁ I₀ I₁ θ₀ θ₁ ε : ℝ,
    -(a * I₀ + (1 - a) * I₁) + L * (a * u₀ + (1 - a) * u₁) - L + (a * d₀ + (1 - a) * d₁) * s
        - ε * (a * θ₀ + (1 - a) * θ₁) =
      a * (-I₀ + L * u₀ - L + d₀ * s - ε * θ₀) + (1 - a) * (-I₁ + L * u₁ - L + d₁ * s - ε * θ₁)
  /-- `two_units.tex` `sec:two-pricing`: `ψ₁ ≥ -ϑ`, `ψ₂ ≥ ϑ`, `ϑ` nondecreasing give a
  nonnegative ordered potential sum. Ledger `fpm_20260921_pricing_obstacle_new_exact` (exact),
  check `ordered_compensation_farkas_certificate`. -/
  ordered_farkas : ∀ ψ₁ ψ₂ θ₁ θ₂ : ℝ, 0 ≤ ψ₁ + θ₁ → 0 ≤ ψ₂ - θ₂ → 0 ≤ θ₂ - θ₁ → 0 ≤ ψ₁ + ψ₂
  /-- `two_unit_pricing_proofs.tex`, "Rounding the buyer bodies": adding tail mass `δ` raises
  each potential by `-ΔL + ΔG + δ ≥ 0`. Ledger `fpm_20260921_pricing_obstacle_new_exact`
  (exact), check `rounding_tail_repair_farkas_certificate`. -/
  tail_repair : ∀ ΔL ΔG δ : ℝ, 0 ≤ ΔL → ΔL ≤ δ → 0 ≤ ΔG → 0 ≤ -ΔL + ΔG + δ
  /-- `two_unit_pricing_proofs.tex`, "The least price for fixed compensation": the kernel mass
  `(L̄ - 1)/L̄ ≤ b̄/(1+b̄)` after clearing denominators. Ledger
  `fpm_20260921_pricing_scalar_new_smt` (z3 and cvc5 unsat), check
  `scalar_kernel_contraction_after_common_denominator`. -/
  kernel_contraction : ∀ b L E k : ℝ, 0 ≤ b → 1 ≤ L → L ≤ b + 1 → 0 ≤ E →
    |k| ≤ E * (L - 1) → (b + 1) * |k| ≤ E * L * b
  /-- Same passage: the three-way maximum does not increase uniform differences. Ledger
  `fpm_20260921_pricing_scalar_new_smt` (z3 and cvc5), check `two_obstacle_max_is_nonexpansive`. -/
  max_nonexpansive : ∀ E x₁ x₂ y₁ y₂ : ℝ, 0 ≤ E → |x₁ - y₁| ≤ E → |x₂ - y₂| ≤ E →
    |max 0 (max x₁ x₂) - max 0 (max y₁ y₂)| ≤ E
  /-- "The constant `ϖ = 1 + b̄`, with `ϑ = 0`, is feasible." Ledger
  `fpm_20260921_pricing_scalar_new_smt` (z3 and cvc5), check
  `constant_cumulative_mass_feasible_scalar`. -/
  constant_mass_feasible : ∀ L b d s : ℝ, 0 < d → 0 ≤ s → s ≤ b → 1 ≤ L → L ≤ b + 1 →
    0 ≤ -L + b + d * s + 1
  /-- Canonical prefix, one-step (finite) form. Ledger `fpm_20260921_pricing_scalar_new_smt`
  (z3 and cvc5), check `finite_canonical_prefix_extension`. -/
  prefix_extension : ∀ old ψ₁ ψ₂ : ℝ, old ≤ ψ₂ → 0 ≤ ψ₁ + ψ₂ →
    old ≤ max old (-ψ₁) ∧ max old (-ψ₁) ≤ ψ₂ ∧ -ψ₁ ≤ max old (-ψ₁)
  /-- "Rounding the buyer bodies": `0 ≤ L̄ - L̄^δ ≤ δ` pointwise. Ledger
  `fpm_20260921_buyer_rounding_pointwise_smt` (z3 and cvc5), check
  `rounded_stoploss_loss_all_real_regions`. -/
  rounded_stopLoss : ∀ r x δ s : ℝ, 0 ≤ r → r ≤ x → x < δ + r → 0 < δ → 0 ≤ s →
    0 ≤ max 0 (x - s) - max 0 (r - s) ∧ max 0 (x - s) - max 0 (r - s) ≤ δ
  /-- `g_i ≥ g_i^δ`, branch where both buyers accept. Ledger
  `fpm_20260921_buyer_rounding_pointwise_smt`, check `rounded_gain_both_buyers_accept`. -/
  rounded_gain_both : ∀ x z r s : ℝ, 0 ≤ s → s < z → z ≤ r → r ≤ x → 0 ≤ x - r
  /-- `g_i ≥ g_i^δ`, branch where only the original buyer accepts. Ledger
  `fpm_20260921_buyer_rounding_pointwise_smt`, check `rounded_gain_only_original_buyer_accepts`. -/
  rounded_gain_original_only : ∀ x z r s : ℝ, 0 ≤ r → r < z → z ≤ x → 0 ≤ s → s < z →
    0 ≤ x - s
  /-- The four acceptance branches are exhaustive. Ledger
  `fpm_20260921_buyer_rounding_pointwise_smt`, check
  `rounded_gain_acceptance_branches_are_exhaustive`. -/
  rounded_branches : ∀ x z r s : ℝ, r ≤ x →
    z ≤ s ∨ (z ≤ r ∧ s < z) ∨ (x < z ∧ s < z) ∨ (z ≤ x ∧ r < z ∧ s < z)

end FixedPrice.TwoUnit.Pricing
