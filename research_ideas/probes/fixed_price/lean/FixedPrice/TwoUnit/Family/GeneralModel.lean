import FixedPrice.TwoUnit.Model

/-!
# General two-unit instances (measure-theoretic model of `two_units.tex`, eq:two-model)

The seller owns two units. The buyer's marginal values `(B₁, B₂)` and the seller's marginal
costs `(S₁, S₂)` are random vectors with `B₁ ≥ B₂ > 0` and `0 < S₁ ≤ S₂`; the two vectors are
independent with finite first moments, and the coordinates of each vector may be dependent.
A common price `z` trades unit `i` exactly when `S_i ≤ z ≤ B_i` (the inclusive rule of
`FixedPrice.TwoUnit.unitGain`; accepting units form an initial segment). Then

* `M₂ = E(S₁ + S₂)` (`sellerWelfare`),
* `O₂ = Σ_i E max{B_i, S_i}` (`optimalWelfare`),
* `Γ₂(z) = Σ_i E[(B_i - S_i) 1{S_i ≤ z ≤ B_i}]` (`priceGain`),
* the best common-price ratio `(M₂ + sup_{z ≥ 0} Γ₂(z))/O₂` (`bestRatio`),
* `r₂* = inf (M₂ + sup_{z≥0} Γ₂)/O₂` over valid instances (`r2star`).

Independence is built in: expectations of functions of both vectors are taken under the product
of the buyer law and the seller law. The finite model of `FixedPrice/TwoUnit/Model.lean`
(lists of weighted ordered vectors, used by Theorem D) is the special case `ofFinite`; that
statement is `Family.OfFiniteStatement` (`Statements.lean`), proved by work package E in
`Family/OfFinite.lean`. This file holds definitions only.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ENNReal

namespace FixedPrice.TwoUnit

/-- A two-unit instance: the law of the buyer vector `(B₁, B₂)` and the law of the seller vector
`(S₁, S₂)`, drawn independently. -/
structure GenInstance where
  buyer : Measure (ℝ × ℝ)
  seller : Measure (ℝ × ℝ)

namespace GenInstance

variable (I : GenInstance)

/-- Validity: probability laws of strictly positive ordered vectors with finite first moments.
With `0 < B₂ ≤ B₁` and `0 < S₁ ≤ S₂`, integrability of `B₁` and `S₂` gives all first moments. -/
structure Valid : Prop where
  buyer_prob : IsProbabilityMeasure I.buyer
  seller_prob : IsProbabilityMeasure I.seller
  buyer_ordered : ∀ᵐ b ∂I.buyer, 0 < b.2 ∧ b.2 ≤ b.1
  seller_ordered : ∀ᵐ s ∂I.seller, 0 < s.1 ∧ s.1 ≤ s.2
  buyer_integrable : Integrable (fun b : ℝ × ℝ => b.1) I.buyer
  seller_integrable : Integrable (fun s : ℝ × ℝ => s.2) I.seller

/-- The joint law of the independent pair (buyer vector, seller vector). -/
def joint : Measure ((ℝ × ℝ) × (ℝ × ℝ)) := I.buyer.prod I.seller

/-- `M₂ = E(S₁ + S₂)`, the seller welfare without trade. -/
def sellerWelfare : ℝ := ∫ s, (s.1 + s.2) ∂I.seller

/-- `O₂ = Σ_i E max{B_i, S_i}`, the efficient welfare. -/
def optimalWelfare : ℝ := ∫ x, (max x.1.1 x.2.1 + max x.1.2 x.2.2) ∂I.joint

/-- `O₂ - M₂ = Σ_i E(B_i - S_i)_+`, the efficient gains. -/
def efficientGains : ℝ := I.optimalWelfare - I.sellerWelfare

/-- `Γ₂(z) = Σ_i E[(B_i - S_i) 1{S_i ≤ z ≤ B_i}]`, the gain of the common price `z`. -/
def priceGain (z : ℝ) : ℝ :=
  ∫ x, (unitGain x.1.1 x.2.1 z + unitGain x.1.2 x.2.2 z) ∂I.joint

/-- `sup_{z ≥ 0} Γ₂(z)`, the best price gain. -/
def bestGain : ℝ := sSup (I.priceGain '' Ici 0)

/-- `(M₂ + sup_{z≥0} Γ₂(z))/O₂`, the optimal common-price welfare ratio. -/
def bestRatio : ℝ := (I.sellerWelfare + I.bestGain) / I.optimalWelfare

end GenInstance

/-- `r₂* = inf (M₂ + sup_{z ≥ 0} Γ₂)/O₂` over valid two-unit instances (eq:two-model). -/
def r2star : ℝ := sInf {r | ∃ I : GenInstance, I.Valid ∧ I.bestRatio = r}

/-- A sequence of instances has a common escaping buyer atom: the buyer law of the `n`-th
instance puts mass `η_n > 0` on the common point `(x_n, x_n)`, with `η_n → 0`, `x_n → ∞` and
first moment `η_n x_n → 1` per unit. -/
def HasCommonEscapingAtom (I : ℕ → GenInstance) : Prop :=
  ∃ x η : ℕ → ℝ, (∀ n, 0 < η n ∧ (I n).buyer {(x n, x n)} = ENNReal.ofReal (η n)) ∧
    Tendsto η atTop (𝓝 0) ∧ Tendsto x atTop atTop ∧
    Tendsto (fun n => η n * x n) atTop (𝓝 1)

/-- The buyer and seller laws of the instances `I n` converge weakly to `μB` and `μS`: all of them
are probability measures, and the laws converge in the topology of `ProbabilityMeasure (ℝ × ℝ)`
(convergence of the integrals of every bounded continuous function). An escaping buyer atom of
vanishing mass does not affect this limit. -/
def LawsConvergeTo (I : ℕ → GenInstance) (μB μS : Measure (ℝ × ℝ)) : Prop :=
  ∃ (hB : ∀ n, IsProbabilityMeasure (I n).buyer) (hS : ∀ n, IsProbabilityMeasure (I n).seller)
    (hμB : IsProbabilityMeasure μB) (hμS : IsProbabilityMeasure μS),
    Tendsto (β := ProbabilityMeasure (ℝ × ℝ)) (fun n => ⟨(I n).buyer, hB n⟩) atTop
        (𝓝 ⟨μB, hμB⟩) ∧
      Tendsto (β := ProbabilityMeasure (ℝ × ℝ)) (fun n => ⟨(I n).seller, hS n⟩) atTop
        (𝓝 ⟨μS, hμS⟩)

/-! ### The finite model of `Model.lean` as a special case -/

/-- The finitely supported instance with buyer types `B` and seller types `S`
(each a list of `((v₁, v₂), weight)`). -/
def ofFinite (B S : RLaw) : GenInstance where
  buyer := (B.map fun b => ENNReal.ofReal b.2 • Measure.dirac b.1).sum
  seller := (S.map fun s => ENNReal.ofReal s.2 • Measure.dirac s.1).sum

end FixedPrice.TwoUnit
