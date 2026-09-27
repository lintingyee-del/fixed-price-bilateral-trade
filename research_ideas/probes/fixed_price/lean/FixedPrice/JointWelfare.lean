import FixedPrice.PricingLemma

/-! Welfare functionals under a joint prior on `ℝ × ℝ` (seller value first, buyer value second),
used in Section 11. -/

noncomputable section

open Set MeasureTheory

namespace FixedPrice

/-- Expected welfare of a mechanism with trade probability `φ` under a joint prior `μ`. -/
def mechWelfare (μ : Measure (ℝ × ℝ)) (φ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p, (p.1 + (p.2 - p.1) * φ p.1 p.2) ∂μ

/-- The trade gain of the posted price `z` at values `(s, b)`, inclusive rule. -/
def priceGainAt (z : ℝ) (p : ℝ × ℝ) : ℝ := if p.1 ≤ z ∧ z ≤ p.2 then p.2 - p.1 else 0

/-- Expected welfare of the posted price `z` under a joint prior `μ`. -/
def jointPriceWelfare (μ : Measure (ℝ × ℝ)) (z : ℝ) : ℝ := ∫ p, (p.1 + priceGainAt z p) ∂μ

/-- First-best welfare `E max {V_s, V_b}` under a joint prior `μ`. -/
def firstBest (μ : Measure (ℝ × ℝ)) : ℝ := ∫ p, max p.1 p.2 ∂μ

theorem priceGainAt_nonneg (z : ℝ) (p : ℝ × ℝ) : 0 ≤ priceGainAt z p := by
  unfold priceGainAt
  split_ifs with h
  · linarith [h.1, h.2]
  · exact le_rfl

theorem measurable_priceGainAt (z : ℝ) : Measurable (priceGainAt z) :=
  measurable_tradeGain z

end FixedPrice
