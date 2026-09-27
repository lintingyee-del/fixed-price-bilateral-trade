import FixedPrice.MechanismWelfare
import FixedPrice.TheoremA

/-! The mechanism class of Corollary 11.3 on the nonnegative report domain, and the guarantee
direction. A mechanism is described by its trade probability `φ` and expected buyer-to-seller
transfer `pay`; dominant-strategy incentive compatibility is required in expectation and
individual rationality in the form `s φ ≤ pay ≤ b φ`, which realizationwise individual
rationality with strong budget balance implies. Every fixed price belongs to the class, so
Theorem A gives the guarantee `β_*` with strict inequality on every admissible pair. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- Dominant-strategy mechanisms on the nonnegative report domain. -/
structure DSICNonneg (φ pay : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ s ∈ Ici (0 : ℝ), ∀ b ∈ Ici (0 : ℝ), 0 ≤ φ s b
  le_one : ∀ s ∈ Ici (0 : ℝ), ∀ b ∈ Ici (0 : ℝ), φ s b ≤ 1
  buyerIC : ∀ s ∈ Ici (0 : ℝ), ∀ b ∈ Ici (0 : ℝ), ∀ b' ∈ Ici (0 : ℝ),
    b * φ s b' - pay s b' ≤ b * φ s b - pay s b
  sellerIC : ∀ s ∈ Ici (0 : ℝ), ∀ s' ∈ Ici (0 : ℝ), ∀ b ∈ Ici (0 : ℝ),
    pay s' b - s * φ s' b ≤ pay s b - s * φ s b
  ir : ∀ s ∈ Ici (0 : ℝ), ∀ b ∈ Ici (0 : ℝ), s * φ s b ≤ pay s b ∧ pay s b ≤ b * φ s b

/-- A mechanism on the nonnegative reports restricts to every report interval `(0, Λ)`. -/
theorem DSICNonneg.restrict {φ pay : ℝ → ℝ → ℝ} (M : DSICNonneg φ pay) (Λ : ℝ) :
    DSICOn Λ φ pay := by
  have h : ∀ x ∈ Ioo (0 : ℝ) Λ, x ∈ Ici (0 : ℝ) := fun x hx => mem_Ici.mpr hx.1.le
  exact
    { nonneg := fun s hs b hb => M.nonneg s (h s hs) b (h b hb)
      le_one := fun s hs b hb => M.le_one s (h s hs) b (h b hb)
      buyerIC := fun s hs b hb b' hb' => M.buyerIC s (h s hs) b (h b hb) b' (h b' hb')
      sellerIC := fun s hs s' hs' b hb => M.sellerIC s (h s hs) s' (h s' hs') b (h b hb)
      ir := fun s hs b hb => M.ir s (h s hs) b (h b hb) }

/-- Trade probability of the posted price `z`. -/
def fpAlloc (z s b : ℝ) : ℝ := if s ≤ z ∧ z ≤ b then 1 else 0

/-- Transfer of the posted price `z`. -/
def fpPay (z s b : ℝ) : ℝ := z * fpAlloc z s b

theorem measurable_fpAlloc (z : ℝ) : Measurable (uncurry (fpAlloc z)) := by
  apply Measurable.ite _ measurable_const measurable_const
  rw [setOf_and]
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_const measurable_snd)

/-- Every posted price is a dominant-strategy mechanism. -/
theorem fixedPrice_dsic (z : ℝ) : DSICNonneg (fpAlloc z) (fpPay z) where
  nonneg := fun s _ b _ => by unfold fpAlloc; split_ifs <;> norm_num
  le_one := fun s _ b _ => by unfold fpAlloc; split_ifs <;> norm_num
  buyerIC := fun s _ b _ b' _ => by
    have key : (b - z) * fpAlloc z s b' ≤ (b - z) * fpAlloc z s b := by
      unfold fpAlloc
      by_cases h1 : s ≤ z ∧ z ≤ b' <;> by_cases h2 : s ≤ z ∧ z ≤ b
      · rw [if_pos h1, if_pos h2]
      · rw [if_pos h1, if_neg h2]
        have : b < z := by
          by_contra hc
          exact h2 ⟨h1.1, not_lt.mp hc⟩
        nlinarith
      · rw [if_neg h1, if_pos h2]
        nlinarith [h2.2]
      · rw [if_neg h1, if_neg h2]
    unfold fpPay
    linarith
  sellerIC := fun s _ s' _ b _ => by
    have key : (z - s) * fpAlloc z s' b ≤ (z - s) * fpAlloc z s b := by
      unfold fpAlloc
      by_cases h1 : s' ≤ z ∧ z ≤ b <;> by_cases h2 : s ≤ z ∧ z ≤ b
      · rw [if_pos h1, if_pos h2]
      · rw [if_pos h1, if_neg h2]
        have : z < s := by
          by_contra hc
          exact h2 ⟨not_lt.mp hc, h1.2⟩
        nlinarith
      · rw [if_neg h1, if_pos h2]
        nlinarith [h2.1]
      · rw [if_neg h1, if_neg h2]
    unfold fpPay
    linarith
  ir := fun s _ b _ => by
    unfold fpPay fpAlloc
    split_ifs with h
    · constructor <;> nlinarith [h.1, h.2]
    · simp

section Prod

variable {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

theorem integrable_prod_bound (hsint : Integrable (fun s => s) μs)
    (hbint : Integrable (fun b => b) μb) {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    (hbd : ∀ p : ℝ × ℝ, |g p| ≤ |p.1| + |p.2|) : Integrable g (μs.prod μb) := by
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) (μs.prod μb) := hsint.comp_fst μb
  have h2 : Integrable (fun p : ℝ × ℝ => p.2) (μs.prod μb) := hbint.comp_snd μs
  refine Integrable.mono' (h1.norm.add h2.norm) hg.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  simpa [Real.norm_eq_abs] using hbd p

/-- First-best welfare of an independent pair is `M + G`. -/
theorem firstBest_prod (hsint : Integrable (fun s => s) μs)
    (hbint : Integrable (fun b => b) μb) :
    firstBest (μs.prod μb) = sellerMean μs + gainsFromTrade μs μb := by
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) (μs.prod μb) := hsint.comp_fst μb
  have hg : Integrable (fun p : ℝ × ℝ => max (p.2 - p.1) 0) (μs.prod μb) := by
    refine integrable_prod_bound hsint hbint
      ((measurable_snd.sub measurable_fst).max measurable_const) fun p => ?_
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self p.2, neg_abs_le p.1])
      (by positivity)
  have hmax : ∀ p : ℝ × ℝ, max p.1 p.2 = p.1 + max (p.2 - p.1) 0 := fun p => by
    rcases le_total p.1 p.2 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  unfold firstBest
  simp_rw [hmax]
  rw [integral_add h1 hg, integral_prod _ h1, integral_prod _ hg]
  simp only [integral_const_prob]
  rfl

/-- Welfare of the posted price `z` on an independent pair is `M + Γ(z)`. -/
theorem mechWelfare_fixedPrice (hsint : Integrable (fun s => s) μs)
    (hbint : Integrable (fun b => b) μb) (z : ℝ) :
    mechWelfare (μs.prod μb) (fpAlloc z) = sellerMean μs + gain μs μb z := by
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) (μs.prod μb) := hsint.comp_fst μb
  have hg : Integrable (fun p : ℝ × ℝ => if p.1 ≤ z ∧ z ≤ p.2 then p.2 - p.1 else 0)
      (μs.prod μb) := by
    refine integrable_prod_bound hsint hbint (measurable_tradeGain z) fun p => ?_
    split_ifs
    · rw [abs_le]
      constructor <;> linarith [le_abs_self p.2, neg_abs_le p.1, le_abs_self p.1, neg_abs_le p.2]
    · simp only [abs_zero]; positivity
  have hpt : ∀ p : ℝ × ℝ, p.1 + (p.2 - p.1) * fpAlloc z p.1 p.2 =
      p.1 + (if p.1 ≤ z ∧ z ≤ p.2 then p.2 - p.1 else 0) := fun p => by
    unfold fpAlloc
    split_ifs <;> ring
  unfold mechWelfare
  simp_rw [hpt]
  rw [integral_add h1 hg, integral_prod _ h1, integral_prod _ hg]
  simp only [integral_const_prob]
  rfl

end Prod

/-- **Corollary 11.3, guarantee direction.** On every admissible pair some posted price, a
measurable dominant-strategy mechanism on the nonnegative reports, has welfare strictly above
`β_*` times first-best welfare. -/
theorem dsic_guarantee {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) {μs μb : Measure ℝ}
    (A : AdmissiblePair μs μb) :
    ∃ z : ℝ, 0 ≤ z ∧ DSICNonneg (fpAlloc z) (fpPay z) ∧ Measurable (uncurry (fpAlloc z)) ∧
      (optimalValue C)⁻¹ * firstBest (μs.prod μb) < mechWelfare (μs.prod μb) (fpAlloc z) := by
  haveI := A.probS
  haveI := A.probB
  obtain ⟨z, hz, hlt⟩ := theoremA_strict hC hroot A.nonnegS A.intS A.intB A.pos
  refine ⟨z, hz, fixedPrice_dsic z, measurable_fpAlloc z, ?_⟩
  rw [firstBest_prod A.intS A.intB, mechWelfare_fixedPrice A.intS A.intB]
  exact hlt

end FixedPrice
