import FixedPrice.TwoUnit.Pricing.PriceTargetGain

/-!
# Theorem E, package B, part 2: a price meeting the target forces `β 𝒥 ≤ 1`

Divide the survival function of the price by `β`: `ϖ̃(t) = π((t,∞))/β` is a cumulative mass (the
zero-price atom is excluded automatically, and prices above `b̄` act as ideal tail mass). By the
gain representation the target at an ordered seller pair `s₁ ≤ s₂ ≤ b̄` says exactly that the
ordered potential sum of `ϖ̃` is nonnegative, so the canonical compensation makes `ϖ̃` feasible,
and leastness gives `𝒥 ≤ ϖ̃(0) = π((0,∞))/β ≤ 1/β`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section Scaling

variable {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem gainFromMass_const_mul (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (h : GoodMass bbar μ ϖ) (c s : ℝ) :
    gainFromMass bbar μ (fun t => c * ϖ t) s = c * gainFromMass bbar μ ϖ s := by
  have h0 : GoodMass bbar μ (fun _ => (0 : ℝ)) :=
    ⟨aestronglyMeasurable_const, ⟨0, fun _ _ => by simp⟩⟩
  have hlin := kernelIntegral_linear hsupp h h0 c 0 s
  simp only [mul_zero, add_zero, zero_mul] at hlin
  unfold gainFromMass
  rw [hlin]
  ring

end Scaling

section Reverse

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d β : ℝ}

/-- The ordered potential sum of the normalized survival function of a price meeting the target
is nonnegative. -/
theorem orderedSum_of_priceTarget (hB : IsBuyerBodies bbar law) (hβ : 0 < β) {π : Measure ℝ}
    [IsFiniteMeasure π] (htarget : PriceTarget law d β π) {s₁ s₂ : ℝ} (h1 : 0 ≤ s₁)
    (h12 : s₁ ≤ s₂) :
    0 ≤ sellerPotential bbar (law 0) d (fun t => π.real (Ioi t) / β) s₁ +
      sellerPotential bbar (law 1) d (fun t => π.real (Ioi t) / β) s₂ := by
  have ht := htarget ![s₁, s₂] (by simpa using h1) (by simpa using h12)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at ht
  have hg : ∀ i : Fin 2, ∀ s, 0 ≤ s → ∫ z, gainKernel (law i) s z ∂π =
      β * gainFromMass bbar (law i) (fun t => π.real (Ioi t) / β) s := fun i s hs => by
    haveI := hB.isProbability i
    have hsupp := hB.supported i
    rw [integral_gainKernel' hsupp π s]
    have hgm : GoodMass bbar (law i) (fun t => π.real (Ioi t) / β) :=
      goodMass_of_antitoneOn hsupp fun a _ b _ hab =>
        div_le_div_of_nonneg_right (survival_antitone hab) hβ.le
    rw [← gainFromMass_const_mul hsupp hgm β s]
    congr 1
    funext t
    field_simp
  rw [hg 0 s₁ h1, hg 1 s₂ (h1.trans h12)] at ht
  unfold sellerPotential
  have : β * (d * s₁ - Lbar (law 0) s₁ + gainFromMass bbar (law 0)
      (fun t => π.real (Ioi t) / β) s₁ + (d * s₂ - Lbar (law 1) s₂ +
        gainFromMass bbar (law 1) (fun t => π.real (Ioi t) / β) s₂)) ≥ 0 := by
    nlinarith
  exact nonneg_of_mul_nonneg_right (by linarith) hβ

theorem isCumulativeMass_survival_div (hβ : 0 < β) (π : Measure ℝ) [IsFiniteMeasure π] :
    IsCumulativeMass bbar (fun t => π.real (Ioi t) / β) := by
  refine ⟨fun s _ => div_nonneg measureReal_nonneg hβ.le, fun a _ b _ hab =>
    div_le_div_of_nonneg_right (survival_antitone hab) hβ.le, fun s _ => ?_⟩
  exact ((survival_rightContinuous (ν := π) s).mono
    (Icc_subset_Ici_self : Icc s bbar ⊆ Ici s)).div_const β

/-- **Theorem E (iii), reverse implication.** -/
theorem le_one_of_priceTarget (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) (hβ : 0 < β) {π : Measure ℝ} (hπ : IsBoundedPriceLaw π)
    (htarget : PriceTarget law d β π) : β * pricingValue bbar law d ≤ 1 := by
  haveI := hπ.isProbability
  have hb := bbar_nonneg_of_bodies hB
  set ϖ := fun t => π.real (Ioi t) / β with hϖ
  have hcum : IsCumulativeMass bbar ϖ := isCumulativeMass_survival_div hβ π
  have hsum : ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ bbar →
      0 ≤ sellerPotential bbar (law 0) d ϖ s₁ + sellerPotential bbar (law 1) d ϖ s₂ :=
    fun s₁ s₂ h1 h12 _ => orderedSum_of_priceTarget hB hβ htarget h1 h12
  obtain ⟨hΘ, hF⟩ := canonicalCompensation_spec' hB hcum hsum
  have h1 := leastMass_le_of_isFeasible' cert hB hd hΘ hF 0 ⟨le_rfl, hb⟩
  have h2 := pricingValue_le cert hB hd hΘ
  have h3 : π.real (Ioi 0) ≤ 1 := by
    have := measureReal_mono (μ := π) (subset_univ (Ioi (0 : ℝ)))
    rwa [probReal_univ] at this
  have h4 : ϖ 0 ≤ 1 / β := by
    simp only [hϖ]
    exact div_le_div_of_nonneg_right h3 hβ.le
  have : pricingValue bbar law d ≤ 1 / β := h2.trans (h1.trans h4)
  rw [le_div_iff₀ hβ] at this
  linarith

end Reverse

end FixedPrice.TwoUnit.Pricing
