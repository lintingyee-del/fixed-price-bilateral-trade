import FixedPrice.TwoUnit.Pricing.PriceTargetFinal

/-!
# Theorem E, package B, part 5: the welfare clause of part (iii)

At `d = (1 - β)/β` we have `βd = 1 - β`. For a seller vector `y` with `0 ≤ y₁ ≤ y₂` the price
target at `s = y` and `s + L̄_i(s) = 1 + E max {Z_i, s}` give
`β (2 + Σ_i E max {Z_i, y_i}) ≤ y₁ + y₂ + Σ_i ∫ g_i(y_i, z) π(dz)`.
The inner buyer integral of `eq:two-body` is the gain kernel `g_i(y_i, z)`, which lies in
`[0, 1 + b̄]` for `y_i ≥ 0`; integrating over the seller law and exchanging the price and seller
integrals (Fubini on `π ⊗ ν`) gives the welfare guarantee.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section Kernel

variable {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The inner buyer integral of `eq:two-body` is the gain kernel. -/
theorem integral_welfareKernel (hsupp : μ (Icc 0 bbar)ᶜ = 0) (s z : ℝ) :
    ∫ x, (if s < z then 1 + (if z ≤ x then x - s else 0) else 0) ∂μ = gainKernel μ s z := by
  unfold gainKernel
  by_cases h : s < z
  · simp only [if_pos h]
    have hind : (fun x => if z ≤ x then x - s else (0 : ℝ)) = (Ici z).indicator (fun x => x - s) := by
      ext x; simp only [indicator, mem_Ici]
    have hsub : Integrable (fun x => x - s) μ :=
      integrable_of_bdd_on_supp hsupp (measurable_id.sub_const s).aestronglyMeasurable
        (fun x hx => abs_sub_le_of_mem x s hx)
    have hint : Integrable (fun x => if z ≤ x then x - s else (0 : ℝ)) μ := by
      rw [hind]; exact hsub.indicator measurableSet_Ici
    rw [integral_add (integrable_const 1) hint, integral_const, probReal_univ, one_smul, hind,
      integral_indicator measurableSet_Ici]
  · simp only [if_neg h, integral_zero]

theorem gainKernel_mem_Icc (hsupp : μ (Icc 0 bbar)ᶜ = 0) {s : ℝ} (hs : 0 ≤ s) (z : ℝ) :
    0 ≤ gainKernel μ s z ∧ gainKernel μ s z ≤ 1 + bbar := by
  have hb := bbar_nonneg_of_supp hsupp
  rw [← integral_welfareKernel hsupp s z]
  have hw : ∀ᵐ x ∂μ, 0 ≤ (if s < z then 1 + (if z ≤ x then x - s else 0) else (0 : ℝ)) ∧
      (if s < z then 1 + (if z ≤ x then x - s else 0) else (0 : ℝ)) ≤ 1 + bbar := by
    filter_upwards [ae_mem_Icc_of_supp hsupp] with x hx
    split_ifs with h1 h2 <;> constructor <;> linarith [hx.1, hx.2]
  constructor
  · exact integral_nonneg_of_ae (hw.mono fun x hx => hx.1)
  · have := norm_integral_le_of_norm_le_const (μ := μ) (hw.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this

/-- Joint measurability of `(z, y) ↦ g(y_i, z)`: it is a parametric integral of a measurable
integrand. -/
theorem measurable_gainKernel_prod (hsupp : μ (Icc 0 bbar)ᶜ = 0) (i : Fin 2) :
    Measurable (fun p : ℝ × (Fin 2 → ℝ) => gainKernel μ (p.2 i) p.1) := by
  have hyi : Measurable (fun q : (ℝ × (Fin 2 → ℝ)) × ℝ => q.1.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hz : Measurable (fun q : (ℝ × (Fin 2 → ℝ)) × ℝ => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hF : Measurable (fun q : (ℝ × (Fin 2 → ℝ)) × ℝ =>
      if q.1.2 i < q.1.1 then 1 + (if q.1.1 ≤ q.2 then q.2 - q.1.2 i else 0) else (0 : ℝ)) :=
    Measurable.ite (measurableSet_lt hyi hz)
      (measurable_const.add (Measurable.ite (measurableSet_le hz measurable_snd)
        (measurable_snd.sub hyi) measurable_const)) measurable_const
  have h := (hF.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  convert h using 1
  funext p
  exact (integral_welfareKernel hsupp _ _).symm

theorem integrable_gainKernel_prod (hsupp : μ (Icc 0 bbar)ᶜ = 0) (π : Measure ℝ)
    [IsFiniteMeasure π] (ν : Measure (Fin 2 → ℝ)) [IsFiniteMeasure ν] (i : Fin 2)
    (hν : ∀ᵐ y ∂ν, 0 ≤ y i) :
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => gainKernel μ (p.2 i) p.1) (π.prod ν) := by
  refine Integrable.of_bound (measurable_gainKernel_prod hsupp i).aestronglyMeasurable
    (1 + bbar) ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hν] with p hp
  obtain ⟨h0, h1⟩ := gainKernel_mem_Icc hsupp hp p.1
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

theorem integrable_Lbar_coord (hsupp : μ (Icc 0 bbar)ᶜ = 0) (ν : Measure (Fin 2 → ℝ))
    [IsFiniteMeasure ν] (i : Fin 2) (hν : ∀ᵐ y ∂ν, 0 ≤ y i) :
    Integrable (fun y : Fin 2 → ℝ => Lbar μ (y i)) ν := by
  refine Integrable.of_bound ((Lbar_lipschitz' hsupp).continuous.measurable.comp
    (measurable_pi_apply i)).aestronglyMeasurable (1 + bbar) ?_
  filter_upwards [hν] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (one_le_Lbar' μ _))]
  exact Lbar_le_one_add' hsupp hy

end Kernel

theorem integrable_coord (ν : Measure (Fin 2 → ℝ)) [IsFiniteMeasure ν] (i : Fin 2) {C : ℝ}
    (hν : ∀ᵐ y ∂ν, 0 ≤ y i ∧ y i ≤ C) : Integrable (fun y : Fin 2 → ℝ => y i) ν := by
  refine Integrable.of_bound (measurable_pi_apply i).aestronglyMeasurable C ?_
  filter_upwards [hν] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg hy.1]
  exact hy.2

section Welfare

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ}

/-- **Theorem E (iii), welfare clause.** -/
theorem welfare_of_priceTarget (hB : IsBuyerBodies bbar law) {β : ℝ} (hβ₀ : 0 < β)
    {π : Measure ℝ} (hπ : IsBoundedPriceLaw π) (htarget : PriceTarget law ((1 - β) / β) β π)
    (ν : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ y ∂ν, 0 ≤ y 0 ∧ y 0 ≤ y 1) (hνb : ∃ C : ℝ, ∀ᵐ y ∂ν, y 1 ≤ C) :
    β * normalizedEfficientWelfare law ν ≤ ∫ z, normalizedWelfare law ν z ∂π := by
  haveI := hπ.isProbability
  haveI := hB.isProbability 0
  haveI := hB.isProbability 1
  obtain ⟨C, hC⟩ := hνb
  have hsupp0 := hB.supported 0
  have hsupp1 := hB.supported 1
  have hy0 : ∀ᵐ y ∂ν, 0 ≤ y 0 ∧ y 0 ≤ C := by
    filter_upwards [hν, hC] with y h1 h2
    exact ⟨h1.1, h1.2.trans h2⟩
  have hy1 : ∀ᵐ y ∂ν, 0 ≤ y 1 ∧ y 1 ≤ C := by
    filter_upwards [hν, hC] with y h1 h2
    exact ⟨h1.1.trans h1.2, h2⟩
  have hK0 := integrable_gainKernel_prod hsupp0 π ν 0 (hy0.mono fun y h => h.1)
  have hK1 := integrable_gainKernel_prod hsupp1 π ν 1 (hy1.mono fun y h => h.1)
  have hY0 := integrable_coord ν 0 hy0
  have hY1 := integrable_coord ν 1 hy1
  have hL0 := integrable_Lbar_coord hsupp0 ν 0 (hy0.mono fun y h => h.1)
  have hL1 := integrable_Lbar_coord hsupp1 ν 1 (hy1.mono fun y h => h.1)
  -- the buyer-seller maxima through `s + L̄(s) = 1 + E max {Z, s}`
  have hM0 : ∀ y : Fin 2 → ℝ, ∫ x, max x (y 0) ∂(law 0) = y 0 + Lbar (law 0) (y 0) - 1 :=
    fun y => by linarith [self_add_Lbar' hsupp0 (y 0)]
  have hM1 : ∀ y : Fin 2 → ℝ, ∫ x, max x (y 1) ∂(law 1) = y 1 + Lbar (law 1) (y 1) - 1 :=
    fun y => by linarith [self_add_Lbar' hsupp1 (y 1)]
  have hA0 : Integrable (fun y : Fin 2 → ℝ => ∫ x, max x (y 0) ∂(law 0)) ν := by
    simp only [hM0]; exact (hY0.add hL0).sub (integrable_const 1)
  have hA1 : Integrable (fun y : Fin 2 → ℝ => ∫ x, max x (y 1) ∂(law 1)) ν := by
    simp only [hM1]; exact (hY1.add hL1).sub (integrable_const 1)
  -- the price integrals of the gain kernels
  have hG0 : Integrable (fun y : Fin 2 → ℝ => ∫ z, gainKernel (law 0) (y 0) z ∂π) ν :=
    hK0.integral_prod_right
  have hG1 : Integrable (fun y : Fin 2 → ℝ => ∫ z, gainKernel (law 1) (y 1) z ∂π) ν :=
    hK1.integral_prod_right
  have hI0 : Integrable (fun z => ∫ y, gainKernel (law 0) (y 0) z ∂ν) π :=
    hK0.integral_prod_left
  have hI1 : Integrable (fun z => ∫ y, gainKernel (law 1) (y 1) z ∂ν) π :=
    hK1.integral_prod_left
  have hsw0 : ∫ z, ∫ y, gainKernel (law 0) (y 0) z ∂ν ∂π =
      ∫ y, ∫ z, gainKernel (law 0) (y 0) z ∂π ∂ν := integral_integral_swap hK0
  have hsw1 : ∫ z, ∫ y, gainKernel (law 1) (y 1) z ∂ν ∂π =
      ∫ y, ∫ z, gainKernel (law 1) (y 1) z ∂π ∂ν := integral_integral_swap hK1
  have hA : Integrable (fun y : Fin 2 → ℝ => y 0 + y 1) ν := hY0.add hY1
  have hA01 : Integrable (fun y : Fin 2 → ℝ =>
      ∫ x, max x (y 0) ∂(law 0) + ∫ x, max x (y 1) ∂(law 1)) ν := hA0.add hA1
  have hG01 : Integrable (fun y : Fin 2 → ℝ =>
      ∫ z, gainKernel (law 0) (y 0) z ∂π + ∫ z, gainKernel (law 1) (y 1) z ∂π) ν := hG0.add hG1
  have hI01 : Integrable (fun z =>
      ∫ y, gainKernel (law 0) (y 0) z ∂ν + ∫ y, gainKernel (law 1) (y 1) z ∂ν) π := hI0.add hI1
  -- pointwise inequality from the price target at `s = y`
  have hβd : β * ((1 - β) / β) = 1 - β := by field_simp
  have hpt : ∀ᵐ y ∂ν,
      β * (2 + (∫ x, max x (y 0) ∂(law 0) + ∫ x, max x (y 1) ∂(law 1))) ≤
        y 0 + y 1 + (∫ z, gainKernel (law 0) (y 0) z ∂π + ∫ z, gainKernel (law 1) (y 1) z ∂π) := by
    filter_upwards [hν] with y hy
    have ht := htarget y hy.1 hy.2
    simp only [Fin.sum_univ_two] at ht
    rw [hβd] at ht
    rw [hM0 y, hM1 y]
    linarith
  have hLint : Integrable (fun y : Fin 2 → ℝ =>
      β * (2 + (∫ x, max x (y 0) ∂(law 0) + ∫ x, max x (y 1) ∂(law 1)))) ν :=
    ((integrable_const 2).add hA01).const_mul β
  have hRint : Integrable (fun y : Fin 2 → ℝ =>
      y 0 + y 1 + (∫ z, gainKernel (law 0) (y 0) z ∂π + ∫ z, gainKernel (law 1) (y 1) z ∂π)) ν :=
    hA.add hG01
  have hLval : ∫ y, β * (2 + (∫ x, max x (y 0) ∂(law 0) + ∫ x, max x (y 1) ∂(law 1))) ∂ν =
      β * normalizedEfficientWelfare law ν := by
    rw [integral_const_mul, integral_add (integrable_const 2) hA01, integral_const,
      probReal_univ, one_smul, integral_add hA0 hA1]
    unfold normalizedEfficientWelfare
    rw [Fin.sum_univ_two]
  have hNW : ∀ z, normalizedWelfare law ν z = ∫ y, (y 0 + y 1) ∂ν +
      (∫ y, gainKernel (law 0) (y 0) z ∂ν + ∫ y, gainKernel (law 1) (y 1) z ∂ν) := fun z => by
    unfold normalizedWelfare
    rw [Fin.sum_univ_two]
    simp only [integral_welfareKernel hsupp0, integral_welfareKernel hsupp1]
  have hRval : ∫ z, normalizedWelfare law ν z ∂π = ∫ y, (y 0 + y 1) ∂ν +
      (∫ y, ∫ z, gainKernel (law 0) (y 0) z ∂π ∂ν +
        ∫ y, ∫ z, gainKernel (law 1) (y 1) z ∂π ∂ν) := by
    simp only [hNW]
    rw [integral_add (integrable_const (∫ y, (y 0 + y 1) ∂ν)) hI01, integral_const, probReal_univ,
      one_smul,
      integral_add hI0 hI1, hsw0, hsw1]
  calc β * normalizedEfficientWelfare law ν
      = ∫ y, β * (2 + (∫ x, max x (y 0) ∂(law 0) + ∫ x, max x (y 1) ∂(law 1))) ∂ν := hLval.symm
    _ ≤ ∫ y, (y 0 + y 1 +
          (∫ z, gainKernel (law 0) (y 0) z ∂π + ∫ z, gainKernel (law 1) (y 1) z ∂π)) ∂ν :=
        integral_mono_ae hLint hRint hpt
    _ = ∫ z, normalizedWelfare law ν z ∂π := by
        rw [hRval, integral_add hA hG01, integral_add hG0 hG1]

end Welfare

end FixedPrice.TwoUnit.Pricing
