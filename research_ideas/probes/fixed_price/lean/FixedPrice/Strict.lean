import FixedPrice.PricingLemma
import FixedPrice.Uniqueness

/-! Theorem A, strict inequality: every admissible pair has welfare ratio strictly above
`β_*`. The buyer's normalized control is bounded below by `H(s₀) > 0`, so it misses the
initial zero arc of the unique maximizer of Theorem C; its price density therefore has mass
`α < 1`, and the guarantee holds with room to spare. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

section Strict

variable {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

omit [IsProbabilityMeasure μs] [IsProbabilityMeasure μb] in
theorem gainsFromTrade_eq_integral_tail :
    gainsFromTrade μs μb = ∫ s, tailIntegral μb s ∂μs := rfl

omit [IsProbabilityMeasure μs] [IsProbabilityMeasure μb] in
theorem gainsFromTrade_nonneg : 0 ≤ gainsFromTrade μs μb :=
  integral_nonneg fun s => tailIntegral_nonneg μb s

/-- Positive first-best gains produce a positive price with positive gain. -/
theorem exists_gain_pos (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb)
    (hG : 0 < gainsFromTrade μs μb) : ∃ z : ℝ, 0 < z ∧ 0 < gain μs μb z := by
  have hLc := tailIntegral_continuous μb hbint
  obtain ⟨q, hLq, hμq⟩ : ∃ q : ℚ, 0 < tailIntegral μb q ∧ μs (Iio (q : ℝ)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : {s | 0 < tailIntegral μb s} ⊆
        ⋃ q : {q : ℚ // 0 < tailIntegral μb q}, Iio (q.1 : ℝ) := by
      intro s hs
      have hev : ∀ᶠ y in 𝓝 s, 0 < tailIntegral μb y :=
        hLc.continuousAt.eventually (lt_mem_nhds hs)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + ε by linarith)
      have hdist : dist (q : ℝ) s < ε := by
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith
      exact mem_iUnion.mpr ⟨⟨q, hball hdist⟩, hq1⟩
    have hnull : μs {s | 0 < tailIntegral μb s} = 0 :=
      measure_mono_null hsub (measure_iUnion_null fun q => hcon q.1 q.2)
    have hae : ∀ᵐ s ∂μs, tailIntegral μb s = 0 := by
      rw [ae_iff]
      apply measure_mono_null _ hnull
      intro s hs
      simp only [mem_setOf_eq] at hs ⊢
      exact lt_of_le_of_ne (tailIntegral_nonneg μb s) (Ne.symm hs)
    have hzero : gainsFromTrade μs μb = 0 := by
      rw [gainsFromTrade_eq_integral_tail, integral_congr_ae hae]
      simp
    linarith
  have hqpos : (0 : ℝ) < q := by
    by_contra hq
    push Not at hq
    apply hμq
    apply measure_mono_null _ (ae_iff.mp hs0)
    intro s hs
    simp only [mem_setOf_eq, not_le]
    exact lt_of_lt_of_le hs hq
  refine ⟨q, hqpos, ?_⟩
  have hint : Integrable (fun s => if s < (q : ℝ) then
      tailIntegral μb q + (q - s) * survival μb q else 0) μs := by
    apply Integrable.mono' ((integrable_const (tailIntegral μb 0 + 2 * |(q : ℝ)|)).add hsint.abs)
    · exact ((measurable_lowerGain_pair μb hbint).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards with s
      simpa [Real.norm_eq_abs] using abs_lowerGain_integrand_le μb hbint q s
  have hind : Integrable ((Iio (q : ℝ)).indicator fun _ => tailIntegral μb q) μs :=
    (integrable_const _).indicator measurableSet_Iio
  have hlow : μs.real (Iio (q : ℝ)) * tailIntegral μb q ≤ lowerGain μs μb q := by
    rw [← smul_eq_mul, ← integral_indicator_const _ measurableSet_Iio]
    apply integral_mono hind hint
    intro s
    simp only [Set.indicator_apply, mem_Iio]
    split_ifs with h
    · have := mul_nonneg (sub_nonneg.mpr h.le) (survival_nonneg μb q)
      linarith
    · exact le_rfl
  have hpos : 0 < μs.real (Iio (q : ℝ)) * tailIntegral μb q := by
    apply mul_pos _ hLq
    rw [measureReal_def]
    exact ENNReal.toReal_pos hμq (measure_ne_top _ _)
  exact hpos.trans_le (hlow.trans (lowerGain_le_gain μs μb hbint hsint q))

/-- The normalized buyer control misses the maximizer, so its objective is strictly below
`S(C)`. -/
theorem IsCutoff.objective_cutControl_lt {d s₀ C : ℝ} (hc : IsCutoff μb d s₀)
    (hbint : Integrable (fun b => b) μb) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) :
    objective d (cutControl μb s₀) < optimalValue C := by
  have hmeas := cutControl_aestronglyMeasurable (μ := μb) (s₀ := s₀)
  have hbox : ∀ t ∈ Icc (0 : ℝ) 1, cutControl μb s₀ t ∈ Icc (0 : ℝ) 1 :=
    fun t _ => cutControl_mem_Icc t
  have hle := objective_le_optimalValue hc.hd hC hinit hmeas hbox
  refine lt_of_le_of_ne hle fun heq => ?_
  have hae := (objective_eq_optimalValue_iff hc.hd hC hinit hmeas hbox).mp heq
  have hC0 : 0 < C := by linarith [hC.1]
  have hsub : Ioo (0 : ℝ) C ⊆ Icc 0 1 := fun t ht => ⟨ht.1.le, by linarith [ht.2, hC.2]⟩
  have hae' : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) C)),
      t ∈ Ioo (0 : ℝ) C ∧ cutControl μb s₀ t = maximizingControl d C t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hae] with t ht hte
    exact ⟨ht, hte⟩
  have hne : volume.restrict (Ioo (0 : ℝ) C) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, sub_zero, ENNReal.ofReal_eq_zero, not_le]
    exact hC0
  haveI : (ae (volume.restrict (Ioo (0 : ℝ) C))).NeBot := ae_neBot.mpr hne
  obtain ⟨t, ht, hte⟩ := hae'.exists
  have hmax : maximizingControl d C t = 0 := by
    unfold maximizingControl
    rw [if_pos ht.2.le]
  have hcut : 0 < cutControl μb s₀ t := by
    unfold cutControl
    apply hc.survival_pos hbint
    have : 0 ≤ s₀ * t := mul_nonneg hc.pos.le ht.1.le
    nlinarith
  rw [hte, hmax] at hcut
  exact lt_irrefl 0 hcut

/-- **Theorem A, strict inequality.** At the root `C_*` of (44), every independent pair of
nonnegative finite-mean value laws with positive first-best welfare admits a price whose
welfare exceeds `β_* = 1/S(C_*)` times first-best welfare. -/
theorem theoremA_strict {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C)
    (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb)
    (hpos : 0 < sellerMean μs + gainsFromTrade μs μb) :
    ∃ z : ℝ, 0 ≤ z ∧
      (optimalValue C)⁻¹ * (sellerMean μs + gainsFromTrade μs μb) <
        sellerMean μs + gain μs μb z := by
  set d := initialState C with hd_def
  have hd : 0 < d := initialState_pos hC
  have hS : 1 < optimalValue C := one_lt_optimalValue hC
  set β := (optimalValue C)⁻¹ with hβ_def
  have hβpos : 0 < β := inv_pos.mpr (by linarith)
  have hβ1 : β < 1 := inv_lt_one_of_one_lt₀ hS
  have hβS : β * optimalValue C = 1 := inv_mul_cancel₀ (by linarith)
  have hβd : β * d = 1 - β := by
    have : β * (1 + d) = 1 := by rw [← hroot]; exact hβS
    linarith
  set M := sellerMean μs with hM_def
  set G := gainsFromTrade μs μb with hG_def
  have hM : 0 ≤ M := integral_nonneg_of_ae hs0
  have hG0 : 0 ≤ G := gainsFromTrade_nonneg
  rcases eq_or_lt_of_le hG0 with hG | hG
  · refine ⟨0, le_rfl, ?_⟩
    have := gain_nonneg μs μb 0
    rw [← hG] at hpos ⊢
    nlinarith
  by_cases hsmall : G ≤ d * M
  · obtain ⟨z, hz, hgz⟩ := exists_gain_pos hs0 hsint hbint hG
    refine ⟨z, hz.le, ?_⟩
    have : β * (M + G) ≤ M := by nlinarith
    linarith
  push Not at hsmall
  have hL0 := tailIntegral_zero_pos_of_gainsFromTrade_pos hbint hs0 hG
  obtain ⟨s₀, hs₀, hcut⟩ := exists_cutoff μb hbint hd hL0
  have hc : IsCutoff μb d s₀ := ⟨hd, hs₀, hcut⟩
  set J := objective d (cutControl μb s₀) with hJ_def
  have hJlt : J < optimalValue C := hc.objective_cutControl_lt hbint hC rfl
  have hβJ : β * J < 1 := by
    rw [← hβS]
    exact mul_lt_mul_of_pos_left hJlt hβpos
  set ε := (1 - β * J) / (|J| + 1) with hε_def
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hβ' : (β + ε) * J ≤ 1 := by
    have h1 : ε * J ≤ ε * |J| := mul_le_mul_of_nonneg_left (le_abs_self J) hε.le
    have h2 : ε * |J| ≤ 1 - β * J := by
      rw [hε_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg J]
    nlinarith
  have hT : 0 < (β + ε) * G - (β + ε) * d * M := by
    have : 0 < G - d * M := by linarith
    nlinarith
  obtain ⟨z, hz, hgain⟩ :=
    exists_price_of_cutoff (by linarith) hc hβ' hs0 hsint hbint hT
  refine ⟨z, hz, ?_⟩
  have : β * (G - d * M) < (β + ε) * (G - d * M) := by
    have : 0 < G - d * M := by linarith
    nlinarith
  nlinarith

end Strict

end FixedPrice
