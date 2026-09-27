import FixedPrice.TwoUnit.Family.BasicFTC

/-!
# Work package A, helpers: the parameter bounds of `lem:2fam-compact`

* `smallMassBound` increases on `(0, 1/32]` (from `log x ≥ 1 - 1/x`).
* For a class member: `m_f a_f ≤ 1 - m_f`, `G_f ≤ 4 + 2 log(2/m_f)`, `T_f ≥ 1/p_f - 1` (the buyer
  mean is below `b_f`), `b_f ≥ N_f ξ₀ + (1 - m_f) a_f` (the first seller distribution function is
  at most one), hence `M_f ≥ (1 - m_f)²/m_f` and `M_f ≥ N_f (N_f - 1) ξ₀`.
* At `p_f = 1` the interval is a point and `R_f = (1 + 3t²)/(1+t)² ≥ 3/4` (certified
  `p_one_ratio`).
* Curves with `R_f < β ≤ 3/4` have `1/32 < m_f < 3/4`, `ξ₀ < 600`, `p_f < 1` (certified
  `small_mass_endpoint`, `buyer_mean`).
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

theorem small_mass_mono' : SmallMassMonoStatement := by
  intro m₁ hm₁ m₂ hm₂ hlt
  have h1 := hm₁.1
  have h2 := hm₂.1
  have hm₂le := hm₂.2
  have hlog : 1 - m₂ / m₁ ≤ Real.log (2 / m₂) - Real.log (2 / m₁) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have e : 2 / m₂ / (2 / m₁) = m₁ / m₂ := by field_simp
    rw [e]
    have := Real.one_sub_inv_le_log_of_pos (x := m₁ / m₂) (by positivity)
    rwa [inv_div] at this
  have hkey : 0 < 3 / 2 * (1 - m₂ / m₁) + (1 - m₁) ^ 2 / (4 * m₁) - (1 - m₂) ^ 2 / (4 * m₂) := by
    have e : 3 / 2 * (1 - m₂ / m₁) + (1 - m₁) ^ 2 / (4 * m₁) - (1 - m₂) ^ 2 / (4 * m₂) =
        (m₂ - m₁) * (1 - m₁ * m₂ - 6 * m₂) / (4 * m₁ * m₂) := by
      field_simp; ring
    rw [e]
    apply div_pos _ (by positivity)
    apply mul_pos (by linarith)
    nlinarith
  unfold smallMassBound
  nlinarith

namespace InClass

variable {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
include hP

theorem m_mul_a_le : θ.m * θ.a ≤ 1 - θ.m := by
  have hadm := hP.admissible
  have ht := hadm.t_pos; have hp := hadm.p_pos
  have ht1 := hadm.t_lt_one; have hp1 := hadm.p_le_one
  unfold Params.m Params.a mF aF cF
  rw [show 2 * θ.t / (1 + θ.t) * ((θ.p - θ.t) / 2 / (θ.t * θ.p)) = (1 - θ.t / θ.p) / (1 + θ.t) by
    field_simp]
  rw [show 1 - 2 * θ.t / (1 + θ.t) = (1 - θ.t) / (1 + θ.t) by field_simp; ring]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have : θ.t ≤ θ.t / θ.p := by rw [le_div_iff₀ hp]; nlinarith
  linarith

theorem Gf_le_small : Gf θ P ≤ 4 + 2 * Real.log (2 / θ.m) := by
  have hadm := hP.admissible
  have ht := hadm.t_pos; have hp := hadm.p_pos
  have ht1 := hadm.t_lt_one
  have hQ : 0 ≤ Qf θ P := by
    unfold Qf
    refine intervalIntegral.integral_nonneg_of_ae_restrict hP.c_le_ξ₀ ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have : 0 ≤ x := hadm.c_nonneg.trans hx.1
    positivity
  have hma := hP.m_mul_a_le
  have hN0 := hadm.N_pos
  have hN2 : θ.N ≤ 2 := by
    unfold Params.N NF; rw [div_le_iff₀ (by linarith)]; linarith
  -- `-log p ≤ -log t ≤ log (2/m)`
  have hlogp : -Real.log θ.p ≤ Real.log (2 / θ.m) := by
    have h1 : Real.log θ.t ≤ Real.log θ.p := Real.log_le_log ht hadm.t_le_p
    have h2 : 2 / θ.m = 1 / θ.t + 1 := by
      unfold Params.m mF; field_simp
    have h3 : -Real.log θ.t ≤ Real.log (2 / θ.m) := by
      rw [← Real.log_inv, h2]
      exact Real.log_le_log (by positivity) (by rw [one_div]; linarith)
    linarith
  have hlog0 : 0 ≤ -Real.log θ.p := by
    have := Real.log_nonpos hp.le hadm.p_le_one; linarith
  have hm0 := hadm.m_pos
  unfold Gf
  nlinarith [mul_le_mul hN2 hlogp hlog0 (by norm_num : (0:ℝ) ≤ 2), mul_nonneg hN0.le hQ]

/-- The buyer mean `a + 1/p - 1` is at most `b_f = a + T_f`. -/
theorem Tf_ge_mean : 1 / θ.p - 1 ≤ Tf θ P := by
  rw [← hP.integral_deriv_div_sq]
  unfold Tf
  refine intervalIntegral.integral_mono_ae_restrict hP.c_le_ξ₀ ?_ hP.intervalIntegrable_inv_sq ?_
  · refine hP.intervalIntegrable_of_bound (B := (θ.p ^ 2)⁻¹) hP.aestronglyMeasurable_q2 ?_
    filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
    have hPpos := hP.pos' hxm
    have hp := hP.admissible.p_pos
    have hd0 := (hP.admissible.h_pos.le).trans (hP.h_le_deriv hx.1 hx.2)
    have hd1 := hP.deriv_le_one hx.1 hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hd0 (by positivity)),
      div_le_iff₀ (by positivity)]
    have : θ.p ^ 2 ≤ P x ^ 2 := pow_le_pow_left₀ hp.le (hP.p_le hxm) 2
    calc deriv P x ≤ 1 := hd1
      _ = (θ.p ^ 2)⁻¹ * θ.p ^ 2 := by field_simp
      _ ≤ (θ.p ^ 2)⁻¹ * P x ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
  · filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
    have hPpos := hP.pos' hxm
    show deriv P x / P x ^ 2 ≤ (P x ^ 2)⁻¹
    rw [div_eq_mul_inv]
    have := hP.deriv_le_one hx.1 hx.2
    have h0 : 0 ≤ (P x ^ 2)⁻¹ := by positivity
    nlinarith

theorem ae_deriv_div : ∀ᵐ ξ ∂(volume.restrict (Icc θ.c θ.ξ₀)),
    deriv (fun x => x * (P x)⁻¹) ξ = (P ξ - ξ * deriv P ξ) / P ξ ^ 2 := by
  filter_upwards [hP.ae_good] with x hx
  have hPx := (hP.pos' (Ioo_subset_Icc_self hx.1)).ne'
  have h : HasDerivAt (fun y => y * (P y)⁻¹) (1 * (P x)⁻¹ + x * (-(deriv P x) / P x ^ 2)) x :=
    (hasDerivAt_id' x).mul (hx.2.hasDerivAt.inv hPx)
  rw [h.deriv]
  field_simp
  ring

/-- `b_f ≥ N_f ξ₀ + (1 - m_f) a_f`: the first seller distribution function is at most one. -/
theorem bF_ge : θ.N * θ.ξ₀ + (1 - θ.m) * θ.a ≤ θ.a + Tf θ P := by
  have hadm := hP.admissible
  have hp := hadm.p_pos
  have hFTC := hP.absCont_div.integral_deriv_eq_sub
  rw [hP.right_end, hP.left_end, inv_one, mul_one] at hFTC
  have hint : ∫ ξ in θ.c..θ.ξ₀, (P ξ - ξ * deriv P ξ) / P ξ ^ 2 = θ.ξ₀ - θ.c * θ.p⁻¹ := by
    rw [← hFTC]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hP.ae_Icc_iff hP.ae_deriv_div] with x hx hxI
    rw [hx hxI]
  have hle : θ.N * ∫ ξ in θ.c..θ.ξ₀, (P ξ - ξ * deriv P ξ) / P ξ ^ 2 ≤ Tf θ P := by
    rw [← intervalIntegral.integral_const_mul]
    unfold Tf
    refine intervalIntegral.integral_mono_ae_restrict hP.c_le_ξ₀ ?_ hP.intervalIntegrable_inv_sq ?_
    · refine hP.intervalIntegrable_of_bound (B := θ.N * (θ.e * (θ.p ^ 2)⁻¹)) ?_ ?_
      · exact aestronglyMeasurable_const.mul
          (((hP.aestronglyMeasurable_P.sub (aestronglyMeasurable_id.mul
            (measurable_deriv P).aestronglyMeasurable)).aemeasurable.div
            (hP.aestronglyMeasurable_P.aemeasurable.pow_const 2)).aestronglyMeasurable)
      · filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
        have hPpos := hP.pos' hxm
        have hs0 := hP.sub_mul_deriv_nonneg hx.1 hx.2
        have hs1 := hP.N_mul_sub_mul_deriv_le_one hx.1 hx.2
        have hN := hadm.N_pos
        have hNe := hadm.N_mul_e
        have hse : P x - x * deriv P x ≤ θ.e := by
          rw [hadm.e_eq_inv_N, le_div_iff₀ hN]; linarith
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hN.le (div_nonneg hs0 (by positivity)))]
        refine mul_le_mul_of_nonneg_left ?_ hN.le
        rw [div_eq_mul_inv]
        have : (P x ^ 2)⁻¹ ≤ (θ.p ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (hP.p_le hxm) 2)
        exact mul_le_mul hse this (by positivity) (hadm.e_eq_inv_N ▸ by positivity)
    · filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
      have hPpos := hP.pos' hxm
      have hs1 := hP.N_mul_sub_mul_deriv_le_one hx.1 hx.2
      show θ.N * ((P x - x * deriv P x) / P x ^ 2) ≤ (P x ^ 2)⁻¹
      rw [← mul_div_assoc, div_eq_mul_inv]
      have h0 : 0 ≤ (P x ^ 2)⁻¹ := by positivity
      nlinarith
  rw [hint] at hle
  have hma := hadm.m_mul_a
  have hcp : θ.N * (θ.ξ₀ - θ.c * θ.p⁻¹) = θ.N * θ.ξ₀ - θ.m * θ.a := by
    rw [hma]; field_simp
  linarith

theorem Mf_ge_small : (1 - θ.m) ^ 2 / θ.m ≤ Mf θ P := by
  have hadm := hP.admissible
  have hb := hP.bF_ge
  have hT := hP.Tf_ge_mean
  have hm := hadm.m_pos; have hm1 := hadm.m_lt_one
  have ha := hadm.a_nonneg
  have hN1 : θ.N - 1 = 1 - θ.m := by
    unfold Params.N Params.m NF mF
    have := hadm.t_pos
    field_simp; ring
  -- `M = N(b - ξ₀) ≥ (N - 1) b + (1 - m) a ≥ (1 - m)(a + mean)`, and `a + mean = 2(1-m)/m`
  have hmean : 2 * θ.a + 1 / θ.p - 1 = 2 * (1 - θ.m) / θ.m := by
    unfold Params.a Params.m aF cF mF
    have ht := hadm.t_pos; have hp := hadm.p_pos
    field_simp; ring
  have hM : Mf θ P = θ.N * (θ.a + Tf θ P) - θ.N * θ.ξ₀ := by unfold Mf; ring
  have hNb : (1 - θ.m) * (θ.a + Tf θ P) + (1 - θ.m) * θ.a ≤ Mf θ P := by
    rw [hM]
    have : θ.N * (θ.a + Tf θ P) = (θ.a + Tf θ P) + (θ.N - 1) * (θ.a + Tf θ P) := by ring
    rw [this, hN1]
    linarith
  have hsum : (1 - θ.m) * (2 * (1 - θ.m) / θ.m) ≤ Mf θ P := by
    rw [← hmean]
    have : 0 ≤ 1 - θ.m := by linarith
    nlinarith
  have : (1 - θ.m) ^ 2 / θ.m ≤ (1 - θ.m) * (2 * (1 - θ.m) / θ.m) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hm]
    nlinarith
  linarith

theorem Mf_ge_ξ₀ : θ.N * (θ.N - 1) * θ.ξ₀ ≤ Mf θ P := by
  have hadm := hP.admissible
  have hb := hP.bF_ge
  have hm1 := hadm.m_lt_one
  have ha := hadm.a_nonneg
  have hN := hadm.N_pos
  have hN1 : θ.N - 1 = 1 - θ.m := by
    unfold Params.N Params.m NF mF
    have := hadm.t_pos
    field_simp; ring
  unfold Mf
  have : θ.N * θ.ξ₀ ≤ θ.a + Tf θ P := by nlinarith
  nlinarith

/-- At `p_f = 1` the interval is a point and `R_f ≥ 3/4` (certified `p_one_ratio`). -/
theorem three_quarters_le_Rf_of_p_eq_one (hI : FamilyIdentities) (hp1 : θ.p = 1) :
    3 / 4 ≤ Rf θ P := by
  have hadm := hP.admissible
  have ht := hadm.t_pos; have ht1 := hadm.t_lt_one
  -- the curve is constant `1`, and `P ≤ h ξ + e` at `c_f` forces `c_f = ξ₀`
  have hcξ : θ.c = θ.ξ₀ := by
    have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
    have h1 := hP.le_line₂ hc
    rw [hP.left_end, hp1] at h1
    have e1 := hadm.line₂_ξ₀
    unfold Params.line₂ at h1 e1
    have hh := hadm.h_pos
    have : θ.h * θ.ξ₀ ≤ θ.h * θ.c := by linarith
    have := le_of_mul_le_mul_left this hh
    linarith [hP.c_le_ξ₀]
  have hT : Tf θ P = 0 := by unfold Tf; rw [hcξ, intervalIntegral.integral_same]
  have hQ : Qf θ P = 0 := by unfold Qf; rw [hcξ, intervalIntegral.integral_same]
  have ht0 : θ.t ≠ 0 := ht.ne'
  have h1t : 1 + θ.t ≠ 0 := by linarith
  have hM : Mf θ P = (1 - θ.t) ^ 2 / (θ.t * (1 + θ.t)) := by
    unfold Mf
    rw [hT, ← hcξ]
    unfold Params.N Params.a Params.c NF aF cF
    rw [hp1]
    field_simp
    ring
  have hG : Gf θ P = 4 / (1 + θ.t) := by
    unfold Gf
    rw [hQ, hp1, Real.log_one]
    unfold Params.N Params.a Params.m NF aF mF cF
    rw [hp1]
    field_simp
    ring
  have hMG : Mf θ P + Gf θ P = (1 + θ.t) / θ.t := by
    rw [hM, hG]; field_simp; ring
  have hM2 : Mf θ P + 2 = (1 + 3 * θ.t ^ 2) / (θ.t * (1 + θ.t)) := by
    rw [hM]; field_simp; ring
  have hR : Rf θ P = (1 + 3 * θ.t ^ 2) / (1 + θ.t) ^ 2 := by
    unfold Rf
    rw [hM2, hMG]
    field_simp
  rw [hR, hI.p_one_ratio θ.t ht]
  have : 0 ≤ (3 * θ.t - 1) ^ 2 / (4 * (1 + θ.t) ^ 2) := by positivity
  linarith

end InClass

/-- The parameter bounds of `lem:2fam-compact`. -/
theorem region_bounds (hN : FamilyNumerics) (hI : FamilyIdentities)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 3 / 4) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
    (hR : Rf θ P < β) : 1 / 32 < θ.m ∧ θ.m < 3 / 4 ∧ θ.ξ₀ < 600 ∧ θ.p < 1 := by
  have hadm := hP.admissible
  have hpos := hP.positivity'
  have hcmp := hP.comparison' hI hβ0
  have hm := hadm.m_pos
  have hNpos := hadm.N_pos
  have hMG : 0 < Mf θ P + Gf θ P := by linarith [hpos.2.1, hpos.2.2.1]
  -- `R < β` makes the comparison numerator positive
  have hnum : 0 < β * Gf θ P - (1 - β) * Mf θ P - 2 := by
    have hK : 0 < Kf β θ P := by
      rw [hcmp.2.2]
      apply mul_pos (div_pos hMG hNpos)
      rw [sub_pos, div_lt_one hβ0]; exact hR
    unfold Kf at hK
    exact (div_pos_iff_of_pos_right (mul_pos hβ0 hNpos)).mp hK
  have hm32 : 1 / 32 < θ.m := by
    by_contra hle
    push Not at hle
    have hG := hP.Gf_le_small
    have hM := hP.Mf_ge_small
    have hmono := small_mass_mono' (a := θ.m) ⟨hm, hle⟩ (b := 1 / 32) ⟨by norm_num, le_rfl⟩
    have hend := hN.small_mass_endpoint
    -- `β G - (1-β) M - 2 ≤ smallMassBound m ≤ smallMassBound (1/32) < 0`
    have hsm : β * Gf θ P - (1 - β) * Mf θ P - 2 ≤ smallMassBound θ.m := by
      unfold smallMassBound
      have hG0 : 0 ≤ Gf θ P := by linarith [hpos.2.2.1]
      have h1 : β * Gf θ P ≤ 3 / 4 * (4 + 2 * Real.log (2 / θ.m)) :=
        (mul_le_mul_of_nonneg_right hβ hG0).trans (mul_le_mul_of_nonneg_left hG (by norm_num))
      have h2 : 1 / 4 * ((1 - θ.m) ^ 2 / θ.m) ≤ (1 - β) * Mf θ P :=
        mul_le_mul (by linarith) hM (by positivity) (by linarith)
      have e : (1 - θ.m) ^ 2 / (4 * θ.m) = 1 / 4 * ((1 - θ.m) ^ 2 / θ.m) := by field_simp
      rw [e]
      linarith
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hsm; linarith
    · have := hmono hlt; linarith
  have hm34 : θ.m < 3 / 4 := lt_of_le_of_lt hpos.2.2.2.2.1 (hR.trans_le hβ)
  refine ⟨hm32, hm34, ?_, ?_⟩
  · -- `M < 184` and `M ≥ N(N-1)ξ₀ > (5/16)ξ₀`
    have hG := hpos.2.2.2.1
    have hGm : Gf θ P < 64 := by
      have : 2 / θ.m < 64 := by rw [div_lt_iff₀ hm]; linarith
      linarith
    have hM184 : Mf θ P < 184 := by
      have hG0 : 0 ≤ Gf θ P := by linarith [hpos.2.2.1]
      have : (1 - β) * Mf θ P < 46 := by nlinarith
      nlinarith [hpos.2.1]
    have hMξ := hP.Mf_ge_ξ₀
    have ht35 : θ.t < 3 / 5 := by
      unfold Params.m mF at hm34
      have := hadm.t_pos
      rw [div_lt_iff₀ (by linarith)] at hm34
      linarith
    have hN54 : 5 / 4 < θ.N := by
      unfold Params.N NF; rw [lt_div_iff₀ (by linarith [hadm.t_pos])]; linarith
    have hN14 : 1 / 4 < θ.N - 1 := by linarith
    have hNN : 5 / 16 < θ.N * (θ.N - 1) := by nlinarith
    have hξ := hadm.ξ₀_pos
    nlinarith
  · rcases lt_or_eq_of_le hadm.p_le_one with h | h
    · exact h
    · have := hP.three_quarters_le_Rf_of_p_eq_one hI h
      linarith

end FixedPrice.TwoUnit.Family
