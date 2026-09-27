import FixedPrice.ReferenceEnergy
import FixedPrice.Reciprocal

/-! The universal upper bound of Theorem C: for every measurable control `h` with values
in `[0, 1]`, `J_d(h) ≤ S(C_d)`. The competitor's reciprocal state is compared with the
reference curve at its own endpoint (G1, through the weighted calibration), and the endpoint
value is compared with the maximizing curvature (G2, through the global branch). The endpoint
`x = 1/d` (no trade) uses the constant reference curve. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology

namespace FixedPrice

/-- `S(C) - 1` is the endpoint value at the maximizing curvature. -/
theorem endpointValue_endParameter {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    endpointValue C (endParameter C) = optimalValue C - 1 := by
  have hC0 : C ≠ 0 := ne_of_gt (by linarith [hC.1])
  have hC1 : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have h1 : C * endParameter C = (1 - 2 * C) / (1 - C) := by
    unfold endParameter
    field_simp
  have h2 : 1 - C * endParameter C = C / (1 - C) := by
    rw [h1]
    field_simp
    ring
  have h3 : C ^ 2 * endParameter C / (1 - C * endParameter C) = 1 - 2 * C := by
    rw [h2, show C ^ 2 * endParameter C = C * (C * endParameter C) by ring, h1]
    field_simp
    try ring
  unfold endpointValue optimalValue
  rw [h3]
  ring

/-- The optimal value is at least one. -/
theorem one_le_optimalValue {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) : 1 ≤ optimalValue C := by
  have hy := endParameter_pos hC
  have hCy := mul_endParameter_lt_one hC
  have hC0 : 0 < C := by linarith [hC.1]
  have hC1 : 0 < 1 - C := by linarith [hC.2]
  have hprim : endParameter C ≤ primitive C (endParameter C) := by
    unfold primitive
    have hi : IntervalIntegrable (fun r => (denominator C r)⁻¹) volume 0 (endParameter C) :=
      ContinuousOn.intervalIntegrable_of_Icc hy.le ((continuous_denominator C).continuousOn.inv₀
        (fun r _ => ne_of_gt (denominator_pos hC.1 r)))
    calc endParameter C = ∫ _r in (0 : ℝ)..endParameter C, (1 : ℝ) := by simp
      _ ≤ ∫ r in (0 : ℝ)..endParameter C, (denominator C r)⁻¹ := by
          apply intervalIntegral.integral_mono_on hy.le intervalIntegrable_const hi
          intro r hr
          rw [one_le_inv₀ (denominator_pos hC.1 r)]
          unfold denominator
          have hCr : C * r ≤ C * endParameter C := mul_le_mul_of_nonneg_left hr.2 hC0.le
          nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr (hCr.trans hCy.le))]
  have h1 : C * endParameter C = (1 - 2 * C) / (1 - C) := by
    unfold endParameter
    field_simp
  have h2 : 1 ≤ 2 * C + C * endParameter C := by
    rw [h1, ← sub_nonneg]
    have : 2 * C + (1 - 2 * C) / (1 - C) - 1 = C * (1 - 2 * C) / (1 - C) := by
      field_simp
      ring
    rw [this]
    apply div_nonneg (mul_nonneg hC0.le (by linarith [hC.2])) hC1.le
  unfold optimalValue
  nlinarith [mul_le_mul_of_nonneg_left hprim hC0.le]

section Comparison

variable {d C Y : ℝ} {h : ℝ → ℝ}

/-- The competitor's log-energy is at most the endpoint value of the branch point with the
same endpoint, and equality forces the competitor's reciprocal state onto the reference curve. -/
theorem objective_endpoint_comparison (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    (hx : (state d h 1)⁻¹ = lineIntercept C Y) :
    objective d h - 1 ≤ endpointValue C Y ∧
      (objective d h - 1 = endpointValue C Y →
        ∀ a ∈ Icc (0 : ℝ) (tailTime d h 0),
          Real.log (reciprocalState d h a) = refLog d C Y a) := by
  have hi := control_intervalIntegrable hmeas hbox
  set R : ℝ := max (tailTime d h 0) (capStart d C) with hR_def
  have hRt : tailTime d h 0 ≤ R := le_max_left _ _
  have hRa : capStart d C ≤ R := le_max_right _ _
  have hRpos : (0 : ℝ) < R := (capStart_pos hd hC).trans_le hRa
  have hR0 : (0 : ℝ) ≤ R := hRpos.le
  set v : ℝ → ℝ := fun a => Real.log (reciprocalState d h a) - refLog d C Y a with hv_def
  have hpv : (fun a => refLog d C Y a + v a) = fun a => Real.log (reciprocalState d h a) := by
    funext a
    simp only [hv_def]
    ring
  have hobj : objective d h - 1 = logEnergy d R (fun a => refLog d C Y a + v a) := by
    rw [reciprocal_energy_identity_extended hd hmeas hbox hRt, hpv]
  have hend : endpointValue C Y = logEnergy d R (refLog d C Y) :=
    (hY.logEnergy_refLog hd hC hRa).symm
  have hell := hY.refLog_absolutelyContinuous hd hC hRa
  have hlogp := log_reciprocalState_absolutelyContinuous (R := R) hd hi hbox
  have hv : AbsolutelyContinuousOnInterval v 0 R := hlogp.sub hell
  have hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R := by
    -- the weighted squared slope of the difference is integrable
    have hA : IntervalIntegrable (fun a => a * (deriv (fun u => Real.log (reciprocalState d h u)) a) ^ 2)
        volume 0 R := by
      have h1 := reciprocalState_weighted_deriv_intervalIntegrable hd hmeas hbox
      have h2 : IntervalIntegrable
          (fun a => a * (deriv (fun u => Real.log (reciprocalState d h u)) a) ^ 2)
          volume (tailTime d h 0) R := by
        apply (intervalIntegrable_const (c := (0 : ℝ))).congr_ae
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
        filter_upwards with a ha
        have ha' : a ∈ Ioc (tailTime d h 0) R := by rwa [uIoc_of_le hRt] at ha
        have hder : HasDerivAt (fun u => Real.log (reciprocalState d h u)) 0 a := by
          refine (hasDerivAt_const a (Real.log d⁻¹)).congr_of_eventuallyEq ?_
          filter_upwards [Ioi_mem_nhds ha'.1] with b hb
          rw [reciprocalState_constant_tail hd hi hbox (le_of_lt hb)]
        rw [hder.deriv]
        ring
      exact h1.trans h2
    have hB := hY.refLog_weighted_deriv_intervalIntegrable hd hC hRa
    refine ((hA.const_mul 2).add (hB.const_mul 2)).mono_fun ?_ ?_
    · exact (measurable_id.mul ((measurable_deriv v).pow_const 2)).aestronglyMeasurable
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hlogp.ae_differentiableAt, hell.ae_differentiableAt] with a h1 h2 ha
      have ha' : a ∈ Ioc 0 R := by rwa [uIoc_of_le hR0] at ha
      have hmem : a ∈ uIcc 0 R := by rw [uIcc_of_le hR0]; exact ⟨ha'.1.le, ha'.2⟩
      have hderv : deriv v a = deriv (fun u => Real.log (reciprocalState d h u)) a -
          deriv (refLog d C Y) a :=
        ((h1 hmem).hasDerivAt.sub (h2 hmem).hasDerivAt).deriv
      simp only [Real.norm_eq_abs]
      rw [hderv]
      have hapos : 0 ≤ a := ha'.1.le
      rw [abs_of_nonneg (mul_nonneg hapos (sq_nonneg _)),
        abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (deriv (fun u => Real.log (reciprocalState d h u)) a +
        deriv (refLog d C Y) a), mul_nonneg hapos (sq_nonneg (deriv (fun u => Real.log (reciprocalState d h u)) a +
        deriv (refLog d C Y) a))]
  have hv0 : v 0 = 0 := by
    simp only [hv_def]
    rw [reciprocalState_zero hd hi hbox, hx, hY.refLog_zero hC, sub_self]
  have hvR : v R = 0 := by
    simp only [hv_def]
    rw [reciprocalState_constant_tail hd hi hbox hRt, hY.refLog_of_capStart_le hd hC hRa,
      Real.log_inv]
    ring
  have hc : ∀ᵐ a, a ∈ Icc (0 : ℝ) R →
      (Real.exp (-2 * refLog d C Y a) + deriv (refWeight d C Y) a) * v a ≤ 0 := by
    -- the contact sign
    filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (lineEnd C Y),
      volume.ae_ne (capStart d C)] with a h0 h1 h2 ha
    have hapos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm h0)
    have hppos : 0 < reciprocalState d h a :=
      lt_of_lt_of_le (inv_pos.mpr (by linarith)) (reciprocalState_bounds hd hi hbox a).1
    rcases lt_trichotomy a (lineEnd C Y) with hlt | heq | hgt
    · rw [hY.contact_line ⟨hapos, hlt⟩]
      apply mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (by linarith [hY.lineIntercept_pos]) (sq_nonneg _))
      simp only [hv_def]
      rw [refLog_of_le_lineEnd hlt.le, sub_nonpos]
      apply Real.log_le_log hppos
      have hline := reciprocalState_line_obstacle hd hi hbox hapos.le
      rwa [reciprocalState_zero hd hi hbox, hx] at hline
    · exact absurd heq h1
    · rcases lt_trichotomy a (capStart d C) with hlt' | heq' | hgt'
      · rw [hY.contact_arc hd hC ⟨hgt, hlt'⟩, zero_mul]
      · exact absurd heq' h2
      · rw [hY.contact_cap hd hC hgt']
        apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg d)
        simp only [hv_def]
        rw [hY.refLog_of_capStart_le hd hC hgt'.le, sub_neg_eq_add]
        have hcap := Real.log_le_log hppos (reciprocalState_bounds hd hi hbox a).2
        rw [Real.log_inv] at hcap
        linarith
  have hw := hY.refWeight_absolutelyContinuous hd hC hRa
  have hw_ae := hY.refWeight_ae_eq hd hC hRa
  have hellSq := hY.refLog_weighted_deriv_intervalIntegrable hd hC hRa
  refine ⟨?_, ?_⟩
  · rw [hobj, hend]
    exact logEnergy_le_of_weight_calibration hR0 hell hv hw hw_ae hellSq hvSq hv0 hvR hc
  · intro heq a ha
    have hzero := eqOn_zero_of_weight_calibration hRpos hell hv hw hw_ae hellSq hvSq hv0 hvR hc
      (by rw [← hobj, ← hend]; exact heq)
    have := hzero ⟨ha.1, ha.2.trans hRt⟩
    simp only [hv_def] at this
    linarith

/-- The competitor's log-energy is at most the endpoint value of the branch point with the
same endpoint. -/
theorem objective_sub_one_le_endpointValue (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    (hx : (state d h 1)⁻¹ = lineIntercept C Y) :
    objective d h - 1 ≤ endpointValue C Y :=
  (objective_endpoint_comparison hd hC hY hmeas hbox hx).1

/-- The no-trade endpoint: the constant reference curve gives `J_d(h) ≤ 1`. -/
theorem objective_le_one_of_cap (hd : 0 < d)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    (hcap : (state d h 1)⁻¹ = d⁻¹) : objective d h ≤ 1 := by
  have hi := control_intervalIntegrable hmeas hbox
  set R := tailTime d h 0 with hR_def
  have hR0 : (0 : ℝ) ≤ R := (tailTime_pos_zero hd hi hbox).le
  set v : ℝ → ℝ := fun a => Real.log (reciprocalState d h a) + Real.log d with hv_def
  have hpv : (fun a => (fun _ : ℝ => -Real.log d) a + v a) =
      fun a => Real.log (reciprocalState d h a) := by
    funext a
    simp only [hv_def]
    ring
  have hE := reciprocal_energy_identity hd hmeas hbox
  have hconst : logEnergy d R (fun _ => -Real.log d) = 0 := by
    unfold logEnergy
    have hz : ∀ a : ℝ, d ^ 2 - Real.exp (-2 * -Real.log d) -
        a * (deriv (fun _ : ℝ => -Real.log d) a) ^ 2 = 0 := by
      intro a
      rw [deriv_const, show -2 * -Real.log d = Real.log (d ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (pow_pos hd 2)]
      ring
    simp only [hz, intervalIntegral.integral_zero]
    ring
  have hle : logEnergy d R (fun a => Real.log (reciprocalState d h a)) ≤
      logEnergy d R (fun _ => -Real.log d) := by
    rw [← hpv]
    have hlogp := log_reciprocalState_absolutelyContinuous (R := R) hd hi hbox
    have hcst : AbsolutelyContinuousOnInterval (fun _ : ℝ => -Real.log d) 0 R :=
      (LipschitzWith.const (-Real.log d)).lipschitzOnWith.absolutelyContinuousOnInterval
    have hzero : AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℝ)) 0 R :=
      (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
    have hv : AbsolutelyContinuousOnInterval v 0 R :=
      hlogp.add ((LipschitzWith.const (Real.log d)).lipschitzOnWith.absolutelyContinuousOnInterval)
    apply logEnergy_le_of_weight_calibration (w := fun _ => 0) hR0 hcst hv hzero
    · filter_upwards with a _
      rw [deriv_const]
      ring
    · simp only [deriv_const, mul_zero, zero_pow (two_ne_zero), mul_zero]
      exact intervalIntegrable_const
    · have hv' : (fun a => a * (deriv v a) ^ 2) =
          fun a => a * (deriv (fun u => Real.log (reciprocalState d h u)) a) ^ 2 := by
        funext a
        simp only [hv_def, deriv_add_const]
      rw [hv']
      exact reciprocalState_weighted_deriv_intervalIntegrable hd hmeas hbox
    · simp only [hv_def]
      rw [reciprocalState_zero hd hi hbox, hcap, Real.log_inv]
      ring
    · simp only [hv_def]
      rw [reciprocalState_constant_tail hd hi hbox le_rfl, Real.log_inv]
      ring
    · filter_upwards with a _
      rw [deriv_const, add_zero, show -2 * -Real.log d = Real.log (d ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (pow_pos hd 2)]
      apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg d)
      simp only [hv_def]
      have hppos : 0 < reciprocalState d h a :=
        lt_of_lt_of_le (inv_pos.mpr (by linarith)) (reciprocalState_bounds hd hi hbox a).1
      have hcap' := Real.log_le_log hppos (reciprocalState_bounds hd hi hbox a).2
      rw [Real.log_inv] at hcap'
      linarith
  linarith [hE, hle, hconst]

end Comparison

/-- **Theorem C, upper bound.** Every measurable control with values in `[0, 1]` has
objective at most `S(C_d)`, where `τ(C_d) = d`. -/
theorem objective_le_optimalValue {d C : ℝ} (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    objective d h ≤ optimalValue C := by
  have hg := state_bounds (d := d) hbox (t := 1) ⟨zero_le_one, le_rfl⟩
  have hgpos : 0 < state d h 1 := hd.trans_le hg.1
  set x₀ := (state d h 1)⁻¹ with hx₀
  have hx₀pos : 0 < x₀ := inv_pos.mpr hgpos
  have hx₀le : x₀ ≤ d⁻¹ := inv_anti₀ hd hg.1
  rcases eq_or_lt_of_le hx₀le with heq | hlt
  · exact (objective_le_one_of_cap hd hmeas hbox heq).trans (one_le_optimalValue hC)
  · set D₀ : ℝ := 1 / (1 + x₀) with hD₀_def
    have h1x : 0 < 1 + x₀ := by linarith
    have hD₀ : D₀ ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by rw [hD₀_def, div_lt_one h1x]; linarith⟩
    have hdx : d * x₀ < 1 := by
      have := mul_lt_mul_of_pos_left hlt hd
      rwa [mul_inv_cancel₀ (ne_of_gt hd)] at this
    have hdD : d * (1 - D₀) < D₀ := by
      have h1D : 1 - D₀ = x₀ / (1 + x₀) := by
        rw [hD₀_def]
        field_simp
        ring
      rw [h1D, hD₀_def, ← mul_div_assoc, div_lt_div_iff_of_pos_right h1x]
      exact hdx
    obtain ⟨C₁, Y₁, hC₁, hY₁, hDen⟩ := exists_branch_point hd hD₀ hdD
    have hx : (state d h 1)⁻¹ = lineIntercept C₁ Y₁ := by
      unfold lineIntercept
      rw [hDen, ← hx₀, hD₀_def]
      field_simp
      ring
    have h1 := objective_sub_one_le_endpointValue hd hC₁ hY₁ hmeas hbox hx
    have h2 := endpointValue_branch_le hd hC hinit hC₁ ⟨Y₁, hY₁⟩
    rw [hY₁.branchRoot_eq, endpointValue_endParameter hC] at h2
    linarith

end FixedPrice
