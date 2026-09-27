import FixedPrice.ReferenceRegularity

/-! The log-energy of the reference curve equals the endpoint value `Φ_d(x(C))` of the
paper's (G2): the line contributes an elementary integral, the middle arc is integrated
through the antiderivative `arcPrimitive` composed with the inverse clock, and the cap
contributes nothing. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology

namespace FixedPrice

/-- The integrand of the log-energy of the reference curve. -/
def refEnergyIntegrand (d C Y a : ℝ) : ℝ :=
  d ^ 2 - Real.exp (-2 * refLog d C Y a) - a * (deriv (refLog d C Y) a) ^ 2

/-- Antiderivative of the middle-arc energy in the curve parameter. -/
def arcPrimitive (C r : ℝ) : ℝ :=
  C * (-Real.exp (-primitive C r) - 2 * r) + (C - 1 / 2) * primitive C r -
    Real.log (denominator C r) / 2

theorem arcPrimitive_zero (C : ℝ) : arcPrimitive C 0 = -C := by
  simp [arcPrimitive, primitive, denominator]

theorem hasDerivAt_arcPrimitive {C r : ℝ} (hr : 0 ≤ r)
    (hD : ∀ s ∈ Icc (0 : ℝ) r, 0 < denominator C s) :
    HasDerivAt (arcPrimitive C)
      (C * Real.exp (-primitive C r) / denominator C r - C -
        C ^ 2 * r ^ 2 / denominator C r) r := by
  have hDr := hD r ⟨hr, le_rfl⟩
  have h1 := hasDerivAt_primitive_of_positive hr hD
  have h2 := h1.neg.exp
  have h3 := (hasDerivAt_denominator C r).log (ne_of_gt hDr)
  have h : HasDerivAt
      (fun s => C * (-Real.exp (-primitive C s) - 2 * s) + (C - 1 / 2) * primitive C s -
        Real.log (denominator C s) / 2)
      (C * (-(Real.exp (-primitive C r) * -(denominator C r)⁻¹) - 2 * 1) +
        (C - 1 / 2) * (denominator C r)⁻¹ - (2 * C * r - 1) / denominator C r / 2) r :=
    (((h2.neg.sub ((hasDerivAt_id r).const_mul 2)).const_mul C).add
      (h1.const_mul (C - 1 / 2))).sub (h3.div_const 2)
  refine h.congr_deriv ?_
  have hD_eq : denominator C r = 1 - r + C * r ^ 2 := rfl
  field_simp
  rw [hD_eq]
  ring

section BranchPoint

variable {d C Y : ℝ}

theorem IsBranchRoot.exp_neg_two_arcLog (hd : 0 < d) (hY : IsBranchRoot d C Y)
    {r : ℝ} (hr : r ∈ Icc 0 Y) :
    Real.exp (-2 * arcLog d C r) = d ^ 2 * denominator C r * Real.exp (primitive C r) := by
  have hDpos := hY.2.2.1 r hr
  unfold arcLog
  rw [show -2 * (-Real.log d - (Real.log (denominator C r) + primitive C r) / 2) =
      Real.log (d ^ 2) + Real.log (denominator C r) + primitive C r by
    rw [Real.log_pow]; push_cast; ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_log (pow_pos hd 2), Real.exp_log hDpos]

/-- On the middle arc, `arcPrimitive ∘ arcParam` is an antiderivative of minus the integrand. -/
theorem IsBranchRoot.hasDerivAt_arcPrimitive_comp (hd : 0 < d) (hC : 0 < C)
    (hY : IsBranchRoot d C Y) {a : ℝ} (ha : a ∈ Ioo (lineEnd C Y) (capStart d C)) :
    HasDerivAt (fun b => arcPrimitive C (arcParam d C Y b)) (-(refEnergyIntegrand d C Y a)) a := by
  have hr := hY.arcParam_mem hd hC a
  have h1 := hasDerivAt_arcPrimitive hr.1 (hY.physical_below hr.2)
  have h2 := hY.hasDerivAt_arcParam hd hC ha
  refine (h1.comp a h2).congr_deriv ?_
  unfold refEnergyIntegrand
  rw [(hY.hasDerivAt_refLog_arc hd hC ha).deriv, refLog_of_mem_arc ha.1 ha.2.le,
    hY.exp_neg_two_arcLog hd hr]
  have hta : arcTime d C (arcParam d C Y a) = a := hY.arcTime_arcParam hd hC (Ioo_subset_Icc_self ha)
  have hDpos := hY.2.2.1 _ hr
  have hapos : 0 < a := (hY.lineEnd_pos hC).trans ha.1
  set r := arcParam d C Y a with hr_def
  rw [← hta]
  unfold arcTime
  rw [Real.exp_neg]
  have hE : Real.exp (primitive C r) ≠ 0 := Real.exp_ne_zero _
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hC0 : C ≠ 0 := ne_of_gt hC
  have hD0 : denominator C r ≠ 0 := ne_of_gt hDpos
  field_simp
  try ring

theorem IsBranchRoot.refEnergyIntegrand_intervalIntegrable (hd : 0 < d) (hC : 0 < C)
    (hY : IsBranchRoot d C Y) {R : ℝ} (hR : capStart d C ≤ R) :
    IntervalIntegrable (refEnergyIntegrand d C Y) volume 0 R := by
  have hac := hY.refLog_absolutelyContinuous hd hC hR
  have he : ContinuousOn (fun a => Real.exp (-2 * refLog d C Y a)) (uIcc 0 R) :=
    Real.continuous_exp.comp_continuousOn (hac.continuousOn.const_mul (-2))
  exact (continuousOn_const.sub he).intervalIntegrable.sub
    (hY.refLog_weighted_deriv_intervalIntegrable hd hC hR)

/-- The line piece of the energy. -/
theorem IsBranchRoot.energy_line (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    (∫ a in (0 : ℝ)..lineEnd C Y, refEnergyIntegrand d C Y a) =
      (d ^ 2 * lineEnd C Y - Real.log (lineIntercept C Y + lineEnd C Y) +
        (1 - lineIntercept C Y) / (lineIntercept C Y + lineEnd C Y)) -
      (d ^ 2 * 0 - Real.log (lineIntercept C Y + 0) +
        (1 - lineIntercept C Y) / (lineIntercept C Y + 0)) := by
  have hx := hY.lineIntercept_pos
  have hE := hY.lineEnd_pos hC
  have hcongr : (∫ a in (0 : ℝ)..lineEnd C Y, refEnergyIntegrand d C Y a) =
      ∫ a in (0 : ℝ)..lineEnd C Y, d ^ 2 - (1 + a) / (lineIntercept C Y + a) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (lineEnd C Y)] with a hne ha
    have ha' : a ∈ Ioc 0 (lineEnd C Y) := by rwa [uIoc_of_le hE.le] at ha
    have hlt : a < lineEnd C Y := lt_of_le_of_ne ha'.2 hne
    unfold refEnergyIntegrand
    rw [(hY.hasDerivAt_refLog_line ⟨ha'.1, hlt⟩).deriv, refLog_of_le_lineEnd hlt.le]
    have hpos : 0 < lineIntercept C Y + a := by linarith [ha'.1]
    rw [show -2 * Real.log (lineIntercept C Y + a) = Real.log ((lineIntercept C Y + a) ^ 2)⁻¹ by
      rw [Real.log_inv, Real.log_pow]; push_cast; ring]
    rw [Real.exp_log (inv_pos.mpr (pow_pos hpos 2))]
    field_simp
    try ring
  rw [hcongr]
  have hderiv : ∀ a ∈ uIcc (0 : ℝ) (lineEnd C Y),
      HasDerivAt (fun a => d ^ 2 * a - Real.log (lineIntercept C Y + a) +
        (1 - lineIntercept C Y) / (lineIntercept C Y + a))
        (d ^ 2 - (1 + a) / (lineIntercept C Y + a) ^ 2) a := by
    intro a ha
    have ha' : a ∈ Icc 0 (lineEnd C Y) := by rwa [uIcc_of_le hE.le] at ha
    have hpos : 0 < lineIntercept C Y + a := by linarith [ha'.1]
    have h1 := (hasDerivAt_id a).const_mul (d ^ 2)
    have h2 := ((hasDerivAt_id a).const_add (lineIntercept C Y)).log (ne_of_gt hpos)
    have h3 := (hasDerivAt_const a (1 - lineIntercept C Y)).div
      ((hasDerivAt_id a).const_add (lineIntercept C Y)) (ne_of_gt hpos)
    refine ((h1.sub h2).add h3).congr_deriv ?_
    simp only [id_eq]
    field_simp
    ring
  have hint : IntervalIntegrable (fun a => d ^ 2 - (1 + a) / (lineIntercept C Y + a) ^ 2)
      volume 0 (lineEnd C Y) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    have ha' : a ∈ Icc 0 (lineEnd C Y) := by rwa [uIcc_of_le hE.le] at ha
    exact pow_ne_zero 2 (ne_of_gt (by linarith [ha'.1]))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- The middle-arc piece of the energy. -/
theorem IsBranchRoot.energy_arc (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    (∫ a in lineEnd C Y..capStart d C, refEnergyIntegrand d C Y a) =
      arcPrimitive C Y - arcPrimitive C 0 := by
  have hEA := hY.lineEnd_lt_capStart hd hC
  have hE := hY.lineEnd_pos hC
  have hint : IntervalIntegrable (fun a => -(refEnergyIntegrand d C Y a)) volume
      (lineEnd C Y) (capStart d C) := by
    apply IntervalIntegrable.neg
    apply (hY.refEnergyIntegrand_intervalIntegrable hd hC le_rfl).mono_set
    rw [uIcc_of_le hEA.le, uIcc_of_le (capStart_pos hd hC).le]
    exact Icc_subset_Icc hE.le le_rfl
  have hcont : ContinuousOn (fun b => arcPrimitive C (arcParam d C Y b))
      (uIcc (lineEnd C Y) (capStart d C)) := by
    rw [uIcc_of_le hEA.le]
    have h1 : ContinuousOn (arcPrimitive C) (Icc 0 Y) := fun r hr =>
      (hasDerivAt_arcPrimitive hr.1 (hY.physical_below hr.2)).continuousAt.continuousWithinAt
    exact h1.comp (hY.arcParam_continuousOn hd hC) (fun a _ => hY.arcParam_mem hd hC a)
  have hderiv : ∀ a ∈ Ioo (min (lineEnd C Y) (capStart d C)) (max (lineEnd C Y) (capStart d C)),
      HasDerivWithinAt (fun b => arcPrimitive C (arcParam d C Y b))
        (-(refEnergyIntegrand d C Y a)) (Ioi a) a := by
    intro a ha
    rw [min_eq_left hEA.le, max_eq_right hEA.le] at ha
    exact (hY.hasDerivAt_arcPrimitive_comp hd hC ha).hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint
  rw [intervalIntegral.integral_neg, hY.arcParam_capStart hd hC, hY.arcParam_lineEnd hd hC] at h
  linarith

/-- The cap contributes nothing. -/
theorem IsBranchRoot.energy_cap (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {R : ℝ} (hR : capStart d C ≤ R) :
    (∫ a in capStart d C..R, refEnergyIntegrand d C Y a) = 0 := by
  have hzero : (∫ a in capStart d C..R, refEnergyIntegrand d C Y a) =
      ∫ _a in capStart d C..R, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with a ha
    have ha' : a ∈ Ioc (capStart d C) R := by rwa [uIoc_of_le hR] at ha
    unfold refEnergyIntegrand
    rw [(hY.hasDerivAt_refLog_cap hd hC ha'.1).deriv, hY.refLog_of_capStart_le hd hC ha'.1.le]
    rw [show -2 * -Real.log d = Real.log (d ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (pow_pos hd 2)]
    ring
  rw [hzero]
  simp

/-- The log-energy of the reference curve is the endpoint value of (G2). -/
theorem IsBranchRoot.logEnergy_refLog (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {R : ℝ} (hR : capStart d C ≤ R) :
    logEnergy d R (refLog d C Y) = endpointValue C Y := by
  have hE := hY.lineEnd_pos hC
  have hEA := hY.lineEnd_lt_capStart hd hC
  have hA := capStart_pos hd hC
  have hR0 : (0 : ℝ) ≤ R := hA.le.trans hR
  have hint := hY.refEnergyIntegrand_intervalIntegrable hd hC hR
  have hsub : ∀ {a b : ℝ}, a ∈ Icc (0 : ℝ) R → b ∈ Icc (0 : ℝ) R →
      IntervalIntegrable (refEnergyIntegrand d C Y) volume a b := by
    intro a b ha hb
    apply hint.mono_set
    rw [uIcc_of_le hR0]
    exact uIcc_subset_Icc ha hb
  have hsplit : (∫ a in (0 : ℝ)..R, refEnergyIntegrand d C Y a) =
      (∫ a in (0 : ℝ)..lineEnd C Y, refEnergyIntegrand d C Y a) +
      (∫ a in lineEnd C Y..capStart d C, refEnergyIntegrand d C Y a) +
      ∫ a in capStart d C..R, refEnergyIntegrand d C Y a := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hsub ⟨le_rfl, hR0⟩ ⟨hE.le, hEA.le.trans hR⟩)
      (hsub ⟨hE.le, hEA.le.trans hR⟩ ⟨hA.le, hR⟩),
      intervalIntegral.integral_add_adjacent_intervals (hsub ⟨le_rfl, hR0⟩ ⟨hA.le, hR⟩)
      (hsub ⟨hA.le, hR⟩ ⟨hR0, le_rfl⟩)]
  have hL : logEnergy d R (refLog d C Y) =
      -Real.log d - refLog d C Y 0 + ∫ a in (0 : ℝ)..R, refEnergyIntegrand d C Y a := rfl
  rw [hL, hsplit, hY.energy_line hd hC, hY.energy_arc hd hC, hY.energy_cap hd hC hR,
    hY.refLog_zero hC, arcPrimitive_zero, hY.lineIntercept_add_lineEnd,
    Real.log_div (ne_of_gt hY.1) (ne_of_gt hY.denominator_pos')]
  unfold arcPrimitive
  rw [Real.exp_neg, hY.exp_primitive hd, inv_div]
  have hcontact : Real.log d = (Real.log (denominator C Y) - primitive C Y) / 2 - Real.log Y := by
    have h := hY.2.2.2
    unfold contactLog at h
    linarith
  rw [hcontact]
  have hD0 : denominator C Y ≠ 0 := ne_of_gt hY.denominator_pos'
  have h1D : 1 - denominator C Y ≠ 0 := ne_of_gt (sub_pos.mpr hY.denominator_lt_one)
  have hY0 : Y ≠ 0 := ne_of_gt hY.1
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hCY : 1 - C * Y ≠ 0 := ne_of_gt (sub_pos.mpr hY.2.1)
  have hxdef : lineIntercept C Y = (1 - denominator C Y) / denominator C Y := rfl
  have hx_inv : (1 - lineIntercept C Y) / lineIntercept C Y =
      (2 * denominator C Y - 1) / (1 - denominator C Y) := by
    rw [hxdef]
    field_simp
    try ring
  have hx_Y : (1 - lineIntercept C Y) / (Y / denominator C Y) =
      (2 * denominator C Y - 1) / Y := by
    rw [hxdef]
    field_simp
    try ring
  have haE : d ^ 2 * lineEnd C Y = d ^ 2 * C * Y ^ 2 / denominator C Y := by
    unfold lineEnd
    ring
  simp only [mul_zero, add_zero, zero_sub]
  rw [hx_inv, hx_Y, haE]
  unfold endpointValue
  have hDeq : denominator C Y = 1 - Y + C * Y ^ 2 := rfl
  field_simp
  rw [hDeq]
  ring

end BranchPoint

end FixedPrice
