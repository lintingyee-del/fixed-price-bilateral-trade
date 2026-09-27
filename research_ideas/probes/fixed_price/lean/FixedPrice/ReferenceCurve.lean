import FixedPrice.GlobalBranch

/-! The reference curve `P_x` of the paper as a function of the tail time, built from a
branch point `(C, Y)`: the line `x + a` up to `a_e`, the middle arc (parametrised by the
curve parameter `r` and inverted here), and the cap `1/d` from `a_a` on. Everything is
recorded for the logarithm `ℓ = log P_x`, together with the weight `w = a ℓ'`. Derivatives are
only computed at interior points of the three pieces. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology

namespace FixedPrice

/-- Tail time along the middle arc as a function of the curve parameter. -/
def arcTime (d C r : ℝ) : ℝ := C / d ^ 2 * Real.exp (-primitive C r)

/-- The endpoint `x` of the reference curve, `(1 - D)/D` with `D = D_C(Y)`. -/
def lineIntercept (C Y : ℝ) : ℝ := (1 - denominator C Y) / denominator C Y

/-- The tail time `a_e` at which the line meets the middle arc. -/
def lineEnd (C Y : ℝ) : ℝ := C * Y ^ 2 / denominator C Y

/-- The tail time `a_a` at which the middle arc meets the cap. -/
def capStart (d C : ℝ) : ℝ := C / d ^ 2

/-- The curve parameter as a function of tail time on the middle arc. -/
def arcParam (d C Y a : ℝ) : ℝ :=
  invFunOn (arcTime d C) (Icc 0 Y) (max (lineEnd C Y) (min a (capStart d C)))

/-- `log P_x` on the middle arc, as a function of the curve parameter. -/
def arcLog (d C r : ℝ) : ℝ :=
  -Real.log d - (Real.log (denominator C r) + primitive C r) / 2

/-- `ℓ_x = log P_x` as a function of tail time. -/
def refLog (d C Y a : ℝ) : ℝ :=
  if a ≤ lineEnd C Y then Real.log (lineIntercept C Y + a)
  else if a ≤ capStart d C then arcLog d C (arcParam d C Y a)
  else -Real.log d

/-- The weight `a ℓ_x'`, written without derivatives. -/
def refWeight (d C Y a : ℝ) : ℝ :=
  if a ≤ lineEnd C Y then a / (lineIntercept C Y + a)
  else if a ≤ capStart d C then C * arcParam d C Y a
  else 0

section BranchPoint

variable {d C Y : ℝ}

theorem IsBranchRoot.denominator_pos' (hY : IsBranchRoot d C Y) : 0 < denominator C Y :=
  hY.2.2.1 Y ⟨hY.1.le, le_rfl⟩

theorem IsBranchRoot.denominator_lt_one (hY : IsBranchRoot d C Y) : denominator C Y < 1 := by
  have h1 := hY.1
  have h2 := hY.2.1
  unfold denominator
  nlinarith

theorem IsBranchRoot.lineIntercept_pos (hY : IsBranchRoot d C Y) : 0 < lineIntercept C Y :=
  div_pos (sub_pos.mpr hY.denominator_lt_one) hY.denominator_pos'

theorem IsBranchRoot.lineEnd_pos (hC : 0 < C) (hY : IsBranchRoot d C Y) : 0 < lineEnd C Y :=
  div_pos (mul_pos hC (pow_pos hY.1 2)) hY.denominator_pos'

theorem capStart_pos (hd : 0 < d) (hC : 0 < C) : 0 < capStart d C :=
  div_pos hC (pow_pos hd 2)

theorem arcTime_pos (hd : 0 < d) (hC : 0 < C) (r : ℝ) : 0 < arcTime d C r :=
  mul_pos (div_pos hC (pow_pos hd 2)) (Real.exp_pos _)

/-- The contact equation in exponential form. -/
theorem IsBranchRoot.exp_primitive (hd : 0 < d) (hY : IsBranchRoot d C Y) :
    Real.exp (primitive C Y) = denominator C Y / (d ^ 2 * Y ^ 2) := by
  have h := hY.2.2.2
  unfold contactLog at h
  have hD := hY.denominator_pos'
  have hprim : primitive C Y = Real.log (denominator C Y) - Real.log (Y ^ 2) -
      Real.log (d ^ 2) := by
    rw [Real.log_pow, Real.log_pow]
    push_cast
    linarith
  rw [hprim, Real.exp_sub, Real.exp_sub, Real.exp_log hD, Real.exp_log (pow_pos hY.1 2),
    Real.exp_log (pow_pos hd 2)]
  field_simp

theorem arcTime_zero (d C : ℝ) : arcTime d C 0 = capStart d C := by
  simp [arcTime, capStart, primitive]

theorem IsBranchRoot.arcTime_Y (hd : 0 < d) (hY : IsBranchRoot d C Y) :
    arcTime d C Y = lineEnd C Y := by
  unfold arcTime lineEnd
  rw [Real.exp_neg, hY.exp_primitive hd]
  have hD := ne_of_gt hY.denominator_pos'
  have hY0 := ne_of_gt hY.1
  have hd0 := ne_of_gt hd
  field_simp

theorem IsBranchRoot.lineIntercept_add_lineEnd (hY : IsBranchRoot d C Y) :
    lineIntercept C Y + lineEnd C Y = Y / denominator C Y := by
  have hD := ne_of_gt hY.denominator_pos'
  unfold lineIntercept lineEnd
  rw [← add_div, div_left_inj' hD]
  unfold denominator
  ring

theorem IsBranchRoot.arcLog_Y (hY : IsBranchRoot d C Y) :
    arcLog d C Y = Real.log (Y / denominator C Y) := by
  have h := hY.2.2.2
  unfold contactLog at h
  unfold arcLog
  rw [Real.log_div (ne_of_gt hY.1) (ne_of_gt hY.denominator_pos')]
  linarith

theorem arcLog_zero (d C : ℝ) : arcLog d C 0 = -Real.log d := by
  simp [arcLog, primitive, denominator]

theorem hasDerivAt_arcTime {r : ℝ} (hr : 0 ≤ r)
    (hD : ∀ s ∈ Icc (0 : ℝ) r, 0 < denominator C s) :
    HasDerivAt (arcTime d C) (-(arcTime d C r) / denominator C r) r := by
  have h1 := hasDerivAt_primitive_of_positive hr hD
  have h2 : HasDerivAt (fun y => C / d ^ 2 * Real.exp (-primitive C y))
      (C / d ^ 2 * (Real.exp (-primitive C r) * -(denominator C r)⁻¹)) r :=
    h1.neg.exp.const_mul (C / d ^ 2)
  refine h2.congr_deriv ?_
  unfold arcTime
  field_simp
  try ring

theorem hasDerivAt_arcLog {r : ℝ} (hr : 0 ≤ r)
    (hD : ∀ s ∈ Icc (0 : ℝ) r, 0 < denominator C s) :
    HasDerivAt (arcLog d C) (-(C * r) / denominator C r) r := by
  have hDr := hD r ⟨hr, le_rfl⟩
  have h1 := (hasDerivAt_denominator C r).log (ne_of_gt hDr)
  have h2 := hasDerivAt_primitive_of_positive hr hD
  have h3 : HasDerivAt (fun y => -Real.log d - (Real.log (denominator C y) + primitive C y) / 2)
      (-(((2 * C * r - 1) / denominator C r + (denominator C r)⁻¹) / 2)) r :=
    ((h1.add h2).div_const 2).const_sub (-Real.log d)
  refine h3.congr_deriv ?_
  field_simp
  ring

/-- The physical range of the branch point, restricted to `[0, r]`. -/
theorem IsBranchRoot.physical_below (hY : IsBranchRoot d C Y) {r : ℝ} (hr : r ≤ Y) :
    ∀ s ∈ Icc (0 : ℝ) r, 0 < denominator C s :=
  fun s hs => hY.2.2.1 s ⟨hs.1, hs.2.trans hr⟩

theorem IsBranchRoot.arcTime_continuousOn (hd : 0 < d) (hY : IsBranchRoot d C Y) :
    ContinuousOn (arcTime d C) (Icc 0 Y) :=
  fun r hr => (hasDerivAt_arcTime (d := d) hr.1 (hY.physical_below hr.2)).continuousAt.continuousWithinAt

theorem IsBranchRoot.arcTime_strictAntiOn (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    StrictAntiOn (arcTime d C) (Icc 0 Y) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 Y) (hY.arcTime_continuousOn hd)
  intro r hr
  have hr' : r ∈ Icc 0 Y := interior_subset hr
  rw [(hasDerivAt_arcTime (d := d) hr'.1 (hY.physical_below hr'.2)).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (arcTime_pos hd hC r))
    (hY.2.2.1 r hr')

theorem IsBranchRoot.lineEnd_lt_capStart (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    lineEnd C Y < capStart d C := by
  rw [← hY.arcTime_Y hd, ← arcTime_zero d C]
  exact hY.arcTime_strictAntiOn hd hC ⟨le_rfl, hY.1.le⟩ ⟨hY.1.le, le_rfl⟩ hY.1

theorem IsBranchRoot.arcTime_mem (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {r : ℝ} (hr : r ∈ Icc 0 Y) : arcTime d C r ∈ Icc (lineEnd C Y) (capStart d C) := by
  have hanti := hY.arcTime_strictAntiOn hd hC
  constructor
  · rw [← hY.arcTime_Y hd]
    exact hanti.antitoneOn hr ⟨hY.1.le, le_rfl⟩ hr.2
  · rw [← arcTime_zero d C]
    exact hanti.antitoneOn ⟨le_rfl, hY.1.le⟩ hr hr.1

theorem IsBranchRoot.arcTime_surjOn (hd : 0 < d) (hY : IsBranchRoot d C Y) :
    SurjOn (arcTime d C) (Icc 0 Y) (Icc (lineEnd C Y) (capStart d C)) := by
  intro a ha
  have h := intermediate_value_Icc' hY.1.le (hY.arcTime_continuousOn hd)
  rw [arcTime_zero, hY.arcTime_Y hd] at h
  exact h ha

theorem IsBranchRoot.clamp_mem (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) (a : ℝ) :
    max (lineEnd C Y) (min a (capStart d C)) ∈ Icc (lineEnd C Y) (capStart d C) :=
  ⟨le_max_left _ _, max_le (hY.lineEnd_lt_capStart hd hC).le (min_le_right _ _)⟩

theorem IsBranchRoot.arcParam_mem (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) (a : ℝ) :
    arcParam d C Y a ∈ Icc 0 Y :=
  invFunOn_mem (hY.arcTime_surjOn hd (hY.clamp_mem hd hC a))

theorem IsBranchRoot.arcTime_arcParam (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Icc (lineEnd C Y) (capStart d C)) :
    arcTime d C (arcParam d C Y a) = a := by
  have hclamp : max (lineEnd C Y) (min a (capStart d C)) = a := by
    rw [min_eq_left ha.2, max_eq_right ha.1]
  unfold arcParam
  rw [hclamp]
  exact invFunOn_eq (hY.arcTime_surjOn hd ha)

theorem IsBranchRoot.arcParam_arcTime (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {r : ℝ} (hr : r ∈ Icc 0 Y) : arcParam d C Y (arcTime d C r) = r := by
  have hmem := hY.arcTime_mem hd hC hr
  have hclamp : max (lineEnd C Y) (min (arcTime d C r) (capStart d C)) = arcTime d C r := by
    rw [min_eq_left hmem.2, max_eq_right hmem.1]
  unfold arcParam
  rw [hclamp]
  exact (hY.arcTime_strictAntiOn hd hC).injOn.leftInvOn_invFunOn hr

theorem IsBranchRoot.arcParam_lineEnd (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    arcParam d C Y (lineEnd C Y) = Y := by
  rw [← hY.arcTime_Y hd]
  exact hY.arcParam_arcTime hd hC ⟨hY.1.le, le_rfl⟩

theorem IsBranchRoot.arcParam_capStart (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    arcParam d C Y (capStart d C) = 0 := by
  rw [← arcTime_zero d C]
  exact hY.arcParam_arcTime hd hC ⟨le_rfl, hY.1.le⟩

/-- The slope of the middle-arc clock is bounded away from zero. -/
theorem IsBranchRoot.arcTime_slope_le (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {r : ℝ} (hr : r ∈ Icc 0 Y) :
    -(arcTime d C r) / denominator C r ≤ -(lineEnd C Y / (1 + C * Y ^ 2)) := by
  have hDpos := hY.2.2.1 r hr
  have hDle : denominator C r ≤ 1 + C * Y ^ 2 := by
    unfold denominator
    have : C * r ^ 2 ≤ C * Y ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1 hr.2 2) hC.le
    linarith [hr.1]
  have hge : lineEnd C Y ≤ arcTime d C r := (hY.arcTime_mem hd hC hr).1
  have hpos : 0 < 1 + C * Y ^ 2 := by positivity
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ hDpos]
  calc lineEnd C Y / (1 + C * Y ^ 2) * denominator C r
      ≤ lineEnd C Y / (1 + C * Y ^ 2) * (1 + C * Y ^ 2) :=
        mul_le_mul_of_nonneg_left hDle (div_nonneg (hY.lineEnd_pos hC).le hpos.le)
    _ = lineEnd C Y := by field_simp
    _ ≤ arcTime d C r := hge

theorem IsBranchRoot.arcTime_sub_ge (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {r s : ℝ} (hr : r ∈ Icc 0 Y) (hs : s ∈ Icc 0 Y) (hrs : r ≤ s) :
    lineEnd C Y / (1 + C * Y ^ 2) * (s - r) ≤ arcTime d C r - arcTime d C s := by
  have hder : ∀ t ∈ Icc (0 : ℝ) Y,
      HasDerivAt (arcTime d C) (-(arcTime d C t) / denominator C t) t :=
    fun t ht => hasDerivAt_arcTime ht.1 (hY.physical_below ht.2)
  have hmvt := (convex_Icc 0 Y).image_sub_le_mul_sub_of_deriv_le (hY.arcTime_continuousOn hd)
    (fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (C := -(lineEnd C Y / (1 + C * Y ^ 2))) (fun t ht => by
      rw [(hder t (interior_subset ht)).deriv]
      exact hY.arcTime_slope_le hd hC (interior_subset ht)) r hr s hs hrs
  linarith

/-- The inverse of the middle-arc clock is Lipschitz. -/
theorem IsBranchRoot.arcParam_lipschitzOn (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    LipschitzOnWith (Real.toNNReal ((1 + C * Y ^ 2) / lineEnd C Y)) (arcParam d C Y)
      (Icc (lineEnd C Y) (capStart d C)) := by
  apply LipschitzOnWith.of_dist_le'
  intro a ha b hb
  set m : ℝ := lineEnd C Y / (1 + C * Y ^ 2) with hm_def
  have hm : 0 < m := div_pos (hY.lineEnd_pos hC) (by positivity)
  have hminv : (1 + C * Y ^ 2) / lineEnd C Y = 1 / m := by
    rw [hm_def, one_div_div]
  rw [hminv]
  have hra := hY.arcParam_mem hd hC a
  have hrb := hY.arcParam_mem hd hC b
  have hta := hY.arcTime_arcParam hd hC ha
  have htb := hY.arcTime_arcParam hd hC hb
  -- |a - b| ≥ m |arcParam a - arcParam b|
  have key : m * |arcParam d C Y a - arcParam d C Y b| ≤ |a - b| := by
    rcases le_total (arcParam d C Y a) (arcParam d C Y b) with hle | hle
    · have h := hY.arcTime_sub_ge hd hC hra hrb hle
      rw [hta, htb] at h
      have hprod : 0 ≤ m * (arcParam d C Y b - arcParam d C Y a) :=
        mul_nonneg hm.le (sub_nonneg.mpr hle)
      rw [abs_of_nonpos (sub_nonpos.mpr hle), abs_of_nonneg (by linarith)]
      linarith
    · have h := hY.arcTime_sub_ge hd hC hrb hra hle
      rw [hta, htb] at h
      have hprod : 0 ≤ m * (arcParam d C Y a - arcParam d C Y b) :=
        mul_nonneg hm.le (sub_nonneg.mpr hle)
      rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonpos (by linarith)]
      linarith
  rw [Real.dist_eq, Real.dist_eq]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm]
  linarith [key]

theorem IsBranchRoot.arcParam_continuousOn (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    ContinuousOn (arcParam d C Y) (Icc (lineEnd C Y) (capStart d C)) :=
  (hY.arcParam_lipschitzOn hd hC).continuousOn

theorem IsBranchRoot.hasDerivAt_arcParam (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo (lineEnd C Y) (capStart d C)) :
    HasDerivAt (arcParam d C Y) (-(denominator C (arcParam d C Y a)) / a) a := by
  have ha' : a ∈ Icc (lineEnd C Y) (capStart d C) := Ioo_subset_Icc_self ha
  have hr := hY.arcParam_mem hd hC a
  have hcont : ContinuousAt (arcParam d C Y) a :=
    (hY.arcParam_continuousOn hd hC).continuousAt (Icc_mem_nhds ha.1 ha.2)
  have hder := hasDerivAt_arcTime (d := d) hr.1 (hY.physical_below hr.2)
  rw [hY.arcTime_arcParam hd hC ha'] at hder
  have hapos : 0 < a := (hY.lineEnd_pos hC).trans ha.1
  have hDpos := hY.2.2.1 _ hr
  have hne : -a / denominator C (arcParam d C Y a) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (ne_of_gt hapos)) (ne_of_gt hDpos)
  have hfg : ∀ᶠ b in 𝓝 a, arcTime d C (arcParam d C Y b) = b := by
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with b hb
    exact hY.arcTime_arcParam hd hC (Ioo_subset_Icc_self hb)
  have h := hder.of_local_left_inverse hcont hne hfg
  convert h using 1
  rw [inv_div]
  ring

/-- `x + a_e = Y / D`, the value of the reference curve at the first join. -/
theorem IsBranchRoot.refLog_lineEnd_eq (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    Real.log (lineIntercept C Y + lineEnd C Y) = arcLog d C (arcParam d C Y (lineEnd C Y)) := by
  rw [hY.arcParam_lineEnd hd hC, hY.arcLog_Y, hY.lineIntercept_add_lineEnd]

theorem refLog_of_le_lineEnd {a : ℝ} (ha : a ≤ lineEnd C Y) :
    refLog d C Y a = Real.log (lineIntercept C Y + a) := if_pos ha

theorem refLog_of_mem_arc {a : ℝ} (ha : lineEnd C Y < a) (ha' : a ≤ capStart d C) :
    refLog d C Y a = arcLog d C (arcParam d C Y a) := by
  unfold refLog
  rw [if_neg (not_le.mpr ha), if_pos ha']

theorem refLog_of_capStart_lt {a : ℝ} (haE : lineEnd C Y < a) (ha : capStart d C < a) :
    refLog d C Y a = -Real.log d := by
  unfold refLog
  rw [if_neg (not_le.mpr haE), if_neg (not_le.mpr ha)]

theorem IsBranchRoot.refLog_zero (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    refLog d C Y 0 = Real.log (lineIntercept C Y) := by
  rw [refLog_of_le_lineEnd (hY.lineEnd_pos hC).le, add_zero]

theorem IsBranchRoot.refLog_of_capStart_le (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : capStart d C ≤ a) : refLog d C Y a = -Real.log d := by
  have hlt := hY.lineEnd_lt_capStart hd hC
  rcases eq_or_lt_of_le ha with heq | hgt
  · rw [← heq, refLog_of_mem_arc hlt le_rfl, hY.arcParam_capStart hd hC, arcLog_zero]
  · exact refLog_of_capStart_lt (hlt.trans hgt) hgt

theorem IsBranchRoot.refLog_eqOn_arc (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    EqOn (refLog d C Y) (fun a => arcLog d C (arcParam d C Y a))
      (Icc (lineEnd C Y) (capStart d C)) := by
  intro a ha
  rcases eq_or_lt_of_le ha.1 with heq | hlt
  · rw [← heq, refLog_of_le_lineEnd le_rfl]
    exact hY.refLog_lineEnd_eq hd hC
  · exact refLog_of_mem_arc hlt ha.2

theorem refWeight_of_le_lineEnd {a : ℝ} (ha : a ≤ lineEnd C Y) :
    refWeight d C Y a = a / (lineIntercept C Y + a) := if_pos ha

theorem refWeight_of_mem_arc {a : ℝ} (ha : lineEnd C Y < a) (ha' : a ≤ capStart d C) :
    refWeight d C Y a = C * arcParam d C Y a := by
  unfold refWeight
  rw [if_neg (not_le.mpr ha), if_pos ha']

theorem refWeight_of_capStart_lt {a : ℝ} (haE : lineEnd C Y < a) (ha : capStart d C < a) :
    refWeight d C Y a = 0 := by
  unfold refWeight
  rw [if_neg (not_le.mpr haE), if_neg (not_le.mpr ha)]

theorem IsBranchRoot.refWeight_lineEnd_eq (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    lineEnd C Y / (lineIntercept C Y + lineEnd C Y) = C * arcParam d C Y (lineEnd C Y) := by
  rw [hY.arcParam_lineEnd hd hC, hY.lineIntercept_add_lineEnd]
  have hD := ne_of_gt hY.denominator_pos'
  have hY0 := ne_of_gt hY.1
  unfold lineEnd
  field_simp
  try ring

theorem IsBranchRoot.refWeight_eqOn_arc (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    EqOn (refWeight d C Y) (fun a => C * arcParam d C Y a)
      (Icc (lineEnd C Y) (capStart d C)) := by
  intro a ha
  rcases eq_or_lt_of_le ha.1 with heq | hlt
  · rw [← heq, refWeight_of_le_lineEnd le_rfl]
    exact hY.refWeight_lineEnd_eq hd hC
  · exact refWeight_of_mem_arc hlt ha.2

theorem IsBranchRoot.refWeight_of_capStart_le (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : capStart d C ≤ a) : refWeight d C Y a = 0 := by
  have hlt := hY.lineEnd_lt_capStart hd hC
  rcases eq_or_lt_of_le ha with heq | hgt
  · rw [← heq, refWeight_of_mem_arc hlt le_rfl, hY.arcParam_capStart hd hC, mul_zero]
  · exact refWeight_of_capStart_lt (hlt.trans hgt) hgt

/-! ### Derivatives at interior points of the three pieces -/

theorem IsBranchRoot.hasDerivAt_refLog_line (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo 0 (lineEnd C Y)) :
    HasDerivAt (refLog d C Y) (lineIntercept C Y + a)⁻¹ a := by
  have hx := hY.lineIntercept_pos
  have hne : lineIntercept C Y + a ≠ 0 := ne_of_gt (by linarith [ha.1])
  have h := ((hasDerivAt_id a).const_add (lineIntercept C Y)).log hne
  have h' : HasDerivAt (fun b => Real.log (lineIntercept C Y + b))
      (lineIntercept C Y + a)⁻¹ a := by
    refine h.congr_deriv ?_
    simp
  refine h'.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds ha.2] with b hb
  exact refLog_of_le_lineEnd (le_of_lt hb)

theorem IsBranchRoot.hasDerivAt_refLog_arc (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo (lineEnd C Y) (capStart d C)) :
    HasDerivAt (refLog d C Y) (C * arcParam d C Y a / a) a := by
  have hr := hY.arcParam_mem hd hC a
  have h1 := hasDerivAt_arcLog (d := d) hr.1 (hY.physical_below hr.2)
  have h2 := hY.hasDerivAt_arcParam hd hC ha
  have h := h1.comp a h2
  have hapos : 0 < a := (hY.lineEnd_pos hC).trans ha.1
  have hDpos := hY.2.2.1 _ hr
  have h' : HasDerivAt (fun b => arcLog d C (arcParam d C Y b)) (C * arcParam d C Y a / a) a := by
    refine h.congr_deriv ?_
    field_simp
    try ring
  refine h'.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ha.1 ha.2] with b hb
  exact refLog_of_mem_arc hb.1 hb.2.le

theorem IsBranchRoot.hasDerivAt_refLog_cap (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : capStart d C < a) : HasDerivAt (refLog d C Y) 0 a := by
  refine (hasDerivAt_const a (-Real.log d)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact hY.refLog_of_capStart_le hd hC (le_of_lt hb)

theorem IsBranchRoot.hasDerivAt_refWeight_line (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo 0 (lineEnd C Y)) :
    HasDerivAt (refWeight d C Y) (lineIntercept C Y / (lineIntercept C Y + a) ^ 2) a := by
  have hx := hY.lineIntercept_pos
  have hne : lineIntercept C Y + a ≠ 0 := ne_of_gt (by linarith [ha.1])
  have h := (hasDerivAt_id a).div ((hasDerivAt_id a).const_add (lineIntercept C Y)) hne
  have h' : HasDerivAt (fun b => b / (lineIntercept C Y + b))
      (lineIntercept C Y / (lineIntercept C Y + a) ^ 2) a := by
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  refine h'.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds ha.2] with b hb
  exact refWeight_of_le_lineEnd (le_of_lt hb)

theorem IsBranchRoot.hasDerivAt_refWeight_arc (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo (lineEnd C Y) (capStart d C)) :
    HasDerivAt (refWeight d C Y) (C * (-(denominator C (arcParam d C Y a)) / a)) a := by
  have h := (hY.hasDerivAt_arcParam hd hC ha).const_mul C
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ha.1 ha.2] with b hb
  exact refWeight_of_mem_arc hb.1 hb.2.le

theorem IsBranchRoot.hasDerivAt_refWeight_cap (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : capStart d C < a) : HasDerivAt (refWeight d C Y) 0 a := by
  refine (hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact hY.refWeight_of_capStart_le hd hC (le_of_lt hb)

/-! ### The multiplier `Q_x = e^{-2ℓ} + (a ℓ')'` on the three pieces -/

theorem IsBranchRoot.contact_line (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo 0 (lineEnd C Y)) :
    Real.exp (-2 * refLog d C Y a) + deriv (refWeight d C Y) a =
      (1 + lineIntercept C Y) / (lineIntercept C Y + a) ^ 2 := by
  have hx := hY.lineIntercept_pos
  have hpos : 0 < lineIntercept C Y + a := by linarith [ha.1]
  rw [(hY.hasDerivAt_refWeight_line ha).deriv, refLog_of_le_lineEnd ha.2.le]
  rw [show -2 * Real.log (lineIntercept C Y + a) = Real.log ((lineIntercept C Y + a) ^ 2)⁻¹ by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring]
  rw [Real.exp_log (inv_pos.mpr (pow_pos hpos 2))]
  field_simp
  try ring

theorem IsBranchRoot.contact_arc (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo (lineEnd C Y) (capStart d C)) :
    Real.exp (-2 * refLog d C Y a) + deriv (refWeight d C Y) a = 0 := by
  have hr := hY.arcParam_mem hd hC a
  have hDpos := hY.2.2.1 _ hr
  have hapos : 0 < a := (hY.lineEnd_pos hC).trans ha.1
  rw [(hY.hasDerivAt_refWeight_arc hd hC ha).deriv, refLog_of_mem_arc ha.1 ha.2.le]
  set r := arcParam d C Y a with hr_def
  have hta : arcTime d C r = a := hY.arcTime_arcParam hd hC (Ioo_subset_Icc_self ha)
  -- exp(-2 arcLog r) = d^2 * D r * exp (primitive r)
  have hexp : Real.exp (-2 * arcLog d C r) =
      d ^ 2 * denominator C r * Real.exp (primitive C r) := by
    unfold arcLog
    rw [show -2 * (-Real.log d - (Real.log (denominator C r) + primitive C r) / 2) =
        Real.log (d ^ 2) + Real.log (denominator C r) + primitive C r by
      rw [Real.log_pow]; push_cast; ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (pow_pos hd 2), Real.exp_log hDpos]
  rw [hexp]
  unfold arcTime at hta
  rw [Real.exp_neg] at hta
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hd)
  have hE : Real.exp (primitive C r) ≠ 0 := Real.exp_ne_zero _
  have hane : a ≠ 0 := ne_of_gt hapos
  rw [← hta]
  field_simp
  ring

theorem IsBranchRoot.contact_cap (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : capStart d C < a) :
    Real.exp (-2 * refLog d C Y a) + deriv (refWeight d C Y) a = d ^ 2 := by
  rw [(hY.hasDerivAt_refWeight_cap hd hC ha).deriv, hY.refLog_of_capStart_le hd hC ha.le]
  rw [show -2 * -Real.log d = Real.log (d ^ 2) by rw [Real.log_pow]; push_cast; ring]
  rw [Real.exp_log (pow_pos hd 2), add_zero]

end BranchPoint

end FixedPrice
