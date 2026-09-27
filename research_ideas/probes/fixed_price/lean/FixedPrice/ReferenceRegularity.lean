import FixedPrice.ReferenceCurve
import FixedPrice.CalibrationAE

/-! Regularity of the reference curve: `ℓ_x` and its weight are Lipschitz on `[0, R]`, hence
absolutely continuous; the weight equals `a ℓ_x'` almost everywhere; `a (ℓ_x')^2` is
integrable. These are the hypotheses of the weighted calibration. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology NNReal

namespace FixedPrice

theorem lipschitzOnWith_of_eqOn {f g : ℝ → ℝ} {K : ℝ≥0} {s : Set ℝ}
    (hg : LipschitzOnWith K g s) (h : EqOn f g s) : LipschitzOnWith K f s := by
  rw [lipschitzOnWith_iff_dist_le_mul] at hg ⊢
  intro x hx y hy
  rw [h hx, h hy]
  exact hg x hx y hy

/-- Lipschitz bounds on two adjacent closed intervals glue. -/
theorem lipschitzOnWith_Icc_glue {f : ℝ → ℝ} {K : ℝ≥0} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : LipschitzOnWith K f (Icc a b)) (h2 : LipschitzOnWith K f (Icc b c)) :
    LipschitzOnWith K f (Icc a c) := by
  rw [lipschitzOnWith_iff_dist_le_mul] at h1 h2 ⊢
  have key : ∀ x ∈ Icc a c, ∀ y ∈ Icc a c, x ≤ y → dist (f x) (f y) ≤ K * dist x y := by
    intro x hx y hy hxy
    by_cases hyb : y ≤ b
    · exact h1 x ⟨hx.1, hxy.trans hyb⟩ y ⟨hy.1, hyb⟩
    · by_cases hxb : b ≤ x
      · exact h2 x ⟨hxb, hx.2⟩ y ⟨hxb.trans hxy, hy.2⟩
      · push Not at hyb hxb
        have e1 := h1 x ⟨hx.1, hxb.le⟩ b ⟨hab, le_rfl⟩
        have e2 := h2 b ⟨le_rfl, hbc⟩ y ⟨hyb.le, hy.2⟩
        calc dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) := dist_triangle _ _ _
          _ ≤ K * dist x b + K * dist b y := add_le_add e1 e2
          _ = K * dist x y := by
              rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
                abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
              ring
  intro x hx y hy
  rcases le_total x y with hxy | hxy
  · exact key x hx y hy hxy
  · rw [dist_comm, dist_comm x y]
    exact key y hy x hx hxy

/-- A function with a bounded derivative on a closed interval is Lipschitz there. -/
theorem lipschitzOnWith_Icc_of_hasDerivAt {f f' : ℝ → ℝ} {a b M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hb : ∀ x ∈ Icc a b, |f' x| ≤ M) :
    LipschitzOnWith (Real.toNNReal M) f (Icc a b) := by
  apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := f')
    (fun x hx => (hf x hx).hasDerivWithinAt)
  intro x hx
  change ‖f' x‖ ≤ Real.toNNReal M
  rw [Real.norm_eq_abs, Real.coe_toNNReal M hM]
  exact hb x hx

section BranchPoint

variable {d C Y : ℝ}

theorem IsBranchRoot.line_lipschitzOn (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    LipschitzOnWith (Real.toNNReal (lineIntercept C Y)⁻¹)
      (fun a => Real.log (lineIntercept C Y + a)) (Icc 0 (lineEnd C Y)) := by
  have hx := hY.lineIntercept_pos
  apply lipschitzOnWith_Icc_of_hasDerivAt (f' := fun a => (lineIntercept C Y + a)⁻¹)
    (inv_pos.mpr hx).le
  · intro a ha
    have hne : lineIntercept C Y + a ≠ 0 := ne_of_gt (by linarith [ha.1])
    have h := ((hasDerivAt_id a).const_add (lineIntercept C Y)).log hne
    refine h.congr_deriv ?_
    simp
  · intro a ha
    rw [abs_of_pos (inv_pos.mpr (by linarith [ha.1]))]
    exact inv_anti₀ hx (by linarith [ha.1])

theorem IsBranchRoot.arcLog_lipschitzOn (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    ∃ K : ℝ≥0, LipschitzOnWith K (arcLog d C) (Icc 0 Y) := by
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hY.1.le)
    ((continuous_denominator C).continuousOn (s := Icc 0 Y))
  have hDmin : 0 < denominator C r₀ := hY.2.2.1 r₀ hr₀
  refine ⟨Real.toNNReal (C * Y / denominator C r₀), ?_⟩
  apply lipschitzOnWith_Icc_of_hasDerivAt (f' := fun r => -(C * r) / denominator C r)
    (div_nonneg (mul_nonneg hC.le hY.1.le) hDmin.le)
  · intro r hr
    exact hasDerivAt_arcLog (d := d) hr.1 (hY.physical_below hr.2)
  · intro r hr
    have hDr := hY.2.2.1 r hr
    rw [abs_div, abs_neg, abs_of_nonneg (mul_nonneg hC.le hr.1), abs_of_pos hDr]
    calc C * r / denominator C r ≤ C * Y / denominator C r :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr.2 hC.le) hDr.le
      _ ≤ C * Y / denominator C r₀ :=
          div_le_div_of_nonneg_left (mul_nonneg hC.le hY.1.le) hDmin (isMinOn_iff.mp hmin r hr)

/-- `ℓ_x` is Lipschitz on `[0, R]` for every `R ≥ a_a`. -/
theorem IsBranchRoot.refLog_lipschitzOn (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {R : ℝ} (hR : capStart d C ≤ R) :
    ∃ K : ℝ≥0, LipschitzOnWith K (refLog d C Y) (Icc 0 R) := by
  obtain ⟨K₂, hK₂⟩ := hY.arcLog_lipschitzOn hd hC
  set K₁ : ℝ≥0 := Real.toNNReal (lineIntercept C Y)⁻¹
  set K₃ : ℝ≥0 := Real.toNNReal ((1 + C * Y ^ 2) / lineEnd C Y)
  refine ⟨K₁ + K₂ * K₃, ?_⟩
  have hE := hY.lineEnd_pos hC
  have hEA := hY.lineEnd_lt_capStart hd hC
  -- the three pieces
  have p1 : LipschitzOnWith (K₁ + K₂ * K₃) (refLog d C Y) (Icc 0 (lineEnd C Y)) := by
    apply lipschitzOnWith_of_eqOn ((hY.line_lipschitzOn hC).weaken le_self_add)
    intro a ha
    exact refLog_of_le_lineEnd ha.2
  have p2 : LipschitzOnWith (K₁ + K₂ * K₃) (refLog d C Y)
      (Icc (lineEnd C Y) (capStart d C)) := by
    have hcomp := hK₂.comp (hY.arcParam_lipschitzOn hd hC)
      (fun a _ => hY.arcParam_mem hd hC a)
    apply lipschitzOnWith_of_eqOn (hcomp.weaken le_add_self)
    exact hY.refLog_eqOn_arc hd hC
  have p3 : LipschitzOnWith (K₁ + K₂ * K₃) (refLog d C Y) (Icc (capStart d C) R) := by
    apply lipschitzOnWith_of_eqOn ((LipschitzWith.const' (-Real.log d)).lipschitzOnWith)
    intro a ha
    exact hY.refLog_of_capStart_le hd hC ha.1
  exact lipschitzOnWith_Icc_glue (capStart_pos hd hC).le hR
    (lipschitzOnWith_Icc_glue hE.le hEA.le p1 p2) p3

theorem IsBranchRoot.lineWeight_lipschitzOn (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    LipschitzOnWith (Real.toNNReal (lineIntercept C Y)⁻¹)
      (fun a => a / (lineIntercept C Y + a)) (Icc 0 (lineEnd C Y)) := by
  have hx := hY.lineIntercept_pos
  apply lipschitzOnWith_Icc_of_hasDerivAt
    (f' := fun a => lineIntercept C Y / (lineIntercept C Y + a) ^ 2) (inv_pos.mpr hx).le
  · intro a ha
    have hne : lineIntercept C Y + a ≠ 0 := ne_of_gt (by linarith [ha.1])
    have h := (hasDerivAt_id a).div ((hasDerivAt_id a).const_add (lineIntercept C Y)) hne
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  · intro a ha
    have hpos : 0 < lineIntercept C Y + a := by linarith [ha.1]
    rw [abs_of_pos (div_pos hx (pow_pos hpos 2))]
    rw [div_le_iff₀ (pow_pos hpos 2)]
    calc lineIntercept C Y = (lineIntercept C Y)⁻¹ * lineIntercept C Y ^ 2 := by
          field_simp
      _ ≤ (lineIntercept C Y)⁻¹ * (lineIntercept C Y + a) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hx).le
          exact pow_le_pow_left₀ hx.le (by linarith [ha.1]) 2

theorem IsBranchRoot.arcWeight_lipschitzOn (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y) :
    LipschitzOnWith (Real.toNNReal (C * ((1 + C * Y ^ 2) / lineEnd C Y)))
      (fun a => C * arcParam d C Y a) (Icc (lineEnd C Y) (capStart d C)) := by
  have h := hY.arcParam_lipschitzOn hd hC
  rw [lipschitzOnWith_iff_dist_le_mul] at h ⊢
  intro a ha b hb
  have hK : 0 ≤ (1 + C * Y ^ 2) / lineEnd C Y := div_nonneg (by positivity) (hY.lineEnd_pos hC).le
  rw [Real.coe_toNNReal _ (mul_nonneg hC.le hK)]
  rw [Real.coe_toNNReal _ hK] at h
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hC, ← Real.dist_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h a ha b hb) hC.le

theorem IsBranchRoot.refWeight_lipschitzOn (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {R : ℝ} (hR : capStart d C ≤ R) :
    ∃ K : ℝ≥0, LipschitzOnWith K (refWeight d C Y) (Icc 0 R) := by
  set K₁ : ℝ≥0 := Real.toNNReal (lineIntercept C Y)⁻¹
  set K₂ : ℝ≥0 := Real.toNNReal (C * ((1 + C * Y ^ 2) / lineEnd C Y))
  refine ⟨K₁ + K₂, ?_⟩
  have hE := hY.lineEnd_pos hC
  have hEA := hY.lineEnd_lt_capStart hd hC
  have p1 : LipschitzOnWith (K₁ + K₂) (refWeight d C Y) (Icc 0 (lineEnd C Y)) := by
    apply lipschitzOnWith_of_eqOn ((hY.lineWeight_lipschitzOn hC).weaken le_self_add)
    intro a ha
    exact refWeight_of_le_lineEnd ha.2
  have p2 : LipschitzOnWith (K₁ + K₂) (refWeight d C Y) (Icc (lineEnd C Y) (capStart d C)) := by
    apply lipschitzOnWith_of_eqOn ((hY.arcWeight_lipschitzOn hd hC).weaken le_add_self)
    exact hY.refWeight_eqOn_arc hd hC
  have p3 : LipschitzOnWith (K₁ + K₂) (refWeight d C Y) (Icc (capStart d C) R) := by
    apply lipschitzOnWith_of_eqOn ((LipschitzWith.const' (0 : ℝ)).lipschitzOnWith)
    intro a ha
    exact hY.refWeight_of_capStart_le hd hC ha.1
  exact lipschitzOnWith_Icc_glue (capStart_pos hd hC).le hR
    (lipschitzOnWith_Icc_glue hE.le hEA.le p1 p2) p3

theorem IsBranchRoot.refLog_absolutelyContinuous (hd : 0 < d) (hC : 0 < C)
    (hY : IsBranchRoot d C Y) {R : ℝ} (hR : capStart d C ≤ R) :
    AbsolutelyContinuousOnInterval (refLog d C Y) 0 R := by
  obtain ⟨K, hK⟩ := hY.refLog_lipschitzOn hd hC hR
  have hR0 : (0 : ℝ) ≤ R := (capStart_pos hd hC).le.trans hR
  rw [← uIcc_of_le hR0] at hK
  exact hK.absolutelyContinuousOnInterval

theorem IsBranchRoot.refWeight_absolutelyContinuous (hd : 0 < d) (hC : 0 < C)
    (hY : IsBranchRoot d C Y) {R : ℝ} (hR : capStart d C ≤ R) :
    AbsolutelyContinuousOnInterval (refWeight d C Y) 0 R := by
  obtain ⟨K, hK⟩ := hY.refWeight_lipschitzOn hd hC hR
  have hR0 : (0 : ℝ) ≤ R := (capStart_pos hd hC).le.trans hR
  rw [← uIcc_of_le hR0] at hK
  exact hK.absolutelyContinuousOnInterval

/-- The weight is `a ℓ_x'` away from the two joins. -/
theorem IsBranchRoot.refWeight_ae_eq (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {R : ℝ} (hR : capStart d C ≤ R) :
    ∀ᵐ a, a ∈ Ι (0 : ℝ) R → refWeight d C Y a = a * deriv (refLog d C Y) a := by
  have hR0 : (0 : ℝ) ≤ R := (capStart_pos hd hC).le.trans hR
  filter_upwards [volume.ae_ne (lineEnd C Y), volume.ae_ne (capStart d C)] with a h1 h2 ha
  have ha' : a ∈ Ioc (0 : ℝ) R := by rwa [uIoc_of_le hR0] at ha
  rcases lt_trichotomy a (lineEnd C Y) with hlt | heq | hgt
  · rw [refWeight_of_le_lineEnd hlt.le, (hY.hasDerivAt_refLog_line ⟨ha'.1, hlt⟩).deriv]
    have hne : lineIntercept C Y + a ≠ 0 := ne_of_gt (by linarith [hY.lineIntercept_pos, ha'.1])
    field_simp
  · exact absurd heq h1
  · rcases lt_trichotomy a (capStart d C) with hlt' | heq' | hgt'
    · rw [refWeight_of_mem_arc hgt hlt'.le, (hY.hasDerivAt_refLog_arc hd hC ⟨hgt, hlt'⟩).deriv]
      have hne : a ≠ 0 := ne_of_gt ha'.1
      field_simp
    · exact absurd heq' h2
    · rw [refWeight_of_capStart_lt hgt hgt', (hY.hasDerivAt_refLog_cap hd hC hgt').deriv]
      ring

/-- The weighted squared slope of the reference curve is bounded, hence integrable. -/
theorem IsBranchRoot.refLog_weighted_deriv_intervalIntegrable (hd : 0 < d) (hC : 0 < C)
    (hY : IsBranchRoot d C Y) {R : ℝ} (hR : capStart d C ≤ R) :
    IntervalIntegrable (fun a => a * (deriv (refLog d C Y) a) ^ 2) volume 0 R := by
  have hR0 : (0 : ℝ) ≤ R := (capStart_pos hd hC).le.trans hR
  have hx := hY.lineIntercept_pos
  have hE := hY.lineEnd_pos hC
  set M : ℝ := (lineIntercept C Y)⁻¹ + C ^ 2 * Y ^ 2 / lineEnd C Y with hM_def
  have hM1 : (lineIntercept C Y)⁻¹ ≤ M := by
    have : 0 ≤ C ^ 2 * Y ^ 2 / lineEnd C Y := by positivity
    linarith
  have hM2 : C ^ 2 * Y ^ 2 / lineEnd C Y ≤ M := by
    have : 0 ≤ (lineIntercept C Y)⁻¹ := (inv_pos.mpr hx).le
    linarith
  have hM0 : 0 ≤ M := (inv_pos.mpr hx).le.trans hM1
  rw [intervalIntegrable_iff, uIoc_of_le hR0]
  apply Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
  · exact (measurable_id.mul ((measurable_deriv (refLog d C Y)).pow_const 2)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [volume.ae_ne (lineEnd C Y), volume.ae_ne (capStart d C)] with a h1 h2 ha
    rw [Real.norm_eq_abs]
    rcases lt_trichotomy a (lineEnd C Y) with hlt | heq | hgt
    · rw [(hY.hasDerivAt_refLog_line ⟨ha.1, hlt⟩).deriv]
      have hpos : 0 < lineIntercept C Y + a := by linarith [ha.1]
      have hval : a * ((lineIntercept C Y + a)⁻¹) ^ 2 = a / (lineIntercept C Y + a) ^ 2 := by
        field_simp
      rw [hval, abs_of_nonneg (div_nonneg ha.1.le (pow_pos hpos 2).le)]
      refine le_trans ?_ hM1
      rw [div_le_iff₀ (pow_pos hpos 2)]
      calc a = (lineIntercept C Y)⁻¹ * (lineIntercept C Y * a) := by field_simp
        _ ≤ (lineIntercept C Y)⁻¹ * (lineIntercept C Y + a) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hx).le
            nlinarith [sq_nonneg (lineIntercept C Y + a), sq_nonneg a, hx, ha.1]
    · exact absurd heq h1
    · rcases lt_trichotomy a (capStart d C) with hlt' | heq' | hgt'
      · rw [(hY.hasDerivAt_refLog_arc hd hC ⟨hgt, hlt'⟩).deriv]
        have hr := hY.arcParam_mem hd hC a
        have hapos : 0 < a := hE.trans hgt
        have hval : a * (C * arcParam d C Y a / a) ^ 2 = C ^ 2 * (arcParam d C Y a) ^ 2 / a := by
          field_simp
          try ring
        rw [hval, abs_of_nonneg (by positivity)]
        refine le_trans ?_ hM2
        calc C ^ 2 * (arcParam d C Y a) ^ 2 / a ≤ C ^ 2 * Y ^ 2 / a := by
              apply div_le_div_of_nonneg_right _ hapos.le
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1 hr.2 2) (sq_nonneg C)
          _ ≤ C ^ 2 * Y ^ 2 / lineEnd C Y :=
              div_le_div_of_nonneg_left (by positivity) hE hgt.le
      · exact absurd heq' h2
      · rw [(hY.hasDerivAt_refLog_cap hd hC hgt').deriv]
        simp [hM0]

end BranchPoint

end FixedPrice
