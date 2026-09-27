import FixedPrice.Controls

/-! The finite-tail perturbation estimate (B2) of Proposition 13.1: lifting a control `h`
to `η + (1 - η) h` moves the objective by at most `η L_err(d)`,
`L_err(d) = 3/d + 3/d² + 2/d³`. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

/-- The constant `L_err(d)` of Proposition 13.1. -/
def perturbConst (d : ℝ) : ℝ := 3 / d + 3 / d ^ 2 + 2 / d ^ 3

/-- The lifted control `η + (1 - η) h`. -/
def liftControl (η : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ := η + (1 - η) * h t

theorem liftControl_mem {η : ℝ} (hη : η ∈ Icc (0 : ℝ) 1) {h : ℝ → ℝ}
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, liftControl η h t ∈ Icc (0 : ℝ) 1 := by
  intro t ht
  have h0 := (hbox t ht).1
  have h1 := (hbox t ht).2
  unfold liftControl
  constructor <;> nlinarith [hη.1, hη.2]

theorem liftControl_aestronglyMeasurable {η : ℝ} {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1))) :
    AEStronglyMeasurable (liftControl η h) (volume.restrict (Icc 0 1)) :=
  aestronglyMeasurable_const.add (aestronglyMeasurable_const.mul hmeas)

/-- The pointwise comparison behind (B2). -/
theorem perturb_pointwise {d η a a' g g' k k' : ℝ} (hd : 0 < d)
    (ha : a ∈ Icc (0 : ℝ) 1) (haa : 0 ≤ a' - a ∧ a' - a ≤ η)
    (hg : d ≤ g) (hgg : 0 ≤ g' - g ∧ g' - g ≤ η)
    (hk : 0 ≤ k ∧ k ≤ 1) (hkk : 0 ≤ k' - k ∧ k' - k ≤ 2 * η) :
    |(a' / g' + (d ^ 2 - k') / g' ^ 2) - (a / g + (d ^ 2 - k) / g ^ 2)| ≤
      η * perturbConst d := by
  have hgpos : 0 < g := hd.trans_le hg
  have hg' : d ≤ g' := by linarith [hgg.1]
  have hg'pos : 0 < g' := hd.trans_le hg'
  have hη : 0 ≤ η := haa.1.trans haa.2
  have e1 : a' / g' - a / g = (a' - a) / g' - a * (g' - g) / (g * g') := by
    field_simp
    ring
  have e2 : (d ^ 2 - k') / g' ^ 2 - (d ^ 2 - k) / g ^ 2 =
      -((k' - k) / g' ^ 2) - (d ^ 2 - k) * ((g' - g) * (1 / (g ^ 2 * g') + 1 / (g * g' ^ 2))) := by
    field_simp
    ring
  -- first term
  have t1 : (a' - a) / g' ≤ η / d :=
    div_le_div₀ hη haa.2 hd hg'
  have t1' : 0 ≤ (a' - a) / g' := div_nonneg haa.1 hg'pos.le
  have hgg' : d * d ≤ g * g' := mul_le_mul hg hg' hd.le hgpos.le
  have t2 : a * (g' - g) / (g * g') ≤ η / d ^ 2 := by
    rw [sq]
    apply div_le_div₀ hη _ (mul_pos hd hd) hgg'
    nlinarith [ha.1, ha.2, hgg.1, hgg.2]
  have t2' : 0 ≤ a * (g' - g) / (g * g') :=
    div_nonneg (mul_nonneg ha.1 hgg.1) (mul_pos hgpos hg'pos).le
  -- second term
  have t3 : (k' - k) / g' ^ 2 ≤ 2 * η / d ^ 2 :=
    div_le_div₀ (by linarith) hkk.2 (pow_pos hd 2) (pow_le_pow_left₀ hd.le hg' 2)
  have t3' : 0 ≤ (k' - k) / g' ^ 2 := div_nonneg hkk.1 (pow_pos hg'pos 2).le
  have hinv1 : 1 / (g ^ 2 * g') ≤ 1 / d ^ 3 := by
    apply one_div_le_one_div_of_le (pow_pos hd 3)
    rw [show d ^ 3 = d ^ 2 * d by ring]
    exact mul_le_mul (pow_le_pow_left₀ hd.le hg 2) hg' hd.le (pow_pos hgpos 2).le
  have hinv2 : 1 / (g * g' ^ 2) ≤ 1 / d ^ 3 := by
    apply one_div_le_one_div_of_le (pow_pos hd 3)
    rw [show d ^ 3 = d * d ^ 2 by ring]
    exact mul_le_mul hg (pow_le_pow_left₀ hd.le hg' 2) (pow_pos hd 2).le hgpos.le
  have hW0 : 0 ≤ 1 / (g ^ 2 * g') + 1 / (g * g' ^ 2) := by positivity
  have hW : (g' - g) * (1 / (g ^ 2 * g') + 1 / (g * g' ^ 2)) ≤ η * (2 / d ^ 3) := by
    have := mul_le_mul hgg.2 (show 1 / (g ^ 2 * g') + 1 / (g * g' ^ 2) ≤ 2 / d ^ 3 by
      have : (2 : ℝ) / d ^ 3 = 1 / d ^ 3 + 1 / d ^ 3 := by ring
      linarith) hW0 hη
    linarith
  have hW' : 0 ≤ (g' - g) * (1 / (g ^ 2 * g') + 1 / (g * g' ^ 2)) := mul_nonneg hgg.1 hW0
  have hdk : |d ^ 2 - k| ≤ d ^ 2 + 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hk.1, hk.2, sq_nonneg d]
  have t4 : |(d ^ 2 - k) * ((g' - g) * (1 / (g ^ 2 * g') + 1 / (g * g' ^ 2)))| ≤
      (d ^ 2 + 1) * (η * (2 / d ^ 3)) := by
    rw [abs_mul, abs_of_nonneg hW']
    exact mul_le_mul hdk hW hW' (by positivity)
  have hsplit : (a' / g' + (d ^ 2 - k') / g' ^ 2) - (a / g + (d ^ 2 - k) / g ^ 2) =
      ((a' - a) / g' - a * (g' - g) / (g * g')) +
        (-((k' - k) / g' ^ 2) - (d ^ 2 - k) * ((g' - g) * (1 / (g ^ 2 * g') + 1 / (g * g' ^ 2)))) := by
    rw [← e1, ← e2]
    ring
  rw [hsplit]
  have hA : |(a' - a) / g' - a * (g' - g) / (g * g')| ≤ η / d + η / d ^ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hB : |-((k' - k) / g' ^ 2) - (d ^ 2 - k) * ((g' - g) * (1 / (g ^ 2 * g') + 1 / (g * g' ^ 2)))| ≤
      2 * η / d ^ 2 + (d ^ 2 + 1) * (η * (2 / d ^ 3)) := by
    calc _ ≤ |-((k' - k) / g' ^ 2)| +
          |(d ^ 2 - k) * ((g' - g) * (1 / (g ^ 2 * g') + 1 / (g * g' ^ 2)))| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_neg, abs_of_nonneg t3']
        linarith
  have hsum : η / d + η / d ^ 2 + (2 * η / d ^ 2 + (d ^ 2 + 1) * (η * (2 / d ^ 3))) =
      η * perturbConst d := by
    unfold perturbConst
    field_simp
    ring
  calc _ ≤ |(a' - a) / g' - a * (g' - g) / (g * g')| +
        |-((k' - k) / g' ^ 2) - (d ^ 2 - k) * ((g' - g) * (1 / (g ^ 2 * g') + 1 / (g * g' ^ 2)))| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

theorem objective_integrand_intervalIntegrable {d : ℝ} {h : ℝ → ℝ} (hd : 0 < d)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun t => h t / state d h t + (d ^ 2 - secondMoment h t) / state d h t ^ 2) volume 0 1 := by
  have hi := control_intervalIntegrable hmeas hbox
  have hsq := control_sq_intervalIntegrable hmeas hbox
  have hginv := inv_state_sq_continuousOn hd hi hbox
  have hginv' : ContinuousOn (fun t => (state d h t ^ 2)⁻¹) (uIcc 0 1) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hginv
  have hk := (secondMoment_absolutelyContinuous hsq).continuousOn
  have hsec : IntervalIntegrable
      (fun t => (d ^ 2 - secondMoment h t) * (state d h t ^ 2)⁻¹) volume 0 1 :=
    ((continuousOn_const.sub hk).mul hginv').intervalIntegrable (μ := volume)
  have hlogi : IntervalIntegrable (fun t => h t * (state d h t)⁻¹) volume 0 1 := by
    apply hi.mul_continuousOn
    apply (state_absolutelyContinuous hi hbox).continuousOn.inv₀
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    exact ne_of_gt (hd.trans_le (state_bounds hbox ht').1)
  simpa only [div_eq_mul_inv] using hlogi.add hsec

theorem secondMoment_bounds {h : ℝ → ℝ}
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ secondMoment h t ∧ secondMoment h t ≤ 1 := by
  unfold secondMoment
  constructor
  · exact intervalIntegral.integral_nonneg ht.1 fun u _ => sq_nonneg _
  · have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (C := (1 : ℝ)) (f := fun u => h u ^ 2) (fun u hu => by
        have hu' : u ∈ Icc (0 : ℝ) 1 :=
          uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ ht (uIoc_subset_uIcc hu)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ (hbox u hu').1 (hbox u hu').2)
    rw [sub_zero, abs_of_nonneg ht.1, one_mul] at hb
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hb) |>.trans ht.2

/-- **(B2)**: `|J_d(η + (1 - η) h) - J_d(h)| ≤ η L_err(d)`. -/
theorem objective_liftControl_sub_le {d η : ℝ} (hd : 0 < d) (hη : η ∈ Icc (0 : ℝ) 1)
    {h : ℝ → ℝ} (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    |objective d (liftControl η h) - objective d h| ≤ η * perturbConst d := by
  set h' := liftControl η h with hh'
  have hmeas' : AEStronglyMeasurable h' (volume.restrict (Icc 0 1)) :=
    liftControl_aestronglyMeasurable hmeas
  have hbox' := liftControl_mem hη hbox
  have hi := control_intervalIntegrable hmeas hbox
  have hi' := control_intervalIntegrable hmeas' hbox'
  have hsq := control_sq_intervalIntegrable hmeas hbox
  have hsq' := control_sq_intervalIntegrable hmeas' hbox'
  unfold objective
  rw [← intervalIntegral.integral_sub (objective_integrand_intervalIntegrable hd hmeas' hbox')
    (objective_integrand_intervalIntegrable hd hmeas hbox)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := η * perturbConst d)
    (f := fun t => (h' t / state d h' t + (d ^ 2 - secondMoment h' t) / state d h' t ^ 2) -
      (h t / state d h t + (d ^ 2 - secondMoment h t) / state d h t ^ 2)) (by
      intro t htm
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at htm
        exact ⟨htm.1.le, htm.2⟩
      have hsub := control_intervalIntegrable_subinterval hi ⟨le_rfl, zero_le_one⟩ ht
      have hsub' := control_intervalIntegrable_subinterval hi' ⟨le_rfl, zero_le_one⟩ ht
      have hsqs := control_intervalIntegrable_subinterval hsq ⟨le_rfl, zero_le_one⟩ ht
      have hsqs' := control_intervalIntegrable_subinterval hsq' ⟨le_rfl, zero_le_one⟩ ht
      have hg : state d h' t - state d h t = ∫ u in (0 : ℝ)..t, η * (1 - h u) := by
        unfold state
        rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hsub' hsub]
        apply intervalIntegral.integral_congr
        intro u _
        simp only [hh', liftControl]
        ring
      have hk : secondMoment h' t - secondMoment h t =
          ∫ u in (0 : ℝ)..t, η * (1 - h u) * (η + (2 - η) * h u) := by
        unfold secondMoment
        rw [← intervalIntegral.integral_sub hsqs' hsqs]
        apply intervalIntegral.integral_congr
        intro u _
        simp only [hh', liftControl]
        ring
      have hbu : ∀ u ∈ Icc (0 : ℝ) t, h u ∈ Icc (0 : ℝ) 1 :=
        fun u hu => hbox u ⟨hu.1, hu.2.trans ht.2⟩
      have hint1 : IntervalIntegrable (fun u => η * (1 - h u)) volume 0 t :=
        (IntervalIntegrable.sub intervalIntegrable_const hsub).const_mul η
      have hint2 : IntervalIntegrable (fun u => η * (1 - h u) * (η + (2 - η) * h u)) volume 0 t := by
        refine (((intervalIntegrable_const (c := η * η)).add
          (hsub.const_mul (η * (2 - η) - η * η))).sub
          (hsqs.const_mul (η * (2 - η)))).congr ?_
        intro u _
        ring
      have hgb : 0 ≤ state d h' t - state d h t ∧ state d h' t - state d h t ≤ η := by
        rw [hg]
        constructor
        · apply intervalIntegral.integral_nonneg ht.1
          intro u hu
          exact mul_nonneg hη.1 (by linarith [(hbu u hu).2])
        · calc (∫ u in (0 : ℝ)..t, η * (1 - h u)) ≤ ∫ _u in (0 : ℝ)..t, η :=
                intervalIntegral.integral_mono_on ht.1 hint1 intervalIntegrable_const
                  (fun u hu => by nlinarith [(hbu u hu).1, hη.1])
            _ = η * t := by simp [mul_comm]
            _ ≤ η := mul_le_of_le_one_right hη.1 ht.2
      have hkb : 0 ≤ secondMoment h' t - secondMoment h t ∧
          secondMoment h' t - secondMoment h t ≤ 2 * η := by
        rw [hk]
        constructor
        · apply intervalIntegral.integral_nonneg ht.1
          intro u hu
          have h0 := (hbu u hu).1
          have h1 := (hbu u hu).2
          have : 0 ≤ η + (2 - η) * h u := by nlinarith [hη.1, hη.2]
          exact mul_nonneg (mul_nonneg hη.1 (by linarith)) this
        · calc (∫ u in (0 : ℝ)..t, η * (1 - h u) * (η + (2 - η) * h u))
              ≤ ∫ _u in (0 : ℝ)..t, 2 * η :=
                intervalIntegral.integral_mono_on ht.1 hint2 intervalIntegrable_const
                  (fun u hu => by
                    have h0 := (hbu u hu).1
                    have h1 := (hbu u hu).2
                    have e : η + (2 - η) * h u ≤ 2 := by nlinarith [hη.1, hη.2]
                    have e0 : 0 ≤ η + (2 - η) * h u := by nlinarith [hη.1, hη.2]
                    have e1 : η * (1 - h u) ≤ η := by nlinarith [hη.1]
                    have e2 : 0 ≤ η * (1 - h u) := mul_nonneg hη.1 (by linarith)
                    nlinarith)
            _ = 2 * η * t := by simp; ring
            _ ≤ 2 * η := mul_le_of_le_one_right (by linarith [hη.1]) ht.2
      have haa : 0 ≤ h' t - h t ∧ h' t - h t ≤ η := by
        simp only [hh', liftControl]
        have h0 := (hbox t ht).1
        have h1 := (hbox t ht).2
        constructor <;> nlinarith [hη.1, hη.2]
      rw [Real.norm_eq_abs]
      exact perturb_pointwise hd (hbox t ht) haa (state_bounds hbox ht).1 hgb
        (secondMoment_bounds hbox ht) hkb)
  simpa only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] using hb

end FixedPrice
