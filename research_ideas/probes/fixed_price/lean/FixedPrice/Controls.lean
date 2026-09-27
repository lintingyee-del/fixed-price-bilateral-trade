import FixedPrice.Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

theorem control_intervalIntegrable {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable h volume 0 1 := by
  have hi : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
  apply hi.mono_fun'
  · apply hmeas.mono_set
    simpa [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc ht
    simpa [Real.norm_eq_abs, abs_of_nonneg (hbox t ht').1] using (hbox t ht').2

theorem control_intervalIntegrable_subinterval {h : ℝ → ℝ}
    (hi : IntervalIntegrable h volume 0 1) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable h volume s t := by
  apply hi.mono_set
  rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact uIcc_subset_Icc hs ht

theorem state_sub_eq_integral {d : ℝ} {h : ℝ → ℝ}
    (hi : IntervalIntegrable h volume 0 1) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    state d h t - state d h s = ∫ u in s..t, h u := by
  unfold state
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (control_intervalIntegrable_subinterval hi ⟨le_rfl, zero_le_one⟩ ht)
    (control_intervalIntegrable_subinterval hi ⟨le_rfl, zero_le_one⟩ hs)

theorem state_lipschitzOn {d : ℝ} {h : ℝ → ℝ}
    (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    LipschitzOnWith 1 (state d h) (Icc 0 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro s hs t ht
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [state_sub_eq_integral hi ht hs]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := s) (C := (1 : ℝ)) (f := h) (fun u hu => by
      have hu' := uIcc_subset_Icc ht hs (uIoc_subset_uIcc hu)
      simpa [Real.norm_eq_abs, abs_of_nonneg (hbox u hu').1] using (hbox u hu').2)
  simpa only [Real.norm_eq_abs, one_mul] using hbound

theorem state_bounds {d : ℝ} {h : ℝ → ℝ}
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : d ≤ state d h t ∧ state d h t ≤ d + 1 := by
  have hnn : 0 ≤ ∫ u in 0..t, h u :=
    intervalIntegral.integral_nonneg ht.1 fun u hu => (hbox u ⟨hu.1, hu.2.trans ht.2⟩).1
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := (1 : ℝ)) (f := h) (fun u hu => by
      have hu' : u ∈ Icc (0 : ℝ) 1 :=
        uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ ht (uIoc_subset_uIcc hu)
      simpa [Real.norm_eq_abs, abs_of_nonneg (hbox u hu').1] using (hbox u hu').2)
  simp only [Real.norm_eq_abs, abs_of_nonneg hnn, sub_zero, abs_of_nonneg ht.1, one_mul] at hbound
  unfold state
  constructor <;> linarith [ht.2]

theorem state_absolutelyContinuous {d : ℝ} {h : ℝ → ℝ}
    (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (state d h) 0 1 := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 1)
  simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using state_lipschitzOn (d := d) hi hbox

theorem state_ae_hasDerivAt {d : ℝ} {h : ℝ → ℝ}
    (hi : IntervalIntegrable h volume 0 1) :
    ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → HasDerivAt (state d h) (h t) t := by
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
  have hmem' : t ∈ uIcc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using hmem
  simpa only [zero_add] using (ht hmem' 0 (by simp)).const_add d

theorem log_state_absolutelyContinuous {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (fun t => Real.log (state d h t)) 0 1 := by
  let K : NNReal := ⟨d⁻¹, le_of_lt (inv_pos.mpr hd)⟩
  have hlog : LipschitzOnWith K Real.log (Ici d) := by
    apply (convex_Ici d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun x : ℝ => x⁻¹)
    · intro x hx
      exact (Real.hasDerivAt_log (ne_of_gt (hd.trans_le hx))).hasDerivWithinAt
    · intro x hx
      change ‖x⁻¹‖ ≤ d⁻¹
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hd.trans_le hx))]
      exact inv_anti₀ hd hx
  have hg := hlog.comp (state_lipschitzOn (d := d) hi hbox)
    (fun t ht => (state_bounds hbox ht).1)
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := K * 1)
  simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num), Function.comp_def] using hg

theorem integral_control_div_state {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, h t / state d h t) = Real.log (state d h 1) - Real.log d := by
  have hg := log_state_absolutelyContinuous hd hi hbox
  calc
    _ = ∫ t in (0 : ℝ)..1, deriv (fun u => Real.log (state d h u)) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [state_ae_hasDerivAt (d := d) hi] with t ht hmem
      have hmem' : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc hmem
      exact ((ht hmem').log (ne_of_gt (hd.trans_le (state_bounds hbox hmem').1))).deriv.symm
    _ = _ := by simpa [state] using hg.integral_deriv_eq_sub

def tailTime (d : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in t..1, (state d h u ^ 2)⁻¹

theorem tailTime_eq_neg_integral (d : ℝ) (h : ℝ → ℝ) :
    tailTime d h = -(fun t => ∫ u in (1 : ℝ)..t, (state d h u ^ 2)⁻¹) := by
  funext t
  exact intervalIntegral.integral_symm 1 t

theorem control_sq_intervalIntegrable {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => h t ^ 2) volume 0 1 := by
  apply control_intervalIntegrable (hmeas.pow 2)
  intro t ht
  exact ⟨sq_nonneg _, (pow_le_one₀ (hbox t ht).1 (hbox t ht).2)⟩

theorem secondMoment_absolutelyContinuous {h : ℝ → ℝ}
    (hi : IntervalIntegrable (fun t => h t ^ 2) volume 0 1) :
    AbsolutelyContinuousOnInterval (secondMoment h) 0 1 :=
  hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)

theorem secondMoment_ae_hasDerivAt {h : ℝ → ℝ}
    (hi : IntervalIntegrable (fun t => h t ^ 2) volume 0 1) :
    ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → HasDerivAt (secondMoment h) (h t ^ 2) t := by
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
  exact ht (by simpa [uIcc_of_le zero_le_one] using hmem) 0 (by simp)

theorem inv_state_sq_continuousOn {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun t => (state d h t ^ 2)⁻¹) (Icc 0 1) := by
  apply ((state_lipschitzOn hi hbox).continuousOn.pow 2).inv₀
  intro t ht
  exact pow_ne_zero _ (ne_of_gt (hd.trans_le (state_bounds hbox ht).1))

theorem tailTime_absolutelyContinuous {d : ℝ} {h : ℝ → ℝ}
    (hi : IntervalIntegrable (fun t => (state d h t ^ 2)⁻¹) volume 0 1) :
    AbsolutelyContinuousOnInterval (tailTime d h) 0 1 := by
  have ha := (hi.absolutelyContinuousOnInterval_intervalIntegral (c := 1) (by simp)).neg
  rw [tailTime_eq_neg_integral]
  exact ha

theorem tailTime_ae_hasDerivAt {d : ℝ} {h : ℝ → ℝ}
    (hi : IntervalIntegrable (fun t => (state d h t ^ 2)⁻¹) volume 0 1) :
    ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (tailTime d h) (-(state d h t ^ 2)⁻¹) t := by
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
  have hmem' : t ∈ uIcc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using hmem
  rw [tailTime_eq_neg_integral]
  exact (ht hmem' 1 (by simp)).neg

theorem integral_secondMoment_div_state_sq {d : ℝ} {h : ℝ → ℝ}
    (hsq : IntervalIntegrable (fun t => h t ^ 2) volume 0 1)
    (hinv : IntervalIntegrable (fun t => (state d h t ^ 2)⁻¹) volume 0 1) :
    (∫ t in (0 : ℝ)..1, secondMoment h t / state d h t ^ 2) =
      ∫ t in (0 : ℝ)..1, tailTime d h t * h t ^ 2 := by
  have hk := secondMoment_absolutelyContinuous hsq
  have ha := tailTime_absolutelyContinuous hinv
  have hibp := ha.integral_mul_deriv_eq_deriv_mul hk
  have hleft : (∫ t in (0 : ℝ)..1, tailTime d h t * deriv (secondMoment h) t) =
      ∫ t in (0 : ℝ)..1, tailTime d h t * h t ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [secondMoment_ae_hasDerivAt hsq] with t ht hmem
    have hmem' : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc hmem
    rw [(ht hmem').deriv]
  have hright : (∫ t in (0 : ℝ)..1, deriv (tailTime d h) t * secondMoment h t) =
      -(∫ t in (0 : ℝ)..1, secondMoment h t / state d h t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [tailTime_ae_hasDerivAt hinv] with t ht hmem
    have hmem' : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using uIoc_subset_uIcc hmem
    rw [(ht hmem').deriv]
    simp [div_eq_mul_inv, mul_comm]
  rw [hleft, hright] at hibp
  simpa [tailTime, secondMoment] using hibp.symm

/-- The original-time identity in Lemma 5.1, before reciprocal-time substitution. -/
theorem objective_originalTime_identity {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    objective d h = Real.log (state d h 1) - Real.log d +
      d ^ 2 * tailTime d h 0 - ∫ t in (0 : ℝ)..1, tailTime d h t * h t ^ 2 := by
  have hi := control_intervalIntegrable hmeas hbox
  have hsq := control_sq_intervalIntegrable hmeas hbox
  have hginv := inv_state_sq_continuousOn hd hi hbox
  have hginv' : ContinuousOn (fun t => (state d h t ^ 2)⁻¹) (uIcc 0 1) := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hginv
  have hinv := hginv'.intervalIntegrable (μ := volume)
  have hk := (secondMoment_absolutelyContinuous hsq).continuousOn
  have hki : IntervalIntegrable
      (fun t => secondMoment h t * (state d h t ^ 2)⁻¹) volume 0 1 :=
    (hk.mul hginv').intervalIntegrable (μ := volume)
  have hlogi : IntervalIntegrable (fun t => h t / state d h t) volume 0 1 := by
    simp only [div_eq_mul_inv]
    apply hi.mul_continuousOn
    apply (state_absolutelyContinuous hi hbox).continuousOn.inv₀
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    exact ne_of_gt (hd.trans_le (state_bounds hbox ht').1)
  have hdi := hinv.const_mul (d ^ 2)
  have hsplit : objective d h =
      (∫ t in (0 : ℝ)..1, h t / state d h t) +
      d ^ 2 * tailTime d h 0 -
      ∫ t in (0 : ℝ)..1, secondMoment h t / state d h t ^ 2 := by
    unfold objective
    simp_rw [sub_div, div_eq_mul_inv]
    rw [intervalIntegral.integral_add (by simpa only [div_eq_mul_inv] using hlogi)
      (hdi.sub hki), intervalIntegral.integral_sub hdi hki,
      intervalIntegral.integral_const_mul]
    simp only [tailTime]
    ring
  rw [hsplit, integral_control_div_state hd hi hbox,
    integral_secondMoment_div_state_sq hsq hinv]

end FixedPrice
