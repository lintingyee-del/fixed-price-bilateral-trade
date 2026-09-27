import FixedPrice.Controls
import FixedPrice.Extremal

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

def switchTime (C : ℝ) : ℝ := C * (1 + endParameter C)

theorem switchTime_bounds {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    C < switchTime C ∧ switchTime C < 1 := by
  have hp : 0 < C := by linarith [hC.1]
  have hq : 0 < 1 - C := by linarith [hC.2]
  have he : 0 < endParameter C :=
    div_pos (by linarith [hC.2]) (mul_pos hp hq)
  have hid : 1 - switchTime C = C ^ 2 / (1 - C) := by
    unfold switchTime endParameter
    field_simp
    ring
  constructor
  · dsimp [switchTime]
    nlinarith
  · have := div_pos (sq_pos_of_pos hp) hq
    linarith

theorem middleState_zero (d C : ℝ) : middleState d C 0 = d := by
  simp [middleState, denominator, primitive]

theorem hasDerivAt_middleState_time {d C : ℝ} (hC : 1 / 4 < C) (t : ℝ) :
    HasDerivAt (fun u => middleState d C (u / C - 1))
      (middleControl d C (t / C - 1)) t := by
  have hp : C ≠ 0 := ne_of_gt (by linarith : 0 < C)
  convert (hasDerivAt_middleState (d := d) hC (t / C - 1)).comp t
    (((hasDerivAt_id t).div_const C).sub_const 1) using 1
  simp only [middleControl]
  field_simp

theorem maximizingControl_on_middle {d C : ℝ}
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc C (switchTime C)) :
    maximizingControl d C t = middleControl d C (t / C - 1) := by
  have hp : C ≠ 0 := ne_of_gt (by linarith [hC.1] : 0 < C)
  rcases ht.1.eq_or_lt with heq | hlt
  · subst t
    simp [maximizingControl, hp, middleControl_zero]
  · simp only [maximizingControl, not_le.mpr hlt, if_false,
      if_pos (show t ≤ C * (1 + endParameter C) from ht.2), middleControl]

theorem state_maximizingControl_zero {d C : ℝ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) C) : state d (maximizingControl d C) t = d := by
  unfold state
  suffices (∫ u in (0 : ℝ)..t, maximizingControl d C u) = 0 by simp [this]
  calc
    _ = ∫ _ in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) t := by simpa [uIcc_of_le ht.1] using hu
      simp [maximizingControl, hu'.2.trans ht.2]
    _ = 0 := by simp

theorem state_maximizingControl_middle {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d)
    {t : ℝ} (ht : t ∈ Icc C (switchTime C)) :
    state d (maximizingControl d C) t = middleState d C (t / C - 1) := by
  have hp : 0 < C := by linarith [hC.1]
  have hb := switchTime_bounds hC
  have hi := control_intervalIntegrable
    (maximizingControl_measurable hC.1).aestronglyMeasurable
    (fun u _ => maximizingControl_mem_Icc hd hC hinit u)
  have hti : t ∈ Icc (0 : ℝ) 1 := ⟨hp.le.trans ht.1, ht.2.trans hb.2.le⟩
  have hCi : C ∈ Icc (0 : ℝ) 1 := ⟨hp.le, (hb.1.trans hb.2).le⟩
  have hint : (∫ u in C..t, maximizingControl d C u) =
      middleState d C (t / C - 1) - d := by
    calc
      _ = ∫ u in C..t, middleControl d C (u / C - 1) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Icc C t := by simpa [uIcc_of_le ht.1] using hu
        exact maximizingControl_on_middle hC ⟨hu'.1, hu'.2.trans ht.2⟩
      _ = _ := by
        have hc : Continuous (fun u : ℝ => middleControl d C (u / C - 1)) :=
          (continuous_middleControl hC.1).comp ((continuous_id.div_const C).sub continuous_const)
        simpa [div_self (ne_of_gt hp), middleState_zero] using
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun u _ => hasDerivAt_middleState_time (d := d) hC.1 u)
            (hc.intervalIntegrable C t)
  have hsub := state_sub_eq_integral (d := d) hi hCi hti
  rw [hint, state_maximizingControl_zero ⟨hp.le, le_rfl⟩] at hsub
  linarith

theorem maximizingControl_on_one {d C : ℝ}
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d)
    {t : ℝ} (ht : switchTime C ≤ t) : maximizingControl d C t = 1 := by
  have hp : 0 < C := by linarith [hC.1]
  have hc : C < t := (switchTime_bounds hC).1.trans_le ht
  rcases ht.eq_or_lt with heq | hlt
  · subst t
    rw [maximizingControl_on_middle hC ⟨(switchTime_bounds hC).1.le, le_rfl⟩]
    have hy : switchTime C / C - 1 = endParameter C := by
      unfold switchTime
      field_simp
      ring
    rw [hy, middleControl_endParameter hC hinit]
  · change C * (1 + endParameter C) < t at hlt
    simp [maximizingControl, not_le.mpr hc, not_le.mpr hlt]

theorem state_maximizingControl_one {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d)
    {t : ℝ} (ht : t ∈ Icc (switchTime C) 1) :
    state d (maximizingControl d C) t = middleState d C (endParameter C) + t - switchTime C := by
  have hp : 0 < C := by linarith [hC.1]
  have hb := switchTime_bounds hC
  have hi := control_intervalIntegrable
    (maximizingControl_measurable hC.1).aestronglyMeasurable
    (fun u _ => maximizingControl_mem_Icc hd hC hinit u)
  have hTi : switchTime C ∈ Icc (0 : ℝ) 1 := ⟨(hp.trans hb.1).le, hb.2.le⟩
  have hti : t ∈ Icc (0 : ℝ) 1 := ⟨hTi.1.trans ht.1, ht.2⟩
  have hsub := state_sub_eq_integral (d := d) hi hTi hti
  have hint : (∫ u in switchTime C..t, maximizingControl d C u) = t - switchTime C := by
    calc
      _ = ∫ _ in switchTime C..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Icc (switchTime C) t := by simpa [uIcc_of_le ht.1] using hu
        exact maximizingControl_on_one hC hinit hu'.1
      _ = _ := by simp
  rw [hint, state_maximizingControl_middle hd hC hinit ⟨hb.1.le, le_rfl⟩] at hsub
  have hy : switchTime C / C - 1 = endParameter C := by
    unfold switchTime
    field_simp
    ring
  rw [hy] at hsub
  linarith

theorem middleState_endParameter {d C : ℝ}
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    middleState d C (endParameter C) = C ^ 3 / ((1 - C) * (1 - 2 * C)) := by
  have hp : C ≠ 0 := ne_of_gt (by linarith [hC.1] : 0 < C)
  have hq : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2] : 0 < 1 - C)
  have hr : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2] : 0 < 1 - 2 * C)
  have hh := middleControl_endParameter hC hinit
  rw [middleControl, denominator_endParameter hp hq, endParameter] at hh
  dsimp [endParameter]
  field_simp [hp, hq, hr] at hh ⊢
  nlinarith [hh]

theorem state_maximizingControl_end {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    state d (maximizingControl d C) 1 = C ^ 2 / (1 - 2 * C) := by
  have hp : C ≠ 0 := ne_of_gt (by linarith [hC.1] : 0 < C)
  have hq : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2] : 0 < 1 - C)
  have hr : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2] : 0 < 1 - 2 * C)
  rw [state_maximizingControl_one hd hC hinit ⟨(switchTime_bounds hC).2.le, le_rfl⟩,
    middleState_endParameter hC hinit]
  unfold switchTime endParameter
  field_simp [hp, hq, hr]
  field_simp [(show 1 - C * 2 ≠ 0 by nlinarith [hC.2])]
  ring

theorem tailTime_maximizingControl_one {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d)
    {t : ℝ} (ht : t ∈ Icc (switchTime C) 1) :
    tailTime d (maximizingControl d C) t =
      (middleState d C (endParameter C) + t - switchTime C)⁻¹ -
      (middleState d C (endParameter C) + 1 - switchTime C)⁻¹ := by
  have hp : 0 < C := by linarith [hC.1]
  have hb := switchTime_bounds hC
  have hti : t ∈ Icc (0 : ℝ) 1 := ⟨(hp.trans hb.1).le.trans ht.1, ht.2⟩
  have hi := control_intervalIntegrable
    (maximizingControl_measurable hC.1).aestronglyMeasurable
    (fun u _ => maximizingControl_mem_Icc hd hC hinit u)
  have hc := inv_state_sq_continuousOn hd hi
    (fun u _ => maximizingControl_mem_Icc hd hC hinit u)
  have hinv := (hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one).mono_set
    (show uIcc t 1 ⊆ uIcc (0 : ℝ) 1 by
      rw [uIcc_of_le zero_le_one]
      exact uIcc_subset_Icc hti ⟨zero_le_one, le_rfl⟩)
  have heq : ∀ u ∈ uIcc t 1,
      state d (maximizingControl d C) u = middleState d C (endParameter C) + u - switchTime C := by
    intro u hu
    have hu' : u ∈ Icc t 1 := by simpa [uIcc_of_le ht.2] using hu
    exact state_maximizingControl_one hd hC hinit ⟨ht.1.trans hu'.1, hu'.2⟩
  have hder : ∀ u ∈ uIcc t 1,
      HasDerivAt (fun s => -(middleState d C (endParameter C) + s - switchTime C)⁻¹)
        ((state d (maximizingControl d C) u ^ 2)⁻¹) u := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      have hsub := uIcc_subset_Icc hti (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hu
      exact hsub
    have hn : middleState d C (endParameter C) + u - switchTime C ≠ 0 := by
      rw [← heq u hu]
      exact ne_of_gt (hd.trans_le (state_bounds
        (fun s _ => maximizingControl_mem_Icc hd hC hinit s) hu').1)
    convert ((((hasDerivAt_id u).const_add (middleState d C (endParameter C))).sub_const
      (switchTime C)).inv hn).neg using 1
    rw [heq u hu]
    simp [div_eq_mul_inv]
  simpa [tailTime, sub_eq_add_neg, add_comm] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder hinv

def middleTail (d C y : ℝ) : ℝ := C * denominator C y / middleState d C y ^ 2

theorem hasDerivAt_middleTail_time {d C : ℝ} (hd : 0 < d) (hC : 1 / 4 < C) (t : ℝ) :
    HasDerivAt (fun u => middleTail d C (u / C - 1))
      (-(middleState d C (t / C - 1) ^ 2)⁻¹) t := by
  have hp : C ≠ 0 := ne_of_gt (by linarith : 0 < C)
  have hg := ne_of_gt (middleState_pos hd hC (t / C - 1))
  have hD := ne_of_gt (denominator_pos hC (t / C - 1))
  have hy := ((hasDerivAt_id t).div_const C).sub_const 1
  have hnum := ((hasDerivAt_denominator C (t / C - 1)).comp t hy).const_mul C
  have hden := (hasDerivAt_middleState_time (d := d) hC t).pow 2
  convert hnum.div hden (pow_ne_zero 2 hg) using 1
  simp only [middleControl, id_eq, Function.comp_apply, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  generalize t / C - 1 = y at hg hD ⊢
  field_simp [hp, hg, hD]
  ring

theorem middleTail_at_switch {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    tailTime d (maximizingControl d C) (switchTime C) = middleTail d C (endParameter C) := by
  have hp : C ≠ 0 := ne_of_gt (by linarith [hC.1] : 0 < C)
  have hq : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2] : 0 < 1 - C)
  have hr : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2] : 0 < 1 - 2 * C)
  rw [tailTime_maximizingControl_one hd hC hinit ⟨le_rfl, (switchTime_bounds hC).2.le⟩]
  rw [← state_maximizingControl_one hd hC hinit ⟨(switchTime_bounds hC).2.le, le_rfl⟩,
    state_maximizingControl_end hd hC hinit]
  simp only [add_sub_cancel_right, middleTail, middleState_endParameter hC hinit,
    denominator_endParameter hp hq]
  field_simp [hp, hq, hr]
  ring

theorem tailTime_maximizingControl_middle {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d)
    {t : ℝ} (ht : t ∈ Icc C (switchTime C)) :
    tailTime d (maximizingControl d C) t = middleTail d C (t / C - 1) := by
  have hp : 0 < C := by linarith [hC.1]
  have hb := switchTime_bounds hC
  have hti : t ∈ Icc (0 : ℝ) 1 := ⟨hp.le.trans ht.1, ht.2.trans hb.2.le⟩
  have hTi : switchTime C ∈ Icc (0 : ℝ) 1 := ⟨(hp.trans hb.1).le, hb.2.le⟩
  have hi := control_intervalIntegrable
    (maximizingControl_measurable hC.1).aestronglyMeasurable
    (fun u _ => maximizingControl_mem_Icc hd hC hinit u)
  have hc := inv_state_sq_continuousOn hd hi
    (fun u _ => maximizingControl_mem_Icc hd hC hinit u)
  have hinv := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hi1 := control_intervalIntegrable_subinterval hinv hti hTi
  have hi2 := control_intervalIntegrable_subinterval hinv hTi (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hs := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hder : ∀ u ∈ uIcc t (switchTime C),
      HasDerivAt (fun s => -middleTail d C (s / C - 1))
        ((state d (maximizingControl d C) u ^ 2)⁻¹) u := by
    intro u hu
    have hu' : u ∈ Icc t (switchTime C) := by simpa [uIcc_of_le ht.2] using hu
    rw [state_maximizingControl_middle hd hC hinit ⟨ht.1.trans hu'.1, hu'.2⟩]
    simpa only [neg_neg] using (hasDerivAt_middleTail_time hd hC.1 u).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi1
  have hy : switchTime C / C - 1 = endParameter C := by
    unfold switchTime
    field_simp
    ring
  rw [hy] at hftc
  change (∫ u in t..switchTime C, (state d (maximizingControl d C) u ^ 2)⁻¹) +
    tailTime d (maximizingControl d C) (switchTime C) =
    tailTime d (maximizingControl d C) t at hs
  rw [hftc, middleTail_at_switch hd hC hinit] at hs
  linarith

theorem tailTime_maximizingControl_zero {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    tailTime d (maximizingControl d C) 0 = 2 * C / d ^ 2 := by
  have hp : 0 < C := by linarith [hC.1]
  have hCi : C ∈ Icc (0 : ℝ) 1 := ⟨hp.le, by linarith [hC.2]⟩
  have hi := control_intervalIntegrable
    (maximizingControl_measurable hC.1).aestronglyMeasurable
    (fun u _ => maximizingControl_mem_Icc hd hC hinit u)
  have hc := inv_state_sq_continuousOn hd hi
    (fun u _ => maximizingControl_mem_Icc hd hC hinit u)
  have hinv := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hi1 := control_intervalIntegrable_subinterval hinv (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hCi
  have hi2 := control_intervalIntegrable_subinterval hinv hCi (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hs := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hint : (∫ u in (0 : ℝ)..C, (state d (maximizingControl d C) u ^ 2)⁻¹) = C / d ^ 2 := by
    calc
      _ = ∫ _ in (0 : ℝ)..C, (d ^ 2)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp only
        rw [state_maximizingControl_zero (by simpa [uIcc_of_le hp.le] using hu)]
      _ = _ := by simp [div_eq_mul_inv]
  change _ + tailTime d (maximizingControl d C) C = tailTime d (maximizingControl d C) 0 at hs
  rw [hint, tailTime_maximizingControl_middle hd hC hinit ⟨le_rfl, (switchTime_bounds hC).1.le⟩] at hs
  simp [div_self (ne_of_gt hp), middleTail, denominator, middleState_zero] at hs
  rw [← hs]
  ring

def middleCostPrimitive (C y : ℝ) : ℝ :=
  C * y - C * primitive C y + (Real.log (denominator C y) + primitive C y) / 2

theorem hasDerivAt_middleCostPrimitive_time {C : ℝ} (hC : 1 / 4 < C) (t : ℝ) :
    HasDerivAt (fun u => middleCostPrimitive C (u / C - 1))
      (C * (t / C - 1) ^ 2 / denominator C (t / C - 1)) t := by
  have hp : C ≠ 0 := ne_of_gt (by linarith : 0 < C)
  have hD := ne_of_gt (denominator_pos hC (t / C - 1))
  have hy := ((hasDerivAt_id t).div_const C).sub_const 1
  have hprim := (hasDerivAt_primitive hC (t / C - 1)).comp t hy
  have hlog := ((hasDerivAt_denominator C (t / C - 1)).log hD).comp t hy
  convert ((hy.const_mul C).sub (hprim.const_mul C)).add ((hlog.add hprim).div_const 2) using 1
  generalize t / C - 1 = y at hD ⊢
  field_simp [hp, hD]
  unfold denominator
  ring

theorem maximizingCost_intervalIntegrable {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    IntervalIntegrable (fun t => tailTime d (maximizingControl d C) t * maximizingControl d C t ^ 2)
      volume 0 1 := by
  have hm := (maximizingControl_measurable (d := d) hC.1).aestronglyMeasurable
    (μ := volume.restrict (Icc 0 1))
  have hb := fun t (_ : t ∈ Icc (0 : ℝ) 1) => maximizingControl_mem_Icc hd hC hinit t
  have hi := control_intervalIntegrable hm hb
  have hinv := (inv_state_sq_continuousOn hd hi hb).intervalIntegrable_of_Icc
    (μ := volume) zero_le_one
  exact (control_sq_intervalIntegrable hm hb).continuousOn_mul
    (tailTime_absolutelyContinuous hinv).continuousOn

theorem maximizingCost_integral_middle {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    (∫ t in C..switchTime C,
      tailTime d (maximizingControl d C) t * maximizingControl d C t ^ 2) =
      middleCostPrimitive C (endParameter C) := by
  have hp : 0 < C := by linarith [hC.1]
  have hb := switchTime_bounds hC
  have hi := control_intervalIntegrable_subinterval (maximizingCost_intervalIntegrable hd hC hinit)
    (show C ∈ Icc (0 : ℝ) 1 from ⟨hp.le, (hb.1.trans hb.2).le⟩)
    (show switchTime C ∈ Icc (0 : ℝ) 1 from ⟨(hp.trans hb.1).le, hb.2.le⟩)
  have heq : ∀ t ∈ uIcc C (switchTime C),
      tailTime d (maximizingControl d C) t * maximizingControl d C t ^ 2 =
        C * (t / C - 1) ^ 2 / denominator C (t / C - 1) := by
    intro t ht
    have ht' : t ∈ Icc C (switchTime C) := by simpa [uIcc_of_le hb.1.le] using ht
    rw [tailTime_maximizingControl_middle hd hC hinit ht', maximizingControl_on_middle hC ht']
    unfold middleTail middleControl
    have hg := ne_of_gt (middleState_pos hd hC.1 (t / C - 1))
    have hD := ne_of_gt (denominator_pos hC.1 (t / C - 1))
    generalize t / C - 1 = y at hg hD ⊢
    field_simp [hg, hD]
  have hder : ∀ t ∈ uIcc C (switchTime C),
      HasDerivAt (fun u => middleCostPrimitive C (u / C - 1))
        (tailTime d (maximizingControl d C) t * maximizingControl d C t ^ 2) t := by
    intro t ht
    rw [heq t ht]
    exact hasDerivAt_middleCostPrimitive_time hC.1 t
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi
  have hy : switchTime C / C - 1 = endParameter C := by
    unfold switchTime
    field_simp
    ring
  simpa [hy, div_self (ne_of_gt hp), middleCostPrimitive, primitive, denominator] using hftc

theorem maximizingCost_integral_one {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    (∫ t in switchTime C..1,
      tailTime d (maximizingControl d C) t * maximizingControl d C t ^ 2) =
      Real.log (state d (maximizingControl d C) 1) -
      Real.log (middleState d C (endParameter C)) -
      (1 - switchTime C) / state d (maximizingControl d C) 1 := by
  have hp : 0 < C := by linarith [hC.1]
  have hb := switchTime_bounds hC
  have hTi : switchTime C ∈ Icc (0 : ℝ) 1 := ⟨(hp.trans hb.1).le, hb.2.le⟩
  have hi := control_intervalIntegrable_subinterval (maximizingCost_intervalIntegrable hd hC hinit)
    hTi (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have he : middleState d C (endParameter C) + 1 - switchTime C =
      state d (maximizingControl d C) 1 :=
    (state_maximizingControl_one hd hC hinit ⟨hb.2.le, le_rfl⟩).symm
  have hder : ∀ t ∈ uIcc (switchTime C) 1,
      HasDerivAt (fun u => Real.log (middleState d C (endParameter C) + u - switchTime C) -
        u / state d (maximizingControl d C) 1)
        (tailTime d (maximizingControl d C) t * maximizingControl d C t ^ 2) t := by
    intro t ht
    have ht' : t ∈ Icc (switchTime C) 1 := by simpa [uIcc_of_le hb.2.le] using ht
    have hn : middleState d C (endParameter C) + t - switchTime C ≠ 0 :=
      ne_of_gt (by linarith [middleState_pos hd hC.1 (endParameter C), ht'.1])
    rw [tailTime_maximizingControl_one hd hC hinit ht', maximizingControl_on_one hC hinit ht'.1, he]
    convert ((((hasDerivAt_id t).const_add (middleState d C (endParameter C))).sub_const
      (switchTime C)).log hn).sub ((hasDerivAt_id t).div_const (state d (maximizingControl d C) 1)) using 1
    simp
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi
  rw [he, add_sub_cancel_right] at hftc
  rw [hftc]
  ring

theorem maximizingCost_integral {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    (∫ t in (0 : ℝ)..1,
      tailTime d (maximizingControl d C) t * maximizingControl d C t ^ 2) =
      middleCostPrimitive C (endParameter C) +
      Real.log (state d (maximizingControl d C) 1) -
      Real.log (middleState d C (endParameter C)) -
      (1 - switchTime C) / state d (maximizingControl d C) 1 := by
  have hp : 0 < C := by linarith [hC.1]
  have hb := switchTime_bounds hC
  have hCi : C ∈ Icc (0 : ℝ) 1 := ⟨hp.le, (hb.1.trans hb.2).le⟩
  have hTi : switchTime C ∈ Icc (0 : ℝ) 1 := ⟨(hp.trans hb.1).le, hb.2.le⟩
  have hi := maximizingCost_intervalIntegrable hd hC hinit
  have hi1 := control_intervalIntegrable_subinterval hi (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hCi
  have hi2 := control_intervalIntegrable_subinterval hi hCi hTi
  have hi3 := control_intervalIntegrable_subinterval hi hTi (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hzero : (∫ t in (0 : ℝ)..C,
      tailTime d (maximizingControl d C) t * maximizingControl d C t ^ 2) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..C, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) C := by simpa [uIcc_of_le hp.le] using ht
        simp [maximizingControl, ht'.2]
      _ = _ := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 (hi2.trans hi3),
    ← intervalIntegral.integral_add_adjacent_intervals hi2 hi3,
    hzero, maximizingCost_integral_middle hd hC hinit, maximizingCost_integral_one hd hC hinit]
  ring

theorem log_middleState {d C : ℝ} (hd : 0 < d) (hC : 1 / 4 < C) (y : ℝ) :
    Real.log (middleState d C y) =
      Real.log d + (Real.log (denominator C y) + primitive C y) / 2 := by
  have hs := ne_of_gt (Real.sqrt_pos.mpr (denominator_pos hC y))
  unfold middleState
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hd) hs) (Real.exp_ne_zero _),
    Real.log_mul (ne_of_gt hd) hs, Real.log_exp, Real.log_sqrt (denominator_pos hC y).le]
  ring

/-- The explicit control of equation (31) attains the value in equation (30). -/
theorem maximizingControl_attains {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    objective d (maximizingControl d C) = optimalValue C := by
  have hp : C ≠ 0 := ne_of_gt (by linarith [hC.1] : 0 < C)
  have hq : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2] : 0 < 1 - C)
  have hr : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2] : 0 < 1 - 2 * C)
  rw [objective_originalTime_identity hd
    (maximizingControl_measurable hC.1).aestronglyMeasurable
    (fun t _ => maximizingControl_mem_Icc hd hC hinit t),
    tailTime_maximizingControl_zero hd hC hinit,
    maximizingCost_integral hd hC hinit, log_middleState hd hC.1,
    state_maximizingControl_end hd hC hinit]
  have hlen : (1 - switchTime C) / (C ^ 2 / (1 - 2 * C)) = C * endParameter C := by
    unfold switchTime endParameter
    field_simp [hp, hq, hr]
    field_simp [(show 1 - C * 2 ≠ 0 by nlinarith [hC.2])]
    ring
  rw [hlen]
  unfold middleCostPrimitive optimalValue
  field_simp [ne_of_gt hd]
  ring

end FixedPrice
