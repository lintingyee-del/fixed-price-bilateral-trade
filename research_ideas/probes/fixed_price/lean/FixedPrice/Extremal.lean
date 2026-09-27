import FixedPrice.Envelope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open Set MeasureTheory
open scoped Interval Topology

namespace FixedPrice

theorem denominator_pos {C : ℝ} (hC : 1 / 4 < C) (y : ℝ) :
    0 < denominator C y := by
  have hCpos : 0 < C := by linarith
  have hsq := sq_nonneg (2 * C * y - 1)
  have hid : 4 * C * denominator C y = (2 * C * y - 1) ^ 2 + 4 * C - 1 := by
    unfold denominator
    ring
  nlinarith

theorem hasDerivAt_denominator (C y : ℝ) :
    HasDerivAt (denominator C) (2 * C * y - 1) y := by
  unfold denominator
  convert ((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
    (((hasDerivAt_id y).pow 2).const_mul C) using 1
  simp only [id_eq]
  ring

theorem continuous_denominator (C : ℝ) : Continuous (denominator C) :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_denominator C y).continuousAt

theorem hasDerivAt_primitive {C : ℝ} (hC : 1 / 4 < C) (y : ℝ) :
    HasDerivAt (primitive C) (denominator C y)⁻¹ y := by
  have hcont : Continuous (fun r => (denominator C r)⁻¹) :=
    (continuous_denominator C).inv₀ fun r => ne_of_gt (denominator_pos hC r)
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 y)
    (hcont.stronglyMeasurableAtFilter volume (𝓝 y)) hcont.continuousAt

theorem middleState_pos {d C : ℝ} (hd : 0 < d) (hC : 1 / 4 < C) (y : ℝ) :
    0 < middleState d C y := by
  exact mul_pos (mul_pos hd (Real.sqrt_pos.2 (denominator_pos hC y))) (Real.exp_pos _)

theorem hasDerivAt_middleState {d C : ℝ} (hC : 1 / 4 < C) (y : ℝ) :
    HasDerivAt (middleState d C) (C * y * middleState d C y / denominator C y) y := by
  have hD := ne_of_gt (denominator_pos hC y)
  have hsqrt := ne_of_gt (Real.sqrt_pos.2 (denominator_pos hC y))
  have hsqrtSq := Real.sq_sqrt (denominator_pos hC y).le
  have hg := (((hasDerivAt_denominator C y).sqrt hD).const_mul d).mul
    (((hasDerivAt_primitive hC y).div_const 2).exp)
  convert hg using 1
  unfold middleState
  field_simp
  rw [hsqrtSq]
  ring

def middleControl (d C y : ℝ) : ℝ := y * middleState d C y / denominator C y

theorem hasDerivAt_middleControl {d C : ℝ} (hC : 1 / 4 < C) (y : ℝ) :
    HasDerivAt (middleControl d C) (middleState d C y / denominator C y ^ 2) y := by
  have hD := ne_of_gt (denominator_pos hC y)
  have hh := ((hasDerivAt_id y).mul (hasDerivAt_middleState (d := d) hC y)).div
    (hasDerivAt_denominator C y) hD
  convert hh using 1
  simp only [id_eq, Pi.mul_apply]
  field_simp
  unfold denominator
  ring

theorem middleControl_strictMono {d C : ℝ} (hd : 0 < d) (hC : 1 / 4 < C) :
    StrictMono (middleControl d C) := by
  apply strictMono_of_deriv_pos
  intro y
  rw [(hasDerivAt_middleControl (d := d) hC y).deriv]
  exact div_pos (middleState_pos hd hC y) (sq_pos_of_pos (denominator_pos hC y))

theorem denominator_endParameter {C : ℝ} (hC : C ≠ 0) (hC1 : 1 - C ≠ 0) :
    denominator C (endParameter C) = C ^ 2 / (1 - C) ^ 2 := by
  unfold denominator endParameter
  field_simp
  ring

theorem sqrt_denominator_endParameter {C : ℝ} (hC : 1 / 4 < C) (hC1 : C < 1) :
    Real.sqrt (denominator C (endParameter C)) = C / (1 - C) := by
  have hCp : 0 < C := by linarith
  have h1 : 0 < 1 - C := sub_pos.mpr hC1
  have hsq : (C / (1 - C)) ^ 2 = denominator C (endParameter C) := by
    rw [denominator_endParameter (ne_of_gt hCp) (ne_of_gt h1), div_pow]
  have hp : 0 < C / (1 - C) := div_pos hCp h1
  have hs := Real.sq_sqrt (denominator_pos hC (endParameter C)).le
  have hnn := Real.sqrt_nonneg (denominator C (endParameter C))
  nlinarith

theorem middleControl_zero (d C : ℝ) : middleControl d C 0 = 0 := by
  simp [middleControl]

theorem middleControl_endParameter {d C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) : middleControl d C (endParameter C) = 1 := by
  have hCp : 0 < C := by linarith [hC.1]
  have h1 : 0 < 1 - C := by linarith [hC.2]
  have h2 : 0 < 1 - 2 * C := by linarith [hC.2]
  rw [← hinit]
  unfold middleControl middleState initialState
  rw [sqrt_denominator_endParameter hC.1 (by linarith [hC.2]),
    denominator_endParameter (ne_of_gt hCp) (ne_of_gt h1)]
  rw [show -primitive C (endParameter C) / 2 = -(primitive C (endParameter C) / 2) by ring,
    Real.exp_neg]
  unfold endParameter
  field_simp

theorem continuous_middleControl {d C : ℝ} (hC : 1 / 4 < C) :
    Continuous (middleControl d C) :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_middleControl hC y).continuousAt

theorem maximizingControl_measurable {d C : ℝ} (hC : 1 / 4 < C) :
    Measurable (maximizingControl d C) := by
  classical
  have hm : Measurable (fun t : ℝ => middleControl d C (t / C - 1)) :=
    ((continuous_middleControl hC).comp ((continuous_id.div_const C).sub continuous_const)).measurable
  change Measurable (fun t : ℝ => if t ≤ C then (0 : ℝ) else
    if t ≤ C * (1 + endParameter C) then middleControl d C (t / C - 1) else 1)
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_id measurable_const) hm measurable_const)

theorem maximizingControl_mem_Icc {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) (t : ℝ) :
    maximizingControl d C t ∈ Icc (0 : ℝ) 1 := by
  have hCp : 0 < C := by linarith [hC.1]
  have hm := (middleControl_strictMono hd hC.1).monotone
  unfold maximizingControl
  split_ifs with ht hte
  · exact ⟨le_rfl, zero_le_one⟩
  · change 0 ≤ middleControl d C (t / C - 1) ∧ middleControl d C (t / C - 1) ≤ 1
    have hlo : 0 ≤ t / C - 1 := by
      have := (le_div_iff₀ hCp).2 (show 1 * C ≤ t by linarith)
      linarith
    have hhi : t / C - 1 ≤ endParameter C := by
      have := (div_le_iff₀ hCp).2 (show t ≤ (1 + endParameter C) * C by nlinarith [hte])
      linarith
    constructor
    · simpa only [middleControl_zero] using hm hlo
    · simpa only [middleControl_endParameter hC hinit] using hm hhi
  · exact ⟨zero_le_one, le_rfl⟩

theorem maximizingControl_strictMonoOn {d C : ℝ} (hd : 0 < d) (hC : 1 / 4 < C) :
    StrictMonoOn (maximizingControl d C) (Ioo C (C * (1 + endParameter C))) := by
  have hCp : 0 < C := by linarith
  intro a ha b hb hab
  simp only [maximizingControl, not_le.mpr ha.1, not_le.mpr hb.1, if_false,
    if_pos ha.2.le, if_pos hb.2.le]
  apply middleControl_strictMono hd hC
  exact sub_lt_sub_right ((div_lt_div_iff_of_pos_right hCp).2 hab) 1

theorem maximizingControl_feasible {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    AEStronglyMeasurable (maximizingControl d C) (volume.restrict (Icc 0 1)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, maximizingControl d C t ∈ Icc (0 : ℝ) 1) ∧
    StrictMonoOn (maximizingControl d C) (Ioo C (C * (1 + endParameter C))) := by
  exact ⟨(maximizingControl_measurable hC.1).aestronglyMeasurable,
    fun t _ => maximizingControl_mem_Icc hd hC hinit t,
    maximizingControl_strictMonoOn hd hC.1⟩

end FixedPrice
