import FixedPrice.PhysicalBranch

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

def curvatureAtEndpoint (D y : ℝ) : ℝ := (D - 1 + y) / y ^ 2

theorem denominator_curvature_rescale {D y : ℝ} (hy : y ≠ 0) (s : ℝ) :
    denominator (curvatureAtEndpoint D y) (y * s) = 1 - y * s + (D - 1 + y) * s ^ 2 := by
  unfold denominator curvatureAtEndpoint
  field_simp

theorem denominator_curvature_endpoint {D y : ℝ} (hy : y ≠ 0) :
    denominator (curvatureAtEndpoint D y) y = D := by
  have hh := denominator_curvature_rescale (D := D) hy 1
  simpa using hh

theorem curvature_physical {D y : ℝ} (hD : D ∈ Ioo (0 : ℝ) 1)
    (hy : 1 - D < y) (hu : y < 2 + 2 * Real.sqrt D) :
    0 < curvatureAtEndpoint D y ∧ curvatureAtEndpoint D y * y < 1 ∧
      ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator (curvatureAtEndpoint D y) r := by
  have hyp : 0 < y := by linarith [hD.2]
  have hq : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD.1
  have hq2 := Real.sq_sqrt hD.1.le
  refine ⟨div_pos (by linarith) (sq_pos_of_pos hyp), ?_, ?_⟩
  · have heq : curvatureAtEndpoint D y * y = (D - 1 + y) / y := by
      unfold curvatureAtEndpoint
      field_simp
    rw [heq]
    exact (div_lt_one hyp).2 (by linarith [hD.2])
  · intro r hr
    let s := r / y
    have hs : s ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hr.1 hyp.le, (div_le_one hyp).2 hr.2⟩
    have hrs : y * s = r := mul_div_cancel₀ _ (ne_of_gt hyp)
    rw [← hrs, denominator_curvature_rescale (ne_of_gt hyp)]
    have heq : 1 - y * s + (D - 1 + y) * s ^ 2 =
        (1 - (1 + Real.sqrt D) * s) ^ 2 + (2 + 2 * Real.sqrt D - y) * s * (1 - s) := by
      nlinarith [hq2]
    rw [heq]
    by_cases hs0 : s = 0
    · simp [hs0]
    by_cases hs1 : s = 1
    · simp only [hs1, mul_one, sub_self, mul_zero, add_zero]
      nlinarith [sq_pos_of_pos hq]
    have hp : 0 < (2 + 2 * Real.sqrt D - y) * s * (1 - s) :=
      mul_pos (mul_pos (sub_pos.mpr hu) (lt_of_le_of_ne hs.1 (Ne.symm hs0)))
        (sub_pos.mpr (lt_of_le_of_ne hs.2 hs1))
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hp

theorem primitive_zero_parameter {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    primitive 0 y = -Real.log (1 - y) := by
  have hi : IntervalIntegrable (fun r : ℝ => (1 - r)⁻¹) volume 0 y := by
    apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hy.1
    apply (continuousOn_const.sub continuousOn_id).inv₀
    intro r hr
    change 1 - r ≠ 0
    exact ne_of_gt (by linarith [hr.2, hy.2])
  have hder : ∀ r ∈ uIcc (0 : ℝ) y, HasDerivAt (fun r => -Real.log (1 - r)) (1 - r)⁻¹ r := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) y := by simpa [uIcc_of_le hy.1] using hr
    have hn : 1 - r ≠ 0 := ne_of_gt (by linarith [hr'.2, hy.2])
    convert (((hasDerivAt_id r).const_sub 1).log hn).neg using 1
    simp [div_eq_mul_inv]
  simpa [primitive, denominator] using intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi

theorem contactLog_curvature_lower {D : ℝ} (hD : D ∈ Ioo (0 : ℝ) 1) :
    contactLog (curvatureAtEndpoint D (1 - D)) (1 - D) = Real.log (D / (1 - D)) := by
  have hy : 0 < 1 - D := sub_pos.mpr hD.2
  have hC : curvatureAtEndpoint D (1 - D) = 0 := by simp [curvatureAtEndpoint]
  rw [hC, contactLog, primitive_zero_parameter ⟨hy.le, by linarith [hD.1]⟩]
  simp only [denominator, zero_mul, add_zero, sub_sub_cancel]
  rw [Real.log_div (ne_of_gt hD.1) (ne_of_gt hy)]
  ring

theorem primitive_rescale (C y : ℝ) :
    primitive C y = y * ∫ r in (0 : ℝ)..1, (denominator C (y * r))⁻¹ := by
  simpa only [smul_eq_mul, mul_zero, mul_one, primitive] using
    (intervalIntegral.smul_integral_comp_mul_left
      (fun r => (denominator C r)⁻¹) (a := (0 : ℝ)) (b := 1) y).symm

theorem primitive_lower_near_boundary {D ε : ℝ} (hD : D ∈ Ioo (0 : ℝ) 1)
    (he : 0 < ε) (he1 : ε < 1)
    (hel : ε < (1 / (1 + Real.sqrt D)) / 2)
    (her : ε < (1 - 1 / (1 + Real.sqrt D)) / 2) :
    2 / (((1 + Real.sqrt D) ^ 2 + 1) * ε) ≤
      primitive (curvatureAtEndpoint D (2 + 2 * Real.sqrt D - ε ^ 2))
        (2 + 2 * Real.sqrt D - ε ^ 2) := by
  let q := Real.sqrt D
  let s₀ := 1 / (1 + q)
  let y := 2 + 2 * q - ε ^ 2
  let C := curvatureAtEndpoint D y
  let K := (1 + q) ^ 2 + 1
  have hq : 0 < q := Real.sqrt_pos.mpr hD.1
  have hq2 : q ^ 2 = D := Real.sq_sqrt hD.1.le
  have hq1 : 0 < 1 + q := by linarith
  have hs : 0 < s₀ := div_pos zero_lt_one hq1
  have hs1 : s₀ < 1 := (div_lt_one hq1).2 (by linarith)
  have he2 : ε ^ 2 < 1 := by nlinarith
  have hy : 1 < y := by dsimp [y]; nlinarith
  have hyl : 1 - D < y := by linarith [hD.1]
  have hyu : y < 2 + 2 * q := by dsimp [y]; nlinarith [sq_pos_of_pos he]
  have hphysical := curvature_physical hD hyl hyu
  have hK : 0 < K := by dsimp [K]; positivity
  have hlo : 0 ≤ s₀ - ε := by change ε < s₀ / 2 at hel; linarith
  have hhi : s₀ + ε ≤ 1 := by change ε < (1 - s₀) / 2 at her; linarith
  have hden : ∀ s ∈ Icc (0 : ℝ) 1, 0 < denominator C (y * s) := by
    intro s hs'
    exact hphysical.2.2 _ ⟨mul_nonneg (by linarith) hs'.1,
      by nlinarith [hs'.2]⟩
  have hc : ContinuousOn (fun s => (denominator C (y * s))⁻¹) (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · unfold denominator
      fun_prop
    · exact fun s hs' => ne_of_gt (hden s hs')
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have his := control_intervalIntegrable_subinterval hi ⟨hlo, by linarith⟩ ⟨by linarith, hhi⟩
  have hupper : ∀ s ∈ Icc (s₀ - ε) (s₀ + ε), denominator C (y * s) ≤ K * ε ^ 2 := by
    intro s hs'
    have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hlo.trans hs'.1, hs'.2.trans hhi⟩
    have hss : (s - s₀) ^ 2 ≤ ε ^ 2 := by nlinarith [hs'.1, hs'.2]
    have hmid : (1 + q) * s₀ = 1 := mul_one_div_cancel (ne_of_gt hq1)
    have hformula : denominator C (y * s) =
        (1 + q) ^ 2 * (s - s₀) ^ 2 + ε ^ 2 * s * (1 - s) := by
      rw [denominator_curvature_rescale (by linarith : y ≠ 0)]
      dsimp [y]
      linear_combination (2 * (1 + q) * s - (1 + q) * s₀ - 1) * hmid + (-s ^ 2) * hq2
    rw [hformula]
    have hbound : s * (1 - s) ≤ 1 := by nlinarith [sq_nonneg s, hs01.1, hs01.2]
    have hfirst := mul_le_mul_of_nonneg_left hss (sq_nonneg (1 + q))
    have hsecond := mul_le_mul_of_nonneg_left hbound (sq_nonneg ε)
    dsimp [K]
    nlinarith
  have hsmall : 2 / (K * ε) ≤ ∫ s in s₀ - ε..s₀ + ε, (denominator C (y * s))⁻¹ := by
    have hm := intervalIntegral.integral_mono_on (by linarith : s₀ - ε ≤ s₀ + ε)
      (intervalIntegrable_const (c := (K * ε ^ 2)⁻¹)) his (fun s hs' =>
        inv_anti₀ (hden s ⟨hlo.trans hs'.1, hs'.2.trans hhi⟩) (hupper s hs'))
    calc
      2 / (K * ε) = ∫ _s in s₀ - ε..s₀ + ε, (K * ε ^ 2)⁻¹ := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        field_simp
        <;> ring
      _ ≤ _ := hm
  have hlarge : (∫ s in s₀ - ε..s₀ + ε, (denominator C (y * s))⁻¹) ≤
      ∫ s in (0 : ℝ)..1, (denominator C (y * s))⁻¹ := by
    apply intervalIntegral.integral_mono_interval hlo (by linarith) hhi ?_ hi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs'
    exact (inv_pos.mpr (hden s ⟨hs'.1.le, hs'.2⟩)).le
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..1, (denominator C (y * s))⁻¹ := by
    exact intervalIntegral.integral_nonneg zero_le_one (fun s hs' => (inv_pos.mpr (hden s hs')).le)
  change 2 / (K * ε) ≤ primitive C y
  rw [primitive_rescale]
  exact (hsmall.trans hlarge).trans (le_mul_of_one_le_left hnonneg hy.le)

end FixedPrice
