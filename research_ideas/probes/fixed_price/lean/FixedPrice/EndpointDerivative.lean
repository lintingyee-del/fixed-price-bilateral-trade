import FixedPrice.BranchRegularity

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

def contactWeight (C y : ℝ) : ℝ := ∫ r in 0..y, (y - r) / denominator C r ^ 2

theorem contactWeight_nonneg {C y : ℝ} (hy : 0 ≤ y) : 0 ≤ contactWeight C y := by
  apply intervalIntegral.integral_nonneg hy
  intro r hr
  exact div_nonneg (sub_nonneg.mpr hr.2) (sq_nonneg _)

theorem contactWeight_identity {C y : ℝ} (hy : 0 ≤ y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    2 * contactWeight C y = y ^ 2 / denominator C y + (2 * C * y - 1) * secondPrimitive C y := by
  have hcD : ContinuousOn (fun r => denominator C r ^ 2) (Icc 0 y) :=
    (continuous_denominator C).continuousOn.pow 2
  have hnD : ∀ r ∈ Icc (0 : ℝ) y, denominator C r ^ 2 ≠ 0 :=
    fun r hr => pow_ne_zero 2 (ne_of_gt (hD r hr))
  have hu : IntervalIntegrable (fun r => (y - r) / denominator C r ^ 2) volume 0 y :=
    ((continuousOn_const.sub continuousOn_id).div hcD hnD).intervalIntegrable_of_Icc
      (μ := volume) hy
  have hz : IntervalIntegrable (fun r => r ^ 2 / denominator C r ^ 2) volume 0 y :=
    ((continuousOn_id.pow 2).div hcD hnD).intervalIntegrable_of_Icc (μ := volume) hy
  have hder : ∀ r ∈ uIcc (0 : ℝ) y,
      HasDerivAt (fun r => (2 * y * r - r ^ 2) / denominator C r)
        (2 * ((y - r) / denominator C r ^ 2) - (2 * C * y - 1) * (r ^ 2 / denominator C r ^ 2)) r := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) y := by simpa [uIcc_of_le hy] using hr
    have hn := ne_of_gt (hD r hr')
    convert (((hasDerivAt_id r).const_mul (2 * y)).sub ((hasDerivAt_id r).pow 2)).div
      (hasDerivAt_denominator C r) hn using 1
    simp only [id_eq, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hn]
    unfold denominator
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((hu.const_mul 2).sub (hz.const_mul (2 * C * y - 1)))
  rw [intervalIntegral.integral_sub (hu.const_mul 2) (hz.const_mul (2 * C * y - 1)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hf
  change 2 * contactWeight C y - (2 * C * y - 1) * secondPrimitive C y = _ at hf
  simp at hf
  have he : (2 * y * y - y ^ 2) / denominator C y = y ^ 2 / denominator C y := by ring
  rw [he] at hf
  linarith

def endpointValue (C y : ℝ) : ℝ := C * primitive C y - C ^ 2 * y / (1 - C * y)

theorem hasDerivAt_denominator_along {Y : ℝ → ℝ} {C Y' : ℝ} (hY : HasDerivAt Y Y' C) :
    HasDerivAt (fun x => denominator x (Y x))
      ((Y C) ^ 2 + (2 * C * Y C - 1) * Y') C := by
  convert ((hY.const_sub 1).add ((hasDerivAt_id C).mul (hY.pow 2))) using 1
  simp only [id_eq, Pi.pow_apply]
  ring

theorem hasDerivAt_primitive_along_contact {Y : ℝ → ℝ} {C Y' d : ℝ}
    (hY : HasDerivAt Y Y' C) (hy : 0 < Y C)
    (hD : ∀ r ∈ Icc (0 : ℝ) (Y C), 0 < denominator C r)
    (hcontact : ∀ᶠ x in 𝓝 C, contactLog x (Y x) = Real.log d) :
    HasDerivAt (fun x => primitive x (Y x))
      (-secondPrimitive C (Y C) + Y' / denominator C (Y C)) C := by
  have hn := ne_of_gt (hD (Y C) ⟨hy.le, le_rfl⟩)
  have hder := (((hasDerivAt_denominator_along hY).log hn).sub
    ((hY.log (ne_of_gt hy)).const_mul 2)).sub_const (2 * Real.log d)
  have heq : (fun x => primitive x (Y x)) =ᶠ[𝓝 C]
      fun x => Real.log (denominator x (Y x)) - 2 * Real.log (Y x) - 2 * Real.log d := by
    filter_upwards [hcontact] with x hx
    unfold contactLog at hx
    linarith
  have hh := hder.congr_of_eventuallyEq heq
  have hYeq := implicitBranch_derivative hY hy hD hcontact
  have hYs : Y' = ((Y C) ^ 3 + Y C * denominator C (Y C) * secondPrimitive C (Y C)) / 2 := by
    linarith
  convert hh using 1
  rw [hYs]
  generalize Y C = y at hn hy ⊢
  field_simp [hn, ne_of_gt hy]
  unfold denominator
  ring

/-- The differentiated formula in (G2), derived from the actual contact equation. -/
theorem hasDerivAt_endpointValue {Y : ℝ → ℝ} {C Y' d : ℝ}
    (hY : HasDerivAt Y Y' C) (hy : 0 < Y C) (hline : C * Y C < 1)
    (hD : ∀ r ∈ Icc (0 : ℝ) (Y C), 0 < denominator C r)
    (hcontact : ∀ᶠ x in 𝓝 C, contactLog x (Y x) = Real.log d) :
    HasDerivAt (fun x => endpointValue x (Y x))
      (-((Y C + contactWeight C (Y C)) / (1 - C * Y C) ^ 2) * branchDefect C (Y C)) C := by
  have hn := ne_of_gt (hD (Y C) ⟨hy.le, le_rfl⟩)
  have hl : 1 - C * Y C ≠ 0 := ne_of_gt (sub_pos.mpr hline)
  have hI := hasDerivAt_primitive_along_contact hY hy hD hcontact
  have hder := ((hasDerivAt_id C).mul hI).sub
    ((((hasDerivAt_id C).pow 2).mul hY).div (((hasDerivAt_id C).mul hY).const_sub 1) hl)
  have hYs : Y' = ((Y C) ^ 3 + Y C * denominator C (Y C) * secondPrimitive C (Y C)) / 2 := by
    linarith [implicitBranch_derivative hY hy hD hcontact]
  have hIs : primitive C (Y C) = ((4 * C - 1) * secondPrimitive C (Y C) -
      Y C * (Y C - 2) / denominator C (Y C)) / 2 := by
    linarith [primitive_secondPrimitive_identity hy.le hD]
  have hUs : contactWeight C (Y C) = ((Y C) ^ 2 / denominator C (Y C) +
      (2 * C * Y C - 1) * secondPrimitive C (Y C)) / 2 := by
    linarith [contactWeight_identity hy.le hD]
  convert hder using 1
  simp only [id_eq, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [hYs, hIs, hUs]
  generalize Y C = y at hn hl ⊢
  field_simp [hn, hl]
  field_simp [(show 1 - y * C ≠ 0 by simpa only [mul_comm] using hl)]
  unfold branchDefect denominator
  ring

end FixedPrice
