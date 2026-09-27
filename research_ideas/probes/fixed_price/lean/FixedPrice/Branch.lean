import FixedPrice.Extremal
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Order.Compact

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

def secondPrimitive (C y : ℝ) : ℝ :=
  ∫ r in 0..y, r ^ 2 / denominator C r ^ 2

theorem denominator_uniform_lower {C y : ℝ} (hy : 0 ≤ y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    ∃ m ε : ℝ, 0 < m ∧ 0 < ε ∧
      ∀ x ∈ Metric.ball C ε, ∀ r ∈ Icc (0 : ℝ) y, m ≤ denominator x r := by
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hy) (continuous_denominator C).continuousOn
  let m := denominator C r₀ / 2
  let ε := m / (y ^ 2 + 1)
  have hm : 0 < m := half_pos (hD r₀ hr₀)
  have hε : 0 < ε := div_pos hm (by positivity)
  refine ⟨m, ε, hm, hε, ?_⟩
  intro x hx r hr
  have hx' : |x - C| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hr2 : r ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hr.1 hy).2 hr.2
  have heq : ε * (y ^ 2 + 1) = m := by dsimp [ε]; field_simp
  have hlower : 2 * m ≤ denominator C r := by
    have hh : denominator C r₀ ≤ denominator C r := hmin hr
    dsimp [m]
    linarith
  have hxr : -ε ≤ x - C := (abs_lt.mp hx').1.le
  have hprod := mul_le_mul_of_nonneg_right hxr (sq_nonneg r)
  have heprod := mul_le_mul_of_nonneg_left hr2 hε.le
  have hdiff : denominator x r = denominator C r + (x - C) * r ^ 2 := by
    unfold denominator
    ring
  rw [hdiff]
  nlinarith

theorem hasDerivAt_primitive_parameter {C y : ℝ} (hy : 0 ≤ y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    HasDerivAt (fun x => primitive x y) (-secondPrimitive C y) C := by
  obtain ⟨m, ε, hm, hε, hbound⟩ := denominator_uniform_lower hy hD
  let μ := volume.restrict (Icc (0 : ℝ) y)
  let F : ℝ → ℝ → ℝ := fun x r => (denominator x r)⁻¹
  let F' : ℝ → ℝ → ℝ := fun x r => -(r ^ 2 / denominator x r ^ 2)
  have hcont : ∀ x ∈ Metric.ball C ε, ContinuousOn (F x) (Icc 0 y) := by
    intro x hx
    exact (continuous_denominator x).continuousOn.inv₀
      (fun r hr => ne_of_gt (hm.trans_le (hbound x hx r hr)))
  have hCmem : C ∈ Metric.ball C ε := Metric.mem_ball_self hε
  have hmeas : ∀ᶠ x in 𝓝 C, AEStronglyMeasurable (F x) μ := by
    filter_upwards [Metric.ball_mem_nhds C hε] with x hx
    exact (hcont x hx).aestronglyMeasurable measurableSet_Icc
  have hFint : Integrable (F C) μ := (hcont C hCmem).integrableOn_Icc
  have hF'meas : AEStronglyMeasurable (F' C) μ := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Icc
    exact ((continuousOn_id.pow 2).div ((continuous_denominator C).continuousOn.pow 2)
      (fun r hr => pow_ne_zero 2 (ne_of_gt (hD r hr)))).neg
  have hnorm : ∀ᵐ r ∂μ, ∀ x ∈ Metric.ball C ε, ‖F' x r‖ ≤ y ^ 2 / m ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr x hx
    have hr2 : r ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hr.1 hy).2 hr.2
    have hDr := hbound x hx r hr
    have hpos := hm.trans_le hDr
    change ‖-(r ^ 2 / denominator x r ^ 2)‖ ≤ y ^ 2 / m ^ 2
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact div_le_div₀ (sq_nonneg _) hr2 (sq_pos_of_pos hm)
      ((sq_le_sq₀ hm.le hpos.le).2 hDr)
  have hbi : Integrable (fun _ : ℝ => y ^ 2 / m ^ 2) μ := continuousOn_const.integrableOn_Icc
  have hdiff : ∀ᵐ r ∂μ, ∀ x ∈ Metric.ball C ε, HasDerivAt (fun x => F x r) (F' x r) x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr x hx
    have hn := ne_of_gt (hm.trans_le (hbound x hx r hr))
    convert (((hasDerivAt_id x).mul_const (r ^ 2)).const_add (1 - r)).inv hn using 1
    simp only [F', one_mul, neg_div, id_eq, denominator]
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds C hε) hmeas hFint hF'meas hnorm hbi hdiff).2
  simpa only [F, F', μ, primitive, secondPrimitive, intervalIntegral.integral_of_le hy,
    integral_Icc_eq_integral_Ioc, integral_neg] using hder

theorem hasDerivAt_primitive_of_positive {C y : ℝ} (hy : 0 ≤ y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    HasDerivAt (primitive C) (denominator C y)⁻¹ y := by
  have hcont : ContinuousOn (fun r => (denominator C r)⁻¹) (Icc 0 y) :=
    (continuous_denominator C).continuousOn.inv₀ (fun r hr => ne_of_gt (hD r hr))
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable_of_Icc (μ := volume) hy)
    ((continuous_denominator C).measurable.inv.stronglyMeasurable.stronglyMeasurableAtFilter)
    ((continuous_denominator C).continuousAt.inv₀ (ne_of_gt (hD y ⟨hy, le_rfl⟩)))

/-- Equation (28) without division by 4C-1; valid on the whole physical domain. -/
theorem primitive_secondPrimitive_identity {C y : ℝ} (hy : 0 ≤ y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    (4 * C - 1) * secondPrimitive C y =
      2 * primitive C y + y * (y - 2) / denominator C y := by
  have hcont : ContinuousOn (fun r => r ^ 2 / denominator C r ^ 2) (Icc 0 y) :=
    (continuousOn_id.pow 2).div ((continuous_denominator C).continuousOn.pow 2)
      (fun r hr => pow_ne_zero 2 (ne_of_gt (hD r hr)))
  have hi := (hcont.intervalIntegrable_of_Icc (μ := volume) hy).const_mul (4 * C - 1)
  have hder : ∀ r ∈ uIcc (0 : ℝ) y,
      HasDerivAt (fun u => 2 * primitive C u + u * (u - 2) / denominator C u)
        ((4 * C - 1) * (r ^ 2 / denominator C r ^ 2)) r := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) y := by simpa [uIcc_of_le hy] using hr
    have hn := ne_of_gt (hD r hr')
    have hprim := hasDerivAt_primitive_of_positive hr'.1
      (fun u hu => hD u ⟨hu.1, hu.2.trans hr'.2⟩)
    convert (hprim.const_mul 2).add (((hasDerivAt_id r).mul
      ((hasDerivAt_id r).sub_const 2)).div (hasDerivAt_denominator C r) hn) using 1
    simp only [id_eq, Pi.mul_apply]
    field_simp [hn]
    unfold denominator
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi
  simpa [intervalIntegral.integral_const_mul, secondPrimitive, primitive] using hftc

def contactLog (C y : ℝ) : ℝ :=
  (Real.log (denominator C y) - primitive C y) / 2 - Real.log y

theorem hasDerivAt_contactLog_parameter {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    HasDerivAt (fun x => contactLog x y)
      ((y ^ 2 / denominator C y + secondPrimitive C y) / 2) C := by
  have hn := ne_of_gt (hD y ⟨hy.le, le_rfl⟩)
  have hden : HasDerivAt (fun x => denominator x y) (y ^ 2) C := by
    convert ((hasDerivAt_id C).mul_const (y ^ 2)).const_add (1 - y) using 1
    simp
  have hh := (((hden.log hn).sub (hasDerivAt_primitive_parameter hy.le hD)).div_const 2).sub_const (Real.log y)
  simpa only [sub_neg_eq_add] using hh

theorem hasDerivAt_contactLog_variable {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    HasDerivAt (contactLog C) (-(y * denominator C y)⁻¹) y := by
  have hn := ne_of_gt (hD y ⟨hy.le, le_rfl⟩)
  convert ((((hasDerivAt_denominator C y).log hn).sub
    (hasDerivAt_primitive_of_positive hy.le hD)).div_const 2).sub
      (Real.hasDerivAt_log (ne_of_gt hy)) using 1
  field_simp [hn, ne_of_gt hy]
  unfold denominator
  ring

end FixedPrice
