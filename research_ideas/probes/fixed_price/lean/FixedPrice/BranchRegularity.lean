import FixedPrice.Branch
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

theorem secondPrimitive_rescale (C y : ℝ) :
    secondPrimitive C y = y * ∫ r in (0 : ℝ)..1, (y * r) ^ 2 / denominator C (y * r) ^ 2 := by
  simpa only [smul_eq_mul, mul_zero, mul_one, secondPrimitive] using
    (intervalIntegral.smul_integral_comp_mul_left
      (fun r => r ^ 2 / denominator C r ^ 2) (a := (0 : ℝ)) (b := 1) y).symm

theorem physical_neighborhood_uniform {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ q : ℝ × ℝ in 𝓝 (C, y),
      0 < q.2 ∧ ∀ r ∈ Icc (0 : ℝ) 1, m ≤ denominator q.1 (q.2 * r) := by
  obtain ⟨m, ε, hm, hε, hb⟩ := denominator_uniform_lower hy.le hD
  refine ⟨m / 2, half_pos hm, ?_⟩
  have hu : ∀ᶠ q : ℝ × ℝ in 𝓝 (C, y),
      ∀ r ∈ Icc (0 : ℝ) 1, m / 2 ≤ denominator q.1 (q.2 * r) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have hyr : y * r ∈ Icc (0 : ℝ) y :=
      ⟨mul_nonneg hy.le hr.1, mul_le_of_le_one_right hy.le hr.2⟩
    have hd : m / 2 < denominator C (y * r) := by
      have := hb C (Metric.mem_ball_self hε) (y * r) hyr
      linarith
    have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => denominator z.1.1 (z.1.2 * z.2)) := by
      unfold denominator
      fun_prop
    exact (hc.continuousAt.eventually (Ioi_mem_nhds hd)).mono fun _ hz => hz.le
  have hy' : ∀ᶠ q : ℝ × ℝ in 𝓝 (C, y), 0 < q.2 :=
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds hy)
  exact hy'.and hu

theorem physical_neighborhood {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (C, y),
      0 < q.2 ∧ ∀ r ∈ Icc (0 : ℝ) q.2, 0 < denominator q.1 r := by
  obtain ⟨m, hm, he⟩ := physical_neighborhood_uniform hy hD
  filter_upwards [he] with q hq
  refine ⟨hq.1, ?_⟩
  intro r hr
  have hratio : r / q.2 ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr.1 hq.1.le, (div_le_one hq.1).2 hr.2⟩
  have hb := hm.trans_le (hq.2 (r / q.2) hratio)
  simpa only [mul_div_cancel₀ _ (ne_of_gt hq.1)] using hb

theorem continuousAt_secondPrimitive {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    ContinuousAt (fun q : ℝ × ℝ => secondPrimitive q.1 q.2) (C, y) := by
  obtain ⟨m, hm, he⟩ := physical_neighborhood_uniform hy hD
  let F : (ℝ × ℝ) → ℝ → ℝ := fun q r =>
    (q.2 * r) ^ 2 / (max m (denominator q.1 (q.2 * r))) ^ 2
  have hc : Continuous F.uncurry := by
    apply Continuous.div
    · dsimp [F, Function.uncurry]
      fun_prop
    · dsimp [F, Function.uncurry]
      unfold denominator
      fun_prop
    · intro z
      exact pow_ne_zero 2 (ne_of_gt (hm.trans_le (le_max_left _ _)))
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hc
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  have hall : Continuous (fun q : ℝ × ℝ => q.2 * ∫ r in (0 : ℝ)..1, F q r) := by
    have heq : (fun q => ∫ r in (0 : ℝ)..1, F q r) = fun q => ∫ r in Icc (0 : ℝ) 1, F q r := by
      funext q
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
    apply continuous_snd.mul
    rw [heq]
    exact hi
  apply hall.continuousAt.congr_of_eventuallyEq
  filter_upwards [he] with q hq
  rw [secondPrimitive_rescale]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using hr
  dsimp only [F]
  rw [max_eq_right (hq.2 r hr')]

def contactDerivativeC (C y : ℝ) : ℝ :=
  (y ^ 2 / denominator C y + secondPrimitive C y) / 2

def contactDerivativeY (C y : ℝ) : ℝ := -(y * denominator C y)⁻¹

theorem hasStrictFDerivAt_contactLog {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    HasStrictFDerivAt (fun q : ℝ × ℝ => contactLog q.1 q.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeC C y)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeY C y))) (C, y) := by
  have he := physical_neighborhood hy hD
  have hd1 : ∀ᶠ q : ℝ × ℝ in 𝓝 (C, y),
      HasFDerivAt (fun x => contactLog x q.2)
        (ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeC q.1 q.2)) q.1 := by
    filter_upwards [he] with q hq
    exact (hasDerivAt_contactLog_parameter hq.1 hq.2).hasFDerivAt
  have hd2 : ∀ᶠ q : ℝ × ℝ in 𝓝 (C, y),
      HasFDerivAt (contactLog q.1)
        (ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeY q.1 q.2)) q.2 := by
    filter_upwards [he] with q hq
    exact (hasDerivAt_contactLog_variable hq.1 hq.2).hasFDerivAt
  have hden : Continuous (fun q : ℝ × ℝ => denominator q.1 q.2) := by
    unfold denominator
    fun_prop
  have hn := ne_of_gt (hD y ⟨hy.le, le_rfl⟩)
  have hc1 : ContinuousAt (fun q : ℝ × ℝ => contactDerivativeC q.1 q.2) (C, y) :=
    (((continuous_snd.continuousAt.pow 2).div hden.continuousAt hn).add
      (continuousAt_secondPrimitive hy hD)).div_const 2
  have hc2 : ContinuousAt (fun q : ℝ × ℝ => contactDerivativeY q.1 q.2) (C, y) :=
    ((continuous_snd.continuousAt.mul hden.continuousAt).inv₀
      (mul_ne_zero (ne_of_gt hy) hn)).neg
  exact hasStrictFDerivAt_uncurry_coprod (f := contactLog) (u := (C, y))
    (f₁ := fun x r => ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeC x r))
    (f₂ := fun x r => ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeY x r)) hd1 hd2
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc1)
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc2)

theorem contactLog_deriv_along_branch {Y : ℝ → ℝ} {C Y' : ℝ}
    (hY : HasDerivAt Y Y' C) (hy : 0 < Y C)
    (hD : ∀ r ∈ Icc (0 : ℝ) (Y C), 0 < denominator C r) :
    HasDerivAt (fun x => contactLog x (Y x))
      (contactDerivativeC C (Y C) + contactDerivativeY C (Y C) * Y') C := by
  have hh := (hasStrictFDerivAt_contactLog hy hD).hasFDerivAt.comp C
    ((hasDerivAt_id C).hasFDerivAt.prodMk hY.hasFDerivAt)
  convert hh.hasDerivAt using 1
  simp [ContinuousLinearMap.coprod_apply, mul_comm]

theorem implicitBranch_derivative {Y : ℝ → ℝ} {C Y' d : ℝ}
    (hY : HasDerivAt Y Y' C) (hy : 0 < Y C)
    (hD : ∀ r ∈ Icc (0 : ℝ) (Y C), 0 < denominator C r)
    (hcontact : ∀ᶠ x in 𝓝 C, contactLog x (Y x) = Real.log d) :
    2 * Y' = (Y C) ^ 3 + Y C * denominator C (Y C) * secondPrimitive C (Y C) := by
  have hd := contactLog_deriv_along_branch hY hy hD
  have hz : HasDerivAt (fun x => contactLog x (Y x)) 0 C :=
    (hasDerivAt_const C (Real.log d)).congr_of_eventuallyEq hcontact
  have heq := hd.unique hz
  have hn := ne_of_gt (hD (Y C) ⟨hy.le, le_rfl⟩)
  unfold contactDerivativeC contactDerivativeY at heq
  field_simp [hn, ne_of_gt hy] at heq
  nlinarith

theorem local_contact_branch_exists {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    ∃ Y : ℝ → ℝ, Y C = y ∧
      HasDerivAt Y ((y ^ 3 + y * denominator C y * secondPrimitive C y) / 2) C ∧
      (∀ᶠ x in 𝓝 C, contactLog x (Y x) = contactLog C y) ∧
      (∀ᶠ q : ℝ × ℝ in 𝓝 (C, y), contactLog q.1 q.2 = contactLog C y ↔ Y q.1 = q.2) := by
  have hh := hasStrictFDerivAt_contactLog hy hD
  let L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeY C y)
  let M : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeY C y)⁻¹
  have hn : contactDerivativeY C y ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (ne_of_gt hy) (ne_of_gt (hD y ⟨hy.le, le_rfl⟩))))
  have hinv : L.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := M)
    · ext
      simp [L, M, hn]
    · ext
      simp [L, M, hn]
  have hinv' : (((ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeC C y)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (contactDerivativeY C y))) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    simpa only [ContinuousLinearMap.coprod_comp_inr] using hinv
  let Y := hh.implicitFunctionOfProdDomain hinv'
  have hlocal : ∀ᶠ q : ℝ × ℝ in 𝓝 (C, y),
      contactLog q.1 q.2 = contactLog C y ↔ Y q.1 = q.2 :=
    hh.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv'
  have hYC : Y C = y := hlocal.self_of_nhds.mp rfl
  have hcontact : ∀ᶠ x in 𝓝 C, contactLog x (Y x) = contactLog C y :=
    hh.eventually_apply_implicitFunctionOfProdDomain hinv'
  have hY : DifferentiableAt ℝ Y C :=
    (hh.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv').hasFDerivAt.differentiableAt
  have heq := implicitBranch_derivative (d := Real.exp (contactLog C y)) hY.hasDerivAt
    (by rwa [hYC]) (by rwa [hYC]) (by simpa only [Real.log_exp] using hcontact)
  rw [hYC] at heq
  refine ⟨Y, hYC, ?_, hcontact, hlocal⟩
  convert hY.hasDerivAt using 1
  linarith

end FixedPrice
