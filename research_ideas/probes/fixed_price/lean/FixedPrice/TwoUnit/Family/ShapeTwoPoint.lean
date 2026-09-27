import FixedPrice.TwoUnit.Family.ShapeTrap

/-!
# Work package B, part 6: the two-point inequalities

With `ω = √s w` (`= ξ z'`), Lebesgue points `x < y` of `ω` inside the curve interval, and
`F(ξ) = d ∫ e^{-2z}`:

* where the lower obstacle is slack on `[x, y']` (`y' > y`), pushing down gives
  `ω(x) - ω(y) ≤ F(y) - F(x)`;
* where the upper obstacle is slack on `[x, y']`, pushing up gives `F(y) - F(x) ≤ ω(x) - ω(y)`.

So `ω + F` is nondecreasing, resp. nonincreasing, along Lebesgue points.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

theorem zfun_neg (u : H θ) (ξ : ℝ) : zfun θ (-u) ξ = -zfun θ u ξ := by
  unfold zfun; rw [inner_neg_left]

theorem continuous_trap (x y r : ℝ) : Continuous (trap x y r) := by
  unfold trap
  exact continuous_const.max (continuous_const.min
    (((continuous_id.sub continuous_const).div_const r).min
      ((continuous_const.sub continuous_id).div_const r)))

theorem eventually_small {ε : ℝ} (hε : 0 < ε) : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r ≤ ε := by
  filter_upwards [Ioc_mem_nhdsGT hε] with r hr using hr

theorem setIntegral_μ_Ioo {a b : ℝ} (hab : a ≤ b) (hsub : Ioo a b ⊆ Ioc θ.c θ.ξ₀) (f : ℝ → ℝ) :
    ∫ s in Ioo a b, f s ∂(μ θ) = ∫ s in a..b, f s := by
  show ∫ s in Ioo a b, f s ∂(volume.restrict (Ioc θ.c θ.ξ₀)) = _
  rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem setIntegral_μ_Ioc {a b : ℝ} (hab : a ≤ b) (hsub : Ioc a b ⊆ Ioc θ.c θ.ξ₀) (f : ℝ → ℝ) :
    ∫ s in Ioc a b, f s ∂(μ θ) = ∫ s in a..b, f s := by
  show ∫ s in Ioc a b, f s ∂(volume.restrict (Ioc θ.c θ.ξ₀)) = _
  rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub,
    intervalIntegral.integral_of_le hab]

theorem integrable_indicator_μ {f : ℝ → ℝ} {a b : ℝ} (hsub : Ioo a b ⊆ Ioc θ.c θ.ξ₀)
    (hf : IntegrableOn f (Ioc θ.c θ.ξ₀) volume) : Integrable ((Ioo a b).indicator f) (μ θ) := by
  have h := (hf.mono_set hsub).integrable_indicator measurableSet_Ioo
  show Integrable _ (volume.restrict (Ioc θ.c θ.ξ₀))
  exact h.integrableOn

/-- `ω = √s w`, the paper's `ξ z'` (`ξ P'/P`). -/
def omega (w : H θ) (s : ℝ) : ℝ := Real.sqrt s * w s

theorem integrableOn_omega (w : H θ) : IntegrableOn (omega w) (Ioc θ.c θ.ξ₀) volume := by
  refine ((integrableOn_w w).norm.const_mul (Real.sqrt θ.ξ₀)).mono' ?_ ?_
  · exact (Real.continuous_sqrt.measurable.aemeasurable.mul
      (Lp.aestronglyMeasurable w).aemeasurable).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
    unfold omega
    rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg s)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hs.2) (norm_nonneg _)

theorem intervalIntegrable_omega (w : H θ) (hcξ : θ.c ≤ θ.ξ₀) :
    IntervalIntegrable (omega w) volume θ.c θ.ξ₀ :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hcξ).mpr (integrableOn_omega w)

/-- A Lebesgue point of `ω`. -/
def IsLeb (w : H θ) (x : ℝ) : Prop :=
  HasDerivAt (fun t => ∫ s in θ.c..t, omega w s) (omega w x) x

theorem ae_isLeb (w : H θ) (hcξ : θ.c ≤ θ.ξ₀) : ∀ᵐ x, x ∈ Ioo θ.c θ.ξ₀ → IsLeb w x := by
  filter_upwards [(intervalIntegrable_omega w hcξ).ae_hasDerivAt_integral] with x hx hxI
  exact hx (by rw [uIcc_of_le hcξ]; exact Ioo_subset_Icc_self hxI) θ.c
    (by rw [uIcc_of_le hcξ]; exact left_mem_Icc.mpr hcξ)

theorem tendsto_avg (w : H θ) {x : ℝ} (hx : IsLeb w x) (hcx : θ.c ≤ x) (hxξ : x < θ.ξ₀) :
    Tendsto (fun r => r⁻¹ * ∫ s in x..x + r, omega w s) (𝓝[>] 0) (𝓝 (omega w x)) := by
  refine hx.tendsto_slope_zero_right.congr' ?_
  filter_upwards [eventually_small (sub_pos.mpr hxξ)] with r hr
  have hr' : x + r ≤ θ.ξ₀ := by linarith [hr.2]
  have h1 : IntervalIntegrable (omega w) volume θ.c x :=
    (intervalIntegrable_omega w (hcx.trans hxξ.le)).mono_set (by
      rw [uIcc_of_le hcx, uIcc_of_le (hcx.trans hxξ.le)]; exact Icc_subset_Icc_right hxξ.le)
  have h2 : IntervalIntegrable (omega w) volume x (x + r) :=
    (intervalIntegrable_omega w (hcx.trans hxξ.le)).mono_set (by
      rw [uIcc_of_le (by linarith [hr.1]), uIcc_of_le (hcx.trans hxξ.le)]
      exact Icc_subset_Icc hcx hr')
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  ring

section Trap

variable {x y r : ℝ}

theorem memLp_vtrap : MemLp (fun s => Real.sqrt s * dtrap x y r s) 2 (μ θ) := by
  refine MemLp.of_bound (C := Real.sqrt θ.ξ₀ * (2 * |1 / r|)) ?_ ?_
  · refine (Real.continuous_sqrt.measurable.mul ?_).aestronglyMeasurable
    unfold dtrap
    exact (measurable_const.indicator measurableSet_Ioo).sub
      (measurable_const.indicator measurableSet_Ioo)
  · filter_upwards [ae_mem_I] with s hs
    rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg s)]
    refine mul_le_mul (Real.sqrt_le_sqrt hs.2) ?_ (norm_nonneg _) (Real.sqrt_nonneg _)
    unfold dtrap
    calc ‖(Ioo x (x + r)).indicator (fun _ => 1 / r) s -
          (Ioo y (y + r)).indicator (fun _ => 1 / r) s‖
        ≤ ‖(Ioo x (x + r)).indicator (fun _ => 1 / r) s‖ +
            ‖(Ioo y (y + r)).indicator (fun _ => 1 / r) s‖ := norm_sub_le _ _
      _ ≤ ‖(1 / r : ℝ)‖ + ‖(1 / r : ℝ)‖ :=
          add_le_add (norm_indicator_le_norm_self _ _) (norm_indicator_le_norm_self _ _)
      _ = 2 * |1 / r| := by rw [Real.norm_eq_abs]; ring

/-- The trapezoid variation as a vector. -/
def vtrap (θ : Params) (x y r : ℝ) : H θ :=
  (memLp_vtrap (θ := θ) (x := x) (y := y) (r := r)).toLp _

theorem vtrap_ae : ∀ᵐ s ∂(μ θ), vtrap θ x y r s = Real.sqrt s * dtrap x y r s :=
  (memLp_vtrap (θ := θ) (x := x) (y := y) (r := r)).coeFn_toLp

theorem vtrap_ae' : ∀ᵐ s, s ∈ Ioc θ.c θ.ξ₀ → vtrap θ x y r s = Real.sqrt s * dtrap x y r s :=
  (ae_restrict_iff' measurableSet_Ioc).mp vtrap_ae

theorem zfun_vtrap (hr : 0 < r) (hxy : x + r ≤ y) (hyξ : y + r ≤ θ.ξ₀) {ξ : ℝ}
    (hξ : ξ ∈ Icc θ.c θ.ξ₀) (hξ0 : 0 < ξ) : zfun θ (vtrap θ x y r) ξ = trap x y r ξ := by
  rw [zfun_eq_integral θ _ hξ0 hξ.1 hξ.2]
  have hae : ∀ᵐ s, s ∈ Ι ξ θ.ξ₀ → vtrap θ x y r s / Real.sqrt s = dtrap x y r s := by
    filter_upwards [vtrap_ae' (θ := θ) (x := x) (y := y) (r := r)] with s hs hsI
    rw [uIoc_of_le hξ.2] at hsI
    have hsI' : s ∈ Ioc θ.c θ.ξ₀ := ⟨lt_of_le_of_lt hξ.1 hsI.1, hsI.2⟩
    have hs0 : 0 < s := hξ0.trans hsI.1
    rw [hs hsI']
    exact mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hs0).ne'
  rw [intervalIntegral.integral_congr_ae hae, integral_dtrap hr hxy hξ.2 hyξ, neg_neg]

theorem inner_vtrap (w : H θ) (hr : 0 < r) (hcx : θ.c ≤ x) (hxy : x + r ≤ y)
    (hyξ : y + r ≤ θ.ξ₀) :
    ⟪w, vtrap θ x y r⟫ =
      (r⁻¹ * ∫ s in x..x + r, omega w s) - r⁻¹ * ∫ s in y..y + r, omega w s := by
  rw [inner_eq_integral]
  have hae : (fun s => w s * vtrap θ x y r s) =ᵐ[μ θ] fun s =>
      (Ioo x (x + r)).indicator (fun s => r⁻¹ * omega w s) s -
        (Ioo y (y + r)).indicator (fun s => r⁻¹ * omega w s) s := by
    filter_upwards [vtrap_ae (θ := θ) (x := x) (y := y) (r := r)] with s hs
    rw [hs]
    unfold dtrap omega
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  rw [integral_congr_ae hae]
  have hsub1 : Ioo x (x + r) ⊆ Ioc θ.c θ.ξ₀ := fun s hs =>
    ⟨lt_of_le_of_lt hcx hs.1, by linarith [hs.2]⟩
  have hsub2 : Ioo y (y + r) ⊆ Ioc θ.c θ.ξ₀ := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hf : IntegrableOn (fun s => r⁻¹ * omega w s) (Ioc θ.c θ.ξ₀) volume :=
    (integrableOn_omega w).const_mul r⁻¹
  rw [integral_sub (integrable_indicator_μ hsub1 hf) (integrable_indicator_μ hsub2 hf),
    integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioo,
    setIntegral_μ_Ioo (by linarith) hsub1, setIntegral_μ_Ioo (by linarith) hsub2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem tendsto_inner_vtrap (w : H θ) (hcx : θ.c ≤ x) (hxy : x < y) (hyξ : y < θ.ξ₀)
    (hx : IsLeb w x) (hy : IsLeb w y) :
    Tendsto (fun r => ⟪w, vtrap θ x y r⟫) (𝓝[>] 0) (𝓝 (omega w x - omega w y)) := by
  have h := (tendsto_avg w hx hcx (hxy.trans hyξ)).sub
    (tendsto_avg w hy (hcx.trans hxy.le) hyξ)
  refine h.congr' ?_
  have hε : 0 < min (y - x) (θ.ξ₀ - y) := lt_min (by linarith) (by linarith)
  filter_upwards [eventually_small hε] with r hr
  have h1 : x + r ≤ y := by linarith [hr.2, min_le_left (y - x) (θ.ξ₀ - y)]
  have h2 : y + r ≤ θ.ξ₀ := by linarith [hr.2, min_le_right (y - x) (θ.ξ₀ - y)]
  exact (inner_vtrap w hr.1 hcx h1 h2).symm

theorem tendsto_trap_indicator (hxy : x < y) (f : ℝ → ℝ) (s : ℝ) :
    Tendsto (fun r => f s * trap x y r s) (𝓝[>] 0) (𝓝 ((Ioc x y).indicator f s)) := by
  have hε : 0 < y - x := by linarith
  by_cases h1 : s ≤ x
  · rw [indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr h1))]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_small hε] with r hr
    rw [trap_of_le hr.1 (by linarith [hr.2]) h1, mul_zero]
  by_cases h2 : s ≤ y
  · have hs : s ∈ Ioc x y := ⟨not_le.mp h1, h2⟩
    rw [indicator_of_mem hs]
    refine tendsto_const_nhds.congr' ?_
    have hε' : 0 < min (y - x) (s - x) := lt_min hε (by linarith [not_le.mp h1])
    filter_upwards [eventually_small hε'] with r hr
    rw [trap_of_mid hr.1 (by linarith [hr.2, min_le_left (y - x) (s - x)])
      (by linarith [hr.2, min_le_right (y - x) (s - x)]) h2, mul_one]
  · rw [indicator_of_notMem (fun h => h2 h.2)]
    refine tendsto_const_nhds.congr' ?_
    have hε' : 0 < min (y - x) (s - y) := lt_min hε (by linarith [not_le.mp h2])
    filter_upwards [eventually_small hε'] with r hr
    rw [trap_of_ge hr.1 (by linarith [hr.2, min_le_left (y - x) (s - y)])
      (by linarith [hr.2, min_le_right (y - x) (s - y)]), mul_zero]

theorem tendsto_int_trap (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) (hcx : θ.c ≤ x)
    (hxy : x < y) (hyξ : y ≤ θ.ξ₀) :
    Tendsto (fun r => ∫ s, Real.exp (-2 * zfun θ w s) * trap x y r s ∂(μ θ)) (𝓝[>] 0)
      (𝓝 (∫ s in x..y, Real.exp (-2 * zfun θ w s))) := by
  have hsub : Ioc x y ⊆ Ioc θ.c θ.ξ₀ := Ioc_subset_Ioc hcx hyξ
  rw [← setIntegral_μ_Ioc hxy.le hsub, ← integral_indicator measurableSet_Ioc]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (θ.p ^ 2)⁻¹) ?_ ?_
    (integrable_const _) (Eventually.of_forall fun s =>
      tendsto_trap_indicator hxy (fun s => Real.exp (-2 * zfun θ w s)) s)
  · exact Eventually.of_forall fun r =>
      (aesm_exp hθ w).mul (continuous_trap x y r).aestronglyMeasurable
  · have hε : 0 < y - x := by linarith
    filter_upwards [eventually_small hε] with r hr
    filter_upwards [ae_mem_I] with s hs
    have hr' : x + r ≤ y := by linarith [hr.2]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_nonneg (trap_nonneg hr.1 hr' s)]
    calc Real.exp (-2 * zfun θ w s) * trap x y r s ≤ (θ.p ^ 2)⁻¹ * 1 :=
          mul_le_mul (exp_le hθ hw hs) (trap_le_one hr.1 hr' s) (trap_nonneg hr.1 hr' s)
            (by have := hθ.p_pos; positivity)
      _ = (θ.p ^ 2)⁻¹ := mul_one _

end Trap

variable (d : ℝ)

/-- Pushing down where the lower obstacle is slack. -/
theorem two_point_down (hθ : θ.Admissible) (hd : 0 ≤ d) {w : H θ} (hw : w ∈ W θ)
    (hmin : ∀ v ∈ W θ, J θ d w ≤ J θ d v) {x y y' κ : ℝ} (hcx : θ.c < x) (hxy : x < y)
    (hyy' : y < y') (hy'ξ : y' ≤ θ.ξ₀) (hκ : 0 < κ)
    (hslack : ∀ ξ ∈ Icc x y', Real.log θ.p + κ ≤ zfun θ w ξ) (hx : IsLeb w x) (hy : IsLeb w y) :
    omega w x - omega w y ≤ d * ∫ s in x..y, Real.exp (-2 * zfun θ w s) := by
  have hyξ : y < θ.ξ₀ := hyy'.trans_le hy'ξ
  refine le_of_tendsto_of_tendsto (tendsto_inner_vtrap w hcx.le hxy hyξ hx hy)
    ((tendsto_int_trap hθ hw hcx.le hxy hyξ.le).const_mul d) ?_
  have hε : 0 < min (y - x) (y' - y) := lt_min (by linarith) (by linarith)
  filter_upwards [eventually_small hε] with r hr
  have hr0 := hr.1
  have hr1 : x + r ≤ y := by linarith [hr.2, min_le_left (y - x) (y' - y)]
  have hr2 : y + r ≤ y' := by linarith [hr.2, min_le_right (y - x) (y' - y)]
  have hr3 : y + r ≤ θ.ξ₀ := hr2.trans hy'ξ
  have hadm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), w + ε • (-vtrap θ x y r) ∈ W θ := by
    filter_upwards [eventually_small hκ] with ε hε
    intro ξ hξ hξ0
    obtain ⟨h1, h2⟩ := hw ξ hξ hξ0
    rw [zfun_add, zfun_smul, zfun_neg, zfun_vtrap hr0 hr1 hr3 hξ hξ0]
    have ht0 := trap_nonneg hr0 hr1 ξ
    have ht1 := trap_le_one hr0 hr1 ξ
    have hεt : ε * trap x y r ξ ≤ ε := mul_le_of_le_one_right hε.1.le ht1
    have hεt0 : 0 ≤ ε * trap x y r ξ := mul_nonneg hε.1.le ht0
    constructor
    · by_cases hsupp : ξ ∈ Icc x y'
      · have := hslack ξ hsupp
        linarith [hε.2]
      · have ht : trap x y r ξ = 0 := by
          rw [mem_Icc, not_and_or, not_le, not_le] at hsupp
          rcases hsupp with h | h
          · exact trap_of_le hr0 hr1 h.le
          · exact trap_of_ge hr0 hr1 (by linarith)
        rw [ht]; linarith
    · linarith
  have hφ : ∀ s ∈ Ioc θ.c θ.ξ₀, zfun θ (-vtrap θ x y r) s = (fun s => -trap x y r s) s := by
    intro s hs
    rw [zfun_neg, zfun_vtrap hr0 hr1 hr3 ⟨hs.1.le, hs.2⟩ (lt_of_le_of_lt hθ.c_nonneg hs.1)]
  have hM : ∀ s, |(fun s => -trap x y r s) s| ≤ 1 := fun s => by
    simp only [abs_neg]
    rw [abs_of_nonneg (trap_nonneg hr0 hr1 s)]
    exact trap_le_one hr0 hr1 s
  have hvar := var_ineq d hθ hd hw hmin hφ hM (continuous_trap x y r).neg.measurable hadm
  rw [inner_neg_right] at hvar
  have e : ∫ s, Real.exp (-2 * zfun θ w s) * (fun s => -trap x y r s) s ∂(μ θ) =
      -∫ s, Real.exp (-2 * zfun θ w s) * trap x y r s ∂(μ θ) := by
    rw [← integral_neg]; congr 1; ext s; ring
  rw [e] at hvar
  linarith

/-- Pushing up where the upper obstacle is slack. -/
theorem two_point_up (hθ : θ.Admissible) (hd : 0 ≤ d) {w : H θ} (hw : w ∈ W θ)
    (hmin : ∀ v ∈ W θ, J θ d w ≤ J θ d v) {x y y' κ : ℝ} (hcx : θ.c < x) (hxy : x < y)
    (hyy' : y < y') (hy'ξ : y' ≤ θ.ξ₀) (hκ : 0 < κ)
    (hslack : ∀ ξ ∈ Icc x y', zfun θ w ξ + κ ≤ Real.log (θ.U ξ)) (hx : IsLeb w x)
    (hy : IsLeb w y) :
    d * ∫ s in x..y, Real.exp (-2 * zfun θ w s) ≤ omega w x - omega w y := by
  have hyξ : y < θ.ξ₀ := hyy'.trans_le hy'ξ
  refine le_of_tendsto_of_tendsto ((tendsto_int_trap hθ hw hcx.le hxy hyξ.le).const_mul d)
    (tendsto_inner_vtrap w hcx.le hxy hyξ hx hy) ?_
  have hε : 0 < min (y - x) (y' - y) := lt_min (by linarith) (by linarith)
  filter_upwards [eventually_small hε] with r hr
  have hr0 := hr.1
  have hr1 : x + r ≤ y := by linarith [hr.2, min_le_left (y - x) (y' - y)]
  have hr2 : y + r ≤ y' := by linarith [hr.2, min_le_right (y - x) (y' - y)]
  have hr3 : y + r ≤ θ.ξ₀ := hr2.trans hy'ξ
  have hadm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), w + ε • vtrap θ x y r ∈ W θ := by
    filter_upwards [eventually_small hκ] with ε hε
    intro ξ hξ hξ0
    obtain ⟨h1, h2⟩ := hw ξ hξ hξ0
    rw [zfun_add, zfun_smul, zfun_vtrap hr0 hr1 hr3 hξ hξ0]
    have ht0 := trap_nonneg hr0 hr1 ξ
    have ht1 := trap_le_one hr0 hr1 ξ
    have hεt : ε * trap x y r ξ ≤ ε := mul_le_of_le_one_right hε.1.le ht1
    have hεt0 : 0 ≤ ε * trap x y r ξ := mul_nonneg hε.1.le ht0
    constructor
    · linarith
    · by_cases hsupp : ξ ∈ Icc x y'
      · have := hslack ξ hsupp
        linarith [hε.2]
      · have ht : trap x y r ξ = 0 := by
          rw [mem_Icc, not_and_or, not_le, not_le] at hsupp
          rcases hsupp with h | h
          · exact trap_of_le hr0 hr1 h.le
          · exact trap_of_ge hr0 hr1 (by linarith)
        rw [ht]; linarith
  have hφ : ∀ s ∈ Ioc θ.c θ.ξ₀, zfun θ (vtrap θ x y r) s = trap x y r s := fun s hs =>
    zfun_vtrap hr0 hr1 hr3 ⟨hs.1.le, hs.2⟩ (lt_of_le_of_lt hθ.c_nonneg hs.1)
  have hM : ∀ s, |trap x y r s| ≤ 1 := fun s => by
    rw [abs_of_nonneg (trap_nonneg hr0 hr1 s)]
    exact trap_le_one hr0 hr1 s
  exact var_ineq d hθ hd hw hmin hφ hM (continuous_trap x y r).measurable hadm

end Relaxed

end FixedPrice.TwoUnit.Family
