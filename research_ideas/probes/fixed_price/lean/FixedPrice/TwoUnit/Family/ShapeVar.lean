import FixedPrice.TwoUnit.Family.ShapeClass

/-!
# Work package B, part 4: the first variation at the relaxed minimizer

If `w` minimizes `J` on the obstacle class and `w + εv` stays admissible for small `ε > 0`, where
`z_v = φ` is bounded, then `d ∫ e^{-2z_w} φ ≤ ⟪w, v⟫`. Indeed
`J(w + εv) - J(w) = 2ε⟪w, v⟫ + ε²‖v‖² - 2ε · d ∫ e^{-2z_w} (1 - e^{-2εφ})/(2ε)`, and the last
integral tends to `∫ e^{-2z_w} φ` by dominated convergence.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params} (d : ℝ)

theorem tendsto_one_sub_exp (x : ℝ) :
    Tendsto (fun ε : ℝ => (1 - Real.exp (-2 * ε * x)) / (2 * ε)) (𝓝[>] 0) (𝓝 x) := by
  have hd : HasDerivAt (fun ε : ℝ => Real.exp (-2 * ε * x)) (-2 * x) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => -2 * ε * x) (-2 * x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-2)).mul_const x
    have h2 := h1.exp
    simpa using h2
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono _ (fun ε (hε : 0 < ε) => ne_of_gt hε))
  have := hs.const_mul (-1 / 2)
  refine (this.congr' ?_).trans_eq (by ring)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  rw [slope_def_field]
  simp only [mul_zero, zero_mul, Real.exp_zero, sub_zero]
  field_simp
  ring

theorem abs_one_sub_exp_le {ε x M : ℝ} (hε : 0 < ε) (hx : |x| ≤ M) (hεM : 2 * ε * M ≤ 1) :
    |(1 - Real.exp (-2 * ε * x)) / (2 * ε)| ≤ 2 * M := by
  have hy : |-2 * ε * x| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos hε]
    nlinarith [abs_nonneg x]
  have h := Real.abs_exp_sub_one_le hy
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε), div_le_iff₀ (by positivity),
    abs_sub_comm]
  calc |Real.exp (-2 * ε * x) - 1| ≤ 2 * |-2 * ε * x| := h
    _ = 2 * M * (2 * ε) - 2 * (2 * ε) * (M - |x|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos hε]; ring
    _ ≤ 2 * M * (2 * ε) := by nlinarith [abs_nonneg x, hx]

/-- The first variation at the relaxed minimizer. -/
theorem var_ineq (hθ : θ.Admissible) (hd : 0 ≤ d) {w : H θ} (hw : w ∈ W θ)
    (hmin : ∀ x ∈ W θ, J θ d w ≤ J θ d x) {v : H θ} {φ : ℝ → ℝ}
    (hφ : ∀ s ∈ Ioc θ.c θ.ξ₀, zfun θ v s = φ s) {M : ℝ} (hM : ∀ s, |φ s| ≤ M)
    (hφm : Measurable φ) (hadm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), w + ε • v ∈ W θ) :
    d * ∫ s, Real.exp (-2 * zfun θ w s) * φ s ∂(μ θ) ≤ ⟪w, v⟫ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- the difference quotients of the exponential term
  set G : ℝ → ℝ := fun ε =>
    ∫ s, Real.exp (-2 * zfun θ w s) * ((1 - Real.exp (-2 * ε * φ s)) / (2 * ε)) ∂(μ θ) with hG
  have hGlim : Tendsto G (𝓝[>] 0) (𝓝 (∫ s, Real.exp (-2 * zfun θ w s) * φ s ∂(μ θ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (θ.p ^ 2)⁻¹ * (2 * M))
      ?_ ?_ (integrable_const _) ?_
    · refine Eventually.of_forall fun ε => ?_
      exact (aesm_exp hθ w).mul (((measurable_const.sub
        ((measurable_const.mul hφm).exp)).div_const _).aestronglyMeasurable)
    · have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ 2 * ε * M ≤ 1 := by
        have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
        have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε * M ≤ 1 := by
          have : Tendsto (fun ε : ℝ => 2 * ε * M) (𝓝[>] 0) (𝓝 0) := by
            have hc : Continuous fun ε : ℝ => 2 * ε * M :=
              (continuous_const.mul continuous_id).mul continuous_const
            simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
          exact this.eventually (ge_mem_nhds (by norm_num))
        exact h1.and h2
      filter_upwards [hsmall] with ε hε
      filter_upwards [ae_mem_I] with s hs
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact mul_le_mul (exp_le hθ hw hs) (abs_one_sub_exp_le hε.1 (hM s) hε.2) (abs_nonneg _)
        (by positivity)
    · exact Eventually.of_forall fun s => (tendsto_one_sub_exp (φ s)).const_mul _
  -- the inequality for small `ε > 0`
  have hineq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), d * G ε ≤ ⟪w, v⟫ + ε * ‖v‖ ^ 2 / 2 := by
    filter_upwards [hadm, self_mem_nhdsWithin] with ε hεW hε
    have hε0 : (0 : ℝ) < ε := hε
    have hJ := hmin _ hεW
    unfold J at hJ
    have hnorm : ‖w + ε • v‖ ^ 2 = ‖w‖ ^ 2 + 2 * ε * ⟪w, v⟫ + ε ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    have hz : ∀ s ∈ Ioc θ.c θ.ξ₀, zfun θ (w + ε • v) s = zfun θ w s + ε * φ s := fun s hs => by
      rw [zfun_add, zfun_smul, hφ s hs]
    have hint : ∫ s, Real.exp (-2 * zfun θ (w + ε • v) s) ∂(μ θ) =
        ∫ s, Real.exp (-2 * zfun θ w s) ∂(μ θ) -
          2 * ε * G ε := by
      rw [hG]
      simp only []
      rw [← integral_const_mul, ← integral_sub (integrable_exp hθ hw)]
      · refine integral_congr_ae ?_
        filter_upwards [ae_mem_I] with s hs
        rw [hz s hs]
        have : Real.exp (-2 * (zfun θ w s + ε * φ s)) =
            Real.exp (-2 * zfun θ w s) * Real.exp (-2 * ε * φ s) := by
          rw [← Real.exp_add]; ring_nf
        rw [this]
        field_simp
        ring
      · refine (Integrable.of_bound ((aesm_exp hθ w).mul (((measurable_const.sub
          ((measurable_const.mul hφm).exp)).div_const _).aestronglyMeasurable))
          ((θ.p ^ 2)⁻¹ * (Real.exp (2 * ε * M) + 1) / (2 * ε)) ?_).const_mul _
        filter_upwards [ae_mem_I] with s hs
        show ‖Real.exp (-2 * zfun θ w s) * ((1 - Real.exp (-2 * ε * φ s)) / (2 * ε))‖ ≤ _
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
          abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε), mul_div_assoc]
        refine mul_le_mul (exp_le hθ hw hs) (div_le_div_of_nonneg_right ?_ (by positivity))
          (by positivity) (by positivity)
        calc |1 - Real.exp (-2 * ε * φ s)| ≤ 1 + Real.exp (-2 * ε * φ s) := by
              rw [abs_le]; constructor <;> linarith [Real.exp_pos (-2 * ε * φ s)]
          _ ≤ Real.exp (2 * ε * M) + 1 := by
              have : -2 * ε * φ s ≤ 2 * ε * M := by
                have := hM s; rw [abs_le] at this; nlinarith
              linarith [Real.exp_le_exp.mpr this]
    rw [hnorm, hint] at hJ
    have : 0 ≤ 2 * ε * (⟪w, v⟫ + ε * ‖v‖ ^ 2 / 2 - d * G ε) := by nlinarith
    have := nonneg_of_mul_nonneg_right (by linarith [this] : 0 ≤ (2 * ε) *
      (⟪w, v⟫ + ε * ‖v‖ ^ 2 / 2 - d * G ε)) (by positivity)
    linarith
  have hR : Tendsto (fun ε => ⟪w, v⟫ + ε * ‖v‖ ^ 2 / 2) (𝓝[>] 0) (𝓝 ⟪w, v⟫) := by
    have hc : Continuous fun ε : ℝ => ⟪w, v⟫ + ε * ‖v‖ ^ 2 / 2 :=
      continuous_const.add ((continuous_id.mul continuous_const).div_const 2)
    simpa using (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  exact le_of_tendsto_of_tendsto (hGlim.const_mul d) hR hineq

end Relaxed

end FixedPrice.TwoUnit.Family
