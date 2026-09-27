import FixedPrice.TwoUnit.Family.ShapeSpace

/-!
# Work package B, part 2: existence and uniqueness of the relaxed minimizer

On the obstacle class `W`, `e^{-2z} ≤ p_f^{-2}`, so the energy is finite and bounded below by
`0`. The parallelogram law and the convexity of `exp` give
`J((u+v)/2) ≤ (J u + J v)/2 - ‖u - v‖²/4`. A minimizing sequence is therefore Cauchy; its limit
lies in the closed class, and the energy converges along it (continuity of `z(ξ)` in `w` and
dominated convergence), so the limit is a minimizer; the same inequality makes it unique.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

theorem integrableOn_w (w : H θ) : IntegrableOn (fun s => w s) (Ioc θ.c θ.ξ₀) volume := by
  have := (Lp.memLp w).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact this

theorem integrableOn_div_sqrt (w : H θ) {a : ℝ} (ha0 : 0 < a) (hca : θ.c ≤ a) :
    IntegrableOn (fun s => w s / Real.sqrt s) (Ioc a θ.ξ₀) volume := by
  have hw : IntegrableOn (fun s => w s) (Ioc a θ.ξ₀) volume :=
    (integrableOn_w w).mono_set (Ioc_subset_Ioc_left hca)
  refine (hw.norm.const_mul (1 / Real.sqrt a)).mono' ?_ ?_
  · exact (((Lp.aestronglyMeasurable w).mono_measure
      (Measure.restrict_mono (Ioc_subset_Ioc_left hca) le_rfl)).aemeasurable.div
      Real.continuous_sqrt.measurable.aemeasurable).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := ha0.trans hs.1
    rw [norm_div, Real.norm_of_nonneg (Real.sqrt_nonneg s), div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (by
      rw [one_div]; exact inv_anti₀ (Real.sqrt_pos.mpr ha0) (Real.sqrt_le_sqrt hs.1.le))
      (norm_nonneg _)

theorem continuousOn_zfun (hθ : θ.Admissible) (w : H θ) :
    ContinuousOn (zfun θ w) (Ioc θ.c θ.ξ₀) := by
  intro ξ hξ
  have hc0 := hθ.c_nonneg
  have hξ0 : 0 < ξ := lt_of_le_of_lt hc0 hξ.1
  set a := max (ξ / 2) θ.c with ha
  have haξ : a < ξ := max_lt (by linarith) hξ.1
  have ha0 : 0 < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hca : θ.c ≤ a := le_max_right _ _
  have haξ₀ : a ≤ θ.ξ₀ := haξ.le.trans hξ.2
  have hint : IntegrableOn (fun s => w s / Real.sqrt s) (uIcc a θ.ξ₀) volume := by
    rw [uIcc_of_le haξ₀, integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_div_sqrt w ha0 hca
  have hprim := intervalIntegral.continuousOn_primitive_interval hint
  rw [uIcc_of_le haξ₀] at hprim
  -- on `[a, ξ₀]`, `z(x) = ∫_a^x f - ∫_a^{ξ₀} f`
  have heq : ∀ x ∈ Icc a θ.ξ₀ ∩ Ioc θ.c θ.ξ₀, zfun θ w x =
      (∫ s in a..x, w s / Real.sqrt s) - ∫ s in a..θ.ξ₀, w s / Real.sqrt s := by
    intro x hx
    rw [zfun_eq_integral θ w (ha0.trans_le hx.1.1) hx.2.1.le hx.2.2]
    have hi1 : IntervalIntegrable (fun s => w s / Real.sqrt s) volume a x := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1.1]
      exact (integrableOn_div_sqrt w ha0 hca).mono_set (Ioc_subset_Ioc_right hx.1.2)
    have hi2 : IntervalIntegrable (fun s => w s / Real.sqrt s) volume x θ.ξ₀ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1.2]
      exact (integrableOn_div_sqrt w ha0 hca).mono_set (Ioc_subset_Ioc_left hx.1.1)
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    ring
  have hcont : ContinuousWithinAt (fun x => (∫ s in a..x, w s / Real.sqrt s) -
      ∫ s in a..θ.ξ₀, w s / Real.sqrt s) (Icc a θ.ξ₀ ∩ Ioc θ.c θ.ξ₀) ξ :=
    ((hprim ξ ⟨haξ.le, hξ.2⟩).sub continuousWithinAt_const).mono inter_subset_left
  have hcont' := hcont.congr (fun x hx => heq x hx) (heq ξ ⟨⟨haξ.le, hξ.2⟩, hξ⟩)
  refine hcont'.mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.mpr ⟨Ioi a, isOpen_Ioi, haξ, fun x hx => ⟨⟨hx.1.le, hx.2.2⟩, hx.2⟩⟩

theorem ae_mem_I : ∀ᵐ s ∂(μ θ), s ∈ Ioc θ.c θ.ξ₀ :=
  show ∀ᵐ s ∂(volume.restrict (Ioc θ.c θ.ξ₀)), s ∈ Ioc θ.c θ.ξ₀ from
    ae_restrict_mem measurableSet_Ioc

/-- On the obstacle class, `e^{-2z} ≤ p^{-2}` on the curve interval. -/
theorem exp_le (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) {s : ℝ} (hs : s ∈ Ioc θ.c θ.ξ₀) :
    Real.exp (-2 * zfun θ w s) ≤ (θ.p ^ 2)⁻¹ := by
  have hs0 : 0 < s := lt_of_le_of_lt hθ.c_nonneg hs.1
  have h := (hw s ⟨hs.1.le, hs.2⟩ hs0).1
  have hp := hθ.p_pos
  have e : -2 * Real.log θ.p = Real.log ((θ.p ^ 2)⁻¹) := by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  calc Real.exp (-2 * zfun θ w s) ≤ Real.exp (-2 * Real.log θ.p) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = (θ.p ^ 2)⁻¹ := by rw [e, Real.exp_log (by positivity)]

theorem aesm_exp (hθ : θ.Admissible) (w : H θ) :
    AEStronglyMeasurable (fun s => Real.exp (-2 * zfun θ w s)) (μ θ) :=
  (Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (continuousOn_zfun hθ w))).aestronglyMeasurable measurableSet_Ioc

theorem integrable_exp (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) :
    Integrable (fun s => Real.exp (-2 * zfun θ w s)) (μ θ) := by
  refine Integrable.of_bound (aesm_exp hθ w) ((θ.p ^ 2)⁻¹) ?_
  filter_upwards [ae_mem_I] with s hs
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_le hθ hw hs

variable (d : ℝ)

theorem J_nonneg (hd : 0 ≤ d) (w : H θ) : 0 ≤ J θ d w := by
  unfold J
  have : 0 ≤ ∫ s, Real.exp (-2 * zfun θ w s) ∂(μ θ) :=
    integral_nonneg fun s => (Real.exp_pos _).le
  positivity

theorem exp_mid_le (a b : ℝ) :
    Real.exp (-2 * ((1 / 2 : ℝ) * (a + b))) ≤ (Real.exp (-2 * a) + Real.exp (-2 * b)) / 2 := by
  have e1 : Real.exp (-2 * ((1 / 2 : ℝ) * (a + b))) = Real.exp (-a) * Real.exp (-b) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-2 * a) = Real.exp (-a) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have e3 : Real.exp (-2 * b) = Real.exp (-b) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [e1, e2, e3]
  nlinarith [sq_nonneg (Real.exp (-a) - Real.exp (-b))]

theorem mid_mem (u v : H θ) (hu : u ∈ W θ) (hv : v ∈ W θ) :
    (1 / 2 : ℝ) • (u + v) ∈ W θ := by
  rw [smul_add]
  exact convex_W θ hu hv (by norm_num) (by norm_num) (by norm_num)

/-- Uniform convexity of the energy. -/
theorem J_mid_le (hθ : θ.Admissible) (hd : 0 ≤ d) {u v : H θ} (hu : u ∈ W θ) (hv : v ∈ W θ) :
    J θ d ((1 / 2 : ℝ) • (u + v)) ≤ (J θ d u + J θ d v) / 2 - ‖u - v‖ ^ 2 / 4 := by
  unfold J
  have hnorm : ‖(1 / 2 : ℝ) • (u + v)‖ ^ 2 = (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 - ‖u - v‖ ^ 2 / 4 := by
    rw [norm_smul, mul_pow]
    have := parallelogram_law_with_norm ℝ u v
    norm_num
    linarith
  have hexp : ∫ s, Real.exp (-2 * zfun θ ((1 / 2 : ℝ) • (u + v)) s) ∂(μ θ) ≤
      (∫ s, Real.exp (-2 * zfun θ u s) ∂(μ θ) + ∫ s, Real.exp (-2 * zfun θ v s) ∂(μ θ)) / 2 := by
    rw [← integral_add (integrable_exp hθ hu) (integrable_exp hθ hv), ← integral_div]
    refine integral_mono (integrable_exp hθ (mid_mem u v hu hv))
      (((integrable_exp hθ hu).add (integrable_exp hθ hv)).div_const 2) fun s => ?_
    rw [zfun_smul, zfun_add]
    exact exp_mid_le _ _
  rw [hnorm]
  nlinarith [mul_le_mul_of_nonneg_left hexp hd]

theorem J_tendsto (hθ : θ.Admissible) {w : ℕ → H θ} {w₀ : H θ} (hw : ∀ n, w n ∈ W θ)
    (hw₀ : w₀ ∈ W θ) (hlim : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun n => J θ d (w n)) atTop (𝓝 (J θ d w₀)) := by
  unfold J
  refine ((continuous_norm.tendsto w₀).comp hlim).pow 2 |>.add (Tendsto.const_mul d ?_)
  refine tendsto_integral_of_dominated_convergence (fun _ => (θ.p ^ 2)⁻¹)
    (fun n => aesm_exp hθ (w n)) (integrable_const _) (fun n => ?_) ?_
  · filter_upwards [ae_mem_I] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_le hθ (hw n) hs
  · refine Eventually.of_forall fun s => ?_
    exact (Real.continuous_exp.tendsto _).comp
      ((((continuous_zfun θ s).tendsto w₀).comp hlim).const_mul (-2))

/-- Existence of the relaxed minimizer. -/
theorem exists_minimizer (hθ : θ.Admissible) (hd : 0 ≤ d) (hne : (W θ).Nonempty) :
    ∃ w ∈ W θ, ∀ v ∈ W θ, J θ d w ≤ J θ d v := by
  set S := J θ d '' W θ with hS
  have hSne : S.Nonempty := hne.image _
  have hSbdd : BddBelow S := ⟨0, by rintro _ ⟨v, -, rfl⟩; exact J_nonneg d hd v⟩
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sInf hSne hSbdd
  choose w hwW hwJ using huS
  have hcauchy : CauchySeq w := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε2 : sInf S < sInf S + ε ^ 2 / 8 := by linarith [pow_pos hε 2]
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.eventually (gt_mem_nhds hε2))
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmid := J_mid_le d hθ hd (hwW m) (hwW n)
    have hge : sInf S ≤ J θ d ((1 / 2 : ℝ) • (w m + w n)) :=
      csInf_le hSbdd ⟨_, mid_mem _ _ (hwW m) (hwW n), rfl⟩
    rw [hwJ, hwJ] at hmid
    have h1 := hN m hm
    have h2 := hN n hn
    have hsq : ‖w m - w n‖ ^ 2 < ε ^ 2 := by nlinarith
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq
  obtain ⟨w₀, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hw₀ : w₀ ∈ W θ := (isClosed_W θ).mem_of_tendsto hlim (Eventually.of_forall hwW)
  have hJ := J_tendsto d hθ hwW hw₀ hlim
  have hJ' : Tendsto (fun n => J θ d (w n)) atTop (𝓝 (sInf S)) := by
    simp only [hwJ]; exact hu
  have hval : J θ d w₀ = sInf S := tendsto_nhds_unique hJ hJ'
  exact ⟨w₀, hw₀, fun v hv => hval ▸ csInf_le hSbdd ⟨v, hv, rfl⟩⟩

/-- Uniqueness of the relaxed minimizer. -/
theorem minimizer_unique (hθ : θ.Admissible) (hd : 0 ≤ d) {u v : H θ} (hu : u ∈ W θ)
    (hv : v ∈ W θ) (humin : ∀ x ∈ W θ, J θ d u ≤ J θ d x)
    (hvmin : ∀ x ∈ W θ, J θ d v ≤ J θ d x) : u = v := by
  have hmid := J_mid_le d hθ hd hu hv
  have h1 := humin _ (mid_mem u v hu hv)
  have h2 := hvmin u hu
  have h3 := humin v hv
  have hsq : ‖u - v‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Relaxed

end FixedPrice.TwoUnit.Family
