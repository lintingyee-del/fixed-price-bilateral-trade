import FixedPrice.TwoUnit.Family.BasicClass

/-!
# Work package A, helpers: integrals over a class member

* Almost everywhere on `[c_f, ξ₀]`: `h_f ≤ P' ≤ 1`, `(log P)' = P'/P`, `(1/P)' = -P'/P²`, and
  `0 ≤ P - ξP' ≤ 1/N_f`.
* The integrands of `T_f`, `Q_f`, `E_f` are integrable; `s_f' = P⁻²` within `[c_f, ξ₀]`.
* `∫ P'/P = -log p_f`, `∫ P'/P² = 1/p_f - 1`, `T_f ≥ ξ₀ - c_f`.
* The moving-endpoint dominated convergence lemma.
* Positivity (`G_f ≥ 2`, `G_f ≤ 2/m_f`, `M_f ≥ 0`, `m_f ≤ R_f ≤ 1`) and the comparison identities
  (`E_f = Q_f + d_f T_f`, `K_f = Kconst - E_f`, the ratio form), with the certified identities
  `buyer_mean`, `comparison_second_form`, `ratio_comparison`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

namespace InClass

variable {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
include hP

theorem ae_Icc_iff {q : ℝ → Prop} :
    (∀ᵐ x ∂(volume.restrict (Icc θ.c θ.ξ₀)), q x) → ∀ᵐ x, x ∈ Ι θ.c θ.ξ₀ → q x := by
  intro h
  have h' := (ae_restrict_iff' measurableSet_Icc).mp h
  filter_upwards [h'] with x hx hxI
  rw [uIoc_of_le hP.c_le_ξ₀] at hxI
  exact hx (Ioc_subset_Icc_self hxI)

theorem ae_deriv_bounds : ∀ᵐ ξ ∂(volume.restrict (Icc θ.c θ.ξ₀)),
    θ.h ≤ deriv P ξ ∧ deriv P ξ ≤ 1 := by
  filter_upwards [hP.ae_good] with x hx
  exact ⟨hP.h_le_deriv hx.1 hx.2, hP.deriv_le_one hx.1 hx.2⟩

theorem ae_deriv_log : ∀ᵐ ξ ∂(volume.restrict (Icc θ.c θ.ξ₀)),
    deriv (fun x => Real.log (P x)) ξ = deriv P ξ / P ξ := by
  filter_upwards [hP.ae_good] with x hx
  exact (hx.2.hasDerivAt.log (hP.pos' (Ioo_subset_Icc_self hx.1)).ne').deriv

theorem ae_deriv_inv : ∀ᵐ ξ ∂(volume.restrict (Icc θ.c θ.ξ₀)),
    deriv (fun x => (P x)⁻¹) ξ = -(deriv P ξ) / P ξ ^ 2 := by
  filter_upwards [hP.ae_good] with x hx
  exact (hx.2.hasDerivAt.inv (hP.pos' (Ioo_subset_Icc_self hx.1)).ne').deriv

theorem continuousOn_inv_sq : ContinuousOn (fun ξ => (P ξ ^ 2)⁻¹) (Icc θ.c θ.ξ₀) :=
  (hP.continuousOn.pow 2).inv₀ fun _ hx => pow_ne_zero 2 (hP.pos' hx).ne'

theorem intervalIntegrable_inv_sq : IntervalIntegrable (fun ξ => (P ξ ^ 2)⁻¹) volume θ.c θ.ξ₀ :=
  hP.continuousOn_inv_sq.intervalIntegrable_of_Icc hP.c_le_ξ₀

theorem aestronglyMeasurable_P : AEStronglyMeasurable P (volume.restrict (Icc θ.c θ.ξ₀)) :=
  hP.continuousOn.aestronglyMeasurable measurableSet_Icc

theorem aestronglyMeasurable_q :
    AEStronglyMeasurable (fun x => deriv P x / P x) (volume.restrict (Icc θ.c θ.ξ₀)) :=
  ((measurable_deriv P).aemeasurable.div hP.aestronglyMeasurable_P.aemeasurable).aestronglyMeasurable

theorem aestronglyMeasurable_q2 :
    AEStronglyMeasurable (fun x => deriv P x / P x ^ 2) (volume.restrict (Icc θ.c θ.ξ₀)) :=
  ((measurable_deriv P).aemeasurable.div
    (hP.aestronglyMeasurable_P.aemeasurable.pow_const 2)).aestronglyMeasurable

/-- A bounded measurable integrand in `ξ`, `P'` and `P` is integrable on the curve interval. -/
theorem intervalIntegrable_of_bound {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Icc θ.c θ.ξ₀))) {B : ℝ}
    (hB : ∀ᵐ x ∂(volume.restrict (Icc θ.c θ.ξ₀)), ‖f x‖ ≤ B) :
    IntervalIntegrable f volume θ.c θ.ξ₀ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hP.c_le_ξ₀]
  exact Integrable.of_bound hf B hB

theorem intervalIntegrable_Q : IntervalIntegrable (fun ξ => ξ * (deriv P ξ / P ξ) ^ 2) volume
    θ.c θ.ξ₀ := by
  have hp := hP.admissible.p_pos
  refine hP.intervalIntegrable_of_bound (B := θ.ξ₀ * (θ.p⁻¹) ^ 2) ?_ ?_
  · exact aestronglyMeasurable_id.mul (hP.aestronglyMeasurable_q.pow 2)
  · filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
    have hPx := hP.p_le hxm
    have hPpos := hP.pos' hxm
    have hd1 := hP.deriv_le_one hx.1 hx.2
    have hd0 := (hP.admissible.h_pos.le).trans (hP.h_le_deriv hx.1 hx.2)
    have hx0 : 0 ≤ x := hP.admissible.c_nonneg.trans hxm.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hq : deriv P x / P x ≤ θ.p⁻¹ := by
      rw [div_le_iff₀ hPpos]
      calc deriv P x ≤ 1 := hd1
        _ = θ.p⁻¹ * θ.p := by field_simp
        _ ≤ θ.p⁻¹ * P x := mul_le_mul_of_nonneg_left hPx (by positivity)
    have hq0 : 0 ≤ deriv P x / P x := div_nonneg hd0 hPpos.le
    calc x * (deriv P x / P x) ^ 2 ≤ θ.ξ₀ * (θ.p⁻¹) ^ 2 :=
          mul_le_mul hxm.2 (pow_le_pow_left₀ hq0 hq 2) (by positivity) (hP.admissible.ξ₀_pos.le)

theorem intervalIntegrable_E₁ : IntervalIntegrable
    (fun ξ => ξ * deriv (fun x => Real.log (P x)) ξ ^ 2) volume θ.c θ.ξ₀ := by
  refine hP.intervalIntegrable_Q.congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (by rw [uIoc_of_le hP.c_le_ξ₀]; exact Ioc_subset_Icc_self) hP.ae_deriv_log] with x hx
  rw [hx]

theorem hasDerivWithinAt_sF {x : ℝ} (hx : x ∈ Icc θ.c θ.ξ₀) :
    HasDerivWithinAt (sF θ P) ((P x ^ 2)⁻¹) (Icc θ.c θ.ξ₀) x := by
  haveI : Fact (x ∈ Icc θ.c θ.ξ₀) := ⟨hx⟩
  have hint : IntervalIntegrable (fun ξ => (P ξ ^ 2)⁻¹) volume θ.c x :=
    (hP.continuousOn_inv_sq.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
  have h := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc θ.c θ.ξ₀)
    (t := Icc θ.c θ.ξ₀) hint
    (hP.continuousOn_inv_sq.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
    (hP.continuousOn_inv_sq x hx)
  exact h.const_add θ.a

/-! ### Integrals of derivatives -/

theorem integral_deriv_div : ∫ ξ in θ.c..θ.ξ₀, deriv P ξ / P ξ = -Real.log θ.p := by
  have h := hP.absCont_log.integral_deriv_eq_sub
  rw [hP.right_end, hP.left_end, Real.log_one, zero_sub] at h
  rw [← h]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hP.ae_Icc_iff hP.ae_deriv_log] with x hx hxI
  rw [hx hxI]

theorem integral_deriv_div_sq : ∫ ξ in θ.c..θ.ξ₀, deriv P ξ / P ξ ^ 2 = 1 / θ.p - 1 := by
  have h := hP.absCont_inv.integral_deriv_eq_sub
  rw [hP.right_end, hP.left_end, inv_one] at h
  have h' : ∫ ξ in θ.c..θ.ξ₀, deriv P ξ / P ξ ^ 2 =
      -∫ ξ in θ.c..θ.ξ₀, deriv (fun x => (P x)⁻¹) ξ := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hP.ae_Icc_iff hP.ae_deriv_inv] with x hx hxI
    rw [hx hxI]; ring
  rw [h', h]; ring

theorem Tf_ge : θ.ξ₀ - θ.c ≤ Tf θ P := by
  unfold Tf
  have h := intervalIntegral.integral_mono_on hP.c_le_ξ₀
    (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume θ.c θ.ξ₀ from intervalIntegrable_const)
    hP.intervalIntegrable_inv_sq (fun x hx => by
      have h1 := hP.le_one hx
      have h0 := hP.pos' hx
      show (1 : ℝ) ≤ (P x ^ 2)⁻¹
      rw [le_inv_comm₀ one_pos (by positivity), inv_one]
      nlinarith)
  simpa using h

/-! ### Positivity -/

/-- `G_f - 2 = 2 m_f a_f + N_f ∫ (P'/P)(1 - ξP'/P)`. -/
theorem Gf_sub_two : Gf θ P - 2 =
    2 * θ.m * θ.a + θ.N * ∫ ξ in θ.c..θ.ξ₀, (deriv P ξ / P ξ - ξ * (deriv P ξ / P ξ) ^ 2) := by
  have hI1 : IntervalIntegrable (fun ξ => deriv P ξ / P ξ) volume θ.c θ.ξ₀ := by
    refine hP.intervalIntegrable_of_bound (B := θ.p⁻¹) ?_ ?_
    · exact hP.aestronglyMeasurable_q
    · filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
      have hPpos := hP.pos' hxm
      have hd0 := (hP.admissible.h_pos.le).trans (hP.h_le_deriv hx.1 hx.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hd0 hPpos.le), div_le_iff₀ hPpos]
      have := hP.admissible.p_pos
      calc deriv P x ≤ 1 := hP.deriv_le_one hx.1 hx.2
        _ = θ.p⁻¹ * θ.p := by field_simp
        _ ≤ θ.p⁻¹ * P x := mul_le_mul_of_nonneg_left (hP.p_le hxm) (by positivity)
  rw [intervalIntegral.integral_sub hI1 hP.intervalIntegrable_Q, hP.integral_deriv_div]
  unfold Gf Qf
  ring

theorem two_le_Gf : 2 ≤ Gf θ P := by
  have hadm := hP.admissible
  have hint : 0 ≤ ∫ ξ in θ.c..θ.ξ₀, (deriv P ξ / P ξ - ξ * (deriv P ξ / P ξ) ^ 2) := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hP.c_le_ξ₀ ?_
    filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
    have hPpos := hP.pos' hxm
    have hd0 := (hadm.h_pos.le).trans (hP.h_le_deriv hx.1 hx.2)
    have hs := hP.sub_mul_deriv_nonneg hx.1 hx.2
    show 0 ≤ deriv P x / P x - x * (deriv P x / P x) ^ 2
    have e : deriv P x / P x - x * (deriv P x / P x) ^ 2 =
        deriv P x * (P x - x * deriv P x) / P x ^ 2 := by field_simp
    rw [e]
    exact div_nonneg (mul_nonneg hd0 hs) (by positivity)
  have h := hP.Gf_sub_two
  have hma := mul_nonneg hadm.m_pos.le hadm.a_nonneg
  have := mul_nonneg hadm.N_pos.le hint
  linarith

theorem Gf_le : Gf θ P ≤ 2 / θ.m := by
  have hadm := hP.admissible
  -- `N (P'/P)(1 - ξP'/P) ≤ P'/P²` pointwise
  have hint : θ.N * ∫ ξ in θ.c..θ.ξ₀, (deriv P ξ / P ξ - ξ * (deriv P ξ / P ξ) ^ 2) ≤
      1 / θ.p - 1 := by
    rw [← hP.integral_deriv_div_sq, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_ae_restrict hP.c_le_ξ₀ ?_ ?_ ?_
    · refine (IntervalIntegrable.const_mul ?_ θ.N)
      refine hP.intervalIntegrable_of_bound (B := θ.p⁻¹ + θ.ξ₀ * (θ.p⁻¹) ^ 2) ?_ ?_
      · exact hP.aestronglyMeasurable_q.sub
          (aestronglyMeasurable_id.mul (hP.aestronglyMeasurable_q.pow 2))
      · filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
        have hPpos := hP.pos' hxm
        have hPx := hP.p_le hxm
        have hp := hadm.p_pos
        have hd0 := (hadm.h_pos.le).trans (hP.h_le_deriv hx.1 hx.2)
        have hd1 := hP.deriv_le_one hx.1 hx.2
        have hx0 : 0 ≤ x := hadm.c_nonneg.trans hxm.1
        have hq : deriv P x / P x ≤ θ.p⁻¹ := by
          rw [div_le_iff₀ hPpos]
          calc deriv P x ≤ 1 := hd1
            _ = θ.p⁻¹ * θ.p := by field_simp
            _ ≤ θ.p⁻¹ * P x := mul_le_mul_of_nonneg_left hPx (by positivity)
        have hq0 : 0 ≤ deriv P x / P x := div_nonneg hd0 hPpos.le
        have hsq : x * (deriv P x / P x) ^ 2 ≤ θ.ξ₀ * (θ.p⁻¹) ^ 2 :=
          mul_le_mul hxm.2 (pow_le_pow_left₀ hq0 hq 2) (by positivity) hadm.ξ₀_pos.le
        have hsq0 : 0 ≤ x * (deriv P x / P x) ^ 2 := by positivity
        rw [Real.norm_eq_abs]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg hq0, abs_of_nonneg hsq0]
        linarith
    · refine hP.intervalIntegrable_of_bound (B := (θ.p ^ 2)⁻¹) ?_ ?_
      · exact hP.aestronglyMeasurable_q2
      · filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
        have hPpos := hP.pos' hxm
        have hPx := hP.p_le hxm
        have hp := hadm.p_pos
        have hd0 := (hadm.h_pos.le).trans (hP.h_le_deriv hx.1 hx.2)
        have hd1 := hP.deriv_le_one hx.1 hx.2
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hd0 (by positivity)),
          div_le_iff₀ (by positivity)]
        have : θ.p ^ 2 ≤ P x ^ 2 := pow_le_pow_left₀ hp.le hPx 2
        calc deriv P x ≤ 1 := hd1
          _ = (θ.p ^ 2)⁻¹ * θ.p ^ 2 := by field_simp
          _ ≤ (θ.p ^ 2)⁻¹ * P x ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
    · filter_upwards [hP.ae_good, ae_restrict_mem measurableSet_Icc] with x hx hxm
      have hPpos := hP.pos' hxm
      have hd0 := (hadm.h_pos.le).trans (hP.h_le_deriv hx.1 hx.2)
      have hN := hP.N_mul_sub_mul_deriv_le_one hx.1 hx.2
      show θ.N * (deriv P x / P x - x * (deriv P x / P x) ^ 2) ≤ deriv P x / P x ^ 2
      have e : θ.N * (deriv P x / P x - x * (deriv P x / P x) ^ 2) =
          deriv P x * (θ.N * (P x - x * deriv P x)) / P x ^ 2 := by field_simp
      rw [e]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have h := hP.Gf_sub_two
  have hma : 2 * θ.m * θ.a ≤ 2 * θ.a := by
    have := mul_le_mul_of_nonneg_right hadm.m_lt_one.le hadm.a_nonneg
    linarith
  have hbm : 2 * θ.a + 1 / θ.p - 1 = 2 / θ.m - 2 := by
    rw [show 2 * θ.a + 1 / θ.p - 1 = 1 / θ.t - 1 from ?_]
    · unfold Params.m mF
      have := hadm.t_pos
      field_simp
      ring
    · unfold Params.a
      have ht := hadm.t_pos; have hp := hadm.p_pos
      unfold aF cF
      field_simp
      ring
  linarith

theorem Mf_nonneg : 0 ≤ Mf θ P := by
  have hadm := hP.admissible
  unfold Mf
  refine mul_nonneg hadm.N_pos.le ?_
  have hT := hP.Tf_ge
  -- `a ≥ c` since `t p ≤ 1`
  have hac : θ.c ≤ θ.a := by
    unfold Params.a aF
    rw [le_div_iff₀ (mul_pos hadm.t_pos hadm.p_pos)]
    have hc := hadm.c_nonneg
    have htp : θ.t * θ.p ≤ 1 := by
      nlinarith [hadm.t_lt_one, hadm.p_le_one, hadm.t_pos, hadm.p_pos]
    have : θ.c * (θ.t * θ.p) ≤ θ.c * 1 := mul_le_mul_of_nonneg_left htp hc
    show θ.c * (θ.t * θ.p) ≤ cF θ.t θ.p
    have e : cF θ.t θ.p = θ.c := rfl
    linarith
  linarith

theorem positivity' :
    0 < θ.N ∧ 0 ≤ Mf θ P ∧ 2 ≤ Gf θ P ∧ Gf θ P ≤ 2 / θ.m ∧ θ.m ≤ Rf θ P ∧ Rf θ P ≤ 1 := by
  have hadm := hP.admissible
  have hM := hP.Mf_nonneg
  have hG2 := hP.two_le_Gf
  have hGm := hP.Gf_le
  have hm := hadm.m_pos
  have hpos : 0 < Mf θ P + Gf θ P := by linarith
  refine ⟨hadm.N_pos, hM, hG2, hGm, ?_, ?_⟩
  · unfold Rf
    rw [le_div_iff₀ hpos]
    have h1 : θ.m * Gf θ P ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hGm hm.le
      rwa [mul_div_cancel₀ _ hm.ne'] at this
    have h2 : θ.m * Mf θ P ≤ Mf θ P := by
      have := mul_le_mul_of_nonneg_right hadm.m_lt_one.le hM
      linarith
    linarith
  · unfold Rf
    rw [div_le_one hpos]
    linarith

/-! ### The comparison -/

theorem Ef_eq (β : ℝ) : Ef β θ P = Qf θ P + dOf β * Tf θ P := by
  unfold Ef Qf Tf
  rw [intervalIntegral.integral_add hP.intervalIntegrable_E₁
      (hP.intervalIntegrable_inv_sq.const_mul _), intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hP.ae_Icc_iff hP.ae_deriv_log] with x hx hxI
  rw [hx hxI]

theorem comparison' (hI : FamilyIdentities) {β : ℝ} (hβ : 0 < β) :
    Ef β θ P = Qf θ P + dOf β * Tf θ P ∧ Kf β θ P = Kconst β θ - Ef β θ P ∧
    Kf β θ P = (Mf θ P + Gf θ P) / θ.N * (1 - Rf θ P / β) := by
  have hE := hP.Ef_eq β
  refine ⟨hE, ?_, ?_⟩
  · rw [hE]
    exact hI.comparison_second_form β θ (Tf θ P) (Qf θ P) hP.admissible hβ
  · have hpos := hP.positivity'
    unfold Kf Rf
    exact hI.ratio_comparison β (Mf θ P) (Gf θ P) θ.N hβ.ne' hpos.1.ne' (by linarith [hpos.2.1])

end InClass

/-! ### Moving endpoints under dominated convergence -/

theorem movingEndpoint' : MovingEndpointStatement := by
  intro g g₀ a b a₀ b₀ L U B hab ha hb hmeas hbound hlim
  have hLa : L ≤ a₀ := ge_of_tendsto' ha fun n => (hab n).1
  have hab₀ : a₀ ≤ b₀ := le_of_tendsto_of_tendsto' ha hb fun n => (hab n).2.1
  have hbU : b₀ ≤ U := le_of_tendsto' hb fun n => (hab n).2.2
  set μ := volume.restrict (Icc L U) with hμ
  -- rewrite each interval integral as an integral over `[L, U]`
  have hrepr : ∀ {x y : ℝ} (f : ℝ → ℝ), L ≤ x → x ≤ y → y ≤ U →
      ∫ t in x..y, f t = ∫ t, (Ioc x y).indicator f t ∂μ := by
    intro x y f hx hxy hy
    rw [intervalIntegral.integral_of_le hxy, integral_indicator measurableSet_Ioc, hμ,
      Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc x y ⊆ Icc L U from
        fun t ht => ⟨hx.trans ht.1.le, ht.2.trans hy⟩)]
  have hlim₀ : ∀ᵐ x ∂μ, ‖g₀ x‖ ≤ B := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with x hx hxb
    exact le_of_tendsto' (hx.norm) hxb
  have hmeas₀ : AEStronglyMeasurable g₀ μ :=
    aestronglyMeasurable_of_tendsto_ae _ hmeas hlim
  simp_rw [hrepr _ (hab _).1 (hab _).2.1 (hab _).2.2]
  rw [hrepr g₀ hLa hab₀ hbU]
  refine tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (hmeas n).indicator measurableSet_Ioc) (integrable_const B) (fun n => ?_) ?_
  · filter_upwards [hbound n] with x hx
    by_cases h : x ∈ Ioc (a n) (b n)
    · rw [indicator_of_mem h]; exact hx
    · rw [indicator_of_notMem h, norm_zero]; exact (norm_nonneg _).trans hx
  · have hna : ∀ᵐ x ∂μ, x ≠ a₀ := ae_restrict_of_ae (Measure.ae_ne volume a₀)
    have hnb : ∀ᵐ x ∂μ, x ≠ b₀ := ae_restrict_of_ae (Measure.ae_ne volume b₀)
    filter_upwards [hlim, hna, hnb] with x hx hxa hxb
    rcases lt_or_gt_of_ne hxa with h1 | h1
    · -- `x < a₀`: eventually `x < a n`
      have hev : ∀ᶠ n in atTop, x < a n := ha.eventually (lt_mem_nhds h1)
      have : (fun n => (Ioc (a n) (b n)).indicator (g n) x) =ᶠ[atTop] fun _ => 0 := by
        filter_upwards [hev] with n hn
        exact indicator_of_notMem (show x ∉ Ioc (a n) (b n) from
          fun h => absurd h.1 (not_lt.mpr hn.le)) _
      rw [indicator_of_notMem (show x ∉ Ioc a₀ b₀ from fun h => absurd h.1 (not_lt.mpr h1.le))]
      exact tendsto_const_nhds.congr' this.symm
    rcases lt_or_gt_of_ne hxb with h2 | h2
    · -- `a₀ < x < b₀`: eventually `x ∈ (a n, b n]`
      have hev1 : ∀ᶠ n in atTop, a n < x := ha.eventually (gt_mem_nhds h1)
      have hev2 : ∀ᶠ n in atTop, x < b n := hb.eventually (lt_mem_nhds h2)
      have : (fun n => (Ioc (a n) (b n)).indicator (g n) x) =ᶠ[atTop] fun n => g n x := by
        filter_upwards [hev1, hev2] with n hn1 hn2
        exact indicator_of_mem (show x ∈ Ioc (a n) (b n) from ⟨hn1, hn2.le⟩) _
      rw [indicator_of_mem (show x ∈ Ioc a₀ b₀ from ⟨h1, h2.le⟩)]
      exact hx.congr' this.symm
    · -- `b₀ < x`: eventually `b n < x`
      have hev : ∀ᶠ n in atTop, b n < x := hb.eventually (gt_mem_nhds h2)
      have : (fun n => (Ioc (a n) (b n)).indicator (g n) x) =ᶠ[atTop] fun _ => 0 := by
        filter_upwards [hev] with n hn
        exact indicator_of_notMem (show x ∉ Ioc (a n) (b n) from
          fun h => absurd h.2 (not_le.mpr hn)) _
      rw [indicator_of_notMem (show x ∉ Ioc a₀ b₀ from fun h => absurd h.2 (not_le.mpr h2))]
      exact tendsto_const_nhds.congr' this.symm

theorem class_basics' : ClassBasicsStatement := by
  refine ⟨fun θ P hP => ⟨hP.continuousOn, fun ξ hξ => hP.p_le hξ, hP.ae_deriv_bounds,
    hP.ae_deriv_log, hP.intervalIntegrable_inv_sq, hP.intervalIntegrable_Q,
    hP.intervalIntegrable_E₁, fun x hx => hP.hasDerivWithinAt_sF hx⟩, movingEndpoint'⟩

end FixedPrice.TwoUnit.Family
