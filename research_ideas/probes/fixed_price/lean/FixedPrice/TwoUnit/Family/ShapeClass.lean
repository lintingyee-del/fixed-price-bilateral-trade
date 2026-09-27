import FixedPrice.TwoUnit.Family.ShapeExist

/-!
# Work package B, part 3: class members in the obstacle class

For a class member `P`, `w_P = √s P'/P` is bounded, `z_{w_P} = log P` (fundamental theorem of
calculus for `log P`), so `w_P` lies in the obstacle class and `J(w_P) = Q_f + d_f T_f = E_f(P)`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params} {P : ℝ → ℝ}

/-- `s ↦ √s P'(s)/P(s)`. -/
def wfun (P : ℝ → ℝ) (s : ℝ) : ℝ := Real.sqrt s * (deriv P s / P s)

theorem ae_good_I (hP : InClass θ P) :
    ∀ᵐ s ∂(μ θ), s ∈ Ioo θ.c θ.ξ₀ ∧ DifferentiableAt ℝ P s :=
  show ∀ᵐ s ∂(volume.restrict (Ioc θ.c θ.ξ₀)), _ from
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hP.ae_good

theorem abs_wfun_le (hP : InClass θ P) {s : ℝ} (hs : s ∈ Ioo θ.c θ.ξ₀)
    (hd : DifferentiableAt ℝ P s) : |wfun P s| ≤ Real.sqrt θ.ξ₀ * θ.p⁻¹ := by
  have hadm := hP.admissible
  have hsm : s ∈ Icc θ.c θ.ξ₀ := Ioo_subset_Icc_self hs
  have hPpos := hP.pos' hsm
  have hPp := hP.p_le hsm
  have hp := hadm.p_pos
  have hd0 := hadm.h_pos.le.trans (hP.h_le_deriv hs hd)
  have hd1 := hP.deriv_le_one hs hd
  unfold wfun
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (div_nonneg hd0 hPpos.le)]
  refine mul_le_mul (Real.sqrt_le_sqrt hs.2.le) ?_ (div_nonneg hd0 hPpos.le) (Real.sqrt_nonneg _)
  rw [div_le_iff₀ hPpos]
  calc deriv P s ≤ 1 := hd1
    _ = θ.p⁻¹ * θ.p := by field_simp
    _ ≤ θ.p⁻¹ * P s := mul_le_mul_of_nonneg_left hPp (by positivity)

theorem memLp_wfun (hP : InClass θ P) : MemLp (wfun P) 2 (μ θ) := by
  refine MemLp.of_bound (C := Real.sqrt θ.ξ₀ * θ.p⁻¹) ?_ ?_
  · exact (Real.continuous_sqrt.measurable.aemeasurable.mul
      ((measurable_deriv P).aemeasurable.div
        ((hP.aestronglyMeasurable_P.mono_measure
          (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)).aemeasurable))).aestronglyMeasurable
  · filter_upwards [ae_good_I hP] with s hs
    rw [Real.norm_eq_abs]
    exact abs_wfun_le hP hs.1 hs.2

/-- The scaled derivative of a class member. -/
def wP (hP : InClass θ P) : H θ := (memLp_wfun hP).toLp (wfun P)

theorem wP_ae (hP : InClass θ P) : ∀ᵐ s, s ∈ Ioc θ.c θ.ξ₀ → wP hP s = wfun P s :=
  (ae_restrict_iff' measurableSet_Ioc).mp (memLp_wfun hP).coeFn_toLp

theorem zfun_wP (hP : InClass θ P) {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) (hξ0 : 0 < ξ) :
    zfun θ (wP hP) ξ = Real.log (P ξ) := by
  rw [zfun_eq_integral θ _ hξ0 hξ.1 hξ.2]
  have hae : ∀ᵐ s, s ∈ Ι ξ θ.ξ₀ → wP hP s / Real.sqrt s = deriv (fun x => Real.log (P x)) s := by
    have hlog := (ae_restrict_iff' measurableSet_Icc).mp hP.ae_deriv_log
    filter_upwards [wP_ae hP, hlog] with s hs hs2 hsI
    rw [uIoc_of_le hξ.2] at hsI
    have hsI' : s ∈ Ioc θ.c θ.ξ₀ := ⟨hξ.1.trans_lt hsI.1, hsI.2⟩
    have hs0 : 0 < s := hξ0.trans hsI.1
    rw [hs hsI', hs2 (Ioc_subset_Icc_self hsI')]
    unfold wfun
    field_simp
  rw [intervalIntegral.integral_congr_ae hae]
  have hAC : AbsolutelyContinuousOnInterval (fun x => Real.log (P x)) ξ θ.ξ₀ :=
    hP.absCont_log.mono (by
      rw [uIcc_of_le hξ.2, uIcc_of_le hP.c_le_ξ₀]; exact Icc_subset_Icc_left hξ.1)
  rw [hAC.integral_deriv_eq_sub, hP.right_end, Real.log_one]
  ring

theorem wP_mem (hP : InClass θ P) : wP hP ∈ W θ := by
  intro ξ hξ hξ0
  rw [zfun_wP hP hξ hξ0]
  have hPpos := hP.pos' hξ
  exact ⟨Real.log_le_log hP.admissible.p_pos (hP.p_le hξ),
    Real.log_le_log hPpos (hP.obstacle ξ hξ)⟩

theorem J_wP (hP : InClass θ P) (β : ℝ) : J θ (dOf β) (wP hP) = Ef β θ P := by
  rw [hP.Ef_eq β]
  unfold J
  congr 1
  · rw [← real_inner_self_eq_norm_sq, inner_eq_integral]
    unfold Qf
    rw [intervalIntegral.integral_of_le hP.c_le_ξ₀]
    show ∫ s in Ioc θ.c θ.ξ₀, wP hP s * wP hP s = _
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [wP_ae hP] with s hs hsI
    rw [hs hsI]
    unfold wfun
    have hs0 : 0 ≤ s := hP.admissible.c_nonneg.trans hsI.1.le
    rw [show Real.sqrt s * (deriv P s / P s) * (Real.sqrt s * (deriv P s / P s)) =
      (Real.sqrt s * Real.sqrt s) * (deriv P s / P s) ^ 2 by ring, Real.mul_self_sqrt hs0]
  · congr 1
    unfold Tf
    rw [intervalIntegral.integral_of_le hP.c_le_ξ₀]
    show ∫ s in Ioc θ.c θ.ξ₀, Real.exp (-2 * zfun θ (wP hP) s) = _
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := lt_of_le_of_lt hP.admissible.c_nonneg hs.1
    have hsm : s ∈ Icc θ.c θ.ξ₀ := Ioc_subset_Icc_self hs
    rw [zfun_wP hP hsm hs0]
    have hPpos := hP.pos' hsm
    rw [show -2 * Real.log (P s) = Real.log ((P s ^ 2)⁻¹) by
      rw [Real.log_inv, Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

end Relaxed

end FixedPrice.TwoUnit.Family
