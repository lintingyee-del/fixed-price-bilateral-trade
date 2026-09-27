import FixedPrice.TwoUnit.Family.BasicFTC
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Work package C, helpers: endpoint slopes and the entirely affine curves

* A three-arc curve with positive contacts coincides with `ξ + δ_f` near `c_f` and with
  `h_f ξ + e_f` near `ξ₀`, so it has the endpoint slopes `1` and `h_f`.
* On an entirely affine curve `aξ + b` (with `P(c_f) = p_f`, `P(ξ₀) = 1`), the fundamental theorem
  of calculus gives `T_f = (1/p_f - 1)/a` and `Q_f + log p_f = b(1 - 1/p_f)`; the certified closed
  forms `affine_left_closed_form`, `affine_right_closed_form` then give `(eq:2fam-affine-boundaries)`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

theorem endpoint_slopes' : EndpointSlopesStatement := by
  intro d θ P ξl ξr C hP hTA hcl hrξ
  constructor
  · have hline : HasDerivWithinAt θ.line₁ 1 (Icc θ.c θ.ξ₀) θ.c := by
      unfold Params.line₁
      simpa using ((hasDerivAt_id θ.c).add_const θ.δ).hasDerivWithinAt
    refine hline.congr_of_eventuallyEq ?_ (hTA.left_contact θ.c ⟨le_rfl, hTA.c_le⟩)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hcl)] with y hy1 hy2
    exact hTA.left_contact y ⟨hy1.1, hy2.le⟩
  · have hline : HasDerivWithinAt θ.line₂ θ.h (Icc θ.c θ.ξ₀) θ.ξ₀ := by
      unfold Params.line₂
      simpa using (((hasDerivAt_id θ.ξ₀).const_mul θ.h).add_const θ.e).hasDerivWithinAt
    refine hline.congr_of_eventuallyEq ?_ (hTA.right_contact θ.ξ₀ ⟨hTA.r_le, le_rfl⟩)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hrξ)] with y hy1 hy2
    exact hTA.right_contact y ⟨hy2.le, hy1.2⟩

/-- `T_f` and `Q_f` of a curve that is affine, `a ξ + b`, on the whole interval. -/
theorem affine_TQ {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) {a b : ℝ} (ha : 0 < a)
    (hline : ∀ ξ ∈ Icc θ.c θ.ξ₀, P ξ = a * ξ + b) :
    Tf θ P = (1 / θ.p - 1) / a ∧ Qf θ P + Real.log θ.p = b * (1 - 1 / θ.p) := by
  have hcξ := hP.c_le_ξ₀
  have hpos : ∀ x ∈ Icc θ.c θ.ξ₀, 0 < a * x + b := fun x hx => hline x hx ▸ hP.pos' hx
  have hc : a * θ.c + b = θ.p := (hline θ.c (left_mem_Icc.mpr hcξ)).symm.trans hP.left_end
  have hξ : a * θ.ξ₀ + b = 1 := (hline θ.ξ₀ (right_mem_Icc.mpr hcξ)).symm.trans hP.right_end
  have hp := hP.admissible.p_pos
  constructor
  · -- `∫ (aξ + b)⁻² = [-1/(a(aξ + b))]`
    have hderiv : ∀ x ∈ uIcc θ.c θ.ξ₀, HasDerivAt (fun y => -(a * (a * y + b))⁻¹)
        ((a * x + b) ^ 2)⁻¹ x := by
      intro x hx
      rw [uIcc_of_le hcξ] at hx
      have hx0 := hpos x hx
      have h1 : HasDerivAt (fun y => a * (a * y + b)) (a * a) x := by
        simpa using (((hasDerivAt_id x).const_mul a).add_const b).const_mul a
      have h2 := (h1.inv (by positivity)).neg
      convert h2 using 1
      field_simp
    have hint : IntervalIntegrable (fun x => ((a * x + b) ^ 2)⁻¹) volume θ.c θ.ξ₀ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hcξ]
      exact (((continuous_const.mul continuous_id).add continuous_const).pow 2).continuousOn.inv₀
        fun x hx => pow_ne_zero 2 (hpos x hx).ne'
    have hT : Tf θ P = ∫ x in θ.c..θ.ξ₀, ((a * x + b) ^ 2)⁻¹ := by
      unfold Tf
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hcξ] at hx
      simp only [hline x hx]
    rw [hT, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, hc, hξ]
    field_simp
    ring
  · -- `∫ ξ a²/(aξ + b)² = [log(aξ + b) + b/(aξ + b)]`
    have hderiv : ∀ x ∈ uIcc θ.c θ.ξ₀, HasDerivAt (fun y => Real.log (a * y + b) + b / (a * y + b))
        (x * (a / (a * x + b)) ^ 2) x := by
      intro x hx
      rw [uIcc_of_le hcξ] at hx
      have hx0 := hpos x hx
      have h1 : HasDerivAt (fun y => a * y + b) a x := by
        simpa using ((hasDerivAt_id x).const_mul a).add_const b
      have h2 := (h1.log hx0.ne').add ((hasDerivAt_const x b).div h1 hx0.ne')
      convert h2 using 1
      field_simp
      ring
    have hint : IntervalIntegrable (fun x => x * (a / (a * x + b)) ^ 2) volume θ.c θ.ξ₀ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hcξ]
      exact continuousOn_id.mul ((continuousOn_const.div
        ((continuous_const.mul continuous_id).add continuous_const).continuousOn
        fun x hx => (hpos x hx).ne').pow 2)
    have hQ : Qf θ P = ∫ x in θ.c..θ.ξ₀, x * (a / (a * x + b)) ^ 2 := by
      unfold Qf
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume θ.ξ₀] with x hxne hx
      rw [uIoc_of_le hcξ] at hx
      have hxo : x ∈ Ioo θ.c θ.ξ₀ := ⟨hx.1, lt_of_le_of_ne hx.2 hxne⟩
      have heq : P =ᶠ[𝓝 x] fun y => a * y + b := by
        filter_upwards [Ioo_mem_nhds hxo.1 hxo.2] with y hy
        exact hline y (Ioo_subset_Icc_self hy)
      have hd : deriv P x = a := by
        rw [heq.deriv_eq]
        exact (((hasDerivAt_id x).const_mul a).add_const b).deriv.trans (by simp)
      rw [hd, hline x (Ioo_subset_Icc_self hxo)]
    rw [hQ, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, hc, hξ, Real.log_one]
    ring

theorem affine_functionals' (hI : FamilyIdentities) : AffineFunctionalsStatement := by
  intro θ P hP
  have hadm := hP.admissible
  have ht := hadm.t_pos
  have hp := hadm.p_pos
  constructor
  · intro hline _
    have hl : ∀ ξ ∈ Icc θ.c θ.ξ₀, P ξ = 1 * ξ + θ.δ := fun ξ hξ => by
      rw [hline ξ hξ]; unfold Params.line₁; ring
    obtain ⟨hT, hQ⟩ := affine_TQ hP one_pos hl
    have hξ₀ : θ.ξ₀ = 1 - θ.δ := by
      have := hP.right_end
      rw [hl θ.ξ₀ (right_mem_Icc.mpr hP.c_le_ξ₀)] at this
      linarith
    obtain ⟨hM, hG⟩ := hI.affine_left_closed_form θ.t θ.p ht hp
    constructor
    · unfold Mf
      rw [hT, div_one, hξ₀]
      exact hM
    · unfold Gf
      have : θ.N * Real.log θ.p + θ.N * Qf θ P = θ.N * (θ.δ * (1 - 1 / θ.p)) := by
        rw [← hQ]; ring
      rw [← hG]
      show 2 + 2 * θ.m * θ.a - θ.N * Real.log θ.p - θ.N * Qf θ P =
        2 + 2 * mF θ.t * aF θ.t θ.p - NF θ.t * (δF θ.t θ.p * (1 - 1 / θ.p))
      have e1 : θ.N = NF θ.t := rfl
      have e2 : θ.δ = δF θ.t θ.p := rfl
      rw [← e1, ← e2]
      unfold Params.m Params.a
      linarith
  · intro hline hp1
    have hh := hadm.h_pos
    have hl : ∀ ξ ∈ Icc θ.c θ.ξ₀, P ξ = θ.h * ξ + θ.e := fun ξ hξ => by
      rw [hline ξ hξ]; rfl
    -- `c_f > 0`, since `c_f = 0` would force `p = e = t`
    have hc0 : 0 < θ.c := by
      rcases lt_or_eq_of_le hadm.c_nonneg with h | h
      · exact h
      · exfalso
        have hpc := hP.left_end
        rw [hl θ.c (left_mem_Icc.mpr hP.c_le_ξ₀), ← h, mul_zero, zero_add] at hpc
        have hpt : θ.p = θ.t := by
          have : θ.c = (θ.p - θ.t) / 2 := rfl
          linarith
        unfold Params.e eF at hpc
        linarith [hadm.t_lt_one]
    have hpe : θ.p = θ.h * θ.c + θ.e := by
      rw [← hl θ.c (left_mem_Icc.mpr hP.c_le_ξ₀), hP.left_end]
    have hep : (1 + θ.t) / 2 < θ.p := by
      have : θ.e = (1 + θ.t) / 2 := rfl
      nlinarith [mul_pos hh hc0]
    obtain ⟨hT, hQ⟩ := affine_TQ hP hh hl
    have hhpc : θ.h = (θ.p - eF θ.t) / cF θ.t θ.p := by
      have e1 : θ.e = eF θ.t := rfl
      have e2 : θ.c = cF θ.t θ.p := rfl
      rw [← e1, ← e2, eq_div_iff hc0.ne']
      linarith
    have hξ₀ : θ.ξ₀ = vF θ.t / θ.h := by
      unfold Params.h Params.v
      rw [div_div_cancel₀ (show vF θ.t ≠ 0 from hadm.v_pos.ne')]
    obtain ⟨hM, hG⟩ := hI.affine_right_closed_form θ.t θ.p ht hadm.t_lt_one hep
    refine ⟨hep, ?_, ?_⟩
    · unfold Mf
      rw [hT, hξ₀, hhpc]
      exact hM
    · unfold Gf
      have : θ.N * Real.log θ.p + θ.N * Qf θ P = θ.N * (θ.e * (1 - 1 / θ.p)) := by
        rw [← hQ]; ring
      rw [← hG]
      show 2 + 2 * θ.m * θ.a - θ.N * Real.log θ.p - θ.N * Qf θ P =
        2 + 2 * mF θ.t * aF θ.t θ.p - NF θ.t * (eF θ.t * (1 - 1 / θ.p))
      have e1 : θ.N = NF θ.t := rfl
      have e2 : θ.e = eF θ.t := rfl
      rw [← e1, ← e2]
      unfold Params.m Params.a
      linarith

end FixedPrice.TwoUnit.Family
