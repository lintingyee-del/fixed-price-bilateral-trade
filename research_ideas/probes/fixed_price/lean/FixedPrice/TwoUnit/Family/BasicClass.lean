import FixedPrice.TwoUnit.Family.Statements

/-!
# Work package A, helpers: parameters and class members

* Admissible parameters: `p, N, v, h, δ > 0`, `c, a ≥ 0`, `0 < m < 1`, `N e = 1`, `m a = N c/p`,
  and the obstacles pass through `(c_f, p_f)` and `(ξ₀, 1)`.
* A class member lies between `p_f` and `1`, is absolutely continuous, and at every interior point
  where it is differentiable has `h_f ≤ P' ≤ 1` and `0 ≤ P - ξP' ≤ e_f = 1/N_f` (concavity against
  the two obstacles). So `log P`, `1/P` and `ξ/P` are absolutely continuous and the fundamental
  theorem of calculus applies to them.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

namespace Params

variable {θ : Params}

theorem Admissible.p_pos (h : θ.Admissible) : 0 < θ.p := h.t_pos.trans_le h.t_le_p

theorem Admissible.c_nonneg (h : θ.Admissible) : 0 ≤ θ.c := by
  unfold c cF; linarith [h.t_le_p]

theorem Admissible.δ_pos (h : θ.Admissible) : 0 < θ.δ := by
  unfold δ δF; linarith [h.t_pos, h.p_pos]

theorem Admissible.N_pos (h : θ.Admissible) : 0 < θ.N := by
  unfold N NF; have := h.t_pos; positivity

theorem Admissible.v_pos (h : θ.Admissible) : 0 < θ.v := by
  unfold v vF eF; linarith [h.t_lt_one]

theorem Admissible.h_pos (h : θ.Admissible) : 0 < θ.h := div_pos h.v_pos h.ξ₀_pos

theorem Admissible.a_nonneg (h : θ.Admissible) : 0 ≤ θ.a :=
  div_nonneg h.c_nonneg (mul_pos h.t_pos h.p_pos).le

theorem Admissible.m_pos (h : θ.Admissible) : 0 < θ.m := by
  unfold m mF; have := h.t_pos; positivity

theorem Admissible.m_lt_one (h : θ.Admissible) : θ.m < 1 := by
  unfold m mF; rw [div_lt_one (by linarith [h.t_pos])]; linarith [h.t_lt_one]

theorem Admissible.N_mul_e (h : θ.Admissible) : θ.N * θ.e = 1 := by
  unfold N NF e eF
  have : 1 + θ.t ≠ 0 := by linarith [h.t_pos]
  field_simp

theorem Admissible.m_mul_a (h : θ.Admissible) : θ.m * θ.a = θ.N * θ.c / θ.p := by
  unfold m mF a aF N NF c
  have ht := h.t_pos; have hp := h.p_pos
  field_simp

theorem line₁_c : θ.line₁ θ.c = θ.p := by unfold line₁ c δ cF δF; ring

theorem Admissible.line₂_ξ₀ (h : θ.Admissible) : θ.line₂ θ.ξ₀ = 1 := by
  unfold line₂ Params.h v vF e eF
  have := h.ξ₀_pos
  field_simp
  ring

theorem Admissible.line₂_le_one (h : θ.Admissible) {ξ : ℝ} (hξ : ξ ≤ θ.ξ₀) : θ.line₂ ξ ≤ 1 := by
  rw [← h.line₂_ξ₀]; unfold line₂
  have := mul_le_mul_of_nonneg_left hξ h.h_pos.le
  linarith

theorem Admissible.e_eq_inv_N (h : θ.Admissible) : θ.e = 1 / θ.N := by
  rw [eq_div_iff h.N_pos.ne', mul_comm, h.N_mul_e]

end Params

namespace InClass

variable {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
include hP

theorem c_le_ξ₀ : θ.c ≤ θ.ξ₀ := hP.admissible.c_le_ξ₀

theorem continuousOn : ContinuousOn P (Icc θ.c θ.ξ₀) := by
  obtain ⟨K, hK⟩ := hP.lipschitz
  exact hK.continuousOn

theorem le_line₁ {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : P ξ ≤ θ.line₁ ξ :=
  (hP.obstacle ξ hξ).trans (min_le_left _ _)

theorem le_line₂ {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : P ξ ≤ θ.line₂ ξ :=
  (hP.obstacle ξ hξ).trans (min_le_right _ _)

theorem le_one {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : P ξ ≤ 1 :=
  (hP.le_line₂ hξ).trans (hP.admissible.line₂_le_one hξ.2)

theorem p_le {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : θ.p ≤ P ξ := by
  have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
  have hξ₀ : θ.ξ₀ ∈ Icc θ.c θ.ξ₀ := right_mem_Icc.mpr hP.c_le_ξ₀
  have := hP.concave.ge_on_segment (z := ξ) hc hξ₀ (by rw [segment_eq_Icc hP.c_le_ξ₀]; exact hξ)
  rwa [hP.left_end, hP.right_end, min_eq_left hP.admissible.p_le_one] at this

theorem pos' {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : 0 < P ξ :=
  hP.admissible.p_pos.trans_le (hP.p_le hξ)

theorem absCont : AbsolutelyContinuousOnInterval P θ.c θ.ξ₀ := by
  obtain ⟨K, hK⟩ := hP.lipschitz
  exact LipschitzOnWith.absolutelyContinuousOnInterval (by rwa [uIcc_of_le hP.c_le_ξ₀])

/-- A function that is `C¹` near `[p_f, 1]`, composed with `P`, is absolutely continuous. -/
theorem absCont_comp {φ : ℝ → ℝ} {s : Set ℝ} (hs : Icc θ.p 1 ⊆ s)
    (hφ : ContDiffOn ℝ 1 φ s) : AbsolutelyContinuousOnInterval (fun x => φ (P x)) θ.c θ.ξ₀ := by
  obtain ⟨K, hK⟩ := hP.lipschitz
  obtain ⟨L, hL⟩ := (hφ.mono hs).exists_lipschitzOnWith one_ne_zero (convex_Icc _ _)
    isCompact_Icc
  refine LipschitzOnWith.absolutelyContinuousOnInterval (K := L * K) ?_
  rw [uIcc_of_le hP.c_le_ξ₀]
  exact hL.comp hK fun x hx => ⟨hP.p_le hx, hP.le_one hx⟩

theorem absCont_log : AbsolutelyContinuousOnInterval (fun x => Real.log (P x)) θ.c θ.ξ₀ :=
  hP.absCont_comp (s := {0}ᶜ) (fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff]
    exact (hP.admissible.p_pos.trans_le hx.1).ne') (Real.contDiffOn_log)

theorem absCont_inv : AbsolutelyContinuousOnInterval (fun x => (P x)⁻¹) θ.c θ.ξ₀ :=
  hP.absCont_comp (s := {0}ᶜ) (fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff]
    exact (hP.admissible.p_pos.trans_le hx.1).ne') (contDiffOn_inv ℝ)

theorem absCont_div : AbsolutelyContinuousOnInterval (fun x => x * (P x)⁻¹) θ.c θ.ξ₀ := by
  have hid : AbsolutelyContinuousOnInterval (fun x : ℝ => x) θ.c θ.ξ₀ :=
    LipschitzOnWith.absolutelyContinuousOnInterval (K := 1)
      (LipschitzWith.id.lipschitzOnWith)
  exact hid.mul hP.absCont_inv

/-- Almost every point of the curve interval is interior and a point of differentiability. -/
theorem ae_good : ∀ᵐ x ∂(volume.restrict (Icc θ.c θ.ξ₀)),
    x ∈ Ioo θ.c θ.ξ₀ ∧ DifferentiableAt ℝ P x := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae hP.absCont.ae_differentiableAt] with x hx hd
  exact ⟨hx, hd (by rw [uIcc_of_le hP.c_le_ξ₀]; exact Ioo_subset_Icc_self hx)⟩

/-- `P' ≤ 1` at interior points of differentiability (concavity against `ξ + δ_f`). -/
theorem deriv_le_one {x : ℝ} (hx : x ∈ Ioo θ.c θ.ξ₀) (hd : DifferentiableAt ℝ P x) :
    deriv P x ≤ 1 := by
  have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
  have hxm : x ∈ Icc θ.c θ.ξ₀ := Ioo_subset_Icc_self hx
  have h1 := hP.concave.deriv_le_slope hc hxm hx.1 hd
  rw [slope_def_field, hP.left_end] at h1
  have h2 : P x - θ.p ≤ x - θ.c := by
    have := hP.le_line₁ hxm
    have e : θ.line₁ x - θ.p = x - θ.c := by rw [← Params.line₁_c]; unfold Params.line₁; ring
    linarith
  have h3 : (P x - θ.p) / (x - θ.c) ≤ 1 := by
    rw [div_le_one (sub_pos.mpr hx.1)]; exact h2
  linarith

/-- `h_f ≤ P'` at interior points of differentiability (concavity against `h_f ξ + e_f`). -/
theorem h_le_deriv {x : ℝ} (hx : x ∈ Ioo θ.c θ.ξ₀) (hd : DifferentiableAt ℝ P x) :
    θ.h ≤ deriv P x := by
  have hξ₀ : θ.ξ₀ ∈ Icc θ.c θ.ξ₀ := right_mem_Icc.mpr hP.c_le_ξ₀
  have hxm : x ∈ Icc θ.c θ.ξ₀ := Ioo_subset_Icc_self hx
  have h1 := hP.concave.slope_le_deriv hxm hξ₀ hx.2 hd
  rw [slope_def_field, hP.right_end] at h1
  have h2 : θ.h * (θ.ξ₀ - x) ≤ 1 - P x := by
    have := hP.le_line₂ hxm
    have e := hP.admissible.line₂_ξ₀
    unfold Params.line₂ at this e
    linarith
  have h3 : θ.h ≤ (1 - P x) / (θ.ξ₀ - x) := by
    rw [le_div_iff₀ (sub_pos.mpr hx.2)]; exact h2
  linarith

/-- `0 ≤ P - ξP'` at interior points of differentiability. -/
theorem sub_mul_deriv_nonneg {x : ℝ} (hx : x ∈ Ioo θ.c θ.ξ₀) (hd : DifferentiableAt ℝ P x) :
    0 ≤ P x - x * deriv P x := by
  have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
  have hxm : x ∈ Icc θ.c θ.ξ₀ := Ioo_subset_Icc_self hx
  have hx0 : 0 < x := lt_of_le_of_lt hP.admissible.c_nonneg hx.1
  have h1 := hP.concave.deriv_le_slope hc hxm hx.1 hd
  rw [slope_def_field, hP.left_end] at h1
  have hxc : 0 < x - θ.c := sub_pos.mpr hx.1
  -- `x (P x - p) ≤ (x - c) P x`, i.e. `c P x ≤ x p`
  have hkey : x * (P x - θ.p) ≤ (x - θ.c) * P x := by
    have hl := hP.le_line₁ hxm
    have hδ : θ.p = θ.c + θ.δ := by unfold Params.c Params.δ cF δF; ring
    unfold Params.line₁ at hl
    have hcn := hP.admissible.c_nonneg
    have hδp := hP.admissible.δ_pos
    nlinarith [mul_le_mul_of_nonneg_left hl hcn]
  have h2 : x * deriv P x ≤ x * ((P x - θ.p) / (x - θ.c)) :=
    mul_le_mul_of_nonneg_left h1 hx0.le
  have h3 : x * ((P x - θ.p) / (x - θ.c)) ≤ P x := by
    rw [mul_div_assoc', div_le_iff₀ hxc]; linarith
  linarith

/-- `N_f (P - ξP') ≤ 1` at interior points of differentiability: the first seller distribution
function of `(eq:2fam-laws)` is at most one. -/
theorem N_mul_sub_mul_deriv_le_one {x : ℝ} (hx : x ∈ Ioo θ.c θ.ξ₀)
    (hd : DifferentiableAt ℝ P x) : θ.N * (P x - x * deriv P x) ≤ 1 := by
  have hξ₀ : θ.ξ₀ ∈ Icc θ.c θ.ξ₀ := right_mem_Icc.mpr hP.c_le_ξ₀
  have hxm : x ∈ Icc θ.c θ.ξ₀ := Ioo_subset_Icc_self hx
  have hx0 : 0 < x := lt_of_le_of_lt hP.admissible.c_nonneg hx.1
  have h1 := hP.concave.slope_le_deriv hxm hξ₀ hx.2 hd
  rw [slope_def_field, hP.right_end] at h1
  have hξx : 0 < θ.ξ₀ - x := sub_pos.mpr hx.2
  have h2 : x * ((1 - P x) / (θ.ξ₀ - x)) ≤ x * deriv P x :=
    mul_le_mul_of_nonneg_left h1 hx0.le
  -- `P x - x (1 - P x)/(ξ₀ - x) ≤ e`, from `P x ≤ h x + e` and `h ξ₀ + e = 1`
  have hl := hP.le_line₂ hxm
  have e1 := hP.admissible.line₂_ξ₀
  unfold Params.line₂ at hl e1
  have h3 : P x - x * ((1 - P x) / (θ.ξ₀ - x)) ≤ θ.e := by
    have hξ₀p := hP.admissible.ξ₀_pos
    have hh : θ.h * θ.ξ₀ * x = (1 - θ.e) * x := by rw [show θ.h * θ.ξ₀ = 1 - θ.e by linarith]
    have hm := mul_le_mul_of_nonneg_right hl hξ₀p.le
    have key : P x * (θ.ξ₀ - x) - x * (1 - P x) ≤ θ.e * (θ.ξ₀ - x) := by nlinarith
    have e2 : P x - x * ((1 - P x) / (θ.ξ₀ - x)) =
        (P x * (θ.ξ₀ - x) - x * (1 - P x)) / (θ.ξ₀ - x) := by
      field_simp
    rw [e2, div_le_iff₀ hξx]
    exact key
  have hN := hP.admissible.N_pos
  have hNe := hP.admissible.N_mul_e
  have : P x - x * deriv P x ≤ θ.e := by linarith
  calc θ.N * (P x - x * deriv P x) ≤ θ.N * θ.e := mul_le_mul_of_nonneg_left this hN.le
    _ = 1 := hNe

end InClass

end FixedPrice.TwoUnit.Family
