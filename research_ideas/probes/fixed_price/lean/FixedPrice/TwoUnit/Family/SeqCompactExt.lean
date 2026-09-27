import FixedPrice.TwoUnit.Family.CompactnessAttain

/-!
# Work package A, compactness: the extension of a curve by its obstacles

The proof of `lem:2fam-compact` extends each curve leftwards by `ξ + δ_f` and rightwards by
`h_f ξ + e_f`. The extension has increments between `h_f (y - x)` and `y - x` (from concavity
against the two obstacles, with equality at the endpoints), so it is `1`-Lipschitz, and its
slopes decrease, so it is concave on `ℝ`. It stays below both obstacles, above `t_f` on
`[0, ∞)`, and agrees with the curve (and its derivative) inside `[c_f, ξ₀]`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

/-- The extension of a curve by its obstacles. -/
def extCurve (θ : Params) (P : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  if ξ < θ.c then θ.line₁ ξ else if ξ ≤ θ.ξ₀ then P ξ else θ.line₂ ξ

namespace InClass

variable {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
include hP

omit hP in
theorem extCurve_of_mem {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : extCurve θ P ξ = P ξ := by
  unfold extCurve; rw [if_neg (not_lt.mpr hξ.1), if_pos hξ.2]

theorem extCurve_of_le {ξ : ℝ} (hξ : ξ ≤ θ.c) : extCurve θ P ξ = θ.line₁ ξ := by
  rcases lt_or_eq_of_le hξ with h | h
  · unfold extCurve; rw [if_pos h]
  · rw [h, extCurve_of_mem (left_mem_Icc.mpr hP.c_le_ξ₀), hP.left_end, Params.line₁_c]

theorem extCurve_of_ge {ξ : ℝ} (hξ : θ.ξ₀ ≤ ξ) : extCurve θ P ξ = θ.line₂ ξ := by
  rcases lt_or_eq_of_le hξ with h | h
  · unfold extCurve; rw [if_neg (by linarith [hP.c_le_ξ₀]), if_neg (not_le.mpr h)]
  · rw [← h, extCurve_of_mem (right_mem_Icc.mpr hP.c_le_ξ₀), hP.right_end,
      hP.admissible.line₂_ξ₀]

/-- Increments of the curve on `[c_f, ξ₀]` lie between `h_f (y - x)` and `y - x`. -/
theorem incr_mem {x y : ℝ} (hx : x ∈ Icc θ.c θ.ξ₀) (hy : y ∈ Icc θ.c θ.ξ₀) (hxy : x ≤ y) :
    θ.h * (y - x) ≤ P y - P x ∧ P y - P x ≤ y - x := by
  have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
  have hξ₀ : θ.ξ₀ ∈ Icc θ.c θ.ξ₀ := right_mem_Icc.mpr hP.c_le_ξ₀
  rcases eq_or_lt_of_le hxy with h | hlt
  · subst h; simp
  have hδ : θ.p = θ.c + θ.δ := by unfold Params.c Params.δ cF δF; ring
  have e1 := hP.admissible.line₂_ξ₀
  constructor
  · -- lower bound through the slope to `ξ₀`
    have hbase : θ.h * (θ.ξ₀ - y) ≤ 1 - P y := by
      have := hP.le_line₂ hy; unfold Params.line₂ at this e1; linarith
    rcases eq_or_lt_of_le hy.2 with hyξ | hyξ
    · subst hyξ
      have := hP.le_line₂ hx; unfold Params.line₂ at this e1; rw [hP.right_end]; linarith
    · have hs := hP.concave.slope_anti_adjacent hx hξ₀ hlt hyξ
      rw [hP.right_end] at hs
      have h2 : θ.h ≤ (1 - P y) / (θ.ξ₀ - y) := by
        rw [le_div_iff₀ (sub_pos.mpr hyξ)]; exact hbase
      have h3 : θ.h ≤ (P y - P x) / (y - x) := h2.trans hs
      rwa [le_div_iff₀ (sub_pos.mpr hlt)] at h3
  · -- upper bound through the slope from `c_f`
    rcases eq_or_lt_of_le hx.1 with hcx | hcx
    · subst hcx
      have := hP.le_line₁ hy; unfold Params.line₁ at this; rw [hP.left_end]; linarith
    · have hs := hP.concave.slope_anti_adjacent hc hy hcx hlt
      rw [hP.left_end] at hs
      have h2 : (P x - θ.p) / (x - θ.c) ≤ 1 := by
        rw [div_le_one (sub_pos.mpr hcx)]
        have := hP.le_line₁ hx; unfold Params.line₁ at this; linarith
      have h3 : (P y - P x) / (y - x) ≤ 1 := hs.trans h2
      rwa [div_le_one (sub_pos.mpr hlt)] at h3

theorem h_le_one : θ.h ≤ 1 := by
  have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
  have hξ₀ : θ.ξ₀ ∈ Icc θ.c θ.ξ₀ := right_mem_Icc.mpr hP.c_le_ξ₀
  rcases eq_or_lt_of_le hP.c_le_ξ₀ with h | h
  · -- degenerate interval: `p = 1`, `c = v`, so `h = v/ξ₀ = 1`
    have hp1 : θ.p = 1 := by rw [← hP.left_end, h, hP.right_end]
    have hv : θ.v = θ.c := by
      unfold Params.v Params.c vF eF cF; rw [hp1]; ring
    unfold Params.h; rw [hv, h, div_self hP.admissible.ξ₀_pos.ne']
  · have hb := hP.incr_mem hc hξ₀ h.le
    have := hb.1.trans hb.2
    exact le_of_mul_le_mul_right (by linarith) (sub_pos.mpr h)

/-- Increments of the extension lie between `h_f (y - x)` and `y - x`. -/
theorem ext_incr {x y : ℝ} (hxy : x ≤ y) :
    θ.h * (y - x) ≤ extCurve θ P y - extCurve θ P x ∧
      extCurve θ P y - extCurve θ P x ≤ y - x := by
  have hh1 := hP.h_le_one
  have hh0 := hP.admissible.h_pos
  have hcξ := hP.c_le_ξ₀
  by_cases hyc : y ≤ θ.c
  · rw [hP.extCurve_of_le hyc, hP.extCurve_of_le (hxy.trans hyc)]
    unfold Params.line₁
    constructor <;> nlinarith
  by_cases hxξ : θ.ξ₀ ≤ x
  · rw [hP.extCurve_of_ge hxξ, hP.extCurve_of_ge (hxξ.trans hxy)]
    unfold Params.line₂
    constructor <;> nlinarith
  push Not at hyc hxξ
  set x' := max x θ.c
  set y' := min y θ.ξ₀
  have hx'm : x' ∈ Icc θ.c θ.ξ₀ := ⟨le_max_right _ _, max_le hxξ.le hcξ⟩
  have hy'm : y' ∈ Icc θ.c θ.ξ₀ := ⟨le_min hyc.le hcξ, min_le_right _ _⟩
  have hx'y' : x' ≤ y' := max_le (le_min hxy hxξ.le) (le_min hyc.le hcξ)
  have hmid := hP.incr_mem hx'm hy'm hx'y'
  rw [← extCurve_of_mem (P := P) hx'm, ← extCurve_of_mem (P := P) hy'm] at hmid
  -- the left piece
  have hleft : θ.h * (x' - x) ≤ extCurve θ P x' - extCurve θ P x ∧
      extCurve θ P x' - extCurve θ P x ≤ x' - x := by
    rcases le_or_gt θ.c x with h | h
    · have : x' = x := max_eq_left h
      rw [this]; simp
    · have hx'c : x' = θ.c := max_eq_right h.le
      rw [hx'c, hP.extCurve_of_le le_rfl, hP.extCurve_of_le h.le]
      unfold Params.line₁
      constructor <;> nlinarith
  -- the right piece
  have hright : θ.h * (y - y') ≤ extCurve θ P y - extCurve θ P y' ∧
      extCurve θ P y - extCurve θ P y' ≤ y - y' := by
    rcases le_or_gt y θ.ξ₀ with h | h
    · have : y' = y := min_eq_left h
      rw [this]; simp
    · have hy'ξ : y' = θ.ξ₀ := min_eq_right h.le
      rw [hy'ξ, hP.extCurve_of_ge le_rfl, hP.extCurve_of_ge h.le]
      unfold Params.line₂
      constructor <;> nlinarith
  constructor <;> nlinarith [hleft.1, hleft.2, hright.1, hright.2, hmid.1, hmid.2]

theorem ext_lipschitz : LipschitzWith 1 (extCurve θ P) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  have hh0 := hP.admissible.h_pos
  rcases le_total x y with h | h
  · have := hP.ext_incr h
    rw [abs_le]
    constructor <;> nlinarith [abs_of_nonneg (sub_nonneg.mpr h), abs_nonneg (x - y),
      abs_sub_comm x y]
  · have := hP.ext_incr h
    rw [abs_le]
    constructor <;> nlinarith [abs_of_nonneg (sub_nonneg.mpr h), abs_nonneg (x - y),
      abs_sub_comm x y]

theorem ext_concave : ConcaveOn ℝ univ (extCurve θ P) := by
  rw [concaveOn_iff_slope_anti_adjacent]
  refine ⟨convex_univ, fun x y z _ _ hxy hyz => ?_⟩
  have hh0 := hP.admissible.h_pos
  have hcξ := hP.c_le_ξ₀
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hzy : 0 < z - y := sub_pos.mpr hyz
  rw [div_le_div_iff₀ hzy hyx]
  by_cases hyc : y ≤ θ.c
  · -- `E` is `ξ + δ_f` left of `y`
    rw [hP.extCurve_of_le hyc, hP.extCurve_of_le (hxy.le.trans hyc)]
    have := (hP.ext_incr hyz.le).2
    rw [hP.extCurve_of_le hyc] at this
    unfold Params.line₁ at this ⊢
    nlinarith
  by_cases hyξ : θ.ξ₀ ≤ y
  · -- `E` is `h_f ξ + e_f` right of `y`
    rw [hP.extCurve_of_ge hyξ, hP.extCurve_of_ge (hyξ.trans hyz.le)]
    have := (hP.ext_incr hxy.le).1
    rw [hP.extCurve_of_ge hyξ] at this
    unfold Params.line₂ at this ⊢
    nlinarith
  push Not at hyc hyξ
  set E := extCurve θ P
  -- compare with the clipped points `x' = max x c`, `z' = min z ξ₀`
  set x' := max x θ.c
  set z' := min z θ.ξ₀
  have hx'm : x' ∈ Icc θ.c θ.ξ₀ := ⟨le_max_right _ _, max_le (hxy.le.trans hyξ.le) hcξ⟩
  have hz'm : z' ∈ Icc θ.c θ.ξ₀ := ⟨le_min (hyc.le.trans hyz.le) hcξ, min_le_right _ _⟩
  have hym : y ∈ Icc θ.c θ.ξ₀ := ⟨hyc.le, hyξ.le⟩
  have hx'y : x' < y := max_lt hxy hyc
  have hyz' : y < z' := lt_min hyz hyξ
  have hcon := hP.concave.slope_anti_adjacent hx'm hz'm hx'y hyz'
  rw [← extCurve_of_mem (P := P) hx'm, ← extCurve_of_mem (P := P) hym, ← extCurve_of_mem (P := P) hz'm] at hcon
  rw [div_le_div_iff₀ (sub_pos.mpr hyz') (sub_pos.mpr hx'y)] at hcon
  -- `E y - E x ≥ (E y - E x')(y - x)/(y - x')` and `E z - E y ≤ (E z' - E y)(z - y)/(z' - y)`
  have hxside : (E y - E x') * (y - x) ≤ (E y - E x) * (y - x') := by
    rcases le_or_gt θ.c x with h | h
    · have : x' = x := max_eq_left h
      rw [this]
    · have hx'c : x' = θ.c := max_eq_right h.le
      rw [hx'c] at hx'y ⊢
      have hEx : E x = E θ.c - (θ.c - x) := by
        simp only [E]; rw [hP.extCurve_of_le le_rfl, hP.extCurve_of_le h.le]
        unfold Params.line₁; ring
      have hub := (hP.ext_incr hx'y.le).2
      rw [hEx]
      nlinarith
  have hzside : (E z - E y) * (z' - y) ≤ (E z' - E y) * (z - y) := by
    rcases le_or_gt z θ.ξ₀ with h | h
    · have : z' = z := min_eq_left h
      rw [this]
    · have hz'ξ : z' = θ.ξ₀ := min_eq_right h.le
      rw [hz'ξ] at hyz' ⊢
      have hEz : E z = E θ.ξ₀ + θ.h * (z - θ.ξ₀) := by
        simp only [E]; rw [hP.extCurve_of_ge le_rfl, hP.extCurve_of_ge h.le]
        unfold Params.line₂; ring
      have hlb := (hP.ext_incr hyz'.le).1
      rw [hEz]
      nlinarith
  have hx'x : 0 < y - x' := sub_pos.mpr hx'y
  have hz'y : 0 < z' - y := sub_pos.mpr hyz'
  -- combine: `(E z - E y)(y - x) ≤ (E y - E x)(z - y)`
  have h1 : (E z - E y) * (y - x) * (z' - y) * (y - x') ≤
      (E z' - E y) * (z - y) * (y - x) * (y - x') := by
    have := mul_le_mul_of_nonneg_right hzside (le_of_lt (mul_pos hyx hx'x))
    nlinarith
  have h2 : (E z' - E y) * (y - x') ≤ (E y - E x') * (z' - y) := hcon
  have h3 : (E z' - E y) * (z - y) * (y - x) * (y - x') ≤
      (E y - E x') * (z' - y) * (z - y) * (y - x) := by
    have := mul_le_mul_of_nonneg_right h2 (le_of_lt (mul_pos hzy hyx))
    nlinarith
  have h4 : (E y - E x') * (z' - y) * (z - y) * (y - x) ≤
      (E y - E x) * (y - x') * (z - y) * (z' - y) := by
    have := mul_le_mul_of_nonneg_right hxside (le_of_lt (mul_pos hz'y hzy))
    nlinarith
  have h5 : (E z - E y) * (y - x) * ((z' - y) * (y - x')) ≤
      (E y - E x) * (z - y) * ((z' - y) * (y - x')) := by nlinarith
  exact le_of_mul_le_mul_right h5 (mul_pos hz'y hx'x)

theorem ext_le_U (ξ : ℝ) : extCurve θ P ξ ≤ θ.U ξ := by
  have hcξ := hP.c_le_ξ₀
  have hh1 := hP.h_le_one
  by_cases h1 : ξ ≤ θ.c
  · rw [hP.extCurve_of_le h1]
    refine le_min le_rfl ?_
    -- `line₁ ≤ line₂` left of `c_f`, from `p ≤ line₂(c_f)` and slope `h_f ≤ 1`
    have hc := hP.le_line₂ (left_mem_Icc.mpr hcξ)
    rw [hP.left_end, ← Params.line₁_c] at hc
    unfold Params.line₁ Params.line₂ at hc ⊢
    nlinarith
  by_cases h2 : θ.ξ₀ ≤ ξ
  · rw [hP.extCurve_of_ge h2]
    refine le_min ?_ le_rfl
    have hc := hP.le_line₁ (right_mem_Icc.mpr hcξ)
    rw [hP.right_end, ← hP.admissible.line₂_ξ₀] at hc
    unfold Params.line₁ Params.line₂ at hc ⊢
    nlinarith
  push Not at h1 h2
  rw [extCurve_of_mem ⟨h1.le, h2.le⟩]
  exact hP.obstacle ξ ⟨h1.le, h2.le⟩

theorem t_le_ext {ξ : ℝ} (hξ : 0 ≤ ξ) : θ.t ≤ extCurve θ P ξ := by
  have hadm := hP.admissible
  have hcξ := hP.c_le_ξ₀
  by_cases h1 : ξ ≤ θ.c
  · rw [hP.extCurve_of_le h1]
    unfold Params.line₁ Params.δ δF
    linarith [hadm.t_le_p]
  by_cases h2 : θ.ξ₀ ≤ ξ
  · rw [hP.extCurve_of_ge h2]
    have := (hP.ext_incr h2).1
    rw [hP.extCurve_of_ge le_rfl, hP.extCurve_of_ge h2, hadm.line₂_ξ₀] at this
    have := mul_nonneg hadm.h_pos.le (sub_nonneg.mpr h2)
    linarith [hadm.t_lt_one]
  push Not at h1 h2
  rw [extCurve_of_mem ⟨h1.le, h2.le⟩]
  exact hadm.t_le_p.trans (hP.p_le ⟨h1.le, h2.le⟩)

omit hP in
theorem ext_eventuallyEq {x : ℝ} (hx : x ∈ Ioo θ.c θ.ξ₀) : extCurve θ P =ᶠ[𝓝 x] P := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact extCurve_of_mem (Ioo_subset_Icc_self hy)

end InClass

end FixedPrice.TwoUnit.Family
