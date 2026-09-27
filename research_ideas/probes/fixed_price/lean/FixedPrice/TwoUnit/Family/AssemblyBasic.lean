import FixedPrice.TwoUnit.Family.Statements

/-!
# Work package F, helpers

* The trial interval: `0 < βlo < βhi < 3/4`, and `d_f > 0` on it.
* The sign of `K_f` is the sign of `β - R_f` (ratio form of the comparison).
* `r_fam ≤ R_f` on the class.
* A positive maximum of `K_f`, or a minimum of `R_f` with value `β`, in the trial interval is a
  physical stationary point whose recovery formulas reproduce the curve's parameters and contact
  data (`lem:2fam-boundary` and the stationary reduction).
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal
open FixedPrice.TwoUnit (GenInstance HasCommonEscapingAtom LawsConvergeTo)

namespace FixedPrice.TwoUnit.Family

theorem βlo_pos : 0 < βlo := by unfold βlo; norm_num

theorem βlo_lt_βhi : βlo < βhi := by unfold βlo βhi; norm_num

theorem βhi_lt : βhi < 3 / 4 := by unfold βhi; norm_num

theorem βhi_lt_one : βhi < 1 := βhi_lt.trans (by norm_num)

theorem mem_trial_bounds {β : ℝ} (hβ : β ∈ Icc βlo βhi) : 0 < β ∧ β < 1 ∧ β ≤ 3 / 4 :=
  ⟨βlo_pos.trans_le hβ.1, hβ.2.trans_lt βhi_lt_one, (hβ.2.trans βhi_lt.le)⟩

theorem dOf_pos {β : ℝ} (h0 : 0 < β) (h1 : β < 1) : 0 < dOf β := by
  unfold dOf; exact div_pos (by linarith) h0

section Signs

variable (hPos : PositivityStatement) (hCmp : ComparisonStatement)
include hPos hCmp

theorem Kf_eq_ratio {β : ℝ} (hβ : 0 < β) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) :
    Kf β θ P = (Mf θ P + Gf θ P) / θ.N * (1 - Rf θ P / β) ∧
      0 < (Mf θ P + Gf θ P) / θ.N := by
  have hpos := hPos θ P hP
  exact ⟨(hCmp β θ P hP hβ).2.2, div_pos (by linarith [hpos.2.1, hpos.2.2.1]) hpos.1⟩

theorem Kf_pos_iff {β : ℝ} (hβ : 0 < β) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) :
    0 < Kf β θ P ↔ Rf θ P < β := by
  obtain ⟨hK, hc⟩ := Kf_eq_ratio hPos hCmp hβ hP
  rw [hK, mul_pos_iff_of_pos_left hc, sub_pos, div_lt_one hβ]

theorem Kf_neg_iff {β : ℝ} (hβ : 0 < β) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) :
    Kf β θ P < 0 ↔ β < Rf θ P := by
  obtain ⟨hK, hc⟩ := Kf_eq_ratio hPos hCmp hβ hP
  rw [hK]
  constructor
  · intro h
    have hx : 1 - Rf θ P / β < 0 := by
      by_contra hx; push Not at hx; linarith [mul_nonneg hc.le hx]
    rwa [sub_neg, one_lt_div hβ] at hx
  · intro h
    exact mul_neg_of_pos_of_neg hc (by rwa [sub_neg, one_lt_div hβ])

theorem Kf_eq_zero_iff {β : ℝ} (hβ : 0 < β) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) :
    Kf β θ P = 0 ↔ Rf θ P = β := by
  obtain ⟨hK, hc⟩ := Kf_eq_ratio hPos hCmp hβ hP
  rw [hK, mul_eq_zero, or_iff_right hc.ne', sub_eq_zero, eq_comm, div_eq_one_iff_eq hβ.ne']

theorem Kf_le_zero_of_le {β : ℝ} (hβ : 0 < β) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
    (h : β ≤ Rf θ P) : Kf β θ P ≤ 0 := by
  rcases eq_or_lt_of_le h with h | h
  · exact ((Kf_eq_zero_iff hPos hCmp hβ hP).mpr h.symm).le
  · exact ((Kf_neg_iff hPos hCmp hβ hP).mpr h).le

end Signs

/-- A negative comparison numerator gives `K_f < 0`. -/
theorem Kf_neg_of_num {β : ℝ} (hβ : 0 < β) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
    (h : β * Gf θ P - (1 - β) * Mf θ P - 2 < 0) : Kf β θ P < 0 := by
  unfold Kf
  have hN : 0 < θ.N := by
    unfold Params.N NF; have := hP.admissible.t_pos; positivity
  exact div_neg_of_neg_of_pos h (mul_pos hβ hN)

theorem rFam_le (hPos : PositivityStatement) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) :
    rFam ≤ Rf θ P := by
  refine csInf_le ⟨0, ?_⟩ ⟨θ, P, hP, rfl⟩
  rintro r ⟨θ', P', hP', rfl⟩
  have hm : 0 < θ'.m := by
    unfold Params.m mF; have := hP'.admissible.t_pos; positivity
  exact hm.le.trans (hPos θ' P' hP').2.2.2.2.1

theorem params_eq_elim {d : ℝ} {θ : Params} (h : θ.ξ₀ = Elim.ξ₀ d θ.t θ.p) :
    θ = Elim.params d θ.t θ.p := by
  cases θ
  simp only [Elim.params] at h ⊢
  rw [h]

theorem R_nonneg (hPos : PositivityStatement) {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) :
    0 ≤ Rf θ P := by
  have hm : 0 < θ.m := by
    unfold Params.m mF; have := hP.admissible.t_pos; positivity
  exact hm.le.trans (hPos θ P hP).2.2.2.2.1

/-- The stationary reduction at an extremal curve of the trial interval: the point is physical,
the parameters are the recovered ones (any property of `θ` transfers to `Elim.params`), and the
curve is three-arc with the recovered contact data. -/
theorem stationary_of_extremal (hBd : BoundaryStatement) (hRed : ReductionStatement) {β : ℝ}
    (hβ : β ∈ Icc βlo βhi) {θ : Params} {P : ℝ → ℝ}
    (hext : (IsGlobalMaxK β θ P ∧ 0 < Kf β θ P) ∨ (IsGlobalMinR θ P ∧ Rf θ P = β))
    (hP : InClass θ P) :
    PhysStationary (dOf β) θ.t θ.p ∧
      (∀ Φ : Params → Prop, Φ θ → Φ (Elim.params (dOf β) θ.t θ.p)) ∧
      ThreeArc (dOf β) (Elim.params (dOf β) θ.t θ.p) P (Elim.ξl (dOf β) θ.t θ.p)
        (Elim.ξr (dOf β) θ.t θ.p) (Elim.C (dOf β) θ.t θ.p) := by
  obtain ⟨hβ0, hβ1, -⟩ := mem_trial_bounds hβ
  obtain ⟨htp, hp1, ξl, ξr, C, hTA, hcl, hrξ, hsP, hsH, hsT⟩ := hBd β hβ θ P hext
  obtain ⟨hPS, hξ₀, hξl, hξr, hC⟩ :=
    hRed (dOf β) θ P ξl ξr C (dOf_pos hβ0 hβ1) hP hTA hcl hrξ htp hp1 hsP hsH hsT
  have htr : ∀ Φ : Params → Prop, Φ θ → Φ (Elim.params (dOf β) θ.t θ.p) := fun Φ hΦ =>
    @Eq.subst _ Φ _ _ (params_eq_elim hξ₀) hΦ
  refine ⟨hPS, htr, ?_⟩
  rw [← hξl, ← hξr, ← hC]
  exact htr (fun x => ThreeArc (dOf β) x P ξl ξr C) hTA

end FixedPrice.TwoUnit.Family
