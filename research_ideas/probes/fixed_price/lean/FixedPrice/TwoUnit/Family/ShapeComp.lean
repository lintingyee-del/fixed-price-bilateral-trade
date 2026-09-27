import FixedPrice.TwoUnit.Family.ShapeODE

/-!
# Work package B, part 11: the free set is a single interval

Around a free point `x₀` the nearest contacts `a < x₀ < b` bound a free stretch. The curve is
strictly concave there, so it cannot leave and return to the same affine obstacle: `a` touches
only `ξ + δ_f` and `b` only `h_f ξ + e_f`. The difference `line₁ - line₂` is then increasing,
so every free stretch contains its zero, and there is only one free stretch. Before it the curve
is on `line₁`, after it on `line₂`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

/-- A free component with its arc data. -/
structure Comp (θ : Params) (d : ℝ) (w : H θ) (x₀ a b K C : ℝ) : Prop where
  ax : a < x₀
  xb : x₀ < b
  free : Free θ w a b
  Pa : Pstar θ w a = θ.U a
  Pb : Pstar θ w b = θ.U b
  maxa : ∀ ξ ∈ Icc θ.c x₀, Pstar θ w ξ = θ.U ξ → ξ ≤ a
  minb : ∀ ξ ∈ Icc x₀ θ.ξ₀, Pstar θ w ξ = θ.U ξ → b ≤ ξ
  ishat : IsHat θ d w a b K
  a_pos : 0 < a
  C_pos : 0 < C
  C_eq : ∀ t ∈ Ioo a b, Cfun θ d w K t = C
  bounds : ∀ t ∈ Icc a b, 0 < hat θ d w K t ∧ hat θ d w K t < 1
  la : θ.line₁ a < θ.line₂ a
  lb : θ.line₂ b < θ.line₁ b

namespace Setting

variable {d : ℝ} {w : H θ} (S : Setting θ d w)
include S

theorem component {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo θ.c θ.ξ₀) (hlt : Pstar θ w x₀ < θ.U x₀) :
    ∃ a b, a < x₀ ∧ x₀ < b ∧ Free θ w a b ∧ Pstar θ w a = θ.U a ∧ Pstar θ w b = θ.U b ∧
      (∀ ξ ∈ Icc θ.c x₀, Pstar θ w ξ = θ.U ξ → ξ ≤ a) ∧
      (∀ ξ ∈ Icc x₀ θ.ξ₀, Pstar θ w ξ = θ.U ξ → b ≤ ξ) := by
  set Ks := Icc θ.c θ.ξ₀ ∩ (fun ξ => Pstar θ w ξ - θ.U ξ) ⁻¹' {0} with hKs
  have hKc : IsClosed Ks :=
    (S.continuousOn_Pstar.sub (continuous_U (θ := θ)).continuousOn).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have memK : ∀ ξ, ξ ∈ Ks ↔ ξ ∈ Icc θ.c θ.ξ₀ ∧ Pstar θ w ξ = θ.U ξ := by
    intro ξ
    simp only [hKs, mem_inter_iff, mem_preimage, mem_singleton_iff, sub_eq_zero]
  have hc : θ.c ∈ Ks := (memK _).mpr ⟨left_mem_Icc.mpr S.c_lt.le, by rw [Pstar_c, S.U_c]⟩
  have hξ₀ : θ.ξ₀ ∈ Ks := by
    refine (memK _).mpr ⟨right_mem_Icc.mpr S.c_lt.le, ?_⟩
    rw [S.Pstar_ξ₀]
    unfold Params.U
    rw [S.adm.line₂_ξ₀, min_eq_right S.line₁_ξ₀]
  have hLc : IsCompact (Ks ∩ Icc θ.c x₀) := isCompact_Icc.inter_left hKc
  have hRc : IsCompact (Ks ∩ Icc x₀ θ.ξ₀) := isCompact_Icc.inter_left hKc
  have hLne : (Ks ∩ Icc θ.c x₀).Nonempty := ⟨θ.c, hc, left_mem_Icc.mpr hx₀.1.le⟩
  have hRne : (Ks ∩ Icc x₀ θ.ξ₀).Nonempty := ⟨θ.ξ₀, hξ₀, right_mem_Icc.mpr hx₀.2.le⟩
  have ha := hLc.sSup_mem hLne
  have hb := hRc.sInf_mem hRne
  set a := sSup (Ks ∩ Icc θ.c x₀) with hadef
  set b := sInf (Ks ∩ Icc x₀ θ.ξ₀) with hbdef
  have hx₀K : x₀ ∉ Ks := fun h => absurd ((memK _).mp h).2 hlt.ne
  have hax : a < x₀ := lt_of_le_of_ne ha.2.2 fun h => hx₀K (h ▸ ha.1)
  have hxb : x₀ < b := lt_of_le_of_ne hb.2.1 fun h => hx₀K (h.symm ▸ hb.1)
  have hmaxa : ∀ ξ ∈ Icc θ.c x₀, Pstar θ w ξ = θ.U ξ → ξ ≤ a := fun ξ hξ hP =>
    le_csSup hLc.bddAbove ⟨(memK _).mpr ⟨⟨hξ.1, hξ.2.trans hx₀.2.le⟩, hP⟩, hξ⟩
  have hminb : ∀ ξ ∈ Icc x₀ θ.ξ₀, Pstar θ w ξ = θ.U ξ → b ≤ ξ := fun ξ hξ hP =>
    csInf_le hRc.bddBelow ⟨(memK _).mpr ⟨⟨hx₀.1.le.trans hξ.1, hξ.2⟩, hP⟩, hξ⟩
  have haK := (memK _).mp ha.1
  have hbK := (memK _).mp hb.1
  refine ⟨a, b, hax, hxb, ⟨ha.2.1, hax.trans hxb, hb.2.2, fun ξ hξ => ?_⟩, haK.2, hbK.2, hmaxa,
    hminb⟩
  have hξI : ξ ∈ Ioc θ.c θ.ξ₀ := ⟨lt_of_le_of_lt ha.2.1 hξ.1, hξ.2.le.trans hb.2.2⟩
  rw [← S.Pstar_lt_U_iff hξI]
  refine lt_of_le_of_ne (S.Pstar_le_U ⟨hξI.1.le, hξI.2⟩) fun hP => ?_
  rcases le_total ξ x₀ with h | h
  · exact absurd (hmaxa ξ ⟨hξI.1.le, h⟩ hP) (not_le.mpr hξ.1)
  · exact absurd (hminb ξ ⟨h, hξI.2⟩ hP) (not_le.mpr hξ.2)

omit S in
/-- A strictly concave curve cannot touch the same affine obstacle at both ends. -/
theorem not_both {a b α γ : ℝ} (hab : a < b) (hstrict : StrictConcaveOn ℝ (Icc a b) (Pstar θ w))
    (hle : ∀ ξ ∈ Icc a b, Pstar θ w ξ ≤ α * ξ + γ) (ha : Pstar θ w a = α * a + γ)
    (hb : Pstar θ w b = α * b + γ) : False := by
  have h := hstrict.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab.ne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have hm := hle ((1 / 2) * a + (1 / 2) * b) ⟨by linarith, by linarith⟩
  rw [ha, hb] at h
  linarith

theorem line_activity {a b : ℝ} (hF : Free θ w a b) (hPa : Pstar θ w a = θ.U a)
    (hPb : Pstar θ w b = θ.U b) (hstrict : StrictConcaveOn ℝ (Icc a b) (Pstar θ w)) :
    θ.line₁ a < θ.line₂ a ∧ θ.line₂ b < θ.line₁ b := by
  have h1le : ∀ ξ ∈ Icc a b, Pstar θ w ξ ≤ 1 * ξ + θ.δ := fun ξ hξ => by
    have := (S.Pstar_le_U (hF.sub_Icc hξ)).trans (min_le_left _ _)
    unfold Params.line₁ at this; linarith
  have h2le : ∀ ξ ∈ Icc a b, Pstar θ w ξ ≤ θ.h * ξ + θ.e := fun ξ hξ =>
    (S.Pstar_le_U (hF.sub_Icc hξ)).trans (min_le_right _ _)
  have n1 : ¬(θ.line₁ a ≤ θ.line₂ a ∧ θ.line₁ b ≤ θ.line₂ b) := by
    rintro ⟨ha, hb⟩
    refine not_both hF.ab hstrict h1le ?_ ?_
    · rw [hPa]; unfold Params.U; rw [min_eq_left ha]; unfold Params.line₁; ring
    · rw [hPb]; unfold Params.U; rw [min_eq_left hb]; unfold Params.line₁; ring
  have n2 : ¬(θ.line₂ a ≤ θ.line₁ a ∧ θ.line₂ b ≤ θ.line₁ b) := by
    rintro ⟨ha, hb⟩
    refine not_both hF.ab hstrict h2le ?_ ?_
    · rw [hPa]; unfold Params.U; rw [min_eq_right ha]; rfl
    · rw [hPb]; unfold Params.U; rw [min_eq_right hb]; rfl
  have hdc : θ.line₁ θ.c ≤ θ.line₂ θ.c := by rw [Params.line₁_c]; exact S.line₂_c
  have hca := hF.ca
  have hab := hF.ab
  unfold Params.line₁ Params.line₂ at n1 n2 hdc ⊢
  have kab : (b + θ.δ - (θ.h * b + θ.e)) - (a + θ.δ - (θ.h * a + θ.e)) =
      (1 - θ.h) * (b - a) := by ring
  have kca : (a + θ.δ - (θ.h * a + θ.e)) - (θ.c + θ.δ - (θ.h * θ.c + θ.e)) =
      (1 - θ.h) * (a - θ.c) := by ring
  by_contra hcon
  rw [not_and_or, not_lt, not_lt] at hcon
  rcases hcon with h | h
  · -- `line₂` active at `a`
    have hb1 : b + θ.δ < θ.h * b + θ.e := by
      by_contra hb; push_neg at hb; exact n2 ⟨h, hb⟩
    have hs : 1 - θ.h < 0 := by
      by_contra hs; push_neg at hs
      have := mul_nonneg hs (sub_nonneg.mpr hab.le)
      linarith
    have := mul_nonpos_of_nonpos_of_nonneg hs.le (sub_nonneg.mpr hca)
    exact n1 ⟨by linarith, hb1.le⟩
  · -- `line₁` active at `b`
    have ha1 : θ.h * a + θ.e < a + θ.δ := by
      by_contra ha; push_neg at ha; exact n1 ⟨ha, h⟩
    have hs : 1 - θ.h < 0 := by
      by_contra hs; push_neg at hs
      have := mul_nonneg hs (sub_nonneg.mpr hab.le)
      linarith
    have := mul_nonpos_of_nonpos_of_nonneg hs.le (sub_nonneg.mpr hca)
    linarith

theorem exists_comp {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo θ.c θ.ξ₀) (hlt : Pstar θ w x₀ < θ.U x₀) :
    ∃ a b K C, Comp θ d w x₀ a b K C := by
  obtain ⟨a, b, hax, hxb, hF, hPa, hPb, hmaxa, hminb⟩ := S.component hx₀ hlt
  have hza : a = θ.c ∨ zfun θ w a = Real.log (θ.U a) := by
    rcases eq_or_lt_of_le hF.ca with h | h
    · exact Or.inl h.symm
    · exact Or.inr ((Setting.Pstar_eq_iff h (S.U_pos hF.ca)).mp hPa)
  have hzb : zfun θ w b = Real.log (θ.U b) :=
    (Setting.Pstar_eq_iff (lt_of_le_of_lt hF.ca hF.ab) (S.U_pos (hF.ca.trans hF.ab.le))).mp hPb
  obtain ⟨K, C, hK, ha0, hC0, hC, hbounds⟩ := S.free_arc hF hza hzb
  obtain ⟨hla, hlb⟩ := S.line_activity hF hPa hPb (S.strictConcaveOn_Pstar hF hK hC hC0)
  exact ⟨a, b, K, C, ⟨hax, hxb, hF, hPa, hPb, hmaxa, hminb, hK, ha0, hC0, hC, hbounds, hla, hlb⟩⟩

omit S in
theorem slope_pos {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) : 0 < 1 - θ.h := by
  have hla := hc.la
  have hlb := hc.lb
  have hab := hc.free.ab
  unfold Params.line₁ Params.line₂ at hla hlb
  by_contra hs; push_neg at hs
  have := mul_nonpos_of_nonpos_of_nonneg hs (sub_nonneg.mpr hab.le)
  nlinarith

/-- Every free point lies in the component `(a, b)`. -/
theorem free_sub {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) {x₁ : ℝ}
    (hx₁ : x₁ ∈ Ioo θ.c θ.ξ₀) (hlt₁ : Pstar θ w x₁ < θ.U x₁) : x₁ ∈ Ioo a b := by
  obtain ⟨a₁, b₁, K₁, C₁, hc₁⟩ := S.exists_comp hx₁ hlt₁
  have hs := slope_pos hc
  by_contra hnot
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hnot
  rcases hnot with h | h
  · have hb₁ : b₁ ≤ a := hc₁.minb a ⟨h, hc.free.ab.le.trans hc.free.bξ⟩ hc.Pa
    have h1 := hc₁.lb
    have h2 := hc.la
    unfold Params.line₁ Params.line₂ at h1 h2
    have := mul_nonneg hs.le (sub_nonneg.mpr hb₁)
    nlinarith
  · have ha₁ : b ≤ a₁ := hc₁.maxa b ⟨hc.free.ca.trans hc.free.ab.le, h⟩ hc.Pb
    have h1 := hc₁.la
    have h2 := hc.lb
    unfold Params.line₁ Params.line₂ at h1 h2
    have := mul_nonneg hs.le (sub_nonneg.mpr ha₁)
    nlinarith

theorem left_contact {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) :
    ∀ ξ ∈ Icc θ.c a, Pstar θ w ξ = θ.line₁ ξ := by
  intro ξ hξ
  have hbξ := hc.free.bξ
  have hab := hc.free.ab
  have hU : Pstar θ w ξ = θ.U ξ := by
    rcases eq_or_lt_of_le hξ.1 with h | h
    · rw [← h, Pstar_c, S.U_c]
    · by_contra hne
      have hlt := lt_of_le_of_ne (S.Pstar_le_U ⟨hξ.1, hξ.2.trans (hab.le.trans hbξ)⟩) hne
      have := S.free_sub hc ⟨h, lt_of_le_of_lt hξ.2 (lt_of_lt_of_le hab hbξ)⟩ hlt
      linarith [this.1, hξ.2]
  rw [hU]
  unfold Params.U
  apply min_eq_left
  have hs := slope_pos hc
  have hla := hc.la
  unfold Params.line₁ Params.line₂ at hla ⊢
  have := mul_nonneg hs.le (sub_nonneg.mpr hξ.2)
  nlinarith

theorem right_contact {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) :
    ∀ ξ ∈ Icc b θ.ξ₀, Pstar θ w ξ = θ.line₂ ξ := by
  intro ξ hξ
  have hab := hc.free.ab
  have hca := hc.free.ca
  have hs := slope_pos hc
  have hlb := hc.lb
  have hdl : θ.line₂ ξ ≤ θ.line₁ ξ := by
    unfold Params.line₁ Params.line₂ at hlb ⊢
    have := mul_nonneg hs.le (sub_nonneg.mpr hξ.1)
    nlinarith
  have hU : Pstar θ w ξ = θ.U ξ := by
    rcases eq_or_lt_of_le hξ.2 with h | h
    · rw [h, S.Pstar_ξ₀]
      unfold Params.U
      rw [S.adm.line₂_ξ₀, min_eq_right S.line₁_ξ₀]
    · by_contra hne
      have hcξ : θ.c < ξ := lt_of_le_of_lt hca (lt_of_lt_of_le hab hξ.1)
      have hlt := lt_of_le_of_ne (S.Pstar_le_U ⟨hcξ.le, hξ.2⟩) hne
      have := S.free_sub hc ⟨hcξ, h⟩ hlt
      linarith [this.2, hξ.1]
  rw [hU]
  unfold Params.U
  exact min_eq_right hdl

end Setting

end Relaxed

end FixedPrice.TwoUnit.Family
