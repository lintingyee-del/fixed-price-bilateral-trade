import FixedPrice.TwoUnit.Family.BoundaryVarArc

/-!
# Work package C, helpers: contacts, the face `p_f = t_f`, and outer stationarity

At a three-arc global maximizer of `K_f` (`MaxData`):

* `final_contact_pos`: `ξ_r < ξ₀` (the lengthening variation, certified `right_variation`);
* `initial_contact_pos`: `c_f < ξ_ℓ` when `c_f > 0` (lowering `p_f`, certified `left_variation`);
* `not_face`: `t_f < p_f` (one-sided `p`-variation, certified `envelope_p`);
* `statP_zero`, `statT_zero`, `statH_zero`: the three expressions of `(eq:2fam-stationarity)`
  vanish (two-sided `p`-, `t`- and `h`-variations, certified `envelope_p`, `envelope_t`,
  `envelope_h`).
-/

noncomputable section
open Real Set Filter Topology MeasureTheory
open scoped Interval

namespace FixedPrice.TwoUnit.Family
namespace PkgC


/-! ### The contacts have positive length -/

section Cases

variable {β : ℝ} {θ : Params} {P : ℝ → ℝ} {ξl ξr C La Lb : ℝ}

lemma params_eta (θ : Params) : (⟨θ.t, θ.p, θ.ξ₀⟩ : Params) = θ := rfl

/-- `ξ_r < ξ₀`: at a zero final contact, lengthening the curve (`ξ₀ ↦ ξ₀ + s`, the arc lowered by
`s H_R` at `ξ₀` and continued by its tangent) raises `K_f` at rate `ξ₀ H_R² > 0`
(`(eq:2fam-right-variation)`, certified `right_variation`). -/
theorem final_contact_pos (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities) :
    ξr < θ.ξ₀ := by
  rcases lt_or_eq_of_le hM.hA3.r_le with h | hr
  · exact h
  exfalso
  have hadm := hM.hP.admissible
  have hPr : P ξr = 1 := by rw [hr]; exact hM.hP.right_end
  have hD := hM.Dtil_nonpos hI (θf := fun s => ⟨θ.t, θ.p, θ.ξ₀ + s⟩) (ya := 0) (ma := 0)
    (yb := -Lb) (mb := 0) (t₁ := 0) (p₁ := 0) (x₁ := 1)
    (by simp only [add_zero]) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    (by simpa using (hasDerivAt_id (0 : ℝ)).const_add θ.ξ₀)
    (by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
      refine ⟨⟨hadm.t_pos, hadm.t_lt_one, hadm.t_le_p, hadm.p_le_one,
        by show 0 < θ.ξ₀ + s; linarith [hadm.ξ₀_pos],
        by show θ.c ≤ θ.ξ₀ + s; linarith [hadm.c_le_ξ₀]⟩,
        hM.hA3.c_le, by show ξr ≤ θ.ξ₀ + s; linarith, by simpa using hM.hLa_1, ?_, ?_, ?_⟩
      · show θ.v / (θ.ξ₀ + s) ≤ Lb + s * 0
        rw [mul_zero, add_zero]
        refine le_trans ?_ hM.hLb_h
        show θ.v / (θ.ξ₀ + s) ≤ θ.v / θ.ξ₀
        exact div_le_div_of_nonneg_left hadm.v_pos.le hadm.ξ₀_pos (by linarith)
      · show P ξl + s * 0 + (La + s * 0) * (θ.c - ξl) = θ.p
        simpa using hM.P_c
      · show P ξr + s * -Lb + (Lb + s * 0) * (θ.ξ₀ + s - ξr) = 1
        rw [hPr, hr]; ring)
  have hPl0 : P ξl ≠ 0 := (hM.hP.pos' ⟨hM.hA3.c_le, (hM.hA3.l_lt_r.trans_le hM.hA3.r_le).le⟩).ne'
  rw [Dtil_right hPr hr hM.Lb_pos.ne' hPl0 hadm.t_pos.ne' hadm.p_pos.ne' hM.La_pos.ne',
    hI.right_variation] at hD
  have : 0 < θ.ξ₀ * Lb ^ 2 := by have := hM.Lb_pos; have := hadm.ξ₀_pos; positivity
  linarith

/-- `c_f < ξ_ℓ` when `c_f > 0`: at a zero initial contact, lowering `p_f` (the arc lowered by
`s (1 - H_L/2)` at `c_f` and continued by its tangent) raises `K_f` at rate
`c_f (H_L - 2)²/(2 p_f²) > 0` (`(eq:2fam-left-variation)`, certified `left_variation`). -/
theorem initial_contact_pos (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities)
    (hc : 0 < θ.c) : θ.c < ξl := by
  rcases lt_or_eq_of_le hM.hA3.c_le with h | hl
  · exact h
  exfalso
  have hadm := hM.hP.admissible
  have hPl : P ξl = θ.p := by rw [← hl]; exact hM.hP.left_end
  have hcdef : θ.c = (θ.p - θ.t) / 2 := rfl
  have hD := hM.Dtil_nonpos hI (θf := fun s => ⟨θ.t, θ.p - s, θ.ξ₀⟩) (ya := -(1 - La / 2))
    (ma := 0) (yb := 0) (mb := 0) (t₁ := 0) (p₁ := -1) (x₁ := 0)
    (by simp only [sub_zero]) (hasDerivAt_const _ _)
    (by simpa using (hasDerivAt_id (0 : ℝ)).const_sub θ.p) (hasDerivAt_const _ _)
    (by
      filter_upwards [Ico_mem_nhdsGE (by linarith : (0 : ℝ) < 2 * θ.c)] with s hs
      obtain ⟨hs0, hs1⟩ := hs
      have hcs : cF θ.t (θ.p - s) = θ.c - s / 2 := by unfold cF; rw [hcdef]; ring
      refine ⟨⟨hadm.t_pos, hadm.t_lt_one, by show θ.t ≤ θ.p - s; linarith,
        by show θ.p - s ≤ 1; linarith [hadm.p_le_one], hadm.ξ₀_pos,
        by show cF θ.t (θ.p - s) ≤ θ.ξ₀; rw [hcs]; linarith [hadm.c_le_ξ₀]⟩,
        by show cF θ.t (θ.p - s) ≤ ξl; rw [hcs]; linarith, hM.hA3.r_le,
        by simpa using hM.hLa_1, by simpa using hM.hLb_h, ?_, ?_⟩
      · show P ξl + s * -(1 - La / 2) + (La + s * 0) * (cF θ.t (θ.p - s) - ξl) = θ.p - s
        rw [hPl, ← hl]
        unfold cF
        rw [hcdef]
        ring
      · show P ξr + s * 0 + (Lb + s * 0) * (θ.ξ₀ - ξr) = 1
        simpa using hM.P_ξ₀)
  have hPr0 : P ξr ≠ 0 := (hM.hP.pos' ⟨hM.hA3.c_le.trans hM.hA3.l_lt_r.le, hM.hA3.r_le⟩).ne'
  rw [Dtil_left hPl hl.symm hadm.t_pos.ne' hadm.p_pos.ne' hM.La_pos.ne' hM.Lb_pos.ne' hPr0,
    hI.left_variation θ.t θ.p (dOf β) La hadm.t_pos hadm.p_pos] at hD
  have hc' : 0 < cF θ.t θ.p := hc
  have : 0 < cF θ.t θ.p * (La - 2) ^ 2 / (2 * θ.p ^ 2) := by
    have : La - 2 ≠ 0 := by linarith [hM.hLa_1]
    have := hadm.p_pos
    positivity
  linarith

end Cases


/-! ### The face `p = t` and the stationarity equations -/

section Stationarity

variable {β : ℝ} {θ : Params} {P : ℝ → ℝ} {ξl ξr C La Lb : ℝ}

lemma eventually_pos_nhds {f : ℝ → ℝ} (hf : Continuous f) (h0 : 0 < f 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), 0 < f s :=
  (hf.tendsto 0).eventually (lt_mem_nhds h0)

/-- The contact data at interior contacts. -/
lemma contact_data (hM : MaxData β θ P ξl ξr C La Lb) (hr : ξr < θ.ξ₀) (hl : θ.c < ξl) :
    La = 1 ∧ Lb = θ.h ∧ P ξl = θ.line₁ ξl ∧ ξl = θ.line₁ ξl - θ.δ ∧
      P ξr = θ.line₂ ξr ∧ ξr = (θ.line₂ ξr - θ.e) / θ.h ∧ θ.ξ₀ = (1 - θ.e) / θ.h ∧
      0 < θ.line₁ ξl ∧ 0 < θ.line₂ ξr := by
  have hadm := hM.hP.admissible
  have hh := hadm.h_pos
  have hPl : P ξl = θ.line₁ ξl := hM.hA3.left_contact ξl ⟨hM.hA3.c_le, le_rfl⟩
  have hPr : P ξr = θ.line₂ ξr := hM.hA3.right_contact ξr ⟨le_rfl, hM.hA3.r_le⟩
  refine ⟨hM.hLa_one hl, hM.hLb_eq hr, hPl, by unfold Params.line₁; ring, hPr, ?_, ?_, ?_, ?_⟩
  · unfold Params.line₂; field_simp; ring
  · show θ.ξ₀ = (1 - θ.e) / (θ.v / θ.ξ₀)
    have : θ.v = 1 - θ.e := by show vF θ.t = 1 - eF θ.t; rfl
    rw [← this]; field_simp [hadm.v_pos.ne']
  · rw [← hPl]; exact hM.hP.pos' ⟨hM.hA3.c_le, (hM.hA3.l_lt_r.trans_le hM.hA3.r_le).le⟩
  · rw [← hPr]; exact hM.hP.pos' ⟨hM.hA3.c_le.trans hM.hA3.l_lt_r.le, hM.hA3.r_le⟩

/-- The `p`-variation at interior contacts gives `statP/2` as the one-sided derivative. -/
lemma p_variation (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities) (hr : ξr < θ.ξ₀)
    (hl : θ.c < ξl) {l : Filter ℝ} (hl0 : l = 𝓝[≥] 0 ∨ l = 𝓝 0)
    (hev : ∀ᶠ s in l, θ.t ≤ θ.p + s ∧ θ.p + s ≤ 1 ∧ θ.c + s / 2 ≤ ξl) :
    (l = 𝓝[≥] 0 → statP (dOf β) θ (θ.line₁ ξl) ≤ 0) ∧
      (l = 𝓝 0 → statP (dOf β) θ (θ.line₁ ξl) = 0) := by
  obtain ⟨hLa, hLb, hPl, hξl, hPr, -, -, hl0', hr0'⟩ := contact_data hM hr hl
  have hadm := hM.hP.admissible
  have hcs : ∀ s, cF θ.t (θ.p + s) = θ.c + s / 2 := fun s => by
    show (θ.p + s - θ.t) / 2 = (θ.p - θ.t) / 2 + s / 2; ring
  have hleft : ∀ s, P ξl + s * (1 / 2) + (La + s * 0) * ((Params.mk θ.t (θ.p + s) θ.ξ₀).c - ξl)
      = (Params.mk θ.t (θ.p + s) θ.ξ₀).p := by
    intro s
    show P ξl + s * (1 / 2) + (La + s * 0) * (cF θ.t (θ.p + s) - ξl) = θ.p + s
    rw [hcs, hLa]
    have := hM.P_c
    rw [hLa] at this
    linarith
  have hright : ∀ s, P ξr + s * 0 + (Lb + s * 0) * ((Params.mk θ.t (θ.p + s) θ.ξ₀).ξ₀ - ξr) = 1 :=
    fun s => by simpa using hM.P_ξ₀
  have hev' : ∀ᶠ s in l, (Params.mk θ.t (θ.p + s) θ.ξ₀).Admissible ∧
      (Params.mk θ.t (θ.p + s) θ.ξ₀).c ≤ ξl ∧ ξr ≤ (Params.mk θ.t (θ.p + s) θ.ξ₀).ξ₀ ∧
      La + s * 0 ≤ 1 ∧ (Params.mk θ.t (θ.p + s) θ.ξ₀).h ≤ Lb + s * 0 ∧
      P ξl + s * (1 / 2) + (La + s * 0) * ((Params.mk θ.t (θ.p + s) θ.ξ₀).c - ξl)
        = (Params.mk θ.t (θ.p + s) θ.ξ₀).p ∧
      P ξr + s * 0 + (Lb + s * 0) * ((Params.mk θ.t (θ.p + s) θ.ξ₀).ξ₀ - ξr) = 1 := by
    filter_upwards [hev] with s ⟨h1, h2, h3⟩
    refine ⟨⟨hadm.t_pos, hadm.t_lt_one, h1, h2, hadm.ξ₀_pos, ?_⟩, ?_, hM.hA3.r_le,
      by rw [hLa]; simp, by rw [hLb]; simp; rfl, hleft s, hright s⟩
    · show cF θ.t (θ.p + s) ≤ θ.ξ₀
      rw [hcs]; linarith [hM.hA3.l_lt_r, hM.hA3.r_le]
    · show cF θ.t (θ.p + s) ≤ ξl
      rw [hcs]; exact h3
  have hθ0 : (fun s => Params.mk θ.t (θ.p + s) θ.ξ₀) 0 = θ := by simp only [add_zero]
  have ht : HasDerivAt (fun s => (Params.mk θ.t (θ.p + s) θ.ξ₀).t) 0 0 := hasDerivAt_const _ _
  have hp : HasDerivAt (fun s => (Params.mk θ.t (θ.p + s) θ.ξ₀).p) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add θ.p
  have hx : HasDerivAt (fun s => (Params.mk θ.t (θ.p + s) θ.ξ₀).ξ₀) 0 0 := hasDerivAt_const _ _
  have hval : Dtil β θ P ξl ξr La Lb (1 / 2) 0 0 0 0 1 0 = statP (dOf β) θ (θ.line₁ ξl) / 2 := by
    rw [hLa, hLb, Dtil_p hPl hξl hPr hadm.t_pos.ne' hadm.p_pos.ne' hl0'.ne' hr0'.ne'
      hadm.h_pos.ne', hI.envelope_p (dOf β) θ (θ.line₁ ξl) (θ.line₂ ξr) hadm.t_pos hadm.p_pos hl0']
  constructor
  · intro hl1
    subst hl1
    have := hM.Dtil_nonpos hI hθ0 ht hp hx hev'
    rw [hval] at this
    linarith
  · intro hl1
    subst hl1
    have := hM.Dtil_eq_zero hI hθ0 ht hp hx hev'
    rw [hval] at this
    linarith

/-- The face `p_f = t_f` is excluded: there `2 ∂_p K_f = (t + d)(t⁻² - P_ℓ⁻²) > 0`. -/
theorem not_face (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities) (hr : ξr < θ.ξ₀)
    (hl : θ.c < ξl) (hface : θ.t = θ.p) : False := by
  have hadm := hM.hP.admissible
  have hε : 0 < min (1 - θ.p) (2 * (ξl - θ.c)) := lt_min (by linarith [hM.hp1]) (by linarith)
  have hev : ∀ᶠ s in 𝓝[≥] (0 : ℝ), θ.t ≤ θ.p + s ∧ θ.p + s ≤ 1 ∧ θ.c + s / 2 ≤ ξl := by
    filter_upwards [Ico_mem_nhdsGE hε] with s hs
    have h1 := min_le_left (1 - θ.p) (2 * (ξl - θ.c))
    have h2 := min_le_right (1 - θ.p) (2 * (ξl - θ.c))
    exact ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hs.2]⟩
  have hle := (p_variation hM hI hr hl (Or.inl rfl) hev).1 rfl
  -- at `p = t`: `δ = t` and `P_ℓ = ξ_ℓ + t > t`
  have hδ : θ.δ = θ.t := by show (θ.p + θ.t) / 2 = θ.t; rw [← hface]; ring
  have hc : θ.c = 0 := by show (θ.p - θ.t) / 2 = 0; rw [← hface]; ring
  have hPl : θ.t < θ.line₁ ξl := by
    show θ.t < ξl + θ.δ
    rw [hδ]; linarith
  have ht := hadm.t_pos
  have hd := hM.d_pos
  unfold statP at hle
  rw [hδ, ← hface] at hle
  have h1 : (θ.t + dOf β) / θ.line₁ ξl ^ 2 < (θ.t + dOf β) / θ.t ^ 2 := by
    apply div_lt_div_of_pos_left (by linarith) (by positivity)
    exact pow_lt_pow_left₀ hPl ht.le (by norm_num)
  linarith

end Stationarity


/-! ### The three stationarity equations at interior parameters -/

section Interior

variable {β : ℝ} {θ : Params} {P : ℝ → ℝ} {ξl ξr C La Lb : ℝ}

lemma eventually_pos_at {f : ℝ → ℝ} (hf : ContinuousAt f 0) (h0 : 0 < f 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), 0 < f s :=
  hf.eventually (lt_mem_nhds h0)

/-- `statP = 0` (two-sided `p`-variation). -/
theorem statP_zero (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities) (hr : ξr < θ.ξ₀)
    (hl : θ.c < ξl) (htp : θ.t < θ.p) : statP (dOf β) θ (θ.line₁ ξl) = 0 := by
  have hε : 0 < min (θ.p - θ.t) (min (1 - θ.p) (2 * (ξl - θ.c))) :=
    lt_min (by linarith) (lt_min (by linarith [hM.hp1]) (by linarith))
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), θ.t ≤ θ.p + s ∧ θ.p + s ≤ 1 ∧ θ.c + s / 2 ≤ ξl := by
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hε) hε] with s hs
    have h1 := min_le_left (θ.p - θ.t) (min (1 - θ.p) (2 * (ξl - θ.c)))
    have h2 := min_le_right (θ.p - θ.t) (min (1 - θ.p) (2 * (ξl - θ.c)))
    have h3 := min_le_left (1 - θ.p) (2 * (ξl - θ.c))
    have h4 := min_le_right (1 - θ.p) (2 * (ξl - θ.c))
    exact ⟨by linarith [hs.1], by linarith [hs.2], by linarith [hs.2]⟩
  exact (p_variation hM hI hr hl (Or.inr rfl) hev).2 rfl

/-- `statT = 0` (two-sided `t`-variation at fixed `(p, h)`). -/
theorem statT_zero (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities) (hr : ξr < θ.ξ₀)
    (hl : θ.c < ξl) (htp : θ.t < θ.p) :
    statT (dOf β) θ (θ.line₁ ξl) (θ.line₂ ξr) = 0 := by
  obtain ⟨hLa, hLb, hPl, hξl, hPr, hξr, hξ₀, hl0', hr0'⟩ := contact_data hM hr hl
  have hadm := hM.hP.admissible
  have hh := hadm.h_pos
  have hv := hadm.v_pos
  have hvξ : θ.v / θ.h = θ.ξ₀ := by
    show θ.v / (θ.v / θ.ξ₀) = θ.ξ₀
    field_simp [hv.ne', hadm.ξ₀_pos.ne']
  have hvs : ∀ s, vF (θ.t + s) = θ.v - s / 2 := fun s => by
    show vF (θ.t + s) = vF θ.t - s / 2; unfold vF eF; ring
  have hcs : ∀ s, cF (θ.t + s) θ.p = θ.c - s / 2 := fun s => by
    show cF (θ.t + s) θ.p = cF θ.t θ.p - s / 2; unfold cF; ring
  have he1 : θ.v + θ.e = 1 := by show vF θ.t + eF θ.t = 1; unfold vF; ring
  let θf : ℝ → Params := fun s => ⟨θ.t + s, θ.p, (θ.v - s / 2) / θ.h⟩
  have hθ0 : θf 0 = θ := by
    show (⟨θ.t + 0, θ.p, (θ.v - 0 / 2) / θ.h⟩ : Params) = θ
    rw [add_zero, zero_div, sub_zero, hvξ]
  have ht : HasDerivAt (fun s => (θf s).t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add θ.t
  have hp : HasDerivAt (fun s => (θf s).p) 0 0 := hasDerivAt_const _ _
  have hx : HasDerivAt (fun s => (θf s).ξ₀) (-1 / (2 * θ.h)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).div_const 2).const_sub θ.v).div_const θ.h
    convert this using 1
    field_simp
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (θf s).Admissible ∧ (θf s).c ≤ ξl ∧ ξr ≤ (θf s).ξ₀ ∧
      La + s * 0 ≤ 1 ∧ (θf s).h ≤ Lb + s * 0 ∧
      P ξl + s * (1 / 2) + (La + s * 0) * ((θf s).c - ξl) = (θf s).p ∧
      P ξr + s * (1 / 2) + (Lb + s * 0) * ((θf s).ξ₀ - ξr) = 1 := by
    have e1 := eventually_pos_at (f := fun s => θ.t + s) (by fun_prop) (by simpa using hadm.t_pos)
    have e2 := eventually_pos_at (f := fun s => 1 - (θ.t + s)) (by fun_prop)
      (by simpa using hadm.t_lt_one)
    have e3 := eventually_pos_at (f := fun s => θ.p - (θ.t + s)) (by fun_prop)
      (by simpa using htp)
    have e4 := eventually_pos_at (f := fun s => θ.v - s / 2) (by fun_prop) (by simpa using hv)
    have e5 := eventually_pos_at (f := fun s => (θ.v - s / 2) / θ.h - (θ.c - s / 2)) (by fun_prop)
      (by
        simp only [zero_div, sub_zero]
        rw [hvξ]; linarith [hM.hA3.l_lt_r, hM.hA3.r_le])
    have e6 := eventually_pos_at (f := fun s => ξl - (θ.c - s / 2)) (by fun_prop)
      (by simp only [zero_div, sub_zero]; linarith)
    have e7 := eventually_pos_at (f := fun s => (θ.v - s / 2) / θ.h - ξr) (by fun_prop)
      (by simp only [zero_div, sub_zero]; rw [hvξ]; linarith)
    filter_upwards [e1, e2, e3, e4, e5, e6, e7] with s h1 h2 h3 h4 h5 h6 h7
    have hcs' : (θf s).c = θ.c - s / 2 := hcs s
    have hhs : (θf s).h = θ.h := by
      show vF (θ.t + s) / ((θ.v - s / 2) / θ.h) = θ.h
      have h4' : 0 < θ.v - s / 2 := h4
      rw [hvs]; field_simp
      exact div_self (by linarith : (0 : ℝ) < θ.v * 2 - s).ne'
    refine ⟨⟨h1, by linarith, by show θ.t + s ≤ θ.p; linarith, hadm.p_le_one,
      by show 0 < (θ.v - s / 2) / θ.h; positivity,
      by show cF (θ.t + s) θ.p ≤ (θ.v - s / 2) / θ.h; rw [hcs]; linarith⟩,
      by rw [hcs']; linarith, by show ξr ≤ (θ.v - s / 2) / θ.h; linarith,
      by rw [hLa]; simp, by rw [hhs, hLb]; simp, ?_, ?_⟩
    · rw [hcs', hLa]
      show P ξl + s * (1 / 2) + (1 + s * 0) * (θ.c - s / 2 - ξl) = θ.p
      have := hM.P_c
      rw [hLa] at this
      linarith
    · rw [hLb, hPr]
      show θ.h * ξr + θ.e + s * (1 / 2) + (θ.h + s * 0) * ((θ.v - s / 2) / θ.h - ξr) = 1
      field_simp
      linear_combination 2 * θ.h * he1
  have := hM.Dtil_eq_zero hI hθ0 ht hp hx hev
  rw [hLa, hLb, Dtil_t hPl hξl hPr hξr hξ₀ hadm.t_pos.ne' hadm.p_pos.ne' hl0'.ne' hr0'.ne' hh.ne',
    hI.envelope_t (dOf β) θ (θ.line₁ ξl) (θ.line₂ ξr) hadm.t_pos hadm.p_pos hadm.ξ₀_pos hv
      hl0' hr0'] at this
  exact this

/-- `statH = 0` (two-sided `h`-variation at fixed `(t, p)`). -/
theorem statH_zero (hM : MaxData β θ P ξl ξr C La Lb) (hI : FamilyIdentities) (hr : ξr < θ.ξ₀)
    (hl : θ.c < ξl) : statH (dOf β) θ (θ.line₂ ξr) = 0 := by
  obtain ⟨hLa, hLb, hPl, hξl, hPr, hξr, hξ₀, hl0', hr0'⟩ := contact_data hM hr hl
  have hadm := hM.hP.admissible
  have hh := hadm.h_pos
  have hv := hadm.v_pos
  have hvξ : θ.v / θ.h = θ.ξ₀ := by
    show θ.v / (θ.v / θ.ξ₀) = θ.ξ₀
    field_simp [hv.ne', hadm.ξ₀_pos.ne']
  have he1 : θ.v + θ.e = 1 := by show vF θ.t + eF θ.t = 1; unfold vF; ring
  let θf : ℝ → Params := fun s => ⟨θ.t, θ.p, θ.v / (θ.h + s)⟩
  have hθ0 : θf 0 = θ := by
    show (⟨θ.t, θ.p, θ.v / (θ.h + 0)⟩ : Params) = θ
    rw [add_zero, hvξ]
  have ht : HasDerivAt (fun s => (θf s).t) 0 0 := hasDerivAt_const _ _
  have hp : HasDerivAt (fun s => (θf s).p) 0 0 := hasDerivAt_const _ _
  have hx : HasDerivAt (fun s => (θf s).ξ₀) (-θ.ξ₀ / θ.h) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => θ.h + s) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add θ.h
    have := (hasDerivAt_const (0 : ℝ) θ.v).div h1 (by simpa using hh.ne')
    convert this using 1
    rw [← hvξ]
    field_simp
    ring
  have hcont : ContinuousAt (fun s : ℝ => θ.v / (θ.h + s)) 0 :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simpa using hh.ne')
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (θf s).Admissible ∧ (θf s).c ≤ ξl ∧ ξr ≤ (θf s).ξ₀ ∧
      La + s * 0 ≤ 1 ∧ (θf s).h ≤ Lb + s * 1 ∧
      P ξl + s * 0 + (La + s * 0) * ((θf s).c - ξl) = (θf s).p ∧
      P ξr + s * ξr + (Lb + s * 1) * ((θf s).ξ₀ - ξr) = 1 := by
    have e1 := eventually_pos_at (f := fun s => θ.h + s) (by fun_prop) (by simpa using hh)
    have e2 := eventually_pos_at (f := fun s => θ.v / (θ.h + s) - θ.c) (hcont.sub continuousAt_const)
      (by
        simp only [add_zero]
        rw [hvξ]; linarith [hM.hA3.l_lt_r, hM.hA3.r_le, hM.hA3.c_le])
    have e3 := eventually_pos_at (f := fun s => θ.v / (θ.h + s) - ξr) (hcont.sub continuousAt_const)
      (by simp only [add_zero]; rw [hvξ]; linarith)
    filter_upwards [e1, e2, e3] with s h1 h2 h3
    have hhs : (θf s).h = θ.h + s := by
      show θ.v / (θ.v / (θ.h + s)) = θ.h + s
      field_simp [hv.ne', h1.ne']
    refine ⟨⟨hadm.t_pos, hadm.t_lt_one, hadm.t_le_p, hadm.p_le_one,
      by show 0 < θ.v / (θ.h + s); positivity,
      by show θ.c ≤ θ.v / (θ.h + s); linarith⟩,
      hM.hA3.c_le, by show ξr ≤ θ.v / (θ.h + s); linarith,
      by rw [hLa]; simp, by rw [hhs, hLb]; simp, ?_, ?_⟩
    · show P ξl + s * 0 + (La + s * 0) * (θ.c - ξl) = θ.p
      simpa using hM.P_c
    · rw [hLb, hPr]
      show θ.h * ξr + θ.e + s * ξr + (θ.h + s * 1) * (θ.v / (θ.h + s) - ξr) = 1
      field_simp
      linear_combination he1
  have := hM.Dtil_eq_zero hI hθ0 ht hp hx hev
  rw [hLa, hLb, Dtil_h hPl hξl hPr hξr hξ₀ hadm.t_pos.ne' hadm.p_pos.ne' hl0'.ne' hr0'.ne' hh.ne',
    hI.envelope_h (dOf β) θ (θ.line₁ ξl) (θ.line₂ ξr) hadm.ξ₀_pos hv hr0'] at this
  exact this

end Interior

end PkgC
end FixedPrice.TwoUnit.Family
