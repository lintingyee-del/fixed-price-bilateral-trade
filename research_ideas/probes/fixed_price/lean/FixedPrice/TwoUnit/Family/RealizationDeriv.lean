import FixedPrice.TwoUnit.Family.BasicFTC

/-!
# Work package E, realization helpers: the right derivative of a class member

For a class member `P` and `c_f ≤ ξ < ξ₀`, the right derivative `P'_+(ξ) = bodySurvival P ξ`
exists (the chord slopes from `ξ` are antitone and bounded by `1`), lies in `[h_f, 1]`, is
antitone and right-continuous on `[c_f, ξ₀)`, and equals `deriv P` wherever `P` is differentiable.
Consequently the two curve distribution functions `buyerCurveCDF` and `sellerCurveCDF` of
`Defs.lean` are nondecreasing and right-continuous, with values in `[0, 1]` and `[m_f, 1]`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

namespace Realize

variable {θ : Params} {P : ℝ → ℝ}

/-- The chord slope from `c_f` is at most `1` (obstacle `ξ + δ_f`). -/
theorem slope_c_le_one (hP : InClass θ P) {y : ℝ} (hcy : θ.c < y) (hy : y ≤ θ.ξ₀) :
    slope P θ.c y ≤ 1 := by
  have hym : y ∈ Icc θ.c θ.ξ₀ := ⟨hcy.le, hy⟩
  rw [slope_def_field, hP.left_end, div_le_one (by linarith)]
  have := hP.le_line₁ hym
  have e : θ.line₁ y - θ.p = y - θ.c := by rw [← Params.line₁_c]; unfold Params.line₁; ring
  linarith

/-- Every chord slope of a class member on the curve interval is at most `1`. -/
theorem slope_le_one (hP : InClass θ P) {ξ y : ℝ} (hξ : θ.c ≤ ξ) (hξy : ξ < y)
    (hy : y ≤ θ.ξ₀) : slope P ξ y ≤ 1 := by
  rcases eq_or_lt_of_le hξ with h | h
  · rw [← h]; exact slope_c_le_one hP (h ▸ hξy) hy
  · have hcm : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
    have hym : y ∈ Icc θ.c θ.ξ₀ := ⟨hξ.trans hξy.le, hy⟩
    have h1 := hP.concave.slope_anti_adjacent hcm hym h hξy
    have h2 := slope_c_le_one hP h (hξy.le.trans hy)
    rw [slope_def_field] at h2 ⊢
    linarith

/-- The right derivative exists on `[c_f, ξ₀)`, as the supremum of the chord slopes. -/
theorem hasDerivWithinAt_sSup_slope (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ)
    (hξ₀ : ξ < θ.ξ₀) :
    HasDerivWithinAt P (sSup (slope P ξ '' Ioo ξ θ.ξ₀)) (Ioi ξ) ξ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, diff_singleton_eq_self (show ξ ∉ Ioi ξ from lt_irrefl ξ)]
  have hanti : AntitoneOn (slope P ξ) (Ioo ξ θ.ξ₀) :=
    (hP.concave.slope_anti ⟨hξ, hξ₀.le⟩).mono
      (fun y hy => ⟨⟨hξ.trans hy.1.le, hy.2.le⟩, hy.1.ne'⟩)
  have hbdd : BddAbove (slope P ξ '' Ioo ξ θ.ξ₀) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact slope_le_one hP hξ hy.1 hy.2.le
  exact hanti.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hξ₀) hbdd

/-- `bodySurvival P ξ = P'_+(ξ)` is the right derivative on `[c_f, ξ₀)`. -/
theorem hasDerivWithinAt_rd (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    HasDerivWithinAt P (bodySurvival P ξ) (Ioi ξ) ξ := by
  have h := hasDerivWithinAt_sSup_slope hP hξ hξ₀
  have e : bodySurvival P ξ = sSup (slope P ξ '' Ioo ξ θ.ξ₀) := by
    unfold bodySurvival
    rw [← derivWithin_Ioi_eq_Ici]
    exact h.derivWithin (uniqueDiffWithinAt_Ioi ξ)
  rw [e]; exact h

theorem tendsto_slope_rd (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    Tendsto (slope P ξ) (𝓝[>] ξ) (𝓝 (bodySurvival P ξ)) := by
  have h := hasDerivWithinAt_iff_tendsto_slope.mp (hasDerivWithinAt_rd hP hξ hξ₀)
  rwa [diff_singleton_eq_self (show ξ ∉ Ioi ξ from lt_irrefl ξ)] at h

/-- Chords from `ξ` lie below the right derivative at `ξ`. -/
theorem slope_le_rd (hP : InClass θ P) {ξ y : ℝ} (hξ : θ.c ≤ ξ) (hξy : ξ < y)
    (hy : y ≤ θ.ξ₀) : slope P ξ y ≤ bodySurvival P ξ :=
  hP.concave.slope_le_of_hasDerivWithinAt_Ioi ⟨hξ, hξy.le.trans hy⟩ ⟨hξ.trans hξy.le, hy⟩ hξy
    (hasDerivWithinAt_rd hP hξ (hξy.trans_le hy))

/-- The right derivative at `ξ` lies below the chords ending at `ξ`. -/
theorem rd_le_slope (hP : InClass θ P) {x ξ : ℝ} (hx : θ.c ≤ x) (hxξ : x < ξ)
    (hξ₀ : ξ < θ.ξ₀) : bodySurvival P ξ ≤ slope P x ξ := by
  refine le_of_tendsto (tendsto_slope_rd hP (hx.trans hxξ.le) hξ₀) ?_
  filter_upwards [Ioo_mem_nhdsGT hξ₀] with y hy
  have hxm : x ∈ Icc θ.c θ.ξ₀ := ⟨hx, (hxξ.trans hξ₀).le⟩
  have hym : y ∈ Icc θ.c θ.ξ₀ := ⟨hx.trans (hxξ.trans hy.1).le, hy.2.le⟩
  have h := hP.concave.slope_anti_adjacent hxm hym hxξ hy.1
  rw [slope_def_field, slope_def_field]
  exact h

theorem rd_le_one (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    bodySurvival P ξ ≤ 1 := by
  refine le_of_tendsto (tendsto_slope_rd hP hξ hξ₀) ?_
  filter_upwards [Ioo_mem_nhdsGT hξ₀] with y hy
  exact slope_le_one hP hξ hy.1 hy.2.le

/-- `h_f ≤ P'_+` on `[c_f, ξ₀)` (the chord to `ξ₀` against the obstacle `h_f ξ + e_f`). -/
theorem h_le_rd (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    θ.h ≤ bodySurvival P ξ := by
  refine le_trans ?_ (slope_le_rd hP hξ hξ₀ le_rfl)
  have hxm : ξ ∈ Icc θ.c θ.ξ₀ := ⟨hξ, hξ₀.le⟩
  rw [slope_def_field, hP.right_end, le_div_iff₀ (sub_pos.mpr hξ₀)]
  have := hP.le_line₂ hxm
  have e := hP.admissible.line₂_ξ₀
  unfold Params.line₂ at this e
  linarith

theorem rd_nonneg (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    0 ≤ bodySurvival P ξ :=
  hP.admissible.h_pos.le.trans (h_le_rd hP hξ hξ₀)

/-- `P'_+` is antitone on `[c_f, ξ₀)`. -/
theorem rd_anti (hP : InClass θ P) {ξ ξ' : ℝ} (hξ : θ.c ≤ ξ) (hξξ' : ξ ≤ ξ')
    (hξ' : ξ' < θ.ξ₀) : bodySurvival P ξ' ≤ bodySurvival P ξ := by
  rcases eq_or_lt_of_le hξξ' with h | h
  · rw [h]
  · exact (rd_le_slope hP hξ h hξ').trans (slope_le_rd hP hξ h hξ'.le)

/-- A class member is right-continuous within the curve interval. -/
theorem continuousWithinAt_Ici (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    ContinuousWithinAt P (Ici ξ) ξ :=
  (hP.continuousOn ξ ⟨hξ, hξ₀.le⟩).mono_of_mem_nhdsWithin
    (mem_of_superset (Icc_mem_nhdsGE hξ₀) (Icc_subset_Icc_left hξ))

/-- `P'_+` is right-continuous on `[c_f, ξ₀)`. -/
theorem continuousWithinAt_rd (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    ContinuousWithinAt (bodySurvival P) (Ici ξ) ξ := by
  rw [ContinuousWithinAt, tendsto_order]
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · obtain ⟨l', hl', hl'D⟩ := exists_between hl
    have hev := (tendsto_slope_rd hP hξ hξ₀).eventually (lt_mem_nhds hl'D)
    obtain ⟨y₀, hy₀l, hy₀⟩ := (hev.and (Ioo_mem_nhdsGT hξ₀)).exists
    -- continuity of `r ↦ slope P r y₀` at `ξ` from the right
    have hcont : Tendsto (fun r => (P y₀ - P r) / (y₀ - r)) (𝓝[≥] ξ)
        (𝓝 ((P y₀ - P ξ) / (y₀ - ξ))) := by
      have hPc : Tendsto P (𝓝[≥] ξ) (𝓝 (P ξ)) := continuousWithinAt_Ici hP hξ hξ₀
      have hid : Tendsto (fun r : ℝ => r) (𝓝[≥] ξ) (𝓝 ξ) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      exact (tendsto_const_nhds.sub hPc).div (tendsto_const_nhds.sub hid)
        (sub_pos.mpr hy₀.1).ne'
    have hlt : l < (P y₀ - P ξ) / (y₀ - ξ) := by
      rw [← slope_def_field]; linarith
    filter_upwards [hcont.eventually (lt_mem_nhds hlt), Ico_mem_nhdsGE hy₀.1] with r hr hrI
    rcases eq_or_lt_of_le hrI.1 with h | h
    · rw [← h]; exact hl
    · have := slope_le_rd hP (hξ.trans h.le) hrI.2 hy₀.2.le
      rw [slope_def_field] at this
      linarith
  · filter_upwards [Ico_mem_nhdsGE hξ₀] with r hr
    exact (rd_anti hP hξ hr.1 hr.2).trans_lt hu

/-- `P'_+ = P'` at every interior point of differentiability. -/
theorem rd_eq_deriv {ξ : ℝ} (hd : DifferentiableAt ℝ P ξ) : bodySurvival P ξ = deriv P ξ :=
  hd.derivWithin (uniqueDiffWithinAt_Ici ξ)

/-- `P'_+ = P'` almost everywhere on the curve interval. -/
theorem ae_rd_eq_deriv (hP : InClass θ P) :
    ∀ᵐ ξ ∂(volume.restrict (Icc θ.c θ.ξ₀)), bodySurvival P ξ = deriv P ξ := by
  filter_upwards [hP.ae_good] with x hx
  exact rd_eq_deriv hx.2

/-! ### The first seller in the curve coordinate -/

/-- `ξ ↦ P(ξ) - ξ P'_+(ξ)` is nondecreasing on `[c_f, ξ₀)`. -/
theorem sub_mul_rd_mono (hP : InClass θ P) {ξ ξ' : ℝ} (hξ : θ.c ≤ ξ) (hξξ' : ξ ≤ ξ')
    (hξ' : ξ' < θ.ξ₀) :
    P ξ - ξ * bodySurvival P ξ ≤ P ξ' - ξ' * bodySurvival P ξ' := by
  rcases eq_or_lt_of_le hξξ' with h | h
  · rw [h]
  have h1 := rd_le_slope hP hξ h hξ'
  rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at h1
  have h2 := rd_anti hP hξ hξξ' hξ'
  have hξ0 : 0 ≤ ξ := hP.admissible.c_nonneg.trans hξ
  have h3 := mul_le_mul_of_nonneg_left h2 hξ0
  nlinarith

/-- `N_f (P - ξ P'_+) ≤ 1` on `[c_f, ξ₀)`. -/
theorem N_mul_sub_mul_rd_le_one (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    θ.N * (P ξ - ξ * bodySurvival P ξ) ≤ 1 := by
  have hxm : ξ ∈ Icc θ.c θ.ξ₀ := ⟨hξ, hξ₀.le⟩
  have hx0 : 0 ≤ ξ := hP.admissible.c_nonneg.trans hξ
  have h1 := slope_le_rd hP hξ hξ₀ le_rfl
  rw [slope_def_field, hP.right_end] at h1
  have hξx : 0 < θ.ξ₀ - ξ := sub_pos.mpr hξ₀
  have h2 : ξ * ((1 - P ξ) / (θ.ξ₀ - ξ)) ≤ ξ * bodySurvival P ξ :=
    mul_le_mul_of_nonneg_left h1 hx0
  have hl := hP.le_line₂ hxm
  have e1 := hP.admissible.line₂_ξ₀
  unfold Params.line₂ at hl e1
  have h3 : P ξ - ξ * ((1 - P ξ) / (θ.ξ₀ - ξ)) ≤ θ.e := by
    have hξ₀p := hP.admissible.ξ₀_pos
    have hm := mul_le_mul_of_nonneg_right hl hξ₀p.le
    have key : P ξ * (θ.ξ₀ - ξ) - ξ * (1 - P ξ) ≤ θ.e * (θ.ξ₀ - ξ) := by nlinarith
    have e2 : P ξ - ξ * ((1 - P ξ) / (θ.ξ₀ - ξ)) =
        (P ξ * (θ.ξ₀ - ξ) - ξ * (1 - P ξ)) / (θ.ξ₀ - ξ) := by
      field_simp
    rw [e2, div_le_iff₀ hξx]
    exact key
  have hN := hP.admissible.N_pos
  have hNe := hP.admissible.N_mul_e
  have : P ξ - ξ * bodySurvival P ξ ≤ θ.e := by linarith
  calc θ.N * (P ξ - ξ * bodySurvival P ξ) ≤ θ.N * θ.e := mul_le_mul_of_nonneg_left this hN.le
    _ = 1 := hNe

/-- `m_f ≤ N_f (P - ξ P'_+)` at `c_f` (certified `initial_seller_atom`: `N(p - c) = m + m a p`). -/
theorem m_le_N_mul_at_c (hI : FamilyIdentities) (hP : InClass θ P) (hc : θ.c < θ.ξ₀) :
    θ.m ≤ θ.N * (P θ.c - θ.c * bodySurvival P θ.c) := by
  have hadm := hP.admissible
  have hD := rd_le_one hP le_rfl hc
  have hc0 := hadm.c_nonneg
  have hatom := hI.initial_seller_atom θ.t θ.p hadm.t_pos hadm.p_pos
  have e1 : NF θ.t * (θ.p - cF θ.t θ.p) = θ.N * (θ.p - θ.c) := rfl
  have e2 : mF θ.t + mF θ.t * aF θ.t θ.p * θ.p = θ.m + θ.m * θ.a * θ.p := rfl
  rw [e1, e2] at hatom
  have hmap : 0 ≤ θ.m * θ.a * θ.p :=
    mul_nonneg (mul_nonneg hadm.m_pos.le hadm.a_nonneg) hadm.p_pos.le
  rw [hP.left_end]
  have : θ.p - θ.c ≤ θ.p - θ.c * bodySurvival P θ.c := by nlinarith
  have := mul_le_mul_of_nonneg_left this hadm.N_pos.le
  linarith

theorem m_le_bodySellerCDF (hI : FamilyIdentities) (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ)
    (hξ₀ : ξ < θ.ξ₀) : θ.m ≤ bodySellerCDF θ P ξ := by
  unfold bodySellerCDF
  have h1 := m_le_N_mul_at_c hI hP (hξ.trans_lt hξ₀)
  have h2 := sub_mul_rd_mono hP le_rfl hξ hξ₀
  have := mul_le_mul_of_nonneg_left h2 hP.admissible.N_pos.le
  exact h1.trans this

theorem bodySellerCDF_le_one (hP : InClass θ P) {ξ : ℝ} (hξ : θ.c ≤ ξ) (hξ₀ : ξ < θ.ξ₀) :
    bodySellerCDF θ P ξ ≤ 1 :=
  N_mul_sub_mul_rd_le_one hP hξ hξ₀

/-! ### The curve distribution functions -/

theorem buyerCDF_of_lt {ξ : ℝ} (h : ξ < θ.c) : buyerCurveCDF θ P ξ = 0 := by
  unfold buyerCurveCDF; rw [if_pos h]

theorem buyerCDF_of_mem {ξ : ℝ} (h1 : θ.c ≤ ξ) (h2 : ξ < θ.ξ₀) :
    buyerCurveCDF θ P ξ = 1 - bodySurvival P ξ := by
  unfold buyerCurveCDF; rw [if_neg (not_lt.mpr h1), if_pos h2]

theorem buyerCDF_of_ge {ξ : ℝ} (hc : θ.c ≤ θ.ξ₀) (h : θ.ξ₀ ≤ ξ) : buyerCurveCDF θ P ξ = 1 := by
  unfold buyerCurveCDF; rw [if_neg (not_lt.mpr (hc.trans h)), if_neg (not_lt.mpr h)]

theorem sellerCDF_of_lt {ξ : ℝ} (h : ξ < θ.c) : sellerCurveCDF θ P ξ = θ.m := by
  unfold sellerCurveCDF; rw [if_pos h]

theorem sellerCDF_of_mem {ξ : ℝ} (h1 : θ.c ≤ ξ) (h2 : ξ < θ.ξ₀) :
    sellerCurveCDF θ P ξ = bodySellerCDF θ P ξ := by
  unfold sellerCurveCDF; rw [if_neg (not_lt.mpr h1), if_pos h2]

theorem sellerCDF_of_ge {ξ : ℝ} (hc : θ.c ≤ θ.ξ₀) (h : θ.ξ₀ ≤ ξ) :
    sellerCurveCDF θ P ξ = 1 := by
  unfold sellerCurveCDF; rw [if_neg (not_lt.mpr (hc.trans h)), if_neg (not_lt.mpr h)]

theorem buyerCDF_nonneg (hP : InClass θ P) (ξ : ℝ) : 0 ≤ buyerCurveCDF θ P ξ := by
  rcases lt_or_ge ξ θ.c with h1 | h1
  · rw [buyerCDF_of_lt h1]
  rcases lt_or_ge ξ θ.ξ₀ with h2 | h2
  · rw [buyerCDF_of_mem h1 h2]; linarith [rd_le_one hP h1 h2]
  · rw [buyerCDF_of_ge hP.c_le_ξ₀ h2]; norm_num

theorem buyerCDF_le_one (hP : InClass θ P) (ξ : ℝ) : buyerCurveCDF θ P ξ ≤ 1 := by
  rcases lt_or_ge ξ θ.c with h1 | h1
  · rw [buyerCDF_of_lt h1]; norm_num
  rcases lt_or_ge ξ θ.ξ₀ with h2 | h2
  · rw [buyerCDF_of_mem h1 h2]; linarith [rd_nonneg hP h1 h2]
  · rw [buyerCDF_of_ge hP.c_le_ξ₀ h2]

theorem m_le_sellerCDF (hI : FamilyIdentities) (hP : InClass θ P) (ξ : ℝ) :
    θ.m ≤ sellerCurveCDF θ P ξ := by
  rcases lt_or_ge ξ θ.c with h1 | h1
  · rw [sellerCDF_of_lt h1]
  rcases lt_or_ge ξ θ.ξ₀ with h2 | h2
  · rw [sellerCDF_of_mem h1 h2]; exact m_le_bodySellerCDF hI hP h1 h2
  · rw [sellerCDF_of_ge hP.c_le_ξ₀ h2]; exact hP.admissible.m_lt_one.le

theorem sellerCDF_le_one (hP : InClass θ P) (ξ : ℝ) : sellerCurveCDF θ P ξ ≤ 1 := by
  rcases lt_or_ge ξ θ.c with h1 | h1
  · rw [sellerCDF_of_lt h1]; exact hP.admissible.m_lt_one.le
  rcases lt_or_ge ξ θ.ξ₀ with h2 | h2
  · rw [sellerCDF_of_mem h1 h2]; exact bodySellerCDF_le_one hP h1 h2
  · rw [sellerCDF_of_ge hP.c_le_ξ₀ h2]

theorem buyerCDF_mono (hP : InClass θ P) : Monotone (buyerCurveCDF θ P) := by
  intro x y hxy
  rcases lt_or_ge x θ.c with hx1 | hx1
  · rw [buyerCDF_of_lt hx1]; exact buyerCDF_nonneg hP y
  rcases lt_or_ge x θ.ξ₀ with hx2 | hx2
  · rw [buyerCDF_of_mem hx1 hx2]
    rcases lt_or_ge y θ.ξ₀ with hy2 | hy2
    · rw [buyerCDF_of_mem (hx1.trans hxy) hy2]
      linarith [rd_anti hP hx1 hxy hy2]
    · rw [buyerCDF_of_ge hP.c_le_ξ₀ hy2]; linarith [rd_nonneg hP hx1 hx2]
  · rw [buyerCDF_of_ge hP.c_le_ξ₀ hx2, buyerCDF_of_ge hP.c_le_ξ₀ (hx2.trans hxy)]

theorem sellerCDF_mono (hI : FamilyIdentities) (hP : InClass θ P) :
    Monotone (sellerCurveCDF θ P) := by
  intro x y hxy
  rcases lt_or_ge x θ.c with hx1 | hx1
  · rw [sellerCDF_of_lt hx1]; exact m_le_sellerCDF hI hP y
  rcases lt_or_ge x θ.ξ₀ with hx2 | hx2
  · rw [sellerCDF_of_mem hx1 hx2]
    rcases lt_or_ge y θ.ξ₀ with hy2 | hy2
    · rw [sellerCDF_of_mem (hx1.trans hxy) hy2]
      unfold bodySellerCDF
      exact mul_le_mul_of_nonneg_left (sub_mul_rd_mono hP hx1 hxy hy2)
        hP.admissible.N_pos.le
    · rw [sellerCDF_of_ge hP.c_le_ξ₀ hy2]; exact bodySellerCDF_le_one hP hx1 hx2
  · rw [sellerCDF_of_ge hP.c_le_ξ₀ hx2, sellerCDF_of_ge hP.c_le_ξ₀ (hx2.trans hxy)]

theorem buyerCDF_rightCont (hP : InClass θ P) (x : ℝ) :
    ContinuousWithinAt (buyerCurveCDF θ P) (Ici x) x := by
  rcases lt_or_ge x θ.c with hx1 | hx1
  · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_
      (buyerCDF_of_lt hx1)
    filter_upwards [Ico_mem_nhdsGE hx1] with y hy
    exact buyerCDF_of_lt hy.2
  rcases lt_or_ge x θ.ξ₀ with hx2 | hx2
  · refine ((continuousWithinAt_const (b := (1 : ℝ))).sub
      (continuousWithinAt_rd hP hx1 hx2)).congr_of_eventuallyEq ?_ (buyerCDF_of_mem hx1 hx2)
    filter_upwards [Ico_mem_nhdsGE hx2] with y hy
    exact buyerCDF_of_mem (hx1.trans hy.1) hy.2
  · refine (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq ?_
      (buyerCDF_of_ge hP.c_le_ξ₀ hx2)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact buyerCDF_of_ge hP.c_le_ξ₀ (hx2.trans hy)

theorem sellerCDF_rightCont (hP : InClass θ P) (x : ℝ) :
    ContinuousWithinAt (sellerCurveCDF θ P) (Ici x) x := by
  rcases lt_or_ge x θ.c with hx1 | hx1
  · refine (continuousWithinAt_const (b := θ.m)).congr_of_eventuallyEq ?_
      (sellerCDF_of_lt hx1)
    filter_upwards [Ico_mem_nhdsGE hx1] with y hy
    exact sellerCDF_of_lt hy.2
  rcases lt_or_ge x θ.ξ₀ with hx2 | hx2
  · have hcont : ContinuousWithinAt (bodySellerCDF θ P) (Ici x) x := by
      unfold bodySellerCDF
      exact continuousWithinAt_const.mul ((continuousWithinAt_Ici hP hx1 hx2).sub
        (continuousWithinAt_id.mul (continuousWithinAt_rd hP hx1 hx2)))
    refine hcont.congr_of_eventuallyEq ?_ (sellerCDF_of_mem hx1 hx2)
    filter_upwards [Ico_mem_nhdsGE hx2] with y hy
    exact sellerCDF_of_mem (hx1.trans hy.1) hy.2
  · refine (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq ?_
      (sellerCDF_of_ge hP.c_le_ξ₀ hx2)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact sellerCDF_of_ge hP.c_le_ξ₀ (hx2.trans hy)

end Realize

end FixedPrice.TwoUnit.Family
