import FixedPrice.TwoUnit.Family.ShapeArc

/-!
# Work package B, part 10: the Euler equation on a free stretch

For a free stretch `(a, b)` whose ends touch the obstacle (or sit at `c_f`), the representative
satisfies `0 < ω̂ < 1` on `[a, b]` and `a > 0`; the conserved quantity is a positive constant `C`;
and `P* = e^z` satisfies `P*'' + CP*/ξ² = 0`, `d = ξP*'² - P*P*' + CP*²/ξ`, is `C²` on `(a, b)`
and strictly concave on `[a, b]`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

theorem Admissible.e_pos' (hθ : θ.Admissible) : 0 < θ.e := by
  unfold Params.e eF; linarith [hθ.t_pos]

namespace Setting

variable {d : ℝ} {w : H θ} (S : Setting θ d w)
include S

theorem z_le_log_line₁ {t : ℝ} (ht : t ∈ Ioc θ.c θ.ξ₀) :
    zfun θ w t ≤ Real.log (1 * t + θ.δ) := by
  have h1 : θ.U t ≤ θ.line₁ t := min_le_left _ _
  have h2 := Real.log_le_log (S.U_pos ht.1.le) h1
  rw [show θ.line₁ t = 1 * t + θ.δ by unfold Params.line₁; ring] at h2
  exact (S.z_le ht).trans h2

theorem z_le_log_line₂ {t : ℝ} (ht : t ∈ Ioc θ.c θ.ξ₀) :
    zfun θ w t ≤ Real.log (θ.h * t + θ.e) :=
  (S.z_le ht).trans (Real.log_le_log (S.U_pos ht.1.le) (min_le_right _ _))

theorem tendsto_z_of_lt {a : ℝ} (hca : θ.c < a) (haξ : a < θ.ξ₀) :
    Tendsto (zfun θ w) (𝓝[>] a) (𝓝 (zfun θ w a)) :=
  (S.continuousAt_z ⟨hca, haξ⟩).tendsto.mono_left nhdsWithin_le_nhds

/-- Left end touching `line₁` (automatic at `c_f`): `ω̂(a) ≤ a/(a + δ_f)`. -/
theorem left_bound_line₁ {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hza : a = θ.c ∨ zfun θ w a = Real.log (θ.line₁ a)) :
    hat θ d w K a ≤ 1 * a / (1 * a + θ.δ) := by
  refine S.left_bound hF hK zero_le_one S.adm.δ_pos
    (fun t ht => S.z_le_log_line₁ ⟨(hF.sub_Ioo ht).1, (hF.sub_Ioo ht).2.le⟩) ?_
  rcases eq_or_lt_of_le hF.ca with h' | h'
  · rw [← h', show 1 * θ.c + θ.δ = θ.p by rw [← Params.line₁_c]; unfold Params.line₁; ring]
    exact S.tendsto_z_c
  · have hz : zfun θ w a = Real.log (θ.line₁ a) := hza.resolve_left h'.ne'
    have := S.tendsto_z_of_lt h' (lt_of_lt_of_le hF.ab hF.bξ)
    rwa [hz, show θ.line₁ a = 1 * a + θ.δ by unfold Params.line₁; ring] at this

/-- Left end touching `line₂` inside the interval: `ω̂(a) ≤ h_f a/(h_f a + e_f)`. -/
theorem left_bound_line₂ {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hca : θ.c < a) (hza : zfun θ w a = Real.log (θ.line₂ a)) :
    hat θ d w K a ≤ θ.h * a / (θ.h * a + θ.e) := by
  refine S.left_bound hF hK S.adm.h_pos.le (Admissible.e_pos' S.adm)
    (fun t ht => S.z_le_log_line₂ ⟨(hF.sub_Ioo ht).1, (hF.sub_Ioo ht).2.le⟩) ?_
  have := S.tendsto_z_of_lt hca (lt_of_lt_of_le hF.ab hF.bξ)
  rwa [hza] at this

theorem right_bound_line₁ {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hzb : zfun θ w b = Real.log (θ.line₁ b)) : 1 * b / (1 * b + θ.δ) ≤ hat θ d w K b :=
  S.right_bound hF hK zero_le_one S.adm.δ_pos
    (fun t ht => S.z_le_log_line₁ ⟨(hF.sub_Ioo ht).1, (hF.sub_Ioo ht).2.le⟩)
    (by rw [hzb, show θ.line₁ b = 1 * b + θ.δ by unfold Params.line₁; ring])

theorem right_bound_line₂ {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hzb : zfun θ w b = Real.log (θ.line₂ b)) :
    θ.h * b / (θ.h * b + θ.e) ≤ hat θ d w K b :=
  S.right_bound hF hK S.adm.h_pos.le (Admissible.e_pos' S.adm)
    (fun t ht => S.z_le_log_line₂ ⟨(hF.sub_Ioo ht).1, (hF.sub_Ioo ht).2.le⟩) hzb

/-- The data of a free stretch touching the obstacle at both ends. -/
theorem free_arc {a b : ℝ} (hF : Free θ w a b)
    (hza : a = θ.c ∨ zfun θ w a = Real.log (θ.U a)) (hzb : zfun θ w b = Real.log (θ.U b)) :
    ∃ K C, IsHat θ d w a b K ∧ 0 < a ∧ 0 < C ∧ (∀ t ∈ Ioo a b, Cfun θ d w K t = C) ∧
      (∀ t ∈ Icc a b, 0 < hat θ d w K t ∧ hat θ d w K t < 1) := by
  obtain ⟨K, hK⟩ := S.exists_hat hF
  have he := Admissible.e_pos' S.adm
  have hδ := S.adm.δ_pos
  have hh := S.adm.h_pos
  have ha0 : 0 ≤ a := S.adm.c_nonneg.trans hF.ca
  have hb0 : 0 < b := lt_of_le_of_lt ha0 hF.ab
  have hleft : hat θ d w K a < 1 ∧ (a = 0 → hat θ d w K a ≤ 0) := by
    rcases eq_or_lt_of_le hF.ca with h' | h'
    · have hb := S.left_bound_line₁ hF hK (Or.inl h'.symm)
      refine ⟨lt_of_le_of_lt hb ?_, fun h0 => ?_⟩
      · rw [div_lt_one (by positivity)]; linarith
      · rw [h0] at hb ⊢; simpa using hb
    · have hz := hza.resolve_left h'.ne'
      have ha0' : a ≠ 0 := (lt_of_le_of_lt S.adm.c_nonneg h').ne'
      refine ⟨?_, fun h0 => absurd h0 ha0'⟩
      rcases min_choice (θ.line₁ a) (θ.line₂ a) with hm | hm
      · have hU : θ.U a = θ.line₁ a := hm
        have hb := S.left_bound_line₁ hF hK (Or.inr (by rw [hz, hU]))
        exact lt_of_le_of_lt hb (by rw [div_lt_one (by positivity)]; linarith)
      · have hU : θ.U a = θ.line₂ a := hm
        have hb := S.left_bound_line₂ hF hK h' (by rw [hz, hU])
        exact lt_of_le_of_lt hb (by rw [div_lt_one (by positivity)]; linarith)
  have hright : 0 < hat θ d w K b := by
    rcases min_choice (θ.line₁ b) (θ.line₂ b) with hm | hm
    · have hU : θ.U b = θ.line₁ b := hm
      have hb := S.right_bound_line₁ hF hK (by rw [hzb, hU])
      exact lt_of_lt_of_le (by positivity) hb
    · have hU : θ.U b = θ.line₂ b := hm
      have hb := S.right_bound_line₂ hF hK (by rw [hzb, hU])
      exact lt_of_lt_of_le (by positivity) hb
  have hanti := S.strictAntiOn_hat K hF.ca hF.bξ
  have hapos : 0 < a := by
    rcases eq_or_lt_of_le ha0 with h0 | h0
    · exfalso
      have h1 := hleft.2 h0.symm
      have h2 := hanti ⟨le_rfl, hF.ab.le⟩ ⟨hF.ab.le, le_rfl⟩ hF.ab
      linarith
    · exact h0
  have hbounds : ∀ t ∈ Icc a b, 0 < hat θ d w K t ∧ hat θ d w K t < 1 := by
    intro t ht
    have h1 : hat θ d w K b ≤ hat θ d w K t := hanti.antitoneOn ht ⟨hF.ab.le, le_rfl⟩ ht.2
    have h2 : hat θ d w K t ≤ hat θ d w K a := hanti.antitoneOn ⟨le_rfl, hF.ab.le⟩ ht ht.1
    exact ⟨lt_of_lt_of_le hright h1, lt_of_le_of_lt h2 hleft.1⟩
  have hx₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith [hF.ab], by linarith [hF.ab]⟩
  refine ⟨K, Cfun θ d w K ((a + b) / 2), hK, hapos, ?_, fun t ht => S.Cfun_const hF hK ht hx₀,
    hbounds⟩
  have hb := hbounds _ (Ioo_subset_Icc_self hx₀)
  unfold Cfun
  have hx0 : 0 < (a + b) / 2 := by linarith [hapos, hF.ab]
  have h1 : 0 < d * ((a + b) / 2) * Real.exp (-2 * zfun θ w ((a + b) / 2)) := by
    have := S.d_pos; positivity
  have h2 := mul_pos hb.1 (sub_pos.mpr hb.2)
  nlinarith

/-! ### The candidate on a free stretch -/

theorem hasDerivAt_Pstar {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K) {t : ℝ}
    (ht : t ∈ Ioo a b) : HasDerivAt (Pstar θ w) (Pstar θ w t * (hat θ d w K t / t)) t := by
  have hct : θ.c < t := (hF.sub_Ioo ht).1
  rw [Pstar_of_lt w hct]
  exact (S.hasDerivAt_z hF hK ht).exp.congr_of_eventuallyEq (Pstar_eventually w hct)

theorem hasDerivAt_D {a b K C : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hC : ∀ t ∈ Ioo a b, Cfun θ d w K t = C) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun t => Pstar θ w t * (hat θ d w K t / t)) (-(C * Pstar θ w t / t ^ 2)) t := by
  have ht0 : t ≠ 0 := (hF.pos_of_mem S.adm ht).ne'
  have hP := S.hasDerivAt_Pstar hF hK ht
  have hω := S.hasDerivAt_hat K (hF.sub_Ioo ht)
  have h := hP.mul (hω.div (hasDerivAt_id' t) ht0)
  refine h.congr_deriv ?_
  simp only [Pi.div_apply]
  rw [← hC t ht]
  unfold Cfun
  field_simp
  ring

theorem deriv_Pstar {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K) {t : ℝ}
    (ht : t ∈ Ioo a b) : deriv (Pstar θ w) t = Pstar θ w t * (hat θ d w K t / t) :=
  (S.hasDerivAt_Pstar hF hK ht).deriv

theorem deriv2_Pstar {a b K C : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hC : ∀ t ∈ Ioo a b, Cfun θ d w K t = C) {t : ℝ} (ht : t ∈ Ioo a b) :
    deriv (deriv (Pstar θ w)) t = -(C * Pstar θ w t / t ^ 2) := by
  have heq : deriv (Pstar θ w) =ᶠ[𝓝 t] fun s => Pstar θ w s * (hat θ d w K s / s) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact S.deriv_Pstar hF hK hs
  rw [heq.deriv_eq]
  exact (S.hasDerivAt_D hF hK hC ht).deriv

theorem euler_Pstar {a b K C : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hC : ∀ t ∈ Ioo a b, Cfun θ d w K t = C) {t : ℝ} (ht : t ∈ Ioo a b) :
    deriv (deriv (Pstar θ w)) t + C / t ^ 2 * Pstar θ w t = 0 := by
  rw [S.deriv2_Pstar hF hK hC ht]; ring

theorem first_integral_Pstar {a b K C : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hC : ∀ t ∈ Ioo a b, Cfun θ d w K t = C) {t : ℝ} (ht : t ∈ Ioo a b) :
    d = t * deriv (Pstar θ w) t ^ 2 - Pstar θ w t * deriv (Pstar θ w) t +
      C * Pstar θ w t ^ 2 / t := by
  have ht0 : t ≠ 0 := (hF.pos_of_mem S.adm ht).ne'
  rw [S.deriv_Pstar hF hK ht, ← hC t ht, Pstar_of_lt w (hF.sub_Ioo ht).1]
  unfold Cfun
  have hPE : Real.exp (zfun θ w t) ^ 2 * Real.exp (-2 * zfun θ w t) = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have e : t * (Real.exp (zfun θ w t) * (hat θ d w K t / t)) ^ 2 -
      Real.exp (zfun θ w t) * (Real.exp (zfun θ w t) * (hat θ d w K t / t)) +
      (hat θ d w K t - hat θ d w K t * hat θ d w K t +
        d * t * Real.exp (-2 * zfun θ w t)) * Real.exp (zfun θ w t) ^ 2 / t =
      d * (Real.exp (zfun θ w t) ^ 2 * Real.exp (-2 * zfun θ w t)) := by
    field_simp; ring
  rw [e, hPE, mul_one]

theorem contDiffOn_Pstar {a b K C : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hC : ∀ t ∈ Ioo a b, Cfun θ d w K t = C) : ContDiffOn ℝ 2 (Pstar θ w) (Ioo a b) := by
  refine contDiffOn_two_of_deriv isOpen_Ioo (fun t ht => S.hasDerivAt_Pstar hF hK ht)
    (fun t ht => S.hasDerivAt_D hF hK hC ht) ?_
  have hPc : ContinuousOn (Pstar θ w) (Ioo a b) :=
    fun t ht => (S.hasDerivAt_Pstar hF hK ht).continuousAt.continuousWithinAt
  exact ((continuousOn_const.mul hPc).div (continuousOn_id.pow 2)
    fun t ht => pow_ne_zero 2 (hF.pos_of_mem S.adm ht).ne').neg

theorem strictConcaveOn_Pstar {a b K C : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hC : ∀ t ∈ Ioo a b, Cfun θ d w K t = C) (hCpos : 0 < C) :
    StrictConcaveOn ℝ (Icc a b) (Pstar θ w) := by
  refine strictConcaveOn_of_deriv2_neg (convex_Icc a b)
    (S.continuousOn_Pstar.mono fun t ht => hF.sub_Icc ht) fun t ht => ?_
  rw [interior_Icc] at ht
  show deriv (deriv (Pstar θ w)) t < 0
  rw [S.deriv2_Pstar hF hK hC ht]
  have hP := S.Pstar_pos (hF.sub_Icc ⟨ht.1.le, ht.2.le⟩)
  have ht0 := hF.pos_of_mem S.adm ht
  have : 0 < C * Pstar θ w t / t ^ 2 := by positivity
  linarith

end Setting

end Relaxed

end FixedPrice.TwoUnit.Family
