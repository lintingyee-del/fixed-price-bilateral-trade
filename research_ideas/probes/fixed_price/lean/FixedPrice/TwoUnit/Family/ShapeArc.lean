import FixedPrice.TwoUnit.Family.ShapeLower

/-!
# Work package B, part 9: a free stretch of the relaxed minimizer

On a stretch `(a, b)` where the upper obstacle is slack, `ω + dF` is constant along good points,
so `ω` has the continuous representative `ω̂ = K - dF` and `z' = ω̂/ξ` there. Comparing `z` with
an affine obstacle touching at an endpoint bounds `ω̂(a) ≤ αa/(αa + γ) < 1` and
`ω̂(b) ≥ αb/(αb + γ) > 0`; since `ω̂' = -d e^{-2z} < 0`, `0 < ω̂ < 1` on the stretch and `a > 0`.
The quantity `C = ω̂ - ω̂² + dξe^{-2z}` is constant and positive, and `P = e^z` satisfies
`P'' + CP/ξ² = 0`, `d = ξP'² - PP' + CP²/ξ`, is `C²` and strictly concave on `[a, b]`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

theorem contDiffOn_two_of_deriv {f g g' : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasDerivAt f (g x) x) (hg : ∀ x ∈ s, HasDerivAt g (g' x) x)
    (hg' : ContinuousOn g' s) : ContDiffOn ℝ 2 f s := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  refine ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  refine ContDiffOn.congr ?_ (fun x hx => (hf x hx).deriv)
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  refine ⟨fun x hx => (hg x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hg'.congr fun x hx => (hg x hx).deriv

/-- The candidate minimizer: `line₁` up to `c_f`, then `e^z`. -/
def Pstar (θ : Params) (w : H θ) (ξ : ℝ) : ℝ :=
  if ξ ≤ θ.c then θ.line₁ ξ else Real.exp (zfun θ w ξ)

theorem Pstar_c (w : H θ) : Pstar θ w θ.c = θ.p := by
  unfold Pstar; rw [if_pos le_rfl, Params.line₁_c]

theorem Pstar_of_lt (w : H θ) {ξ : ℝ} (hξ : θ.c < ξ) : Pstar θ w ξ = Real.exp (zfun θ w ξ) := by
  unfold Pstar; rw [if_neg (not_le.mpr hξ)]

theorem Pstar_eventually (w : H θ) {ξ : ℝ} (hξ : θ.c < ξ) :
    Pstar θ w =ᶠ[𝓝 ξ] fun t => Real.exp (zfun θ w t) := by
  filter_upwards [Ioi_mem_nhds hξ] with t ht using Pstar_of_lt w ht

/-- The continuous representative `ω̂ = K - dF` of `ω` on a free stretch. -/
def hat (θ : Params) (d : ℝ) (w : H θ) (K : ℝ) (t : ℝ) : ℝ := K - d * Fint θ w t

/-- `(a, b)` is a stretch of the curve interval where the upper obstacle is slack. -/
structure Free (θ : Params) (w : H θ) (a b : ℝ) : Prop where
  ca : θ.c ≤ a
  ab : a < b
  bξ : b ≤ θ.ξ₀
  free : ∀ ξ ∈ Ioo a b, zfun θ w ξ < Real.log (θ.U ξ)

/-- `ω̂ = K - dF` represents `ω` at the good points of `(a, b)`. -/
def IsHat (θ : Params) (d : ℝ) (w : H θ) (a b K : ℝ) : Prop :=
  ∀ y ∈ Ioo a b, Good w y → omega w y = hat θ d w K y

/-- The conserved quantity `ω̂ - ω̂² + dξe^{-2z}`. -/
def Cfun (θ : Params) (d : ℝ) (w : H θ) (K : ℝ) (t : ℝ) : ℝ :=
  hat θ d w K t - hat θ d w K t * hat θ d w K t + d * t * Real.exp (-2 * zfun θ w t)

namespace Free

variable {w : H θ} {a b : ℝ} (hF : Free θ w a b)
include hF

theorem sub_Ioo {t : ℝ} (ht : t ∈ Ioo a b) : t ∈ Ioo θ.c θ.ξ₀ :=
  ⟨lt_of_le_of_lt hF.ca ht.1, lt_of_lt_of_le ht.2 hF.bξ⟩

theorem sub_Icc {t : ℝ} (ht : t ∈ Icc a b) : t ∈ Icc θ.c θ.ξ₀ :=
  ⟨hF.ca.trans ht.1, ht.2.trans hF.bξ⟩

theorem pos_of_mem (hθ : θ.Admissible) {t : ℝ} (ht : t ∈ Ioo a b) : 0 < t :=
  lt_of_le_of_lt (hθ.c_nonneg.trans hF.ca) ht.1

end Free

namespace Setting

variable {d : ℝ} {w : H θ} (S : Setting θ d w)
include S

/-! ### The candidate curve -/

theorem continuousOn_Pstar : ContinuousOn (Pstar θ w) (Icc θ.c θ.ξ₀) := by
  intro ξ hξ
  rcases eq_or_lt_of_le hξ.1 with h | h
  · rw [← h]
    have h1 : ContinuousWithinAt (Pstar θ w) (Ioi θ.c) θ.c := by
      show Tendsto (Pstar θ w) (𝓝[>] θ.c) (𝓝 (Pstar θ w θ.c))
      rw [Pstar_c]
      have := (Real.continuous_exp.tendsto _).comp S.tendsto_z_c
      rw [Real.exp_log S.adm.p_pos] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (Pstar_of_lt w ht).symm
    exact (continuousWithinAt_Ioi_iff_Ici.mp h1).mono Icc_subset_Ici_self
  · have h2 : ContinuousWithinAt (zfun θ w) (Ioc θ.c θ.ξ₀) ξ :=
      continuousOn_zfun S.adm w ξ ⟨h, hξ.2⟩
    have h3 : ContinuousWithinAt (zfun θ w) (Icc θ.c θ.ξ₀) ξ :=
      h2.mono_of_mem_nhdsWithin
        (mem_nhdsWithin.mpr ⟨Ioi θ.c, isOpen_Ioi, h, fun t ht => ⟨ht.1, ht.2.2⟩⟩)
    have hz : ContinuousWithinAt (fun t => Real.exp (zfun θ w t)) (Icc θ.c θ.ξ₀) ξ :=
      Real.continuous_exp.continuousAt.comp_continuousWithinAt h3
    exact hz.congr_of_eventuallyEq
      (eventually_nhdsWithin_of_eventually_nhds (Pstar_eventually w h)) (Pstar_of_lt w h)

theorem Pstar_pos {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : 0 < Pstar θ w ξ := by
  rcases eq_or_lt_of_le hξ.1 with h | h
  · rw [← h, Pstar_c]; exact S.adm.p_pos
  · rw [Pstar_of_lt w h]; exact Real.exp_pos _

theorem Pstar_le_U {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : Pstar θ w ξ ≤ θ.U ξ := by
  rcases eq_or_lt_of_le hξ.1 with h | h
  · rw [← h, Pstar_c, S.U_c]
  · rw [Pstar_of_lt w h, ← Real.exp_log (S.U_pos hξ.1)]
    exact Real.exp_le_exp.mpr (S.z_le ⟨h, hξ.2⟩)

theorem p_le_Pstar {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) : θ.p ≤ Pstar θ w ξ := by
  rcases eq_or_lt_of_le hξ.1 with h | h
  · rw [← h, Pstar_c]
  · rw [Pstar_of_lt w h, ← Real.exp_log S.adm.p_pos]
    exact Real.exp_le_exp.mpr (S.z_ge ⟨h, hξ.2⟩)

theorem Pstar_ξ₀ : Pstar θ w θ.ξ₀ = 1 := by
  rw [Pstar_of_lt w S.c_lt, zfun_ξ₀ S.adm w, Real.exp_zero]

theorem Pstar_lt_U_iff {ξ : ℝ} (hξ : ξ ∈ Ioc θ.c θ.ξ₀) :
    Pstar θ w ξ < θ.U ξ ↔ zfun θ w ξ < Real.log (θ.U ξ) := by
  rw [Pstar_of_lt w hξ.1]
  conv_lhs => rw [← Real.exp_log (S.U_pos hξ.1.le)]
  exact Real.exp_lt_exp

omit S in
theorem Pstar_eq_iff {ξ : ℝ} (hξ : θ.c < ξ) {L : ℝ} (hL : 0 < L) :
    Pstar θ w ξ = L ↔ zfun θ w ξ = Real.log L := by
  rw [Pstar_of_lt w hξ]
  constructor
  · intro h; rw [← h, Real.log_exp]
  · intro h; rw [h, Real.exp_log hL]

/-! ### The representative on a free stretch -/

theorem continuousOn_hat (K : ℝ) : ContinuousOn (hat θ d w K) (Icc θ.c θ.ξ₀) :=
  continuousOn_const.sub (continuousOn_const.mul (continuousOn_Fint S.adm S.mem))

theorem hasDerivAt_hat (K : ℝ) {t : ℝ} (ht : t ∈ Ioo θ.c θ.ξ₀) :
    HasDerivAt (hat θ d w K) (-(d * Real.exp (-2 * zfun θ w t))) t :=
  ((hasDerivAt_Fint S.adm S.mem ht).const_mul d).const_sub K

theorem strictAntiOn_hat (K : ℝ) {a b : ℝ} (hca : θ.c ≤ a) (hbξ : b ≤ θ.ξ₀) :
    StrictAntiOn (hat θ d w K) (Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    ((S.continuousOn_hat K).mono fun t ht => ⟨hca.trans ht.1, ht.2.trans hbξ⟩) fun t ht => ?_
  rw [interior_Icc] at ht
  rw [(S.hasDerivAt_hat K ⟨lt_of_le_of_lt hca ht.1, lt_of_lt_of_le ht.2 hbξ⟩).deriv]
  have := mul_pos S.d_pos (Real.exp_pos (-2 * zfun θ w t))
  linarith

/-- `ω + dF` is constant along good points of a free stretch. -/
theorem A_const {a b : ℝ} (hF : Free θ w a b) {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hxy : x < y) (hgx : Good w x) (hgy : Good w y) :
    omega w x + d * Fint θ w x = omega w y + d * Fint θ w y := by
  have hcx : θ.c < x := (hF.sub_Ioo hx).1
  have h1 := S.D_all hcx hxy (hF.sub_Ioo hy).2 hgx hgy
  have h2 := S.U_local (x := x) (y := y) (y' := (y + b) / 2) hcx hxy (by linarith [hy.2])
    (by linarith [hy.2, hF.bξ])
    (fun ξ hξ => hF.free ξ ⟨lt_of_lt_of_le hx.1 hξ.1, by linarith [hξ.2, hy.2]⟩) hgx hgy
  linarith

theorem exists_hat {a b : ℝ} (hF : Free θ w a b) : ∃ K, IsHat θ d w a b K := by
  obtain ⟨x₀, hx₀, hg₀⟩ := exists_good S.adm w S.c_lt hF.ab fun t ht => hF.sub_Ioo ht
  refine ⟨omega w x₀ + d * Fint θ w x₀, fun y hy hgy => ?_⟩
  unfold hat
  rcases lt_trichotomy x₀ y with h | h | h
  · have := S.A_const hF hx₀ hy h hg₀ hgy; linarith
  · rw [← h]; ring
  · have := S.A_const hF hy hx₀ h hgy hg₀; linarith

theorem hat_ae {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K) :
    ∀ᵐ s, s ∈ Ioo a b → omega w s / s = hat θ d w K s / s := by
  filter_upwards [ae_good S.adm w S.c_lt] with s hs hsab
  rw [hK s hsab (hs (hF.sub_Ioo hsab))]

theorem z_eq_hat {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K) {x₀ t : ℝ}
    (hx₀ : x₀ ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    zfun θ w t = zfun θ w x₀ + ∫ s in x₀..t, hat θ d w K s / s := by
  have hae := S.hat_ae hF hK
  have key : ∀ u v, u ∈ Ioo a b → v ∈ Ioo a b → u ≤ v →
      zfun θ w v - zfun θ w u = ∫ s in u..v, hat θ d w K s / s := by
    intro u v hu hv huv
    rw [z_sub_eq_integral w (hF.pos_of_mem S.adm hu) (hF.sub_Ioo hu).1.le huv
      (hF.sub_Ioo hv).2.le]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with s hs hsI
    rw [uIoc_of_le huv] at hsI
    exact hs ⟨hu.1.trans hsI.1, lt_of_le_of_lt hsI.2 hv.2⟩
  rcases le_total x₀ t with h | h
  · have := key x₀ t hx₀ ht h; linarith
  · have := key t x₀ ht hx₀ h
    rw [intervalIntegral.integral_symm]; linarith

theorem continuousOn_hat_div {a b K : ℝ} (hF : Free θ w a b) :
    ContinuousOn (fun s => hat θ d w K s / s) (Ioo a b) :=
  ((S.continuousOn_hat K).mono fun s hs => Ioo_subset_Icc_self (hF.sub_Ioo hs)).div
    continuousOn_id fun s hs => (hF.pos_of_mem S.adm hs).ne'

theorem hasDerivAt_z {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K) {t : ℝ}
    (ht : t ∈ Ioo a b) : HasDerivAt (zfun θ w) (hat θ d w K t / t) t := by
  have hcont := S.continuousOn_hat_div (K := K) hF
  have hFTC : HasDerivAt (fun u => ∫ s in t..u, hat θ d w K s / s) (hat θ d w K t / t) t :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hcont.stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hcont.continuousAt (Ioo_mem_nhds ht.1 ht.2))
  have heq : zfun θ w =ᶠ[𝓝 t] fun u => zfun θ w t + ∫ s in t..u, hat θ d w K s / s := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact S.z_eq_hat hF hK ht hu
  exact (hFTC.const_add _).congr_of_eventuallyEq heq

/-! ### Endpoint bounds -/

/-- At a left endpoint where `z` starts on the line `αξ + γ` and stays below it,
`ω̂(a) ≤ αa/(αa + γ)`. -/
theorem left_bound {a b K α γ : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hz : ∀ t ∈ Ioo a b, zfun θ w t ≤ Real.log (α * t + γ))
    (hlim : Tendsto (zfun θ w) (𝓝[>] a) (𝓝 (Real.log (α * a + γ)))) :
    hat θ d w K a ≤ α * a / (α * a + γ) := by
  have ha0 : 0 ≤ a := S.adm.c_nonneg.trans hF.ca
  have hLa : 0 < α * a + γ := by positivity
  by_contra hlt
  push_neg at hlt
  have h1 : ContinuousWithinAt (hat θ d w K) (Ioi a) a :=
    ((S.continuousOn_hat K) a ⟨hF.ca, hF.ab.le.trans hF.bξ⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hF.ab) fun t ht => hF.sub_Icc ⟨ht.1.le, ht.2.le⟩)
  have h2 : ContinuousAt (fun t => α * t / (α * t + γ)) a :=
    (continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hLa.ne'
  have hev : ∀ᶠ t in 𝓝[>] a, 0 < hat θ d w K t - α * t / (α * t + γ) :=
    (h1.sub h2.continuousWithinAt).eventually (lt_mem_nhds (sub_pos.mpr hlt))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hev.and (Ioo_mem_nhdsGT hF.ab))
  set ψ : ℝ → ℝ := fun t => zfun θ w t - Real.log (α * t + γ) with hψ
  have hψd : ∀ t ∈ Ioo a u, HasDerivAt ψ (hat θ d w K t / t - α / (α * t + γ)) t := by
    intro t ht
    have htab : t ∈ Ioo a b := (hsub ht).2
    have ht0 : 0 < t := hF.pos_of_mem S.adm htab
    have hL : 0 < α * t + γ := by positivity
    have hlog : HasDerivAt (fun t => Real.log (α * t + γ)) (α * 1 / (α * t + γ)) t :=
      (((hasDerivAt_id t).const_mul α).add_const γ).log hL.ne'
    rw [mul_one] at hlog
    exact (S.hasDerivAt_z hF hK htab).sub hlog
  have hψpos : ∀ t ∈ Ioo a u, 0 < hat θ d w K t / t - α / (α * t + γ) := by
    intro t ht
    have htab : t ∈ Ioo a b := (hsub ht).2
    have ht0 : 0 < t := hF.pos_of_mem S.adm htab
    have hL : 0 < α * t + γ := by positivity
    have := (hsub ht).1
    have e : hat θ d w K t / t - α / (α * t + γ) =
        (hat θ d w K t - α * t / (α * t + γ)) / t := by
      field_simp
    rw [e]
    exact div_pos this ht0
  have hmono : StrictMonoOn ψ (Ioo a u) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo a u)
      (fun t ht => (hψd t ht).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Ioo] at ht
    rw [(hψd t ht).deriv]
    exact hψpos t ht
  have hψlim : Tendsto ψ (𝓝[>] a) (𝓝 0) := by
    have hlog : Tendsto (fun t => Real.log (α * t + γ)) (𝓝[>] a) (𝓝 (Real.log (α * a + γ))) := by
      have hc : ContinuousAt (fun t => Real.log (α * t + γ)) a :=
        ((continuousAt_const.mul continuousAt_id).add continuousAt_const).log hLa.ne'
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    have := hlim.sub hlog
    rwa [sub_self] at this
  have hnonneg : ∀ t ∈ Ioo a u, 0 ≤ ψ t := by
    intro t ht
    refine le_of_tendsto hψlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht.1] with t' ht'
    exact (hmono ⟨ht'.1, ht'.2.trans ht.2⟩ ht ht'.2).le
  have hu' : a < u := hu
  have ht₁ : a + (u - a) / 3 ∈ Ioo a u := ⟨by linarith, by linarith⟩
  have ht₂ : a + 2 * (u - a) / 3 ∈ Ioo a u := ⟨by linarith, by linarith⟩
  have h12 := hmono ht₁ ht₂ (by linarith)
  have h0 := hnonneg _ ht₁
  have hle : ψ (a + 2 * (u - a) / 3) ≤ 0 := by
    simp only [hψ]; linarith [hz _ (hsub ht₂).2]
  linarith

/-- At a right endpoint where `z` ends on the line `αξ + γ` and stays below it,
`ω̂(b) ≥ αb/(αb + γ)`. -/
theorem right_bound {a b K α γ : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K)
    (hα : 0 ≤ α) (hγ : 0 < γ) (hz : ∀ t ∈ Ioo a b, zfun θ w t ≤ Real.log (α * t + γ))
    (hzb : zfun θ w b = Real.log (α * b + γ)) :
    α * b / (α * b + γ) ≤ hat θ d w K b := by
  have hb0 : 0 < b := lt_of_le_of_lt (S.adm.c_nonneg.trans hF.ca) hF.ab
  have hLb : 0 < α * b + γ := by positivity
  have hcb : θ.c < b := lt_of_le_of_lt hF.ca hF.ab
  by_contra hlt
  push_neg at hlt
  have h1 : ContinuousWithinAt (hat θ d w K) (Iio b) b :=
    ((S.continuousOn_hat K) b ⟨hcb.le, hF.bξ⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT hF.ab) fun t ht => hF.sub_Icc ⟨ht.1.le, ht.2.le⟩)
  have h2 : ContinuousAt (fun t => α * t / (α * t + γ)) b :=
    (continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hLb.ne'
  have hev : ∀ᶠ t in 𝓝[<] b, 0 < α * t / (α * t + γ) - hat θ d w K t :=
    (h2.continuousWithinAt.sub h1).eventually (lt_mem_nhds (sub_pos.mpr hlt))
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (hev.and (Ioo_mem_nhdsLT hF.ab))
  set ψ : ℝ → ℝ := fun t => zfun θ w t - Real.log (α * t + γ) with hψ
  have hψd : ∀ t ∈ Ioo l b, HasDerivAt ψ (hat θ d w K t / t - α / (α * t + γ)) t := by
    intro t ht
    have htab : t ∈ Ioo a b := (hsub ht).2
    have ht0 : 0 < t := hF.pos_of_mem S.adm htab
    have hL : 0 < α * t + γ := by positivity
    have hlog : HasDerivAt (fun t => Real.log (α * t + γ)) (α * 1 / (α * t + γ)) t :=
      (((hasDerivAt_id t).const_mul α).add_const γ).log hL.ne'
    rw [mul_one] at hlog
    exact (S.hasDerivAt_z hF hK htab).sub hlog
  have hψneg : ∀ t ∈ Ioo l b, hat θ d w K t / t - α / (α * t + γ) < 0 := by
    intro t ht
    have htab : t ∈ Ioo a b := (hsub ht).2
    have ht0 : 0 < t := hF.pos_of_mem S.adm htab
    have hL : 0 < α * t + γ := by positivity
    have := (hsub ht).1
    have e : hat θ d w K t / t - α / (α * t + γ) =
        -((α * t / (α * t + γ) - hat θ d w K t) / t) := by
      field_simp; ring
    rw [e]
    exact neg_neg_of_pos (div_pos this ht0)
  have hanti : StrictAntiOn ψ (Ioo l b) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo l b)
      (fun t ht => (hψd t ht).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Ioo] at ht
    rw [(hψd t ht).deriv]
    exact hψneg t ht
  have hzc : ContinuousWithinAt (zfun θ w) (Iio b) b :=
    (continuousOn_zfun S.adm w b ⟨hcb, hF.bξ⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT hcb) fun t ht => ⟨ht.1, ht.2.le.trans hF.bξ⟩)
  have hψlim : Tendsto ψ (𝓝[<] b) (𝓝 0) := by
    have hlog : Tendsto (fun t => Real.log (α * t + γ)) (𝓝[<] b) (𝓝 (Real.log (α * b + γ))) := by
      have hc : ContinuousAt (fun t => Real.log (α * t + γ)) b :=
        ((continuousAt_const.mul continuousAt_id).add continuousAt_const).log hLb.ne'
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    have := (hzc.tendsto).sub hlog
    rwa [hzb, sub_self] at this
  have hnonneg : ∀ t ∈ Ioo l b, 0 ≤ ψ t := by
    intro t ht
    refine le_of_tendsto hψlim ?_
    filter_upwards [Ioo_mem_nhdsLT ht.2] with t' ht'
    exact (hanti ht ⟨ht.1.trans ht'.1, ht'.2⟩ ht'.1).le
  have hl' : l < b := hl
  have ht₁ : l + (b - l) / 3 ∈ Ioo l b := ⟨by linarith, by linarith⟩
  have ht₂ : l + 2 * (b - l) / 3 ∈ Ioo l b := ⟨by linarith, by linarith⟩
  have h12 := hanti ht₁ ht₂ (by linarith)
  have h0 := hnonneg _ ht₂
  have hle : ψ (l + (b - l) / 3) ≤ 0 := by
    simp only [hψ]; linarith [hz _ (hsub ht₁).2]
  linarith

/-! ### The conserved quantity -/

theorem hasDerivAt_Cfun {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K) {t : ℝ}
    (ht : t ∈ Ioo a b) : HasDerivAt (Cfun θ d w K) 0 t := by
  have ht0 : t ≠ 0 := (hF.pos_of_mem S.adm ht).ne'
  have hω := S.hasDerivAt_hat K (hF.sub_Ioo ht)
  have hz := S.hasDerivAt_z hF hK ht
  have hE : HasDerivAt (fun t => Real.exp (-2 * zfun θ w t))
      (Real.exp (-2 * zfun θ w t) * (-2 * (hat θ d w K t / t))) t :=
    (hz.const_mul (-2)).exp
  have h := (hω.sub (hω.mul hω)).add (((hasDerivAt_id' t).const_mul d).mul hE)
  refine h.congr_deriv ?_
  field_simp
  ring

theorem Cfun_const {a b K : ℝ} (hF : Free θ w a b) (hK : IsHat θ d w a b K) {t₁ t₂ : ℝ}
    (h₁ : t₁ ∈ Ioo a b) (h₂ : t₂ ∈ Ioo a b) : Cfun θ d w K t₁ = Cfun θ d w K t₂ := by
  have key : ∀ u v, u ∈ Ioo a b → v ∈ Ioo a b → u < v → Cfun θ d w K u = Cfun θ d w K v := by
    intro u v hu hv huv
    obtain ⟨ζ, -, hζ⟩ := exists_hasDerivAt_eq_slope (Cfun θ d w K) (fun _ => 0) huv
      (fun s hs => (S.hasDerivAt_Cfun hF hK
        ⟨hu.1.trans_le hs.1, lt_of_le_of_lt hs.2 hv.2⟩).continuousAt.continuousWithinAt)
      (fun s hs => S.hasDerivAt_Cfun hF hK ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩)
    have hne : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
    have := hζ.symm
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · linarith
    · exact absurd h hne
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact key t₁ t₂ h₁ h₂ h
  · rw [h]
  · exact (key t₂ t₁ h₂ h₁ h).symm

end Setting

end Relaxed

end FixedPrice.TwoUnit.Family
