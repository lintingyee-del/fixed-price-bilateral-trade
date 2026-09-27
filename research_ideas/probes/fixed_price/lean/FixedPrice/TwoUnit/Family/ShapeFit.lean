import FixedPrice.TwoUnit.Family.ShapeComp

/-!
# Work package B, part 12: smooth fit, and no contact at the corner

At an interior contact `a` the left derivative is the obstacle slope `1`. Pushing down gives
`ω(x) + dF(x) ≤ ω̂(y) + dF(y)` for good `x < a < y`, so `ω̂(a) ≥ a/(a + δ_f)`; the comparison with
the obstacle on the right gives `≤`. Hence the right derivative `P*(a)ω̂(a)/a` is `1` too. The
same at `b` with slope `h_f`. If the whole curve lies on `U_f`, the same inequality at the corner
of `U_f` would give `1 ≤ h_f`, while a genuine corner needs `h_f < 1`; so `U_f` has no corner
inside and the curve is entirely affine.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

namespace Setting

variable {d : ℝ} {w : H θ} (S : Setting θ d w)
include S

theorem line₁_pos {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 < θ.line₁ ξ := by
  unfold Params.line₁; linarith [S.adm.δ_pos]

theorem line₂_pos {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 < θ.line₂ ξ := by
  unfold Params.line₂
  have := S.adm.h_pos
  have := Admissible.e_pos' S.adm
  positivity

theorem continuousWithinAt_Fint_left {a : ℝ} (hca : θ.c < a) (haξ : a ≤ θ.ξ₀) :
    ContinuousWithinAt (Fint θ w) (Iio a) a :=
  (continuousOn_Fint S.adm S.mem a ⟨hca.le, haξ⟩).mono_of_mem_nhdsWithin
    (mem_of_superset (Ioo_mem_nhdsLT hca) fun t ht => ⟨ht.1.le, ht.2.le.trans haξ⟩)

theorem continuousWithinAt_Fint_right {a : ℝ} (hca : θ.c ≤ a) (haξ : a < θ.ξ₀) :
    ContinuousWithinAt (Fint θ w) (Ioi a) a :=
  (continuousOn_Fint S.adm S.mem a ⟨hca, haξ.le⟩).mono_of_mem_nhdsWithin
    (mem_of_superset (Ioo_mem_nhdsGT haξ) fun t ht => ⟨hca.trans ht.1.le, ht.2.le⟩)

/-- `z = log(1·ξ + δ_f)` near a point of an initial contact stretch. -/
theorem z_eq_line₁_near {x₀ a b K C x : ℝ} (hc : Comp θ d w x₀ a b K C) (hx : x ∈ Ioo θ.c a) :
    zfun θ w =ᶠ[𝓝 x] fun ξ => Real.log (1 * ξ + θ.δ) := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with ξ hξ
  have hP := S.left_contact hc ξ ⟨hξ.1.le, hξ.2.le⟩
  have hL := S.line₁_pos (S.adm.c_nonneg.trans hξ.1.le)
  rw [(Setting.Pstar_eq_iff hξ.1 hL).mp hP]
  unfold Params.line₁; ring_nf

/-- `z = log(h_f ξ + e_f)` near a point of a final contact stretch. -/
theorem z_eq_line₂_near {x₀ a b K C y : ℝ} (hc : Comp θ d w x₀ a b K C) (hy : y ∈ Ioo b θ.ξ₀) :
    zfun θ w =ᶠ[𝓝 y] fun ξ => Real.log (θ.h * ξ + θ.e) := by
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with ξ hξ
  have hcξ : θ.c < ξ := lt_of_le_of_lt hc.free.ca (hc.free.ab.trans hξ.1)
  have hP := S.right_contact hc ξ ⟨hξ.1.le, hξ.2.le⟩
  have hL := S.line₂_pos (S.adm.c_nonneg.trans hcξ.le)
  rw [(Setting.Pstar_eq_iff hcξ hL).mp hP]
  rfl

theorem hat_a_eq {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) (hca : θ.c < a) :
    hat θ d w K a = 1 * a / (1 * a + θ.δ) := by
  have hab := hc.free.ab
  have hbξ := hc.free.bξ
  have hPa : Pstar θ w a = θ.line₁ a := S.left_contact hc a ⟨hca.le, le_rfl⟩
  have hza : zfun θ w a = Real.log (θ.line₁ a) :=
    (Setting.Pstar_eq_iff hca (S.line₁_pos hc.a_pos.le)).mp hPa
  refine le_antisymm (S.left_bound_line₁ hc.free hc.ishat (Or.inr hza)) ?_
  have hη0 : 0 < Min.min (a - θ.c) (b - a) := lt_min (by linarith) (by linarith)
  have hm1 := min_le_left (a - θ.c) (b - a)
  have hm2 := min_le_right (a - θ.c) (b - a)
  have hδ := S.adm.δ_pos
  have hcont₁ : ContinuousWithinAt (fun x => 1 * x / (1 * x + θ.δ) + d * Fint θ w x) (Iio a) a :=
    (((continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const)
      (by have := hc.a_pos; show (1 : ℝ) * a + θ.δ ≠ 0; positivity)).continuousWithinAt).add
      ((S.continuousWithinAt_Fint_left hca (hab.le.trans hbξ)).const_mul d)
  have hle := le_of_good (g₁ := fun x => 1 * x / (1 * x + θ.δ) + d * Fint θ w x)
    (g₂ := fun _ => K) hη0 (Good w)
    (fun a' b' h1 h2 h3 => exists_good S.adm w S.c_lt h2 fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    hcont₁ continuousWithinAt_const (fun x hx y hy hgx hgy => by
      have hxI : x ∈ Ioo θ.c a := ⟨by linarith [hx.1], hx.2⟩
      have hyI : y ∈ Ioo a b := ⟨hy.1, by linarith [hy.2]⟩
      have hx0 : 0 < x := lt_of_le_of_lt S.adm.c_nonneg hxI.1
      have hωx := omega_of_log_affine hgx hx0 (by positivity) (S.z_eq_line₁_near hc hxI)
      have hωy := hc.ishat y hyI hgy
      have hD := S.D_all hxI.1 (hxI.2.trans hyI.1) (lt_of_lt_of_le hyI.2 hbξ) hgx hgy
      unfold hat at hωy
      simp only
      linarith)
  simp only at hle
  unfold hat
  linarith

theorem hat_b_eq {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) (hbξ : b < θ.ξ₀) :
    hat θ d w K b = θ.h * b / (θ.h * b + θ.e) := by
  have hab := hc.free.ab
  have hca := hc.free.ca
  have hcb : θ.c < b := lt_of_le_of_lt hca hab
  have hPb : Pstar θ w b = θ.line₂ b := S.right_contact hc b ⟨le_rfl, hbξ.le⟩
  have hzb : zfun θ w b = Real.log (θ.line₂ b) :=
    (Setting.Pstar_eq_iff hcb (S.line₂_pos (hc.a_pos.le.trans hab.le))).mp hPb
  refine le_antisymm ?_ (S.right_bound_line₂ hc.free hc.ishat hzb)
  have hη0 : 0 < Min.min (b - a) (θ.ξ₀ - b) := lt_min (by linarith) (by linarith)
  have hm1 := min_le_left (b - a) (θ.ξ₀ - b)
  have hm2 := min_le_right (b - a) (θ.ξ₀ - b)
  have he := Admissible.e_pos' S.adm
  have hh := S.adm.h_pos
  have hb0 : 0 < b := hc.a_pos.trans hab
  have hcont₂ : ContinuousWithinAt (fun y => θ.h * y / (θ.h * y + θ.e) + d * Fint θ w y)
      (Ioi b) b :=
    (((continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const)
      (by show θ.h * b + θ.e ≠ 0; positivity)).continuousWithinAt).add
      ((S.continuousWithinAt_Fint_right hcb.le hbξ).const_mul d)
  have hle := le_of_good (g₁ := fun _ => K)
    (g₂ := fun y => θ.h * y / (θ.h * y + θ.e) + d * Fint θ w y) hη0 (Good w)
    (fun a' b' h1 h2 h3 => exists_good S.adm w S.c_lt h2 fun t ht =>
      ⟨by linarith [ht.1, hc.a_pos], by linarith [ht.2]⟩)
    continuousWithinAt_const hcont₂ (fun x hx y hy hgx hgy => by
      have hxI : x ∈ Ioo a b := ⟨by linarith [hx.1], hx.2⟩
      have hyI : y ∈ Ioo b θ.ξ₀ := ⟨hy.1, by linarith [hy.2]⟩
      have hy0 : 0 < y := hb0.trans hyI.1
      have hωy := omega_of_log_affine hgy hy0 (by positivity) (S.z_eq_line₂_near hc hyI)
      have hωx := hc.ishat x hxI hgx
      have hD := S.D_all (lt_of_le_of_lt hca hxI.1) (hxI.2.trans hyI.1) hyI.2 hgx hgy
      unfold hat at hωx
      simp only
      linarith)
  simp only at hle
  unfold hat
  linarith

theorem tendsto_deriv_Pstar_right {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) :
    Tendsto (fun t => deriv (Pstar θ w) t) (𝓝[>] a)
      (𝓝 (Pstar θ w a * (hat θ d w K a / a))) := by
  have hab := hc.free.ab
  have hmem : Icc θ.c θ.ξ₀ ∈ 𝓝[>] a :=
    mem_of_superset (Ioo_mem_nhdsGT hab) fun t ht => hc.free.sub_Icc ⟨ht.1.le, ht.2.le⟩
  have haI : a ∈ Icc θ.c θ.ξ₀ := hc.free.sub_Icc ⟨le_rfl, hab.le⟩
  have h1 : ContinuousWithinAt (Pstar θ w) (Ioi a) a :=
    (S.continuousOn_Pstar a haI).mono_of_mem_nhdsWithin hmem
  have h2 : ContinuousWithinAt (hat θ d w K) (Ioi a) a :=
    (S.continuousOn_hat K a haI).mono_of_mem_nhdsWithin hmem
  have h3 : ContinuousWithinAt (fun t => Pstar θ w t * (hat θ d w K t / t)) (Ioi a) a :=
    h1.mul (h2.div continuousWithinAt_id hc.a_pos.ne')
  refine h3.tendsto.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with t ht
  exact (S.deriv_Pstar hc.free hc.ishat ht).symm

theorem tendsto_deriv_Pstar_left {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) :
    Tendsto (fun t => deriv (Pstar θ w) t) (𝓝[<] b)
      (𝓝 (Pstar θ w b * (hat θ d w K b / b))) := by
  have hab := hc.free.ab
  have hmem : Icc θ.c θ.ξ₀ ∈ 𝓝[<] b :=
    mem_of_superset (Ioo_mem_nhdsLT hab) fun t ht => hc.free.sub_Icc ⟨ht.1.le, ht.2.le⟩
  have hbI : b ∈ Icc θ.c θ.ξ₀ := hc.free.sub_Icc ⟨hab.le, le_rfl⟩
  have h1 : ContinuousWithinAt (Pstar θ w) (Iio b) b :=
    (S.continuousOn_Pstar b hbI).mono_of_mem_nhdsWithin hmem
  have h2 : ContinuousWithinAt (hat θ d w K) (Iio b) b :=
    (S.continuousOn_hat K b hbI).mono_of_mem_nhdsWithin hmem
  have h3 : ContinuousWithinAt (fun t => Pstar θ w t * (hat θ d w K t / t)) (Iio b) b :=
    h1.mul (h2.div continuousWithinAt_id (hc.a_pos.trans hab).ne')
  refine h3.tendsto.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  exact (S.deriv_Pstar hc.free hc.ishat ht).symm

/-- Smooth fit at an interior left contact. -/
theorem fit_left {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) (hca : θ.c < a) :
    HasDerivAt (Pstar θ w) 1 a := by
  have hab := hc.free.ab
  have hL : HasDerivWithinAt (Pstar θ w) 1 (Iic a) a := by
    have hlin : HasDerivWithinAt (fun ξ => θ.line₁ ξ) 1 (Iic a) a := by
      unfold Params.line₁; exact ((hasDerivAt_id' a).add_const θ.δ).hasDerivWithinAt
    refine hlin.congr_of_eventuallyEq ?_ (S.left_contact hc a ⟨hca.le, le_rfl⟩)
    filter_upwards [Icc_mem_nhdsLE hca] with ξ hξ using S.left_contact hc ξ hξ
  have hR : HasDerivWithinAt (Pstar θ w) 1 (Ici a) a := by
    have hval : Pstar θ w a * (hat θ d w K a / a) = 1 := by
      rw [S.left_contact hc a ⟨hca.le, le_rfl⟩, S.hat_a_eq hc hca]
      have ha0 := hc.a_pos
      have hL1 := S.line₁_pos ha0.le
      unfold Params.line₁ at hL1 ⊢
      field_simp
    have hlim := S.tendsto_deriv_Pstar_right hc
    rw [hval] at hlim
    exact hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (S.hasDerivAt_Pstar hc.free hc.ishat ht).differentiableAt.differentiableWithinAt)
      ((S.continuousOn_Pstar a (hc.free.sub_Icc ⟨le_rfl, hab.le⟩)).mono
        fun t ht => hc.free.sub_Icc ⟨ht.1.le, ht.2.le⟩)
      (Ioo_mem_nhdsGT hab) hlim
  have := hL.union hR
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- Smooth fit at an interior right contact. -/
theorem fit_right {x₀ a b K C : ℝ} (hc : Comp θ d w x₀ a b K C) (hbξ : b < θ.ξ₀) :
    HasDerivAt (Pstar θ w) θ.h b := by
  have hab := hc.free.ab
  have hR : HasDerivWithinAt (Pstar θ w) θ.h (Ici b) b := by
    have hlin : HasDerivWithinAt (fun ξ => θ.line₂ ξ) θ.h (Ici b) b := by
      unfold Params.line₂
      have := ((hasDerivAt_id' b).const_mul θ.h).add_const θ.e
      rw [mul_one] at this
      exact this.hasDerivWithinAt
    refine hlin.congr_of_eventuallyEq ?_ (S.right_contact hc b ⟨le_rfl, hbξ.le⟩)
    filter_upwards [Icc_mem_nhdsGE hbξ] with ξ hξ using S.right_contact hc ξ hξ
  have hL : HasDerivWithinAt (Pstar θ w) θ.h (Iic b) b := by
    have hval : Pstar θ w b * (hat θ d w K b / b) = θ.h := by
      rw [S.right_contact hc b ⟨le_rfl, hbξ.le⟩, S.hat_b_eq hc hbξ]
      have hb0 := hc.a_pos.trans hab
      have hL2 := S.line₂_pos hb0.le
      unfold Params.line₂ at hL2 ⊢
      field_simp
    have hlim := S.tendsto_deriv_Pstar_left hc
    rw [hval] at hlim
    exact hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (S.hasDerivAt_Pstar hc.free hc.ishat ht).differentiableAt.differentiableWithinAt)
      ((S.continuousOn_Pstar b (hc.free.sub_Icc ⟨hab.le, le_rfl⟩)).mono
        fun t ht => hc.free.sub_Icc ⟨ht.1.le, ht.2.le⟩)
      (Ioo_mem_nhdsLT hab) hlim
  have := hL.union hR
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- The curve cannot follow `U_f` through a corner inside the interval. -/
theorem no_corner (hPU : ∀ ξ ∈ Icc θ.c θ.ξ₀, Pstar θ w ξ = θ.U ξ)
    (hdc : θ.line₁ θ.c < θ.line₂ θ.c) (hdξ : θ.line₂ θ.ξ₀ < θ.line₁ θ.ξ₀) : False := by
  have hcξ := S.c_lt
  have hδ := S.adm.δ_pos
  have he := Admissible.e_pos' S.adm
  have hh := S.adm.h_pos
  have hc0 := S.adm.c_nonneg
  unfold Params.line₁ Params.line₂ at hdc hdξ
  have hs : 0 < 1 - θ.h := by
    by_contra hs; push_neg at hs
    have := mul_nonpos_of_nonpos_of_nonneg hs (sub_nonneg.mpr hcξ.le)
    nlinarith
  set ξx := (θ.e - θ.δ) / (1 - θ.h) with hξx
  have hx_eq : ξx + θ.δ = θ.h * ξx + θ.e := by
    rw [hξx]; field_simp; ring
  have hcx : θ.c < ξx := by
    have : ξx - θ.c = ((θ.h * θ.c + θ.e) - (θ.c + θ.δ)) / (1 - θ.h) := by
      rw [hξx]; field_simp; ring
    have : 0 < ξx - θ.c := by rw [this]; exact div_pos (by linarith) hs
    linarith
  have hxξ : ξx < θ.ξ₀ := by
    have : θ.ξ₀ - ξx = ((θ.ξ₀ + θ.δ) - (θ.h * θ.ξ₀ + θ.e)) / (1 - θ.h) := by
      rw [hξx]; field_simp; ring
    have : 0 < θ.ξ₀ - ξx := by rw [this]; exact div_pos (by linarith) hs
    linarith
  have hx0 : 0 < ξx := lt_of_le_of_lt hc0 hcx
  -- the two sides of the corner
  have hdl : ∀ ξ, (ξ + θ.δ) - (θ.h * ξ + θ.e) = (1 - θ.h) * (ξ - ξx) := by
    intro ξ; linear_combination hx_eq
  have hz₁ : ∀ x ∈ Ioo θ.c ξx, zfun θ w =ᶠ[𝓝 x] fun ξ => Real.log (1 * ξ + θ.δ) := by
    intro x hx
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with ξ hξ
    have hP := hPU ξ ⟨hξ.1.le, hξ.2.le.trans hxξ.le⟩
    have hmin : θ.U ξ = θ.line₁ ξ := by
      unfold Params.U; apply min_eq_left; unfold Params.line₁ Params.line₂
      have := hdl ξ
      have := mul_neg_of_pos_of_neg hs (sub_neg.mpr hξ.2)
      linarith
    rw [hmin] at hP
    rw [(Setting.Pstar_eq_iff hξ.1 (S.line₁_pos (hc0.trans hξ.1.le))).mp hP]
    unfold Params.line₁; ring_nf
  have hz₂ : ∀ y ∈ Ioo ξx θ.ξ₀, zfun θ w =ᶠ[𝓝 y] fun ξ => Real.log (θ.h * ξ + θ.e) := by
    intro y hy
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with ξ hξ
    have hcξ' : θ.c < ξ := hcx.trans hξ.1
    have hP := hPU ξ ⟨hcξ'.le, hξ.2.le⟩
    have hmin : θ.U ξ = θ.line₂ ξ := by
      unfold Params.U; apply min_eq_right; unfold Params.line₁ Params.line₂
      have := hdl ξ
      have := mul_pos hs (sub_pos.mpr hξ.1)
      linarith
    rw [hmin] at hP
    exact (Setting.Pstar_eq_iff hcξ' (S.line₂_pos (hc0.trans hcξ'.le))).mp hP
  have hη0 : 0 < Min.min (ξx - θ.c) (θ.ξ₀ - ξx) := lt_min (by linarith) (by linarith)
  have hm1 := min_le_left (ξx - θ.c) (θ.ξ₀ - ξx)
  have hm2 := min_le_right (ξx - θ.c) (θ.ξ₀ - ξx)
  have hcont₁ : ContinuousWithinAt (fun x => 1 * x / (1 * x + θ.δ) + d * Fint θ w x)
      (Iio ξx) ξx :=
    (((continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const)
      (by show (1 : ℝ) * ξx + θ.δ ≠ 0; positivity)).continuousWithinAt).add
      ((S.continuousWithinAt_Fint_left hcx hxξ.le).const_mul d)
  have hcont₂ : ContinuousWithinAt (fun y => θ.h * y / (θ.h * y + θ.e) + d * Fint θ w y)
      (Ioi ξx) ξx :=
    (((continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const)
      (by show θ.h * ξx + θ.e ≠ 0; positivity)).continuousWithinAt).add
      ((S.continuousWithinAt_Fint_right hcx.le hxξ).const_mul d)
  have hle := le_of_good (g₁ := fun x => 1 * x / (1 * x + θ.δ) + d * Fint θ w x)
    (g₂ := fun y => θ.h * y / (θ.h * y + θ.e) + d * Fint θ w y) hη0 (Good w)
    (fun a' b' h1 h2 h3 => exists_good S.adm w S.c_lt h2 fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    hcont₁ hcont₂ (fun x hx y hy hgx hgy => by
      have hxI : x ∈ Ioo θ.c ξx := ⟨by linarith [hx.1], hx.2⟩
      have hyI : y ∈ Ioo ξx θ.ξ₀ := ⟨hy.1, by linarith [hy.2]⟩
      have hx0' : 0 < x := lt_of_le_of_lt hc0 hxI.1
      have hy0' : 0 < y := hx0.trans hyI.1
      have hωx := omega_of_log_affine hgx hx0' (by positivity) (hz₁ x hxI)
      have hωy := omega_of_log_affine hgy hy0' (by positivity) (hz₂ y hyI)
      have hD := S.D_all hxI.1 (hxI.2.trans hyI.1) hyI.2 hgx hgy
      simp only
      linarith)
  simp only at hle
  have hden : 0 < 1 * ξx + θ.δ := by positivity
  rw [show θ.h * ξx + θ.e = 1 * ξx + θ.δ by linarith] at hle
  have h' : 1 * ξx / (1 * ξx + θ.δ) ≤ θ.h * ξx / (1 * ξx + θ.δ) := by linarith
  rw [div_le_div_iff_of_pos_right hden] at h'
  nlinarith

/-- With no free point the curve is one of the two entirely affine curves. -/
theorem entirelyAffine_of_contact (hPU : ∀ ξ ∈ Icc θ.c θ.ξ₀, Pstar θ w ξ = θ.U ξ) :
    EntirelyAffine θ (Pstar θ w) := by
  have hdc : θ.line₁ θ.c ≤ θ.line₂ θ.c := by rw [Params.line₁_c]; exact S.line₂_c
  have hdξ : θ.line₂ θ.ξ₀ ≤ θ.line₁ θ.ξ₀ := by rw [S.adm.line₂_ξ₀]; exact S.line₁_ξ₀
  have hpos : 0 < θ.ξ₀ - θ.c := sub_pos.mpr S.c_lt
  by_cases h1 : θ.line₁ θ.ξ₀ ≤ θ.line₂ θ.ξ₀
  · left
    intro ξ hξ
    rw [hPU ξ hξ]; unfold Params.U; apply min_eq_left
    unfold Params.line₁ Params.line₂ at hdc h1 ⊢
    have key : (θ.ξ₀ - θ.c) * ((ξ + θ.δ) - (θ.h * ξ + θ.e)) =
        (θ.ξ₀ - ξ) * ((θ.c + θ.δ) - (θ.h * θ.c + θ.e)) +
          (ξ - θ.c) * ((θ.ξ₀ + θ.δ) - (θ.h * θ.ξ₀ + θ.e)) := by ring
    have h1' := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hξ.2) (sub_nonpos.mpr hdc)
    have h2' := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hξ.1) (sub_nonpos.mpr h1)
    by_contra hcon; push_neg at hcon
    have := mul_pos hpos (sub_pos.mpr hcon)
    linarith
  · by_cases h2 : θ.line₂ θ.c ≤ θ.line₁ θ.c
    · right
      intro ξ hξ
      rw [hPU ξ hξ]; unfold Params.U; apply min_eq_right
      unfold Params.line₁ Params.line₂ at hdξ h2 ⊢
      have key : (θ.ξ₀ - θ.c) * ((θ.h * ξ + θ.e) - (ξ + θ.δ)) =
          (θ.ξ₀ - ξ) * ((θ.h * θ.c + θ.e) - (θ.c + θ.δ)) +
            (ξ - θ.c) * ((θ.h * θ.ξ₀ + θ.e) - (θ.ξ₀ + θ.δ)) := by ring
      have h1' := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hξ.2) (sub_nonpos.mpr h2)
      have h2' := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hξ.1) (sub_nonpos.mpr hdξ)
      by_contra hcon; push_neg at hcon
      have := mul_pos hpos (sub_pos.mpr hcon)
      linarith
    · exact (S.no_corner hPU (not_le.mp h2) (not_le.mp h1)).elim

end Setting

end Relaxed

end FixedPrice.TwoUnit.Family
