import FixedPrice.TwoUnit.Family.ShapeGood

/-!
# Work package B, part 8: the lower obstacle is inactive

In the non-degenerate case (`c_f < ξ₀`, so `p_f < 1` and `U_f > p_f` on `(c_f, ξ₀]`), the relaxed
minimizer stays strictly above `log p_f` inside the curve interval. At an interior touching point
the upper obstacle is slack nearby; pushing up gives `ω(x) - ω(y) ≥ F(y) - F(x) > 0` for good
`x < y` around it, while touching from above forces a good `x` on the left with `ω(x) ≤ 0` and a
good `y` on the right with `ω(y) ≥ 0`. Consequently pushing down is admissible on every
`[x, ξ₀]`, `x > c_f`, and `ω + dF` is nondecreasing along good points.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

theorem continuous_U : Continuous θ.U := by
  unfold Params.U Params.line₁ Params.line₂
  exact (continuous_id.add continuous_const).min
    ((continuous_const.mul continuous_id).add continuous_const)

theorem zfun_ξ₀ (hθ : θ.Admissible) (w : H θ) : zfun θ w θ.ξ₀ = 0 := by
  rw [zfun_eq_integral θ w hθ.ξ₀_pos hθ.c_le_ξ₀ le_rfl, intervalIntegral.integral_same, neg_zero]

theorem exists_pos_gap {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ ξ ∈ Icc a b, 0 < f ξ) : ∃ κ > 0, ∀ ξ ∈ Icc a b, κ ≤ f ξ := by
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf
  exact ⟨f m, hpos m hm, fun ξ hξ => hmin hξ⟩

theorem intervalIntegrable_omega_div (w : H θ) {a b : ℝ} (ha0 : 0 < a) (hca : θ.c ≤ a)
    (hab : a ≤ b) (hbξ : b ≤ θ.ξ₀) : IntervalIntegrable (fun s => omega w s / s) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact ((integrableOn_div_sqrt w ha0 hca).mono_set (Ioc_subset_Ioc_right hbξ)).congr_fun
    (fun s hs => (omega_div w (ha0.trans hs.1)).symm) measurableSet_Ioc

/-- The standing assumptions of the non-degenerate case. -/
structure Setting (θ : Params) (d : ℝ) (w : H θ) : Prop where
  adm : θ.Admissible
  d_pos : 0 < d
  mem : w ∈ W θ
  min : ∀ v ∈ W θ, J θ d w ≤ J θ d v
  c_lt : θ.c < θ.ξ₀
  line₂_c : θ.p ≤ θ.line₂ θ.c
  line₁_ξ₀ : 1 ≤ θ.line₁ θ.ξ₀

namespace Setting

variable {d : ℝ} {w : H θ} (S : Setting θ d w)
include S

theorem line₂_lt_one {ξ : ℝ} (hξ : ξ < θ.ξ₀) : θ.line₂ ξ < 1 := by
  rw [← S.adm.line₂_ξ₀]; unfold Params.line₂; have := S.adm.h_pos; nlinarith

theorem p_lt_one : θ.p < 1 := S.line₂_c.trans_lt (S.line₂_lt_one S.c_lt)

theorem U_c : θ.U θ.c = θ.p := by
  unfold Params.U; rw [Params.line₁_c]; exact min_eq_left S.line₂_c

theorem p_lt_U {ξ : ℝ} (hξ : θ.c < ξ) : θ.p < θ.U ξ := by
  unfold Params.U
  refine lt_min ?_ ?_
  · rw [← Params.line₁_c]; unfold Params.line₁; linarith
  · refine S.line₂_c.trans_lt ?_; unfold Params.line₂; have := S.adm.h_pos; nlinarith

theorem p_le_U {ξ : ℝ} (hξ : θ.c ≤ ξ) : θ.p ≤ θ.U ξ := by
  rcases eq_or_lt_of_le hξ with h | h
  · rw [← h, S.U_c]
  · exact (S.p_lt_U h).le

theorem U_pos {ξ : ℝ} (hξ : θ.c ≤ ξ) : 0 < θ.U ξ := S.adm.p_pos.trans_le (S.p_le_U hξ)

theorem U_le_one {ξ : ℝ} (hξ : ξ ≤ θ.ξ₀) : θ.U ξ ≤ 1 :=
  (min_le_right _ _).trans (S.adm.line₂_le_one hξ)

theorem z_ge {ξ : ℝ} (hξ : ξ ∈ Ioc θ.c θ.ξ₀) : Real.log θ.p ≤ zfun θ w ξ :=
  (S.mem ξ ⟨hξ.1.le, hξ.2⟩ (lt_of_le_of_lt S.adm.c_nonneg hξ.1)).1

theorem z_le {ξ : ℝ} (hξ : ξ ∈ Ioc θ.c θ.ξ₀) : zfun θ w ξ ≤ Real.log (θ.U ξ) :=
  (S.mem ξ ⟨hξ.1.le, hξ.2⟩ (lt_of_le_of_lt S.adm.c_nonneg hξ.1)).2

theorem z_nonpos {ξ : ℝ} (hξ : ξ ∈ Ioc θ.c θ.ξ₀) : zfun θ w ξ ≤ 0 :=
  (S.z_le hξ).trans (Real.log_nonpos (S.U_pos hξ.1.le).le (S.U_le_one hξ.2))

theorem continuousAt_z {ξ : ℝ} (hξ : ξ ∈ Ioo θ.c θ.ξ₀) : ContinuousAt (zfun θ w) ξ :=
  (continuousOn_zfun S.adm w).continuousAt (Ioc_mem_nhds hξ.1 hξ.2)

theorem continuousOn_z {a b : ℝ} (hca : θ.c < a) (hbξ : b ≤ θ.ξ₀) :
    ContinuousOn (zfun θ w) (Icc a b) :=
  (continuousOn_zfun S.adm w).mono fun ξ hξ => ⟨hca.trans_le hξ.1, hξ.2.trans hbξ⟩

theorem continuousOn_logU {a b : ℝ} (hca : θ.c ≤ a) :
    ContinuousOn (fun ξ => Real.log (θ.U ξ)) (Icc a b) :=
  continuous_U.continuousOn.log fun ξ hξ => (S.U_pos (hca.trans hξ.1)).ne'

/-- The squeeze at the left end: `z(ξ) → log p_f` as `ξ ↓ c_f`. -/
theorem tendsto_z_c : Tendsto (zfun θ w) (𝓝[>] θ.c) (𝓝 (Real.log θ.p)) := by
  have hU : Tendsto (fun ξ => Real.log (θ.U ξ)) (𝓝[>] θ.c) (𝓝 (Real.log θ.p)) := by
    have := ((continuous_U (θ := θ)).tendsto θ.c).log (by rw [S.U_c]; exact S.adm.p_pos.ne')
    rw [S.U_c] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT S.c_lt] with ξ hξ
    exact S.z_ge ⟨hξ.1, hξ.2.le⟩
  · filter_upwards [Ioo_mem_nhdsGT S.c_lt] with ξ hξ
    exact S.z_le ⟨hξ.1, hξ.2.le⟩

theorem exists_good_nonpos {a b : ℝ} (hab : a < b) (hca : θ.c < a) (hbξ : b < θ.ξ₀)
    (hint : zfun θ w b ≤ zfun θ w a) : ∃ x ∈ Ioo a b, Good w x ∧ omega w x ≤ 0 := by
  by_contra h
  push_neg at h
  have ha0 : 0 < a := lt_of_le_of_lt S.adm.c_nonneg hca
  have hpos : 0 < ∫ s in a..b, omega w s / s := by
    refine integral_pos_of_ae_pos hab
      (intervalIntegrable_omega_div w ha0 hca.le hab.le hbξ.le) ?_
    filter_upwards [ae_good S.adm w S.c_lt] with x hx hxab
    have hxg := hx ⟨hca.trans hxab.1, hxab.2.trans hbξ⟩
    exact div_pos (h x hxab hxg) (ha0.trans hxab.1)
  have := z_sub_eq_integral w ha0 hca.le hab.le hbξ.le
  linarith

theorem exists_good_nonneg {a b : ℝ} (hab : a < b) (hca : θ.c < a) (hbξ : b < θ.ξ₀)
    (hint : zfun θ w a ≤ zfun θ w b) : ∃ x ∈ Ioo a b, Good w x ∧ 0 ≤ omega w x := by
  by_contra h
  push_neg at h
  have ha0 : 0 < a := lt_of_le_of_lt S.adm.c_nonneg hca
  have hpos : 0 < ∫ s in a..b, -(omega w s / s) := by
    refine integral_pos_of_ae_pos hab
      (intervalIntegrable_omega_div w ha0 hca.le hab.le hbξ.le).neg ?_
    filter_upwards [ae_good S.adm w S.c_lt] with x hx hxab
    have hxg := hx ⟨hca.trans hxab.1, hxab.2.trans hbξ⟩
    exact neg_pos.mpr (div_neg_of_neg_of_pos (h x hxab hxg) (ha0.trans hxab.1))
  rw [intervalIntegral.integral_neg] at hpos
  have := z_sub_eq_integral w ha0 hca.le hab.le hbξ.le
  linarith

/-- Pushing up on a stretch where the upper obstacle is slack. -/
theorem U_local {x y y' : ℝ} (hcx : θ.c < x) (hxy : x < y) (hyy' : y < y') (hy'ξ : y' ≤ θ.ξ₀)
    (hfree : ∀ ξ ∈ Icc x y', zfun θ w ξ < Real.log (θ.U ξ)) (hx : Good w x) (hy : Good w y) :
    d * (Fint θ w y - Fint θ w x) ≤ omega w x - omega w y := by
  have hcont : ContinuousOn (fun ξ => Real.log (θ.U ξ) - zfun θ w ξ) (Icc x y') :=
    (S.continuousOn_logU hcx.le).sub (S.continuousOn_z hcx hy'ξ)
  obtain ⟨κ, hκ, h⟩ := exists_pos_gap (hxy.trans hyy').le hcont
    (fun ξ hξ => sub_pos.mpr (hfree ξ hξ))
  have := two_point_up d S.adm S.d_pos.le S.mem S.min hcx hxy hyy' hy'ξ hκ
    (fun ξ hξ => by linarith [h ξ hξ]) hx.1 hy.1
  rwa [Fint_sub S.adm S.mem hcx.le hxy.le (hyy'.le.trans hy'ξ)] at this

/-- The lower obstacle is inactive inside the curve interval. -/
theorem lower_inactive : ∀ ξ ∈ Ioo θ.c θ.ξ₀, Real.log θ.p < zfun θ w ξ := by
  intro ξ₁ hξ₁
  by_contra hle
  push_neg at hle
  have hz1 : zfun θ w ξ₁ = Real.log θ.p := le_antisymm hle (S.z_ge ⟨hξ₁.1, hξ₁.2.le⟩)
  set g := Real.log (θ.U ξ₁) - Real.log θ.p with hg
  have hg0 : 0 < g := sub_pos.mpr (Real.log_lt_log S.adm.p_pos (S.p_lt_U hξ₁.1))
  have hzc : ContinuousAt (zfun θ w) ξ₁ := S.continuousAt_z hξ₁
  have hUc : ContinuousAt (fun ξ => Real.log (θ.U ξ)) ξ₁ :=
    (continuous_U (θ := θ)).continuousAt.log (S.U_pos hξ₁.1.le).ne'
  have e1 : ∀ᶠ ξ in 𝓝 ξ₁, zfun θ w ξ < Real.log θ.p + g / 3 :=
    hzc.eventually (gt_mem_nhds (by rw [hz1]; linarith))
  have e2 : ∀ᶠ ξ in 𝓝 ξ₁, Real.log (θ.U ξ₁) - g / 3 < Real.log (θ.U ξ) :=
    hUc.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and e2)
  set η := Min.min (ε / 3) (Min.min ((ξ₁ - θ.c) / 3) ((θ.ξ₀ - ξ₁) / 3)) with hη
  have hη0 : 0 < η := lt_min (by linarith) (lt_min (by linarith [hξ₁.1]) (by linarith [hξ₁.2]))
  have hη1 : η ≤ ε / 3 := min_le_left _ _
  have hη2 : η ≤ (ξ₁ - θ.c) / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ (θ.ξ₀ - ξ₁) / 3 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨x, hx, hxg, hxω⟩ := S.exists_good_nonpos (a := ξ₁ - η) (b := ξ₁) (by linarith)
    (by linarith) hξ₁.2 (by rw [hz1]; exact S.z_ge ⟨by linarith, by linarith [hξ₁.2]⟩)
  obtain ⟨y, hy, hyg, hyω⟩ := S.exists_good_nonneg (a := ξ₁) (b := ξ₁ + η) (by linarith)
    hξ₁.1 (by linarith) (by rw [hz1]; exact S.z_ge ⟨by linarith [hξ₁.1], by linarith⟩)
  have hfree : ∀ ξ ∈ Icc x (ξ₁ + 2 * η), zfun θ w ξ < Real.log (θ.U ξ) := by
    intro ξ hξ
    have hd : dist ξ ξ₁ < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hξ.1, hξ.2]
    obtain ⟨h1, h2⟩ := hball hd
    linarith
  have hU := S.U_local (x := x) (y := y) (y' := ξ₁ + 2 * η) (by linarith [hx.1])
    (hx.2.trans hy.1) (by linarith [hy.2]) (by linarith) hfree hxg hyg
  have hF := Fint_sub_pos S.adm S.mem (by linarith [hx.1]) (hx.2.trans hy.1)
    (by linarith [hy.2])
  have := mul_pos S.d_pos hF
  linarith

/-- Uniform lower slack on `[x, ξ₀]` for `x > c_f`. -/
theorem lower_slack {x : ℝ} (hcx : θ.c < x) (hxξ : x ≤ θ.ξ₀) :
    ∃ κ > 0, ∀ ξ ∈ Icc x θ.ξ₀, Real.log θ.p + κ ≤ zfun θ w ξ := by
  have hcont : ContinuousOn (fun ξ => zfun θ w ξ - Real.log θ.p) (Icc x θ.ξ₀) :=
    (S.continuousOn_z hcx le_rfl).sub continuousOn_const
  obtain ⟨κ, hκ, h⟩ := exists_pos_gap hxξ hcont (fun ξ hξ => by
    rcases eq_or_lt_of_le hξ.2 with h' | h'
    · rw [h', zfun_ξ₀ S.adm w]
      have := Real.log_neg S.adm.p_pos S.p_lt_one
      linarith
    · have := S.lower_inactive ξ ⟨hcx.trans_le hξ.1, h'⟩
      linarith)
  exact ⟨κ, hκ, fun ξ hξ => by linarith [h ξ hξ]⟩

/-- Pushing down is admissible everywhere: `ω + dF` is nondecreasing along good points. -/
theorem D_all {x y : ℝ} (hcx : θ.c < x) (hxy : x < y) (hyξ : y < θ.ξ₀) (hx : Good w x)
    (hy : Good w y) : omega w x - omega w y ≤ d * (Fint θ w y - Fint θ w x) := by
  obtain ⟨κ, hκ, hslack⟩ := S.lower_slack hcx (hxy.trans hyξ).le
  have := two_point_down d S.adm S.d_pos.le S.mem S.min hcx hxy hyξ le_rfl hκ hslack hx.1 hy.1
  rwa [Fint_sub S.adm S.mem hcx.le hxy.le hyξ.le] at this

end Setting

end Relaxed

end FixedPrice.TwoUnit.Family
