import FixedPrice.TwoUnit.Family.ShapeTwoPoint

/-!
# Work package B, part 7: good points and the primitive of `e^{-2z}`

A good point is a Lebesgue point of `ω` at which `z` is differentiable with `z' = ω/ξ`; almost
every point of the curve interval is good, so good points are dense. `F(t) = ∫_c^t e^{-2z}` is
continuous on the closed interval and `C¹` inside it.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable {θ : Params}

theorem omega_div (w : H θ) {s : ℝ} (hs : 0 < s) : omega w s / s = w s / Real.sqrt s := by
  unfold omega
  have h := Real.sqrt_pos.mpr hs
  have h2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  rw [div_eq_div_iff hs.ne' h.ne']
  calc Real.sqrt s * w s * Real.sqrt s = w s * (Real.sqrt s * Real.sqrt s) := by ring
    _ = w s * s := by rw [h2]

/-- `z(b) - z(a) = ∫_a^b ω/s` inside the curve interval. -/
theorem z_sub_eq_integral (w : H θ) {a b : ℝ} (ha0 : 0 < a) (hca : θ.c ≤ a) (hab : a ≤ b)
    (hbξ : b ≤ θ.ξ₀) : zfun θ w b - zfun θ w a = ∫ s in a..b, omega w s / s := by
  rw [zfun_eq_integral θ w (ha0.trans_le hab) (hca.trans hab) hbξ,
    zfun_eq_integral θ w ha0 hca (hab.trans hbξ)]
  have hi1 : IntervalIntegrable (fun s => w s / Real.sqrt s) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (integrableOn_div_sqrt w ha0 hca).mono_set (Ioc_subset_Ioc_right hbξ)
  have hi2 : IntervalIntegrable (fun s => w s / Real.sqrt s) volume b θ.ξ₀ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hbξ]
    exact (integrableOn_div_sqrt w ha0 hca).mono_set (Ioc_subset_Ioc_left hab)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have : ∫ s in a..b, omega w s / s = ∫ s in a..b, w s / Real.sqrt s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hab] at hs
    exact omega_div w (ha0.trans_le hs.1)
  rw [this]; ring

theorem ae_hasDerivAt_zfun (hθ : θ.Admissible) (w : H θ) (hcξ : θ.c < θ.ξ₀) :
    ∀ᵐ x, x ∈ Ioo θ.c θ.ξ₀ → HasDerivAt (zfun θ w) (omega w x / x) x := by
  set a : ℕ → ℝ := fun n => θ.c + (θ.ξ₀ - θ.c) / ((n : ℝ) + 2) with ha
  have hc0 := hθ.c_nonneg
  have hn : ∀ n : ℕ, ∀ᵐ x, x ∈ Ioo (a n) θ.ξ₀ → HasDerivAt (zfun θ w) (omega w x / x) x := by
    intro n
    have hpos : 0 < (θ.ξ₀ - θ.c) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
    have hca : θ.c ≤ a n := by simp only [ha]; linarith
    have ha0 : 0 < a n := by simp only [ha]; linarith
    have haξ : a n ≤ θ.ξ₀ := by
      simp only [ha]
      have : (θ.ξ₀ - θ.c) / ((n : ℝ) + 2) ≤ θ.ξ₀ - θ.c :=
        div_le_self (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      linarith
    have hint : IntervalIntegrable (fun s => w s / Real.sqrt s) volume (a n) θ.ξ₀ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le haξ]
      exact integrableOn_div_sqrt w ha0 hca
    filter_upwards [hint.ae_hasDerivAt_integral] with x hx hxI
    have hxI' : x ∈ uIcc (a n) θ.ξ₀ := by rw [uIcc_of_le haξ]; exact Ioo_subset_Icc_self hxI
    have hder := hx hxI' (a n) (by rw [uIcc_of_le haξ]; exact left_mem_Icc.mpr haξ)
    have hx0 : 0 < x := ha0.trans hxI.1
    have heq : zfun θ w =ᶠ[𝓝 x] fun t => (∫ s in a n..t, w s / Real.sqrt s) + zfun θ w (a n) := by
      filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with t ht
      have := z_sub_eq_integral w ha0 hca ht.1.le ht.2.le
      have e : ∫ s in a n..t, omega w s / s = ∫ s in a n..t, w s / Real.sqrt s := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le ht.1.le] at hs
        exact omega_div w (ha0.trans_le hs.1)
      rw [← e, ← this]; ring
    rw [omega_div w hx0]
    exact (hder.add_const _).congr_of_eventuallyEq heq
  filter_upwards [ae_all_iff.mpr hn] with x hx hxI
  obtain ⟨n, hn⟩ := exists_nat_gt ((θ.ξ₀ - θ.c) / (x - θ.c))
  refine hx n ⟨?_, hxI.2⟩
  have hxc : 0 < x - θ.c := by linarith [hxI.1]
  have h2 : (θ.ξ₀ - θ.c) / ((n : ℝ) + 2) < x - θ.c := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hxc] at hn
    nlinarith
  simp only [ha]; linarith

/-- A good point: a Lebesgue point of `ω` at which `z' = ω/ξ`. -/
def Good (w : H θ) (x : ℝ) : Prop :=
  IsLeb w x ∧ HasDerivAt (zfun θ w) (omega w x / x) x

theorem ae_good (hθ : θ.Admissible) (w : H θ) (hcξ : θ.c < θ.ξ₀) :
    ∀ᵐ x, x ∈ Ioo θ.c θ.ξ₀ → Good w x := by
  filter_upwards [ae_isLeb w hcξ.le, ae_hasDerivAt_zfun hθ w hcξ] with x h1 h2 hx
  exact ⟨h1 hx, h2 hx⟩

theorem exists_good (hθ : θ.Admissible) (w : H θ) (hcξ : θ.c < θ.ξ₀) {a b : ℝ} (hab : a < b)
    (hsub : Ioo a b ⊆ Ioo θ.c θ.ξ₀) : ∃ x ∈ Ioo a b, Good w x := by
  by_contra h
  push_neg at h
  have hnull : volume (Ioo a b) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_good hθ w hcξ] with x hx hxab
    exact h x hxab (hx (hsub hxab))
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hnull
  linarith

/-- An integral of a function positive almost everywhere on the interval is positive. -/
theorem integral_pos_of_ae_pos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hpos : ∀ᵐ x, x ∈ Ioo a b → 0 < f x) :
    0 < ∫ x in a..b, f x := by
  have h₀ : 0 ≤ᵐ[volume.restrict (Ι a b)] f := by
    rw [EventuallyLE, uIoc_of_le hab.le]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hpos] with x hx hxab using (hx hxab).le
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' h₀ hf]
  refine ⟨hab, ?_⟩
  have h1 : volume (Ioo a b) ≤ volume (support f ∩ Ioc a b) := by
    refine measure_mono_ae ?_
    filter_upwards [hpos] with x hx
    intro hxab
    exact ⟨(hx hxab).ne', Ioo_subset_Ioc_self hxab⟩
  refine lt_of_lt_of_le ?_ h1
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-- On a stretch where `z = log(αξ + γ)`, a good point has `ω = αξ/(αξ + γ)`. -/
theorem omega_of_log_affine {w : H θ} {x α γ : ℝ} (hx : Good w x) (hx0 : 0 < x)
    (hL : 0 < α * x + γ) (heq : zfun θ w =ᶠ[𝓝 x] fun ξ => Real.log (α * ξ + γ)) :
    omega w x = α * x / (α * x + γ) := by
  have hlog : HasDerivAt (fun ξ => Real.log (α * ξ + γ)) (α * 1 / (α * x + γ)) x :=
    (((hasDerivAt_id x).const_mul α).add_const γ).log hL.ne'
  have h := hx.2.unique (hlog.congr_of_eventuallyEq heq)
  rw [mul_one] at h
  have hx' : x ≠ 0 := hx0.ne'
  calc omega w x = x * (omega w x / x) := by field_simp
    _ = x * (α / (α * x + γ)) := by rw [h]
    _ = α * x / (α * x + γ) := by ring

/-- Continuity from the two sides of a point and an inequality between good points on the two
sides give the inequality at the point. -/
theorem le_of_good {g₁ g₂ : ℝ → ℝ} {ξ η : ℝ} (hη : 0 < η) (G : ℝ → Prop)
    (hG : ∀ a b, ξ - η ≤ a → a < b → b ≤ ξ + η → ∃ x ∈ Ioo a b, G x)
    (h₁ : ContinuousWithinAt g₁ (Iio ξ) ξ) (h₂ : ContinuousWithinAt g₂ (Ioi ξ) ξ)
    (h : ∀ x ∈ Ioo (ξ - η) ξ, ∀ y ∈ Ioo ξ (ξ + η), G x → G y → g₁ x ≤ g₂ y) :
    g₁ ξ ≤ g₂ ξ := by
  by_contra hlt
  push_neg at hlt
  set ε := (g₁ ξ - g₂ ξ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have e1 : ∀ᶠ x in 𝓝[<] ξ, g₁ ξ - ε < g₁ x :=
    h₁.eventually (lt_mem_nhds (by linarith))
  have e2 : ∀ᶠ y in 𝓝[>] ξ, g₂ y < g₂ ξ + ε :=
    h₂.eventually (gt_mem_nhds (by linarith))
  obtain ⟨l, hl, hls⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp e1
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp e2
  obtain ⟨x, hx, hGx⟩ := hG (max l (ξ - η)) ξ (le_max_right _ _)
    (max_lt hl (by linarith)) (by linarith)
  obtain ⟨y, hy, hGy⟩ := hG ξ (min u (ξ + η)) (by linarith) (lt_min hu (by linarith))
    (min_le_right _ _)
  have hx1 : g₁ ξ - ε < g₁ x := hls ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
  have hy1 : g₂ y < g₂ ξ + ε := hus ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
  have hxy := h x ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, hx.2⟩ y
    ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩ hGx hGy
  rw [hε] at hx1 hy1
  linarith

/-! ### The primitive of `e^{-2z}` -/

/-- `F(t) = ∫_c^t e^{-2z}`. -/
def Fint (θ : Params) (w : H θ) (t : ℝ) : ℝ := ∫ s in θ.c..t, Real.exp (-2 * zfun θ w s)

theorem integrableOn_exp (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) :
    IntegrableOn (fun s => Real.exp (-2 * zfun θ w s)) (Ioc θ.c θ.ξ₀) volume :=
  integrable_exp hθ hw

theorem intervalIntegrable_exp (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) {a b : ℝ}
    (hca : θ.c ≤ a) (hab : a ≤ b) (hbξ : b ≤ θ.ξ₀) :
    IntervalIntegrable (fun s => Real.exp (-2 * zfun θ w s)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_exp hθ hw).mono_set (Ioc_subset_Ioc hca hbξ)

theorem Fint_sub (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) {a b : ℝ} (hca : θ.c ≤ a)
    (hab : a ≤ b) (hbξ : b ≤ θ.ξ₀) :
    ∫ s in a..b, Real.exp (-2 * zfun θ w s) = Fint θ w b - Fint θ w a := by
  unfold Fint
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_exp hθ hw le_rfl hca (hab.trans hbξ))
    (intervalIntegrable_exp hθ hw hca hab hbξ)]
  ring

theorem continuousOn_Fint (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) :
    ContinuousOn (Fint θ w) (Icc θ.c θ.ξ₀) := by
  have hcξ := hθ.c_le_ξ₀
  have h : IntegrableOn (fun s => Real.exp (-2 * zfun θ w s)) (uIcc θ.c θ.ξ₀) volume := by
    rw [uIcc_of_le hcξ, integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_exp hθ hw
  have := intervalIntegral.continuousOn_primitive_interval h
  rwa [uIcc_of_le hcξ] at this

theorem continuousOn_exp_z (hθ : θ.Admissible) (w : H θ) :
    ContinuousOn (fun s => Real.exp (-2 * zfun θ w s)) (Ioc θ.c θ.ξ₀) :=
  Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (continuousOn_zfun hθ w))

theorem hasDerivAt_Fint (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) {t : ℝ}
    (ht : t ∈ Ioo θ.c θ.ξ₀) : HasDerivAt (Fint θ w) (Real.exp (-2 * zfun θ w t)) t := by
  have hcont : ContinuousOn (fun s => Real.exp (-2 * zfun θ w s)) (Ioo θ.c θ.ξ₀) :=
    (continuousOn_exp_z hθ w).mono Ioo_subset_Ioc_self
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_exp hθ hw le_rfl ht.1.le ht.2.le)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hcont.continuousAt (Ioo_mem_nhds ht.1 ht.2))

theorem Fint_sub_le (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) {a b : ℝ} (hca : θ.c ≤ a)
    (hab : a ≤ b) (hbξ : b ≤ θ.ξ₀) : Fint θ w b - Fint θ w a ≤ (θ.p ^ 2)⁻¹ * (b - a) := by
  rw [← Fint_sub hθ hw hca hab hbξ]
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (intervalIntegrable_exp hθ hw hca hab hbξ) (intervalIntegrable_const (c := (θ.p ^ 2)⁻¹))
    (fun s hs => exp_le hθ hw ⟨lt_of_le_of_lt hca hs.1, hs.2.le.trans hbξ⟩)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

theorem Fint_sub_pos (hθ : θ.Admissible) {w : H θ} (hw : w ∈ W θ) {a b : ℝ} (hca : θ.c ≤ a)
    (hab : a < b) (hbξ : b ≤ θ.ξ₀) : 0 < Fint θ w b - Fint θ w a := by
  rw [← Fint_sub hθ hw hca hab.le hbξ]
  exact intervalIntegral.intervalIntegral_pos_of_pos (intervalIntegrable_exp hθ hw hca hab.le hbξ)
    (fun _ => Real.exp_pos _) hab

end Relaxed

end FixedPrice.TwoUnit.Family
