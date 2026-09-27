import FixedPrice.TwoUnit.Family.StationaryAlg

/-!
# Work package D: the free arc of a three-arc curve (helper for `Stationary.lean`)

Generic real analysis on the free arc `[a, b]` of a concave curve that is `C²` inside with the
Euler equation `P'' + (C/ξ²)P = 0` and the first integral `d = ξP'² - PP' + CP²/ξ`
(`FreeArc`):

* the one-sided limits of `P'` at the contacts equal the contact slopes (concavity:
  `ConcaveOn.antitoneOn_deriv`, `hasDerivWithinAt_Ici_of_tendsto_deriv` and uniqueness of
  one-sided derivatives), so the first integral holds at the contacts;
* `ω = ξP'/P` has `ω' = -d/P²` (`FamilyIdentities.omega_derivative`), which gives
  `∫_a^b P⁻² = (ω(a) - ω(b))/d` and, with `FamilyIdentities.gradient_integrand`, the free-arc part
  of `Q_f`;
* the substitution `u = ω(ξ)` gives `log(b/a) = ∫_{ω(b)}^{ω(a)} du/𝒟(u)` (the connection equation
  of paper gap G9), `ω(b) < ω(a)` and `𝒟 > 0` on `[ω(b), ω(a)]`.

Then the contact integrals and `(eq:2fam-quadratures)` for a three-arc class curve with positive
contacts (`quadratures`).
-/

noncomputable section
open Real Set Filter Topology MeasureTheory

namespace FixedPrice.TwoUnit.Family

namespace PkgD

/-- The derivative of a concave function that is differentiable at the left end `a` of `[a, b]`
and on `(a, b)` tends to `f'(a)` from the right. -/
lemma tendsto_deriv_right_of_concave {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hconc : ConcaveOn ℝ (Icc a b) f) (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hfa : HasDerivAt f L a) : Tendsto (deriv f) (𝓝[>] a) (𝓝 L) := by
  have hdiffIco : ∀ x ∈ Ico a b, DifferentiableAt ℝ f x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hfa.differentiableAt
    · exact hdiff x ⟨h, hx.2⟩
  have hanti : AntitoneOn (deriv f) (Ico a b) :=
    (hconc.subset Ico_subset_Icc_self (convex_Ico a b)).antitoneOn_deriv hdiffIco
  have hne : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
  have hbdd : BddAbove (deriv f '' Ioo a b) := by
    refine ⟨deriv f a, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hanti ⟨le_rfl, hab⟩ (Ioo_subset_Ico_self hx) hx.1.le
  have hlim := (hanti.mono Ioo_subset_Ico_self).tendsto_nhdsWithin_Ioo_right hne hbdd
  have hdiffOn : DifferentiableOn ℝ f (Ioo a b) :=
    fun x hx => (hdiff x hx).differentiableWithinAt
  have hM := hasDerivWithinAt_Ici_of_tendsto_deriv hdiffOn
    hfa.continuousAt.continuousWithinAt (Ioo_mem_nhdsGT hab) hlim
  have hL : HasDerivWithinAt f L (Ici a) a := hfa.hasDerivWithinAt
  have heq := (uniqueDiffWithinAt_Ici a).eq_deriv _ hM hL
  rwa [heq] at hlim

/-- The derivative of a concave function that is differentiable at the right end `b` of `[a, b]`
and on `(a, b)` tends to `f'(b)` from the left. -/
lemma tendsto_deriv_left_of_concave {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hconc : ConcaveOn ℝ (Icc a b) f) (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hfb : HasDerivAt f L b) : Tendsto (deriv f) (𝓝[<] b) (𝓝 L) := by
  have hdiffIoc : ∀ x ∈ Ioc a b, DifferentiableAt ℝ f x := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h]; exact hfb.differentiableAt
    · exact hdiff x ⟨hx.1, h⟩
  have hanti : AntitoneOn (deriv f) (Ioc a b) :=
    (hconc.subset Ioc_subset_Icc_self (convex_Ioc a b)).antitoneOn_deriv hdiffIoc
  have hne : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
  have hbdd : BddBelow (deriv f '' Ioo a b) := by
    refine ⟨deriv f b, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hanti (Ioo_subset_Ioc_self hx) ⟨hab, le_rfl⟩ hx.2.le
  have hlim := (hanti.mono Ioo_subset_Ioc_self).tendsto_nhdsWithin_Ioo_left hne hbdd
  have hdiffOn : DifferentiableOn ℝ f (Ioo a b) :=
    fun x hx => (hdiff x hx).differentiableWithinAt
  have hM := hasDerivWithinAt_Iic_of_tendsto_deriv hdiffOn
    hfb.continuousAt.continuousWithinAt (Ioo_mem_nhdsLT hab) hlim
  have hL : HasDerivWithinAt f L (Iic b) b := hfb.hasDerivWithinAt
  have heq := (uniqueDiffWithinAt_Iic b).eq_deriv _ hM hL
  rwa [heq] at hlim

/-- Interval integrals agree when the integrands agree on the open interval. -/
lemma intervalIntegral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- Patching a function continuous on `(a, b)` by its one-sided limits gives a function
continuous on `[a, b]`. -/
lemma continuousOn_update_Icc {f : ℝ → ℝ} {a b fa fb : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 fa))
    (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) :
    ContinuousOn (Function.update (Function.update f a fa) b fb) (Icc a b) := by
  rw [continuousOn_update_iff, continuousOn_update_iff, Icc_diff_right, Ico_diff_left]
  refine ⟨⟨hf, ?_⟩, ?_⟩
  · exact fun _ => ha.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
  · rintro -
    refine (hb.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
    filter_upwards [Ioo_mem_nhdsLT hab] with _ hz using
      (Function.update_of_ne hz.1.ne' _ _).symm

/-- The hypotheses on the free arc `[a, b]` of a three-arc curve: `P` is positive, continuous and
concave on `[a, b]`, `C²` on `(a, b)` with the Euler equation and the first integral, and
differentiable at the two contacts with slopes `La`, `Lb`. -/
structure FreeArc (d C : ℝ) (P : ℝ → ℝ) (a b La Lb : ℝ) : Prop where
  a_pos : 0 < a
  a_lt_b : a < b
  cont : ContinuousOn P (Icc a b)
  pos : ∀ x ∈ Icc a b, 0 < P x
  concave : ConcaveOn ℝ (Icc a b) P
  smooth : ContDiffOn ℝ 2 P (Ioo a b)
  euler : ∀ x ∈ Ioo a b, deriv (deriv P) x + C / x ^ 2 * P x = 0
  first_integral : ∀ x ∈ Ioo a b, d = x * deriv P x ^ 2 - P x * deriv P x + C * P x ^ 2 / x
  deriv_a : HasDerivAt P La a
  deriv_b : HasDerivAt P Lb b

namespace FreeArc

variable {d C : ℝ} {P : ℝ → ℝ} {a b La Lb : ℝ}

lemma differentiableAt (hA : FreeArc d C P a b La Lb) {x : ℝ} (hx : x ∈ Ioo a b) :
    DifferentiableAt ℝ P x :=
  ((hA.smooth.differentiableOn (by norm_num)) x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)

lemma hasDerivAt_deriv (hA : FreeArc d C P a b La Lb) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (deriv P) (deriv (deriv P) x) x := by
  have h2 : ContDiffOn ℝ (1 + 1) P (Ioo a b) := by simpa using hA.smooth
  obtain ⟨-, -, h1⟩ := (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).1 h2
  exact ((h1.differentiableOn (by norm_num)) x hx).differentiableAt
    (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt

lemma pos_Ioo (hA : FreeArc d C P a b La Lb) {x : ℝ} (hx : x ∈ Ioo a b) : 0 < P x :=
  hA.pos x (Ioo_subset_Icc_self hx)

lemma x_pos (hA : FreeArc d C P a b La Lb) {x : ℝ} (hx : x ∈ Icc a b) : 0 < x :=
  hA.a_pos.trans_le hx.1

lemma tendsto_deriv_a (hA : FreeArc d C P a b La Lb) : Tendsto (deriv P) (𝓝[>] a) (𝓝 La) :=
  tendsto_deriv_right_of_concave hA.a_lt_b hA.concave (fun _ hx => hA.differentiableAt hx)
    hA.deriv_a

lemma tendsto_deriv_b (hA : FreeArc d C P a b La Lb) : Tendsto (deriv P) (𝓝[<] b) (𝓝 Lb) :=
  tendsto_deriv_left_of_concave hA.a_lt_b hA.concave (fun _ hx => hA.differentiableAt hx)
    hA.deriv_b

lemma tendsto_P_a (hA : FreeArc d C P a b La Lb) : Tendsto P (𝓝[>] a) (𝓝 (P a)) :=
  hA.deriv_a.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

lemma tendsto_P_b (hA : FreeArc d C P a b La Lb) : Tendsto P (𝓝[<] b) (𝓝 (P b)) :=
  hA.deriv_b.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- `ω = ξ P'/P` has `ω' = -d/P²` on the free arc (`omega_derivative` and the first integral). -/
lemma hasDerivAt_ω (hA : FreeArc d C P a b La Lb)
    (homega : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
        = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun x => x * deriv P x / P x) (-(d / P x ^ 2)) x := by
  have hx0 : x ≠ 0 := (hA.a_pos.trans hx.1).ne'
  have hPx : P x ≠ 0 := (hA.pos_Ioo hx).ne'
  have h1 := ((hasDerivAt_id x).mul (hA.hasDerivAt_deriv hx)).div
    (hA.differentiableAt hx).hasDerivAt hPx
  convert h1 using 1
  have heul : deriv (deriv P) x = -C * P x / x ^ 2 := by
    have := hA.euler x hx
    rw [show -C * P x / x ^ 2 = -(C / x ^ 2 * P x) by ring]
    linarith
  simp only [Pi.mul_apply, id]
  rw [heul, hA.first_integral x hx, ← homega x (P x) (deriv P x) C hx0 hPx]
  field_simp

lemma continuousOn_ω (hA : FreeArc d C P a b La Lb)
    (homega : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
        = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)) :
    ContinuousOn (fun x => x * deriv P x / P x) (Ioo a b) :=
  fun _ hx => (hA.hasDerivAt_ω homega hx).continuousAt.continuousWithinAt

lemma tendsto_ω_a (hA : FreeArc d C P a b La Lb) :
    Tendsto (fun x => x * deriv P x / P x) (𝓝[>] a) (𝓝 (a * La / P a)) := by
  have hPa : P a ≠ 0 := (hA.pos a ⟨le_rfl, hA.a_lt_b.le⟩).ne'
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] a) (𝓝 a) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto a)
  exact (hid.mul hA.tendsto_deriv_a).div hA.tendsto_P_a hPa

lemma tendsto_ω_b (hA : FreeArc d C P a b La Lb) :
    Tendsto (fun x => x * deriv P x / P x) (𝓝[<] b) (𝓝 (b * Lb / P b)) := by
  have hPb : P b ≠ 0 := (hA.pos b ⟨hA.a_lt_b.le, le_rfl⟩).ne'
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] b) (𝓝 b) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto b)
  exact (hid.mul hA.tendsto_deriv_b).div hA.tendsto_P_b hPb

/-- The first integral at the left contact. -/
lemma first_integral_a (hA : FreeArc d C P a b La Lb) :
    d = a * La ^ 2 - P a * La + C * P a ^ 2 / a := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] a) (𝓝 a) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto a)
  have hlim : Tendsto (fun x => x * deriv P x ^ 2 - P x * deriv P x + C * P x ^ 2 / x) (𝓝[>] a)
      (𝓝 (a * La ^ 2 - P a * La + C * P a ^ 2 / a)) :=
    ((hid.mul (hA.tendsto_deriv_a.pow 2)).sub (hA.tendsto_P_a.mul hA.tendsto_deriv_a)).add
      ((tendsto_const_nhds.mul (hA.tendsto_P_a.pow 2)).div hid hA.a_pos.ne')
  have hconst : Tendsto (fun x => x * deriv P x ^ 2 - P x * deriv P x + C * P x ^ 2 / x) (𝓝[>] a)
      (𝓝 d) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hA.a_lt_b] with x hx using hA.first_integral x hx
  exact tendsto_nhds_unique hconst hlim

/-- The first integral at the right contact. -/
lemma first_integral_b (hA : FreeArc d C P a b La Lb) :
    d = b * Lb ^ 2 - P b * Lb + C * P b ^ 2 / b := by
  have hb0 : 0 < b := hA.a_pos.trans hA.a_lt_b
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] b) (𝓝 b) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto b)
  have hlim : Tendsto (fun x => x * deriv P x ^ 2 - P x * deriv P x + C * P x ^ 2 / x) (𝓝[<] b)
      (𝓝 (b * Lb ^ 2 - P b * Lb + C * P b ^ 2 / b)) :=
    ((hid.mul (hA.tendsto_deriv_b.pow 2)).sub (hA.tendsto_P_b.mul hA.tendsto_deriv_b)).add
      ((tendsto_const_nhds.mul (hA.tendsto_P_b.pow 2)).div hid hb0.ne')
  have hconst : Tendsto (fun x => x * deriv P x ^ 2 - P x * deriv P x + C * P x ^ 2 / x) (𝓝[<] b)
      (𝓝 d) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT hA.a_lt_b] with x hx using hA.first_integral x hx
  exact tendsto_nhds_unique hconst hlim

lemma continuousOn_inv_sq (hA : FreeArc d C P a b La Lb) :
    ContinuousOn (fun x => (P x ^ 2)⁻¹) (Icc a b) :=
  (hA.cont.pow 2).inv₀ fun x hx => (pow_pos (hA.pos x hx) 2).ne'

/-- `∫_a^b P⁻² = (ω(a) - ω(b))/d`. -/
lemma integral_inv_sq (hA : FreeArc d C P a b La Lb) (hd : d ≠ 0)
    (homega : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
        = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)) :
    ∫ x in a..b, (P x ^ 2)⁻¹ = (a * La / P a - b * Lb / P b) / d := by
  have hderiv : ∀ x ∈ Ioo a b,
      HasDerivAt (fun x => -(x * deriv P x / P x) / d) ((P x ^ 2)⁻¹) x := by
    intro x hx
    have := (hA.hasDerivAt_ω homega hx).neg.div_const d
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hA.a_lt_b hderiv
    ((hA.continuousOn_inv_sq).intervalIntegrable_of_Icc hA.a_lt_b.le)
    (hA.tendsto_ω_a.neg.div_const d) (hA.tendsto_ω_b.neg.div_const d)]
  ring

/-- `∫_a^b ξ (P'/P)² = ω(a) - ω(b) + log P(b) - log P(a) - C (log b - log a)`. -/
lemma integral_grad (hA : FreeArc d C P a b La Lb)
    (homega : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
        = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2))
    (hgrad : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      ξ * H ^ 2 / P ^ 2 = (ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2 + H / P - C / ξ)
    (hint : IntervalIntegrable (fun x => x * (deriv P x / P x) ^ 2) volume a b) :
    ∫ x in a..b, x * (deriv P x / P x) ^ 2
      = (a * La / P a - b * Lb / P b) + (Real.log (P b) - Real.log (P a))
        - C * (Real.log b - Real.log a) := by
  have hPa : P a ≠ 0 := (hA.pos a ⟨le_rfl, hA.a_lt_b.le⟩).ne'
  have hPb : P b ≠ 0 := (hA.pos b ⟨hA.a_lt_b.le, le_rfl⟩).ne'
  have hb0 : 0 < b := hA.a_pos.trans hA.a_lt_b
  have hderiv : ∀ x ∈ Ioo a b,
      HasDerivAt (fun x => -(x * deriv P x / P x) + Real.log (P x) - C * Real.log x)
        (x * (deriv P x / P x) ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hA.a_pos.trans hx.1).ne'
    have hPx : P x ≠ 0 := (hA.pos_Ioo hx).ne'
    have h1 := (hA.hasDerivAt_ω homega hx).neg
    have h2 := (hA.differentiableAt hx).hasDerivAt.log hPx
    have h3 := (Real.hasDerivAt_log hx0).const_mul C
    have := (h1.add h2).sub h3
    convert this using 1
    have hg := hgrad x (P x) (deriv P x) C hx0 hPx
    rw [← hA.first_integral x hx] at hg
    rw [div_pow, ← mul_div_assoc, hg]
    field_simp
  have hla : Tendsto (fun x => Real.log (P x)) (𝓝[>] a) (𝓝 (Real.log (P a))) :=
    (Real.continuousAt_log hPa).tendsto.comp hA.tendsto_P_a
  have hlb : Tendsto (fun x => Real.log (P x)) (𝓝[<] b) (𝓝 (Real.log (P b))) :=
    (Real.continuousAt_log hPb).tendsto.comp hA.tendsto_P_b
  have hxa : Tendsto (fun x : ℝ => Real.log x) (𝓝[>] a) (𝓝 (Real.log a)) :=
    ((Real.continuousAt_log hA.a_pos.ne').tendsto).mono_left nhdsWithin_le_nhds
  have hxb : Tendsto (fun x : ℝ => Real.log x) (𝓝[<] b) (𝓝 (Real.log b)) :=
    ((Real.continuousAt_log hb0.ne').tendsto).mono_left nhdsWithin_le_nhds
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hA.a_lt_b hderiv hint
    ((hA.tendsto_ω_a.neg.add hla).sub (hxa.const_mul C))
    ((hA.tendsto_ω_b.neg.add hlb).sub (hxb.const_mul C))]
  ring


/-- `𝒟(ω) = d ξ/P²` along the free arc (the first integral divided by `P²/ξ`). -/
lemma Dq_ω (hA : FreeArc d C P a b La Lb) {x : ℝ} (hx : x ∈ Ioo a b) :
    (x * deriv P x / P x) ^ 2 - x * deriv P x / P x + C = d * x / P x ^ 2 := by
  have hx0 : x ≠ 0 := (hA.a_pos.trans hx.1).ne'
  have hPx : P x ≠ 0 := (hA.pos_Ioo hx).ne'
  rw [hA.first_integral x hx]
  field_simp

lemma Dq_ω_a (hA : FreeArc d C P a b La Lb) :
    (a * La / P a) ^ 2 - a * La / P a + C = d * a / P a ^ 2 := by
  have hPa : P a ≠ 0 := (hA.pos a ⟨le_rfl, hA.a_lt_b.le⟩).ne'
  have ha0 : a ≠ 0 := hA.a_pos.ne'
  rw [hA.first_integral_a]
  field_simp

lemma Dq_ω_b (hA : FreeArc d C P a b La Lb) :
    (b * Lb / P b) ^ 2 - b * Lb / P b + C = d * b / P b ^ 2 := by
  have hPb : P b ≠ 0 := (hA.pos b ⟨hA.a_lt_b.le, le_rfl⟩).ne'
  have hb0 : b ≠ 0 := (hA.a_pos.trans hA.a_lt_b).ne'
  rw [hA.first_integral_b]
  field_simp

end FreeArc

/-- `ω = ξ P'/P` patched at the contacts by its one-sided limits. -/
def ωt (P : ℝ → ℝ) (a b La Lb : ℝ) : ℝ → ℝ :=
  Function.update (Function.update (fun x => x * deriv P x / P x) a (a * La / P a)) b
    (b * Lb / P b)

lemma ωt_a {P : ℝ → ℝ} {a b La Lb : ℝ} (hab : a < b) : ωt P a b La Lb a = a * La / P a := by
  unfold ωt; rw [Function.update_of_ne hab.ne, Function.update_self]

lemma ωt_b {P : ℝ → ℝ} {a b La Lb : ℝ} : ωt P a b La Lb b = b * Lb / P b := by
  unfold ωt; rw [Function.update_self]

lemma ωt_Ioo {P : ℝ → ℝ} {a b La Lb x : ℝ} (hx : x ∈ Ioo a b) :
    ωt P a b La Lb x = x * deriv P x / P x := by
  unfold ωt; rw [Function.update_of_ne hx.2.ne, Function.update_of_ne hx.1.ne']

namespace FreeArc

variable {d C : ℝ} {P : ℝ → ℝ} {a b La Lb : ℝ}

lemma continuousOn_ωt (hA : FreeArc d C P a b La Lb)
    (homega : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
        = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)) :
    ContinuousOn (ωt P a b La Lb) (Icc a b) :=
  continuousOn_update_Icc hA.a_lt_b (hA.continuousOn_ω homega) hA.tendsto_ω_a hA.tendsto_ω_b

lemma Dq_ωt (hA : FreeArc d C P a b La Lb) {x : ℝ} (hx : x ∈ Icc a b) :
    ωt P a b La Lb x ^ 2 - ωt P a b La Lb x + C = d * x / P x ^ 2 := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h; rw [ωt_a hA.a_lt_b]; exact hA.Dq_ω_a
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · subst h'; rw [ωt_b]; exact hA.Dq_ω_b
  · rw [ωt_Ioo ⟨h, h'⟩]; exact hA.Dq_ω ⟨h, h'⟩

lemma Dq_ωt_pos (hA : FreeArc d C P a b La Lb) (hd : 0 < d) {x : ℝ} (hx : x ∈ Icc a b) :
    0 < ωt P a b La Lb x ^ 2 - ωt P a b La Lb x + C := by
  rw [hA.Dq_ωt hx]
  have := hA.pos x hx
  have := hA.x_pos hx
  positivity

/-- The substitution `u = ω(ξ)` on the free arc: `log(b/a) = ∫_{ω(b)}^{ω(a)} du/𝒟(u)`
(`dξ/ξ = -dω/𝒟(ω)`, the connection equation of paper gap G9). -/
lemma log_ratio (hA : FreeArc d C P a b La Lb) (hd : 0 < d)
    (homega : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
        = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)) :
    Real.log (b / a) = ∫ u in (b * Lb / P b)..(a * La / P a), (u ^ 2 - u + C)⁻¹ := by
  have hab := hA.a_lt_b
  have hcv := intervalIntegral.integral_comp_mul_deriv'' (a := a) (b := b)
    (f := ωt P a b La Lb) (f' := fun x => -(d / P x ^ 2)) (g := fun u => (u ^ 2 - u + C)⁻¹)
    (by rw [uIcc_of_le hab.le]; exact hA.continuousOn_ωt homega)
    (by
      intro x hx
      rw [min_eq_left hab.le, max_eq_right hab.le] at hx
      have h1 := hA.hasDerivAt_ω homega hx
      have h2 : ωt P a b La Lb =ᶠ[𝓝 x] fun x => x * deriv P x / P x := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using ωt_Ioo hy
      exact (h1.congr_of_eventuallyEq h2).hasDerivWithinAt)
    (by
      rw [uIcc_of_le hab.le]
      apply ContinuousOn.neg
      apply ContinuousOn.div continuousOn_const (hA.cont.pow 2)
      intro x hx; exact (pow_pos (hA.pos x hx) 2).ne')
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [uIcc_of_le hab.le] at hx
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.inv₀ (by fun_prop)
      exact (hA.Dq_ωt_pos hd hx).ne')
  rw [ωt_a hab, ωt_b] at hcv
  have hL : ∫ x in a..b, ((fun u => (u ^ 2 - u + C)⁻¹) ∘ ωt P a b La Lb) x * (-(d / P x ^ 2))
      = ∫ x in a..b, -x⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    simp only [Function.comp]
    rw [hA.Dq_ωt hx]
    have := hA.pos x hx
    have := hA.x_pos hx
    field_simp
  rw [hL, intervalIntegral.integral_neg, integral_inv_of_pos hA.a_pos (hA.a_pos.trans hab)] at hcv
  rw [intervalIntegral.integral_symm]
  linarith

/-- `ω` decreases strictly along the free arc: `ω(b) < ω(a)`. -/
lemma ω_lt (hA : FreeArc d C P a b La Lb) (hd : 0 < d)
    (homega : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
        = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)) :
    b * Lb / P b < a * La / P a := by
  have h := hA.integral_inv_sq hd.ne' homega
  have hpos : 0 < ∫ x in a..b, (P x ^ 2)⁻¹ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on ((hA.continuousOn_inv_sq).intervalIntegrable_of_Icc
      hA.a_lt_b.le) (fun x hx => by have := hA.pos_Ioo hx; positivity) hA.a_lt_b
  rw [h] at hpos
  have := (div_pos_iff_of_pos_right hd).1 hpos
  linarith

/-- `𝒟 > 0` on `[ω(b), ω(a)]`: every such value is taken by `ω` on the arc. -/
lemma Dq_pos_Icc (hA : FreeArc d C P a b La Lb) (hd : 0 < d)
    (homega : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
      H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
        = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)) :
    ∀ u ∈ Icc (b * Lb / P b) (a * La / P a), 0 < u ^ 2 - u + C := by
  intro u hu
  have hsub := intermediate_value_Icc' hA.a_lt_b.le (hA.continuousOn_ωt homega)
  rw [ωt_a hA.a_lt_b, ωt_b] at hsub
  obtain ⟨x, hx, rfl⟩ := hsub hu
  exact hA.Dq_ωt_pos hd hx

end FreeArc


/-! ### Three-arc class curves -/

/-- Signs of the parameters of a class member. -/
lemma params_signs {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P) :
    0 < θ.t ∧ θ.t < 1 ∧ 0 < θ.p ∧ 0 ≤ θ.c ∧ 0 < θ.δ ∧ 0 < θ.e ∧ 0 < θ.v ∧ 0 < θ.ξ₀ ∧
      0 < θ.h := by
  obtain ⟨ht, ht1, htp, _, hξ₀, _⟩ := hP.admissible
  have hp : 0 < θ.p := ht.trans_le htp
  have hv : 0 < θ.v := by
    show 0 < vF θ.t
    rw [vF_eq]; linarith
  refine ⟨ht, ht1, hp, ?_, ?_, ?_, hv, hξ₀, ?_⟩
  · show 0 ≤ cF θ.t θ.p
    unfold cF; linarith
  · show 0 < δF θ.t θ.p
    unfold δF; linarith
  · show 0 < eF θ.t
    unfold eF; linarith
  · show 0 < θ.v / θ.ξ₀
    positivity

lemma c_add_δ (θ : Params) : θ.c + θ.δ = θ.p := by
  show cF θ.t θ.p + δF θ.t θ.p = θ.p
  unfold cF δF; ring

lemma v_add_e (θ : Params) : θ.v + θ.e = 1 := by
  show vF θ.t + eF θ.t = 1
  unfold vF; ring

lemma h_mul_ξ₀ {θ : Params} (hξ₀ : θ.ξ₀ ≠ 0) : θ.h * θ.ξ₀ = θ.v := by
  show θ.v / θ.ξ₀ * θ.ξ₀ = θ.v
  field_simp

lemma line₂_ξ₀ {θ : Params} (hξ₀ : θ.ξ₀ ≠ 0) : θ.line₂ θ.ξ₀ = 1 := by
  show θ.h * θ.ξ₀ + θ.e = 1
  rw [h_mul_ξ₀ hξ₀, v_add_e]

/-- The free arc of a three-arc class curve with positive contacts. -/
lemma freeArc_of {d C ξl ξr : ℝ} {θ : Params} {P : ℝ → ℝ} (hCB : ClassBasicsStatement)
    (hP : InClass θ P) (hA : ThreeArc d θ P ξl ξr C) (hl : θ.c < ξl) (hr : ξr < θ.ξ₀) :
    FreeArc d C P ξl ξr 1 θ.h := by
  obtain ⟨ht, -, hp, hc, -⟩ := params_signs hP
  have hsub : Icc ξl ξr ⊆ Icc θ.c θ.ξ₀ := Icc_subset_Icc hA.c_le hA.r_le
  exact
    { a_pos := hc.trans_lt hl
      a_lt_b := hA.l_lt_r
      cont := (hCB.1 θ P hP).1.mono hsub
      pos := fun x hx => hP.pos x (hsub hx)
      concave := hP.concave.subset hsub (convex_Icc _ _)
      smooth := hA.smooth
      euler := hA.euler
      first_integral := hA.first_integral
      deriv_a := hA.fit_left hl
      deriv_b := hA.fit_right hr }

lemma hasDerivAt_left_contact {d C ξl ξr : ℝ} {θ : Params} {P : ℝ → ℝ}
    (hA : ThreeArc d θ P ξl ξr C) {x : ℝ} (hx : x ∈ Ioo θ.c ξl) : HasDerivAt P 1 x := by
  have h : P =ᶠ[𝓝 x] fun y => id y + θ.δ := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy using hA.left_contact y hy
  exact ((hasDerivAt_id x).add_const θ.δ).congr_of_eventuallyEq h

lemma hasDerivAt_right_contact {d C ξl ξr : ℝ} {θ : Params} {P : ℝ → ℝ}
    (hA : ThreeArc d θ P ξl ξr C) {x : ℝ} (hx : x ∈ Ioo ξr θ.ξ₀) : HasDerivAt P θ.h x := by
  have h : P =ᶠ[𝓝 x] fun y => θ.h * id y + θ.e := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy using hA.right_contact y hy
  have := (((hasDerivAt_id x).const_mul θ.h).add_const θ.e).congr_of_eventuallyEq h
  simpa using this

/-- `T_f` on the initial contact. -/
lemma T_left {d C ξl ξr : ℝ} {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
    (hA : ThreeArc d θ P ξl ξr C) :
    ∫ x in θ.c..ξl, (P x ^ 2)⁻¹ = θ.p⁻¹ - (θ.line₁ ξl)⁻¹ := by
  obtain ⟨-, -, -, hc, hδ, -⟩ := params_signs hP
  have hpos : ∀ x ∈ uIcc θ.c ξl, 0 < x + θ.δ := by
    intro x hx
    rw [uIcc_of_le hA.c_le] at hx
    linarith [hx.1]
  rw [intervalIntegral.integral_congr (g := fun x => ((x + θ.δ) ^ 2)⁻¹) (fun x hx => by
    rw [uIcc_of_le hA.c_le] at hx
    simp only
    rw [hA.left_contact x hx]
    rfl)]
  have hderiv : ∀ x ∈ uIcc θ.c ξl,
      HasDerivAt (fun x => -(x + θ.δ)⁻¹) (((x + θ.δ) ^ 2)⁻¹) x := by
    intro x hx
    have := (((hasDerivAt_id x).add_const θ.δ).inv (hpos x hx).ne').neg
    convert this using 1
    simp only [id, neg_div, neg_neg, one_div]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((ContinuousOn.inv₀ (by fun_prop) (fun x hx => (pow_pos (hpos x hx) 2).ne')).intervalIntegrable)]
  rw [c_add_δ]
  show -(ξl + θ.δ)⁻¹ - -θ.p⁻¹ = θ.p⁻¹ - (ξl + θ.δ)⁻¹
  ring

/-- `T_f` on the final contact. -/
lemma T_right {d C ξl ξr : ℝ} {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
    (hA : ThreeArc d θ P ξl ξr C) :
    ∫ x in ξr..θ.ξ₀, (P x ^ 2)⁻¹ = ((θ.line₂ ξr)⁻¹ - 1) / θ.h := by
  obtain ⟨-, -, -, hc, -, he, -, hξ₀, hh⟩ := params_signs hP
  have hξr : 0 ≤ ξr := hc.trans (hA.c_le.trans hA.l_lt_r.le)
  have hpos : ∀ x ∈ uIcc ξr θ.ξ₀, 0 < θ.h * x + θ.e := by
    intro x hx
    rw [uIcc_of_le hA.r_le] at hx
    have : 0 ≤ θ.h * x := mul_nonneg hh.le (hξr.trans hx.1)
    linarith
  rw [intervalIntegral.integral_congr (g := fun x => ((θ.h * x + θ.e) ^ 2)⁻¹) (fun x hx => by
    rw [uIcc_of_le hA.r_le] at hx
    simp only
    rw [hA.right_contact x hx]
    rfl)]
  have hderiv : ∀ x ∈ uIcc ξr θ.ξ₀,
      HasDerivAt (fun x => -(θ.h * x + θ.e)⁻¹ / θ.h) (((θ.h * x + θ.e) ^ 2)⁻¹) x := by
    intro x hx
    have := ((((hasDerivAt_id x).const_mul θ.h).add_const θ.e).inv (hpos x hx).ne').neg.div_const
      θ.h
    convert this using 1
    simp only [id]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((ContinuousOn.inv₀ (by fun_prop) (fun x hx => (pow_pos (hpos x hx) 2).ne')).intervalIntegrable)]
  have h1 : θ.h * θ.ξ₀ + θ.e = 1 := line₂_ξ₀ hξ₀.ne'
  rw [h1]
  show _ = ((θ.h * ξr + θ.e)⁻¹ - 1) / θ.h
  ring

/-- `Q_f` on the initial contact. -/
lemma Q_left {d C ξl ξr : ℝ} {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
    (hA : ThreeArc d θ P ξl ξr C) :
    ∫ x in θ.c..ξl, x * (deriv P x / P x) ^ 2
      = Real.log (θ.line₁ ξl) - Real.log θ.p + θ.δ * ((θ.line₁ ξl)⁻¹ - θ.p⁻¹) := by
  obtain ⟨-, -, -, hc, hδ, -⟩ := params_signs hP
  have hpos : ∀ x ∈ uIcc θ.c ξl, 0 < x + θ.δ := by
    intro x hx
    rw [uIcc_of_le hA.c_le] at hx
    linarith [hx.1]
  rw [intervalIntegral_congr_Ioo hA.c_le (g := fun x => x * (1 / (x + θ.δ)) ^ 2) (fun x hx => by
    simp only
    rw [(hasDerivAt_left_contact hA hx).deriv, hA.left_contact x (Ioo_subset_Icc_self hx)]
    rfl)]
  have hderiv : ∀ x ∈ uIcc θ.c ξl,
      HasDerivAt (fun x => Real.log (x + θ.δ) + θ.δ / (x + θ.δ)) (x * (1 / (x + θ.δ)) ^ 2) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    have h1 := ((hasDerivAt_id x).add_const θ.δ).log hx0
    have h2 := (hasDerivAt_const x θ.δ).div ((hasDerivAt_id x).add_const θ.δ) hx0
    convert h1.add h2 using 1
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((ContinuousOn.mul continuousOn_id (ContinuousOn.pow (ContinuousOn.div continuousOn_const
      (by fun_prop) (fun x hx => (hpos x hx).ne')) 2)).intervalIntegrable)]
  rw [c_add_δ]
  show _ = Real.log (ξl + θ.δ) - Real.log θ.p + θ.δ * ((ξl + θ.δ)⁻¹ - θ.p⁻¹)
  simp only [div_eq_mul_inv]
  ring

/-- `Q_f` on the final contact. -/
lemma Q_right {d C ξl ξr : ℝ} {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
    (hA : ThreeArc d θ P ξl ξr C) :
    ∫ x in ξr..θ.ξ₀, x * (deriv P x / P x) ^ 2
      = -Real.log (θ.line₂ ξr) + θ.e * (1 - (θ.line₂ ξr)⁻¹) := by
  obtain ⟨-, -, -, hc, -, he, -, hξ₀, hh⟩ := params_signs hP
  have hξr : 0 ≤ ξr := hc.trans (hA.c_le.trans hA.l_lt_r.le)
  have hpos : ∀ x ∈ uIcc ξr θ.ξ₀, 0 < θ.h * x + θ.e := by
    intro x hx
    rw [uIcc_of_le hA.r_le] at hx
    have : 0 ≤ θ.h * x := mul_nonneg hh.le (hξr.trans hx.1)
    linarith
  rw [intervalIntegral_congr_Ioo hA.r_le (g := fun x => x * (θ.h / (θ.h * x + θ.e)) ^ 2)
    (fun x hx => by
      simp only
      rw [(hasDerivAt_right_contact hA hx).deriv, hA.right_contact x (Ioo_subset_Icc_self hx)]
      rfl)]
  have hderiv : ∀ x ∈ uIcc ξr θ.ξ₀,
      HasDerivAt (fun x => Real.log (θ.h * x + θ.e) + θ.e / (θ.h * x + θ.e))
        (x * (θ.h / (θ.h * x + θ.e)) ^ 2) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    have hl := ((hasDerivAt_id x).const_mul θ.h).add_const θ.e
    have h1 := hl.log hx0
    have h2 := (hasDerivAt_const x θ.e).div hl hx0
    convert h1.add h2 using 1
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((ContinuousOn.mul continuousOn_id (ContinuousOn.pow (ContinuousOn.div continuousOn_const
      (by fun_prop) (fun x hx => (hpos x hx).ne')) 2)).intervalIntegrable)]
  have h1 : θ.h * θ.ξ₀ + θ.e = 1 := line₂_ξ₀ hξ₀.ne'
  rw [h1]
  show _ = -Real.log (θ.h * ξr + θ.e) + θ.e * (1 - (θ.h * ξr + θ.e)⁻¹)
  simp only [Real.log_one, div_eq_mul_inv]
  ring

/-- `m a + N δ/p - N e = 1 - m` (the constant of the third line of `(eq:2fam-quadratures)`). -/
lemma G_constant {θ : Params} (ht : 0 < θ.t) (hp : 0 < θ.p) :
    θ.m * θ.a + θ.N * θ.δ / θ.p - θ.N * θ.e = 1 - θ.m := by
  show mF θ.t * aF θ.t θ.p + NF θ.t * δF θ.t θ.p / θ.p - NF θ.t * eF θ.t = 1 - mF θ.t
  unfold mF aF NF δF eF cF
  have h1 : 0 < 1 + θ.t := by linarith
  field_simp
  ring

/-- `(eq:2fam-quadratures)` for a three-arc class curve with positive contacts. -/
theorem quadratures (hI : FamilyIdentities) (hCB : ClassBasicsStatement) :
    QuadratureStatement := by
  intro d θ P ξl ξr C hd hP hA hl hr
  obtain ⟨hcont, -, -, -, hTint, hQint, -, -⟩ := hCB.1 θ P hP
  obtain ⟨ht, -, hp, hc, hδ, he, hv, hξ₀, hh⟩ := params_signs hP
  have hF := freeArc_of hCB hP hA hl hr
  have hlr := hA.l_lt_r
  have hcξl := hA.c_le
  have hξr₀ := hA.r_le
  have hPl : P ξl = θ.line₁ ξl := hA.left_contact ξl ⟨hcξl, le_rfl⟩
  have hPr : P ξr = θ.line₂ ξr := hA.right_contact ξr ⟨le_rfl, hξr₀⟩
  have hsub1 : uIcc θ.c ξl ⊆ uIcc θ.c θ.ξ₀ := by
    rw [uIcc_of_le hcξl, uIcc_of_le (hcξl.trans (hlr.le.trans hξr₀))]
    exact Icc_subset_Icc le_rfl (hlr.le.trans hξr₀)
  have hsub2 : uIcc ξl ξr ⊆ uIcc θ.c θ.ξ₀ := by
    rw [uIcc_of_le hlr.le, uIcc_of_le (hcξl.trans (hlr.le.trans hξr₀))]
    exact Icc_subset_Icc hcξl hξr₀
  have hsub3 : uIcc ξr θ.ξ₀ ⊆ uIcc θ.c θ.ξ₀ := by
    rw [uIcc_of_le hξr₀, uIcc_of_le (hcξl.trans (hlr.le.trans hξr₀))]
    exact Icc_subset_Icc (hcξl.trans hlr.le) le_rfl
  have hsub12 : uIcc θ.c ξr ⊆ uIcc θ.c θ.ξ₀ := by
    rw [uIcc_of_le (hcξl.trans hlr.le), uIcc_of_le (hcξl.trans (hlr.le.trans hξr₀))]
    exact Icc_subset_Icc le_rfl hξr₀
  have hl1 : 0 < θ.line₁ ξl := by
    show 0 < ξl + θ.δ
    linarith
  have hr1 : 0 < θ.line₂ ξr := by rw [← hPr]; exact hF.pos ξr ⟨hlr.le, le_rfl⟩
  have hξl0 : 0 < ξl := hc.trans_lt hl
  have hξr0 : 0 < ξr := hξl0.trans hlr
  -- `T_f`
  have hT : Tf θ P = quadT d θ ξl ξr := by
    unfold Tf
    rw [← intervalIntegral.integral_add_adjacent_intervals (hTint.mono_set hsub12)
      (hTint.mono_set hsub3),
      ← intervalIntegral.integral_add_adjacent_intervals (hTint.mono_set hsub1)
      (hTint.mono_set hsub2),
      T_left hP hA, hF.integral_inv_sq hd.ne' hI.omega_derivative, T_right hP hA, hPl, hPr]
    unfold quadT
    ring
  -- `Q_f`
  have hQ : Qf θ P = quadQ θ ξl ξr C := by
    unfold Qf
    rw [← intervalIntegral.integral_add_adjacent_intervals (hQint.mono_set hsub12)
      (hQint.mono_set hsub3),
      ← intervalIntegral.integral_add_adjacent_intervals (hQint.mono_set hsub1)
      (hQint.mono_set hsub2),
      Q_left hP hA, hF.integral_grad hI.omega_derivative hI.gradient_integrand
        (hQint.mono_set hsub2), Q_right hP hA, hPl, hPr]
    have hsum := hI.quadrature_Q_sum θ.p θ.δ θ.e θ.h (θ.line₁ ξl) (θ.line₂ ξr) C
      (Real.log (ξr / ξl)) hp hl1 hr1 hh.ne'
    have hξl : θ.line₁ ξl - θ.δ = ξl := by show ξl + θ.δ - θ.δ = ξl; ring
    have hξr : (θ.line₂ ξr - θ.e) / θ.h = ξr := by
      show (θ.h * ξr + θ.e - θ.e) / θ.h = ξr
      field_simp
      ring
    rw [hξl, hξr, Real.log_div hl1.ne' hp.ne', Real.log_div hr1.ne' hl1.ne',
      Real.log_div hξr0.ne' hξl0.ne'] at hsum
    unfold quadQ
    rw [Real.log_div hξr0.ne' hξl0.ne']
    rw [← hsum]
    ring
  refine ⟨hT, hQ, ?_⟩
  -- `G_f`
  unfold Gf
  rw [hQ]
  unfold quadQ quadG
  have hk := G_constant ht hp
  linear_combination hk

end PkgD

end FixedPrice.TwoUnit.Family
