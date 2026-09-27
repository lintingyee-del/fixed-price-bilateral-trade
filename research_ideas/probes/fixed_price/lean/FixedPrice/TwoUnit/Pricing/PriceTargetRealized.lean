import FixedPrice.TwoUnit.Pricing.PriceTargetReverse

/-!
# Theorem E, package B, part 3: the realized price

For a cumulative mass `ϖ` on `[0, b̄]` (`b̄ ≥ 0`) and `d > 0`, the extended mass
`ϖ_ext = ϖ(0)` below `0`, `ϖ` on `[0, b̄]`, `d · max (M - t) 0` from `b̄` on (`M = b̄ + ϖ(b̄)/d`)
is nonincreasing and right-continuous, so `-ϖ_ext` is a Stieltjes function. Its measure has mass
`ϖ_ext(t)` above `t`, total mass `ϖ(0)`, no mass below `0`, and mass `ϖ_ext(a) - ϖ_ext(c)` on
`(a, c]`. The realized price `β · (-dϖ_ext) + (1 - βϖ(0)) δ₀` is therefore a price probability
with bounded support whose survival function is `βϖ` on `[0, b̄]`, and above `b̄` it is the density
`βd` on `(b̄, M)`.

The realized potential beyond `b̄` exceeds its value at `b̄` by `dw - min {dw, ϖ(b̄)} ≥ 0`, so the
price target at any ordered seller pair reduces to the ordered potential sum at the pair clipped
to `[0, b̄]` (certified field `ordered_farkas`).
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section Extended

variable {bbar d : ℝ} {ϖ : ℝ → ℝ}

theorem extendedMass_of_neg {t : ℝ} (ht : t < 0) : extendedMass bbar d ϖ t = ϖ 0 := by
  unfold extendedMass; rw [if_pos ht]

theorem extendedMass_of_mem {t : ℝ} (ht : t ∈ Icc 0 bbar) : extendedMass bbar d ϖ t = ϖ t := by
  unfold extendedMass; rw [if_neg (not_lt.mpr ht.1), if_pos ht.2]

variable (hb : 0 ≤ bbar) (hd : 0 < d) (hϖ : IsCumulativeMass bbar ϖ)
include hb hd hϖ

theorem extendedMass_of_ge {t : ℝ} (ht : bbar ≤ t) :
    extendedMass bbar d ϖ t = d * max (bbar + ϖ bbar / d - t) 0 := by
  have hϖb : 0 ≤ ϖ bbar := hϖ.nonneg bbar ⟨hb, le_rfl⟩
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    rw [extendedMass_of_mem ⟨hb, le_rfl⟩, show bbar + ϖ bbar / d - bbar = ϖ bbar / d by ring,
      max_eq_left (div_nonneg hϖb hd.le)]
    field_simp
  · unfold extendedMass
    rw [if_neg (by linarith), if_neg (not_le.mpr h), mul_max_of_nonneg _ _ hd.le, mul_zero]
    congr 1
    field_simp
    ring

theorem extendedMass_nonneg (t : ℝ) : 0 ≤ extendedMass bbar d ϖ t := by
  rcases lt_or_ge t 0 with h | h
  · rw [extendedMass_of_neg h]; exact hϖ.nonneg 0 ⟨le_rfl, hb⟩
  rcases le_or_gt t bbar with h' | h'
  · rw [extendedMass_of_mem ⟨h, h'⟩]; exact hϖ.nonneg t ⟨h, h'⟩
  · rw [extendedMass_of_ge hb hd hϖ h'.le]; positivity

theorem extendedMass_le_bbar {t : ℝ} (ht : bbar ≤ t) : extendedMass bbar d ϖ t ≤ ϖ bbar := by
  have hϖb : 0 ≤ ϖ bbar := hϖ.nonneg bbar ⟨hb, le_rfl⟩
  rw [extendedMass_of_ge hb hd hϖ ht, mul_max_of_nonneg _ _ hd.le, mul_zero]
  refine max_le ?_ hϖb
  have : d * (bbar + ϖ bbar / d - t) = ϖ bbar - d * (t - bbar) := by field_simp; ring
  rw [this]
  nlinarith

theorem extendedMass_antitone : Antitone (extendedMass bbar d ϖ) := by
  have hϖ0 : ∀ t ∈ Icc 0 bbar, ϖ t ≤ ϖ 0 := fun t ht => hϖ.antitoneOn ⟨le_rfl, hb⟩ ht ht.1
  have hle0 : ∀ t, extendedMass bbar d ϖ t ≤ ϖ 0 := fun t => by
    rcases lt_or_ge t 0 with h | h
    · rw [extendedMass_of_neg h]
    rcases le_or_gt t bbar with h' | h'
    · rw [extendedMass_of_mem ⟨h, h'⟩]; exact hϖ0 t ⟨h, h'⟩
    · exact (extendedMass_le_bbar hb hd hϖ h'.le).trans (hϖ0 bbar ⟨hb, le_rfl⟩)
  intro x y hxy
  rcases lt_or_ge x 0 with hx | hx
  · rw [extendedMass_of_neg hx]; exact hle0 y
  rcases le_or_gt x bbar with hx' | hx'
  · rw [extendedMass_of_mem ⟨hx, hx'⟩]
    rcases le_or_gt y bbar with hy' | hy'
    · rw [extendedMass_of_mem ⟨hx.trans hxy, hy'⟩]
      exact hϖ.antitoneOn ⟨hx, hx'⟩ ⟨hx.trans hxy, hy'⟩ hxy
    · exact (extendedMass_le_bbar hb hd hϖ hy'.le).trans
        (hϖ.antitoneOn ⟨hx, hx'⟩ ⟨hb, le_rfl⟩ hx')
  · rw [extendedMass_of_ge hb hd hϖ hx'.le, extendedMass_of_ge hb hd hϖ (hx'.le.trans hxy)]
    exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hd.le

theorem extendedMass_rightContinuous (x : ℝ) :
    ContinuousWithinAt (extendedMass bbar d ϖ) (Ici x) x := by
  rcases lt_or_ge x 0 with hx | hx
  · have heq : extendedMass bbar d ϖ =ᶠ[𝓝 x] fun _ => ϖ 0 :=
      (eventually_lt_nhds hx).mono fun t ht => extendedMass_of_neg ht
    exact (continuousAt_const.congr heq.symm).continuousWithinAt
  rcases lt_or_ge x bbar with hxb | hxb
  · have h : ContinuousWithinAt (extendedMass bbar d ϖ) (Icc x bbar) x :=
      (hϖ.rightContinuous x ⟨hx, hxb.le⟩).congr
        (fun y hy => extendedMass_of_mem (d := d) ⟨hx.trans hy.1, hy.2⟩)
        (extendedMass_of_mem (d := d) ⟨hx, hxb.le⟩)
    exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hxb)
  · have hc : Continuous fun t => d * max (bbar + ϖ bbar / d - t) 0 := by fun_prop
    exact hc.continuousWithinAt.congr (fun y hy => extendedMass_of_ge hb hd hϖ (hxb.trans hy))
      (extendedMass_of_ge hb hd hϖ hxb)

/-- `-ϖ_ext` as a Stieltjes function. -/
def extStieltjes : StieltjesFunction ℝ where
  toFun := fun t => -extendedMass bbar d ϖ t
  mono' := fun _ _ h => neg_le_neg (extendedMass_antitone hb hd hϖ h)
  right_continuous' := fun x => (extendedMass_rightContinuous hb hd hϖ x).neg

theorem extendedMassMeasure_eq :
    extendedMassMeasure bbar d ϖ = (extStieltjes hb hd hϖ).measure := by
  unfold extendedMassMeasure
  rw [dif_pos ⟨(extStieltjes hb hd hϖ).mono', (extStieltjes hb hd hϖ).right_continuous'⟩]
  rfl

theorem extStieltjes_tendsto_atTop :
    Tendsto (extStieltjes hb hd hϖ) atTop (𝓝 0) := by
  have heq : (fun _ => (0 : ℝ)) =ᶠ[atTop] extStieltjes hb hd hϖ := by
    filter_upwards [eventually_ge_atTop (bbar + ϖ bbar / d), eventually_ge_atTop bbar]
      with t ht ht'
    show 0 = -extendedMass bbar d ϖ t
    rw [extendedMass_of_ge hb hd hϖ ht', max_eq_right (by linarith)]
    ring
  exact tendsto_const_nhds.congr' heq

theorem extStieltjes_tendsto_atBot :
    Tendsto (extStieltjes hb hd hϖ) atBot (𝓝 (-ϖ 0)) := by
  have heq : (fun _ => -ϖ 0) =ᶠ[atBot] extStieltjes hb hd hϖ := by
    filter_upwards [eventually_lt_atBot 0] with t ht
    show -ϖ 0 = -extendedMass bbar d ϖ t
    rw [extendedMass_of_neg ht]
  exact tendsto_const_nhds.congr' heq

theorem extMeasure_Ioi (t : ℝ) :
    (extStieltjes hb hd hϖ).measure (Ioi t) = ENNReal.ofReal (extendedMass bbar d ϖ t) := by
  rw [StieltjesFunction.measure_Ioi _ (extStieltjes_tendsto_atTop hb hd hϖ)]
  congr 1
  show 0 - -extendedMass bbar d ϖ t = _
  ring

theorem extMeasure_univ :
    (extStieltjes hb hd hϖ).measure univ = ENNReal.ofReal (ϖ 0) := by
  rw [StieltjesFunction.measure_univ _ (extStieltjes_tendsto_atBot hb hd hϖ)
    (extStieltjes_tendsto_atTop hb hd hϖ)]
  congr 1; ring

theorem extMeasure_Iio_zero : (extStieltjes hb hd hϖ).measure (Iio 0) = 0 := by
  rw [StieltjesFunction.measure_Iio _ (extStieltjes_tendsto_atBot hb hd hϖ)]
  have hll : leftLim (extStieltjes hb hd hϖ) 0 = -ϖ 0 := by
    apply leftLim_eq_of_tendsto (NeBot.ne inferInstance)
    have heq : (fun _ => -ϖ 0) =ᶠ[𝓝[<] (0 : ℝ)] extStieltjes hb hd hϖ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      show -ϖ 0 = -extendedMass bbar d ϖ t
      rw [extendedMass_of_neg ht]
    exact tendsto_const_nhds.congr' heq
  rw [hll, sub_self, ENNReal.ofReal_zero]

theorem extMeasure_Ioc (a c : ℝ) :
    (extStieltjes hb hd hϖ).measure (Ioc a c) =
      ENNReal.ofReal (extendedMass bbar d ϖ a - extendedMass bbar d ϖ c) := by
  rw [StieltjesFunction.measure_Ioc]
  congr 1
  show -extendedMass bbar d ϖ c - -extendedMass bbar d ϖ a = _
  ring

end Extended

/-! ### The realized price -/

section Realized

variable {bbar d β : ℝ} {ϖ : ℝ → ℝ}
variable (hb : 0 ≤ bbar) (hd : 0 < d) (hϖ : IsCumulativeMass bbar ϖ)
include hb hd hϖ

theorem realizedPrice_eq :
    realizedPrice bbar d β ϖ = ENNReal.ofReal β • (extStieltjes hb hd hϖ).measure +
      ENNReal.ofReal (1 - β * ϖ 0) • Measure.dirac 0 := by
  unfold realizedPrice
  rw [extendedMassMeasure_eq hb hd hϖ]

theorem realizedPrice_Ioi {t : ℝ} (ht : 0 ≤ t) :
    realizedPrice bbar d β ϖ (Ioi t) = ENNReal.ofReal β * ENNReal.ofReal (extendedMass bbar d ϖ t) := by
  rw [realizedPrice_eq hb hd hϖ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    extMeasure_Ioi, Measure.dirac_apply' _ measurableSet_Ioi,
    indicator_of_notMem (show (0 : ℝ) ∉ Ioi t from fun h => absurd h (not_lt.mpr ht))]
  simp

theorem isBoundedPriceLaw_realizedPrice (hβ : 0 ≤ β) (h1 : β * ϖ 0 ≤ 1) :
    IsBoundedPriceLaw (realizedPrice bbar d β ϖ) := by
  have hϖ0 : 0 ≤ ϖ 0 := hϖ.nonneg 0 ⟨le_rfl, hb⟩
  refine ⟨⟨?_⟩, ?_, ⟨bbar + ϖ bbar / d, ?_⟩⟩
  · rw [realizedPrice_eq hb hd hϖ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      extMeasure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one,
      ← ENNReal.ofReal_mul hβ, ← ENNReal.ofReal_add (by positivity) (by linarith)]
    simp
  · rw [realizedPrice_eq hb hd hϖ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      extMeasure_Iio_zero, Measure.dirac_apply' _ measurableSet_Iio,
      indicator_of_notMem (show (0 : ℝ) ∉ Iio 0 by simp)]
    simp
  · have hϖb : 0 ≤ ϖ bbar := hϖ.nonneg bbar ⟨hb, le_rfl⟩
    have hM : 0 ≤ bbar + ϖ bbar / d := by positivity
    rw [realizedPrice_Ioi hb hd hϖ hM, extendedMass_of_ge hb hd hϖ (by
      have := div_nonneg hϖb hd.le; linarith), sub_self, max_self, mul_zero]
    simp

theorem realizedPrice_real_Ioi (hβ : 0 ≤ β) {t : ℝ} (ht : 0 ≤ t) :
    (realizedPrice bbar d β ϖ).real (Ioi t) = β * extendedMass bbar d ϖ t := by
  rw [measureReal_def, realizedPrice_Ioi hb hd hϖ ht, ← ENNReal.ofReal_mul hβ,
    ENNReal.toReal_ofReal (mul_nonneg hβ (extendedMass_nonneg hb hd hϖ t))]

end Realized

end FixedPrice.TwoUnit.Pricing
