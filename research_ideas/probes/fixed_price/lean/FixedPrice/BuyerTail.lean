import FixedPrice.UpperBound
import Mathlib.MeasureTheory.Integral.Prod

/-! The buyer's survival function `H(z) = P(V > z)` and tail integral `L(s) = E(V - s)_+`
for a value law on the nonnegative reals with finite mean, and the cutoff `s₀` at which
`L(s₀) = d s₀`. The relation `L(s) - L(t) = ∫_s^t H` is obtained by Fubini on a bounded
indicator, so no improper integrals are needed. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- Survival function `P(V > z)`. -/
def survival (μ : Measure ℝ) (z : ℝ) : ℝ := μ.real (Ioi z)

/-- Tail integral `E (V - s)_+`. -/
def tailIntegral (μ : Measure ℝ) (s : ℝ) : ℝ := ∫ v, max (v - s) 0 ∂μ

/-- `1` if the value `v` exceeds the price `u`. -/
def tradeIndicator (v u : ℝ) : ℝ := if u < v then 1 else 0

section Survival

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem survival_nonneg (z : ℝ) : 0 ≤ survival μ z := measureReal_nonneg

theorem survival_le_one (z : ℝ) : survival μ z ≤ 1 := by
  unfold survival
  calc μ.real (Ioi z) ≤ μ.real univ := measureReal_mono (subset_univ _)
    _ = 1 := by rw [measureReal_def, measure_univ, ENNReal.toReal_one]

theorem survival_antitone : Antitone (survival μ) :=
  fun _ _ hzw => measureReal_mono (Ioi_subset_Ioi hzw)

theorem survival_measurable : Measurable (survival μ) := (survival_antitone μ).measurable

theorem tradeIndicator_eq_indicator (v u : ℝ) :
    tradeIndicator v u = (Ioi u).indicator (1 : ℝ → ℝ) v := by
  simp [tradeIndicator, Set.indicator_apply, mem_Ioi]

theorem integral_tradeIndicator (u : ℝ) : (∫ v, tradeIndicator v u ∂μ) = survival μ u := by
  simp_rw [tradeIndicator_eq_indicator]
  rw [integral_indicator_one measurableSet_Ioi]
  rfl

/-- The trade indicator integrates over the price interval to the difference of tails. -/
theorem integral_tradeIndicator_price {s t : ℝ} (hst : s ≤ t) (v : ℝ) :
    (∫ u in s..t, tradeIndicator v u) = max (v - s) 0 - max (v - t) 0 := by
  rcases le_or_gt v s with hvs | hsv
  · have h0 : (∫ u in s..t, tradeIndicator v u) = ∫ _u in s..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc s t := by rwa [uIcc_of_le hst] at hu
      simp only [tradeIndicator]
      rw [if_neg (not_lt.mpr (hvs.trans hu'.1))]
    rw [h0, intervalIntegral.integral_zero, max_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring
  · rcases le_or_gt t v with htv | hvt
    · have h1 : (∫ u in s..t, tradeIndicator v u) = ∫ _u in s..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne v] with u hne hu
        have hu' : u ∈ Ioc s t := by rwa [uIoc_of_le hst] at hu
        simp only [tradeIndicator]
        rw [if_pos (lt_of_le_of_ne (hu'.2.trans htv) hne)]
      rw [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one,
        max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (a := s) (b := v) (c := t) (f := tradeIndicator v) (μ := volume) ?_ ?_
      · rw [← hsplit]
        have h1 : (∫ u in s..v, tradeIndicator v u) = ∫ _u in s..v, (1 : ℝ) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [volume.ae_ne v] with u hne hu
          have hu' : u ∈ Ioc s v := by rwa [uIoc_of_le hsv.le] at hu
          simp only [tradeIndicator]
          rw [if_pos (lt_of_le_of_ne hu'.2 hne)]
        have h2 : (∫ u in v..t, tradeIndicator v u) = ∫ _u in v..t, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro u hu
          have hu' : u ∈ Icc v t := by rwa [uIcc_of_le hvt.le] at hu
          simp only [tradeIndicator]
          rw [if_neg (not_lt.mpr hu'.1)]
        rw [h1, h2, intervalIntegral.integral_const, intervalIntegral.integral_zero, smul_eq_mul,
          mul_one, max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
      · exact (intervalIntegrable_const (c := (1 : ℝ))).congr_ae (by
          rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
          filter_upwards [volume.ae_ne v] with u hne hu
          have hu' : u ∈ Ioc s v := by rwa [uIoc_of_le hsv.le] at hu
          simp only [tradeIndicator]
          rw [if_pos (lt_of_le_of_ne hu'.2 hne)])
      · exact (intervalIntegrable_const (c := (0 : ℝ))).congr (by
          intro u hu
          have hu' : u ∈ Ioc v t := by rwa [uIoc_of_le hvt.le] at hu
          simp only [tradeIndicator]
          rw [if_neg (not_lt.mpr hu'.1.le)])

theorem measurable_tradeIndicator_pair :
    Measurable (fun p : ℝ × ℝ => tradeIndicator p.1 p.2) := by
  unfold tradeIndicator
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const
    measurable_const

theorem integrable_tradeIndicator_prod {s t : ℝ} :
    Integrable (uncurry fun v u => tradeIndicator v u) (μ.prod (volume.restrict (Ioc s t))) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (measurable_tradeIndicator_pair).aestronglyMeasurable
  · filter_upwards with p
    simp only [uncurry, tradeIndicator, Real.norm_eq_abs]
    split_ifs <;> simp

theorem integrable_max_sub (hint : Integrable (fun v => v) μ) (s : ℝ) :
    Integrable (fun v => max (v - s) 0) μ := by
  apply Integrable.mono' (hint.norm.add (integrable_const |s|))
  · exact ((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable
  · filter_upwards with v
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (le_max_right _ _)]
    rcases le_or_gt (v - s) 0 with h | h
    · rw [max_eq_right h]; positivity
    · rw [max_eq_left h.le]
      linarith [abs_nonneg v, abs_nonneg s, abs_sub v s, le_abs_self (v - s)]

/-- `L(s) - L(t) = ∫_s^t H`. -/
theorem tailIntegral_sub (hint : Integrable (fun v => v) μ) {s t : ℝ} (hst : s ≤ t) :
    tailIntegral μ s - tailIntegral μ t = ∫ u in s..t, survival μ u := by
  unfold tailIntegral
  rw [← integral_sub (integrable_max_sub μ hint s) (integrable_max_sub μ hint t)]
  have h1 : (fun v => max (v - s) 0 - max (v - t) 0) =
      fun v => ∫ u in Ioc s t, tradeIndicator v u := by
    funext v
    rw [← intervalIntegral.integral_of_le hst, integral_tradeIndicator_price hst]
  rw [h1, integral_integral_swap (integrable_tradeIndicator_prod μ)]
  rw [intervalIntegral.integral_of_le hst]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u _
  exact integral_tradeIndicator μ u

omit [IsProbabilityMeasure μ] in
theorem tailIntegral_nonneg (s : ℝ) : 0 ≤ tailIntegral μ s :=
  integral_nonneg (fun _ => le_max_right _ _)

theorem tailIntegral_antitone (hint : Integrable (fun v => v) μ) : Antitone (tailIntegral μ) := by
  intro s t hst
  have h := tailIntegral_sub μ hint hst
  have hnn : 0 ≤ ∫ u in s..t, survival μ u :=
    intervalIntegral.integral_nonneg hst (fun u _ => survival_nonneg μ u)
  linarith

theorem tailIntegral_sub_le (hint : Integrable (fun v => v) μ) {s t : ℝ} (hst : s ≤ t) :
    tailIntegral μ s - tailIntegral μ t ≤ t - s := by
  rw [tailIntegral_sub μ hint hst]
  calc (∫ u in s..t, survival μ u) ≤ ∫ _u in s..t, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hst
        · exact (survival_antitone μ).intervalIntegrable
        · exact intervalIntegrable_const
        · exact fun u _ => survival_le_one μ u
    _ = t - s := by simp

theorem tailIntegral_lipschitz (hint : Integrable (fun v => v) μ) :
    LipschitzWith 1 (tailIntegral μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total s t with hst | hts
  · have h1 := tailIntegral_sub_le μ hint hst
    have h2 : 0 ≤ tailIntegral μ s - tailIntegral μ t :=
      sub_nonneg.mpr (tailIntegral_antitone μ hint hst)
    rw [abs_of_nonneg h2, abs_of_nonpos (by linarith)]
    linarith
  · have h1 := tailIntegral_sub_le μ hint hts
    have h2 : 0 ≤ tailIntegral μ t - tailIntegral μ s :=
      sub_nonneg.mpr (tailIntegral_antitone μ hint hts)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem tailIntegral_continuous (hint : Integrable (fun v => v) μ) :
    Continuous (tailIntegral μ) :=
  (tailIntegral_lipschitz μ hint).continuous

omit [IsProbabilityMeasure μ] in
theorem tailIntegral_zero_eq (hnn : ∀ᵐ v ∂μ, 0 ≤ v) : tailIntegral μ 0 = ∫ v, v ∂μ := by
  unfold tailIntegral
  apply integral_congr_ae
  filter_upwards [hnn] with v hv
  simp [max_eq_left hv]

/-- The cutoff at which `d s = L(s)`. -/
theorem exists_cutoff (hint : Integrable (fun v => v) μ) {d : ℝ} (hd : 0 < d)
    (hL0 : 0 < tailIntegral μ 0) : ∃ s₀ : ℝ, 0 < s₀ ∧ tailIntegral μ s₀ = d * s₀ := by
  set φ : ℝ → ℝ := fun s => d * s - tailIntegral μ s with hφ
  have hcont : Continuous φ :=
    (continuous_const.mul continuous_id).sub (tailIntegral_continuous μ hint)
  set s₁ : ℝ := tailIntegral μ 0 / d + 1 with hs₁
  have hs₁pos : 0 < s₁ := by positivity
  have hφ0 : φ 0 < 0 := by
    simp only [hφ, mul_zero, zero_sub, neg_lt_zero]
    exact hL0
  have hφ1 : 0 < φ s₁ := by
    have hL1 : tailIntegral μ s₁ ≤ tailIntegral μ 0 := tailIntegral_antitone μ hint hs₁pos.le
    have hds : d * s₁ = tailIntegral μ 0 + d := by
      rw [hs₁]
      field_simp
    simp only [hφ]
    linarith
  obtain ⟨s₀, hs₀, hφs₀⟩ := intermediate_value_Icc hs₁pos.le hcont.continuousOn ⟨hφ0.le, hφ1.le⟩
  refine ⟨s₀, ?_, ?_⟩
  · rcases eq_or_lt_of_le hs₀.1 with h | h
    · exfalso
      rw [← h] at hφs₀
      linarith
    · exact h
  · simp only [hφ] at hφs₀
    linarith

theorem tailIntegral_lt_of_cutoff (hint : Integrable (fun v => v) μ) {d s₀ s : ℝ} (hd : 0 < d)
    (hcut : tailIntegral μ s₀ = d * s₀) (hs : s₀ < s) : tailIntegral μ s < d * s :=
  calc tailIntegral μ s ≤ tailIntegral μ s₀ := tailIntegral_antitone μ hint hs.le
    _ = d * s₀ := hcut
    _ < d * s := mul_lt_mul_of_pos_left hs hd

theorem survival_pos_of_tailIntegral_pos {s : ℝ} (hL : 0 < tailIntegral μ s) :
    0 < survival μ s := by
  by_contra hneg
  push Not at hneg
  have hzero : survival μ s = 0 := le_antisymm hneg (survival_nonneg μ s)
  have hnull : μ (Ioi s) = 0 := by
    unfold survival at hzero
    rwa [measureReal_eq_zero_iff] at hzero
  have hae : ∀ᵐ v ∂μ, max (v - s) 0 = 0 := by
    rw [ae_iff]
    apply measure_mono_null _ hnull
    intro v hv
    simp only [mem_setOf_eq] at hv
    rw [mem_Ioi]
    by_contra hvs
    push Not at hvs
    exact hv (max_eq_right (by linarith))
  have hL0 : tailIntegral μ s = 0 := by
    unfold tailIntegral
    rw [integral_congr_ae hae]
    simp
  linarith

end Survival

end FixedPrice
