import FixedPrice.PricingIdentity

/-! Lemma 9.1 (pricing from the variational bound) and the guarantee direction of Theorem A.
Given `β sup J_d ≤ 1`, every independent pair of nonnegative finite-mean value laws admits a
posted price whose expected gains from trade are at least `β G - β d M`. With `d = τ(C_*)` and
`β = 1/S(C_*)` this is the welfare guarantee `M + Γ(z) ≥ β_* (M + G)`. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- Expected gains from trade at the posted price `z`, inclusive rule `V_s ≤ z ≤ V_b`. -/
def gain (μs μb : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ s, ∫ b, (if s ≤ z ∧ z ≤ b then b - s else 0) ∂μb ∂μs

/-- Initial seller welfare `E V_s`. -/
def sellerMean (μs : Measure ℝ) : ℝ := ∫ s, s ∂μs

/-- First-best gains from trade `E (V_b - V_s)_+`. -/
def gainsFromTrade (μs μb : Measure ℝ) : ℝ := ∫ s, ∫ b, max (b - s) 0 ∂μb ∂μs

/-- The lower bound for the gain obtained by integrating the buyer first. -/
def lowerGain (μs μb : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ s, (if s < z then tailIntegral μb z + (z - s) * survival μb z else 0) ∂μs

theorem integral_const_prob {μ : Measure ℝ} [IsProbabilityMeasure μ] (c : ℝ) :
    (∫ _s, c ∂μ) = c := by
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

theorem measurable_tradeGain (z : ℝ) :
    Measurable (fun p : ℝ × ℝ => if p.1 ≤ z ∧ z ≤ p.2 then p.2 - p.1 else 0) := by
  apply Measurable.ite _ (measurable_snd.sub measurable_fst) measurable_const
  rw [setOf_and]
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_const measurable_snd)

section Gain

variable (μs μb : Measure ℝ) [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

omit [IsProbabilityMeasure μs] [IsProbabilityMeasure μb] in
theorem gain_nonneg (z : ℝ) : 0 ≤ gain μs μb z := by
  apply integral_nonneg
  intro s
  apply integral_nonneg
  intro b
  simp only [Pi.zero_apply]
  split_ifs with h
  · linarith [h.1, h.2]
  · exact le_rfl

theorem integrable_tradeGain (hbint : Integrable (fun b => b) μb) (s z : ℝ) :
    Integrable (fun b => if s ≤ z ∧ z ≤ b then b - s else 0) μb := by
  apply Integrable.mono' (hbint.abs.add (integrable_const |s|))
  · exact ((measurable_tradeGain z).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards with b
    simp only [Real.norm_eq_abs, Pi.add_apply]
    split_ifs
    · exact abs_sub b s
    · simp only [abs_zero]
      positivity

/-- The per-seller lower bound: for `s < z`, the buyer integral dominates
`L(z) + (z - s) H(z)`. -/
theorem tailIntegral_add_le_integral_gain (hbint : Integrable (fun b => b) μb)
    {s z : ℝ} (hsz : s < z) :
    tailIntegral μb z + (z - s) * survival μb z ≤
      ∫ b, (if s ≤ z ∧ z ≤ b then b - s else 0) ∂μb := by
  have hpt : ∀ b, max (b - z) 0 + (z - s) * (Ioi z).indicator (1 : ℝ → ℝ) b ≤
      (if s ≤ z ∧ z ≤ b then b - s else 0) := by
    intro b
    by_cases hb : z < b
    · rw [if_pos ⟨hsz.le, hb.le⟩, Set.indicator_of_mem (mem_Ioi.mpr hb),
        max_eq_left (by linarith)]
      simp only [Pi.one_apply, mul_one]
      linarith
    · rw [Set.indicator_of_notMem (by simpa using hb), max_eq_right (by linarith)]
      simp only [mul_zero, add_zero]
      split_ifs with h
      · linarith [h.2]
      · exact le_rfl
  have hind : Integrable (fun b => (z - s) * (Ioi z).indicator (1 : ℝ → ℝ) b) μb :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi).const_mul _
  calc tailIntegral μb z + (z - s) * survival μb z
      = ∫ b, (max (b - z) 0 + (z - s) * (Ioi z).indicator (1 : ℝ → ℝ) b) ∂μb := by
        rw [integral_add (integrable_max_sub μb hbint z) hind, integral_const_mul,
          integral_indicator_one measurableSet_Ioi]
        rfl
    _ ≤ _ := integral_mono ((integrable_max_sub μb hbint z).add hind)
        (integrable_tradeGain μb hbint s z) hpt

/-- The inner gain, as a function of the seller value, is integrable. -/
theorem integrable_inner_gain (hbint : Integrable (fun b => b) μb)
    (hsint : Integrable (fun s => s) μs) (z : ℝ) :
    Integrable (fun s => ∫ b, (if s ≤ z ∧ z ≤ b then b - s else 0) ∂μb) μs := by
  have hmeas : StronglyMeasurable (fun s => ∫ b, (if s ≤ z ∧ z ≤ b then b - s else 0) ∂μb) :=
    (measurable_tradeGain z).stronglyMeasurable.integral_prod_right'
  apply Integrable.mono' ((integrable_const (∫ b, |b| ∂μb)).add hsint.abs)
  · exact hmeas.aestronglyMeasurable
  · filter_upwards with s
    simp only [Pi.add_apply, Real.norm_eq_abs]
    calc |∫ b, (if s ≤ z ∧ z ≤ b then b - s else 0) ∂μb|
        ≤ ∫ b, (|b| + |s|) ∂μb := by
          rw [← Real.norm_eq_abs]
          apply norm_integral_le_of_norm_le (hbint.abs.add (integrable_const |s|))
          filter_upwards with b
          simp only [Real.norm_eq_abs, Pi.add_apply]
          split_ifs
          · exact abs_sub b s
          · simp only [abs_zero]
            positivity
      _ = (∫ b, |b| ∂μb) + |s| := by
          rw [integral_add hbint.abs (integrable_const _), integral_const_prob]

theorem lowerGain_le_gain (hbint : Integrable (fun b => b) μb)
    (hsint : Integrable (fun s => s) μs) (z : ℝ) : lowerGain μs μb z ≤ gain μs μb z := by
  unfold lowerGain gain
  apply integral_mono_of_nonneg
  · filter_upwards with s
    simp only [Pi.zero_apply]
    split_ifs with h
    · have h1 := tailIntegral_nonneg μb z
      have h2 := survival_nonneg μb z
      have h3 : 0 ≤ (z - s) * survival μb z := mul_nonneg (by linarith) h2
      linarith
    · exact le_rfl
  · exact integrable_inner_gain μs μb hbint hsint z
  · filter_upwards with s
    split_ifs with h
    · exact tailIntegral_add_le_integral_gain μb hbint h
    · apply integral_nonneg
      intro b
      simp only [Pi.zero_apply]
      split_ifs with h'
      · linarith [h'.1, h'.2]
      · exact le_rfl

theorem measurable_lowerGain_pair (hbint : Integrable (fun b => b) μb) :
    Measurable (fun p : ℝ × ℝ =>
      if p.2 < p.1 then tailIntegral μb p.1 + (p.1 - p.2) * survival μb p.1 else 0) := by
  apply Measurable.ite (measurableSet_lt measurable_snd measurable_fst) _ measurable_const
  exact ((tailIntegral_continuous μb hbint).measurable.comp measurable_fst).add
    ((measurable_fst.sub measurable_snd).mul ((survival_measurable μb).comp measurable_fst))

theorem stronglyMeasurable_lowerGain (hbint : Integrable (fun b => b) μb) :
    StronglyMeasurable (lowerGain μs μb) :=
  (measurable_lowerGain_pair μb hbint).stronglyMeasurable.integral_prod_right'

/-- `|L(z) + (z - s) H(z)| ≤ L(0) + 2|z| + |s|`, uniformly. -/
theorem abs_lowerGain_integrand_le (hbint : Integrable (fun b => b) μb) (z s : ℝ) :
    |if s < z then tailIntegral μb z + (z - s) * survival μb z else 0| ≤
      tailIntegral μb 0 + 2 * |z| + |s| := by
  have hL0 := tailIntegral_nonneg μb 0
  split_ifs with h
  · have hLz : tailIntegral μb z - tailIntegral μb 0 ≤ |z| := by
      have := (tailIntegral_lipschitz μb hbint).dist_le_mul z 0
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, sub_zero] at this
      exact (le_abs_self _).trans this
    have hH0 := survival_nonneg μb z
    have hH1 := survival_le_one μb z
    have hzs : (z - s) * survival μb z ≤ z - s := mul_le_of_le_one_right (by linarith) hH1
    have hnn : 0 ≤ (z - s) * survival μb z := mul_nonneg (by linarith) hH0
    rw [abs_of_nonneg (by linarith [tailIntegral_nonneg μb z])]
    linarith [le_abs_self z, neg_le_abs s]
  · simp only [abs_zero]
    linarith [abs_nonneg z, abs_nonneg s]

theorem abs_lowerGain_le (hbint : Integrable (fun b => b) μb)
    (hsint : Integrable (fun s => s) μs) (z : ℝ) :
    |lowerGain μs μb z| ≤ tailIntegral μb 0 + 2 * |z| + ∫ s, |s| ∂μs := by
  unfold lowerGain
  rw [← Real.norm_eq_abs]
  calc ‖∫ s, (if s < z then tailIntegral μb z + (z - s) * survival μb z else 0) ∂μs‖
      ≤ ∫ s, (tailIntegral μb 0 + 2 * |z| + |s|) ∂μs := by
        apply norm_integral_le_of_norm_le ((integrable_const _).add hsint.abs)
        filter_upwards with s
        simp only [Real.norm_eq_abs, Pi.add_apply]
        exact abs_lowerGain_integrand_le μb hbint z s
    _ = tailIntegral μb 0 + 2 * |z| + ∫ s, |s| ∂μs := by
        rw [integral_add (integrable_const _) hsint.abs, integral_const_prob]

end Gain

section Fubini

variable {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb] {d s₀ β : ℝ}

/-- The price density is integrable on the cutoff interval, as a set integral. -/
theorem IsCutoff.priceDensity_integrableOn (hc : IsCutoff μb d s₀)
    (hbint : Integrable (fun b => b) μb) :
    IntegrableOn (priceDensity β μb d s₀) (Ioc 0 s₀) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hc.pos.le]
  exact hc.priceDensity_intervalIntegrable hbint

theorem IsCutoff.priceDensity_mul_abs_integrableOn (hc : IsCutoff μb d s₀)
    (hbint : Integrable (fun b => b) μb) :
    IntegrableOn (fun z => |priceDensity β μb d s₀ z| * (tailIntegral μb 0 + 2 * |z|))
      (Ioc 0 s₀) := by
  have hq := (hc.priceDensity_integrableOn (β := β) hbint).norm
  apply Integrable.mono' (hq.const_mul (tailIntegral μb 0 + 2 * s₀))
  · exact ((measurable_priceDensity hbint).norm.mul
      (measurable_const.add (measurable_const.mul measurable_id.norm))).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with z hz
    simp only [Real.norm_eq_abs]
    have hL0 := tailIntegral_nonneg μb 0
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (by linarith [abs_nonneg z]))]
    have hz' : |z| ≤ s₀ := by rw [abs_of_pos hz.1]; exact hz.2
    nlinarith [abs_nonneg (priceDensity β μb d s₀ z)]

/-- The Fubini step: integrating the price density against the lower gain equals the
seller expectation of the per-seller identity. -/
theorem IsCutoff.integral_priceDensity_lowerGain (hc : IsCutoff μb d s₀)
    (hbint : Integrable (fun b => b) μb) (hsint : Integrable (fun s => s) μs)
    (hs0 : ∀ᵐ s ∂μs, 0 ≤ s) :
    (∫ z in Ioc 0 s₀, priceDensity β μb d s₀ z * lowerGain μs μb z) =
      ∫ s, (if s ≤ s₀ then β * (tailIntegral μb s - d * s) else 0) ∂μs := by
  set q := priceDensity β μb d s₀ with hq
  set f : ℝ → ℝ → ℝ := fun z s =>
    q z * (if s < z then tailIntegral μb z + (z - s) * survival μb z else 0) with hf
  have hqInt := hc.priceDensity_integrableOn (β := β) hbint
  have hprod : Integrable (uncurry f) ((volume.restrict (Ioc 0 s₀)).prod μs) := by
    have h1 := (hc.priceDensity_mul_abs_integrableOn (β := β) hbint).mul_prod
      (integrable_const (1 : ℝ) (μ := μs))
    have h2 := hqInt.norm.mul_prod hsint.norm
    apply Integrable.mono' (h1.add h2)
    · have hm : Measurable (uncurry f) := by
        simp only [hf]
        exact ((measurable_priceDensity hbint).comp measurable_fst).mul
          (measurable_lowerGain_pair μb hbint)
      exact hm.aestronglyMeasurable
    · filter_upwards with p
      simp only [uncurry, hf, Pi.add_apply, Real.norm_eq_abs, abs_mul, mul_one]
      have hb := abs_lowerGain_integrand_le μb hbint p.1 p.2
      have hq0 := abs_nonneg (q p.1)
      nlinarith [mul_le_mul_of_nonneg_left hb hq0]
  have hswap := integral_integral_swap hprod
  have hleft : (∫ z in Ioc 0 s₀, ∫ s, f z s ∂μs) =
      ∫ z in Ioc 0 s₀, q z * lowerGain μs μb z := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z _
    simp only [hf]
    rw [integral_const_mul]
    rfl
  have hright : (∫ s, (∫ z in Ioc 0 s₀, f z s) ∂μs) =
      ∫ s, (if s ≤ s₀ then β * (tailIntegral μb s - d * s) else 0) ∂μs := by
    apply integral_congr_ae
    filter_upwards [hs0] with s hs
    have hind : (fun z => f z s) =
        (Ioi s).indicator (fun z => q z * (tailIntegral μb z + (z - s) * survival μb z)) := by
      funext z
      simp only [hf, Set.indicator_apply, mem_Ioi]
      split_ifs <;> simp
    rw [hind, setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi, sup_eq_right.mpr hs]
    split_ifs with hss
    · rw [← intervalIntegral.integral_of_le hss]
      exact hc.seller_identity hbint ⟨hs, hss⟩
    · push Not at hss
      rw [Ioc_eq_empty (not_lt.mpr hss.le), Measure.restrict_empty, integral_zero_measure]
  rw [← hleft, hswap, hright]

end Fubini

section Averaging

variable {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb] {d s₀ β : ℝ}

/-- A density of mass at most one that averages `Λ` to at least `T > 0` finds a point with
`Λ ≥ T`. -/
theorem IsCutoff.exists_lowerGain_ge (hc : IsCutoff μb d s₀) (hβ : 0 ≤ β)
    (hbint : Integrable (fun b => b) μb) (hsint : Integrable (fun s => s) μs) {T : ℝ}
    (hT : 0 < T) (hq1 : (∫ z in Ioc 0 s₀, priceDensity β μb d s₀ z) ≤ 1)
    (hint : T ≤ ∫ z in Ioc 0 s₀, priceDensity β μb d s₀ z * lowerGain μs μb z) :
    ∃ z ∈ Ioc (0 : ℝ) s₀, T ≤ lowerGain μs μb z := by
  by_contra hcon
  push Not at hcon
  set q := priceDensity β μb d s₀ with hq
  set Λ := lowerGain μs μb with hΛ
  have hqInt := hc.priceDensity_integrableOn (β := β) hbint
  have hqnn : ∀ᵐ z ∂(volume.restrict (Ioc 0 s₀)), 0 ≤ q z := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with z hz
    exact hc.priceDensity_nonneg hβ hbint hz.2
  have hΛbdd : IntegrableOn (fun z => q z * Λ z) (Ioc 0 s₀) := by
    apply Integrable.mono' (hqInt.norm.const_mul (tailIntegral μb 0 + 2 * s₀ + ∫ s, |s| ∂μs))
    · exact ((measurable_priceDensity hbint).mul
        (stronglyMeasurable_lowerGain μs μb hbint).measurable).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with z hz
      simp only [Real.norm_eq_abs, abs_mul]
      have hb := abs_lowerGain_le μs μb hbint hsint z
      have hz' : |z| ≤ s₀ := by rw [abs_of_pos hz.1]; exact hz.2
      have hq0 := abs_nonneg (q z)
      rw [mul_comm (tailIntegral μb 0 + 2 * s₀ + ∫ s, |s| ∂μs)]
      apply mul_le_mul_of_nonneg_left _ hq0
      linarith
  have hqT : IntegrableOn (fun z => q z * T) (Ioc 0 s₀) := hqInt.mul_const T
  have h2 : (∫ z in Ioc 0 s₀, q z * T) = T * ∫ z in Ioc 0 s₀, q z := by
    rw [integral_mul_const, mul_comm]
  have h3 : T * (∫ z in Ioc 0 s₀, q z) ≤ T := by
    have := mul_le_mul_of_nonneg_left hq1 hT.le
    linarith
  -- the defect q (T - Λ) has zero integral, so q vanishes a.e.
  have hdef : IntegrableOn (fun z => q z * (T - Λ z)) (Ioc 0 s₀) := by
    have := hqT.sub hΛbdd
    refine this.congr_fun ?_ measurableSet_Ioc
    intro z _
    simp only [Pi.sub_apply]
    ring
  have hmem : ∀ᵐ z ∂(volume.restrict (Ioc 0 s₀)), z ∈ Ioc 0 s₀ :=
    ae_restrict_mem measurableSet_Ioc
  have hdef_nn : 0 ≤ᵐ[volume.restrict (Ioc 0 s₀)] fun z => q z * (T - Λ z) := by
    rw [Filter.EventuallyLE]
    filter_upwards [hqnn, hmem] with z hqz hz
    show 0 ≤ q z * (T - Λ z)
    exact mul_nonneg hqz (by linarith [hcon z hz])
  have hdef_int : (∫ z in Ioc 0 s₀, q z * (T - Λ z)) = 0 := by
    have hsplit : (∫ z in Ioc 0 s₀, q z * (T - Λ z)) =
        (∫ z in Ioc 0 s₀, q z * T) - ∫ z in Ioc 0 s₀, q z * Λ z := by
      rw [← integral_sub hqT hΛbdd]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro z _
      ring
    apply le_antisymm
    · linarith
    · exact integral_nonneg_of_ae hdef_nn
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hdef_nn hdef).mp hdef_int
  have hqzero : (fun z => q z * Λ z) =ᵐ[volume.restrict (Ioc 0 s₀)] fun _ => (0 : ℝ) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hzero ⊢
    filter_upwards [hzero] with z hz hmem
    have h := hz hmem
    simp only [Pi.zero_apply] at h
    have hpos : 0 < T - Λ z := by linarith [hcon z hmem]
    have hq0 : q z = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hpos)
    simp [hq0]
  have : (∫ z in Ioc 0 s₀, q z * Λ z) = 0 := by
    rw [integral_congr_ae hqzero]
    simp
  linarith

end Averaging

section Main

variable {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

theorem integrable_tailIntegral_seller (hbint : Integrable (fun b => b) μb)
    (hs0 : ∀ᵐ s ∂μs, 0 ≤ s) : Integrable (fun s => tailIntegral μb s) μs := by
  apply Integrable.mono' (integrable_const (tailIntegral μb 0))
  · exact (tailIntegral_continuous μb hbint).measurable.aestronglyMeasurable
  · filter_upwards [hs0] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (tailIntegral_nonneg μb s)]
    exact tailIntegral_antitone μb hbint hs

/-- The pricing step at a fixed cutoff: a price density of mass `β J_d(H(s₀(1-·))) ≤ 1`
certifies a price with gain at least `β G - β d M` whenever this target is positive. -/
theorem exists_price_of_cutoff {β d s₀ : ℝ} (hβ : 0 ≤ β) (hc : IsCutoff μb d s₀)
    (hJ : β * objective d (cutControl μb s₀) ≤ 1)
    (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb)
    (hT : 0 < β * gainsFromTrade μs μb - β * d * sellerMean μs) :
    ∃ z : ℝ, 0 ≤ z ∧
      β * gainsFromTrade μs μb - β * d * sellerMean μs ≤ gain μs μb z := by
  set T := β * gainsFromTrade μs μb - β * d * sellerMean μs with hT_def
  have hd := hc.hd
  have hLint := integrable_tailIntegral_seller hbint hs0
  have hq1 : (∫ z in Ioc 0 s₀, priceDensity β μb d s₀ z) ≤ 1 := by
    rw [← intervalIntegral.integral_of_le hc.pos.le, hc.priceDensity_integral hbint β]
    exact hJ
  have hT1 : T ≤ ∫ s, (if s ≤ s₀ then β * (tailIntegral μb s - d * s) else 0) ∂μs := by
    have hTeq : T = ∫ s, β * (tailIntegral μb s - d * s) ∂μs := by
      rw [hT_def, integral_const_mul, integral_sub hLint (hsint.const_mul d), integral_const_mul]
      simp only [gainsFromTrade, sellerMean, tailIntegral]
      ring
    rw [hTeq]
    apply integral_mono_ae ((hLint.sub (hsint.const_mul d)).const_mul β)
    · apply Integrable.mono' ((hLint.sub (hsint.const_mul d)).const_mul β).norm
      · apply Measurable.aestronglyMeasurable
        apply Measurable.ite (measurableSet_le measurable_id measurable_const) _ measurable_const
        exact measurable_const.mul
          ((tailIntegral_continuous μb hbint).measurable.sub (measurable_const.mul measurable_id))
      · filter_upwards with s
        simp only [Real.norm_eq_abs, Pi.sub_apply]
        split_ifs
        · exact le_rfl
        · simp only [abs_zero]
          exact abs_nonneg _
    · filter_upwards with s
      simp only [Pi.sub_apply]
      split_ifs with hss
      · exact le_rfl
      · push Not at hss
        have := tailIntegral_lt_of_cutoff μb hbint hd hc.eq hss
        nlinarith
  rw [← hc.integral_priceDensity_lowerGain hbint hsint hs0] at hT1
  obtain ⟨z, hz, hΛ⟩ := hc.exists_lowerGain_ge hβ hbint hsint hT hq1 hT1
  exact ⟨z, hz.1.le, hΛ.trans (lowerGain_le_gain μs μb hbint hsint z)⟩

/-- Positive first-best gains force a positive buyer mean. -/
theorem tailIntegral_zero_pos_of_gainsFromTrade_pos (hbint : Integrable (fun b => b) μb)
    (hs0 : ∀ᵐ s ∂μs, 0 ≤ s) (hG : 0 < gainsFromTrade μs μb) : 0 < tailIntegral μb 0 := by
  have hLint := integrable_tailIntegral_seller hbint hs0
  by_contra hneg
  push Not at hneg
  have h1 : gainsFromTrade μs μb ≤ ∫ _s, tailIntegral μb 0 ∂μs := by
    show (∫ s, tailIntegral μb s ∂μs) ≤ _
    apply integral_mono_ae hLint (integrable_const _)
    filter_upwards [hs0] with s hs
    exact tailIntegral_antitone μb hbint hs
  rw [integral_const_prob] at h1
  linarith

/-- **Lemma 9.1 (pricing from the variational bound).** -/
theorem exists_price_of_variational_bound {β d : ℝ} (hβ : 0 ≤ β) (hd : 0 < d)
    (hJ : ∀ h : ℝ → ℝ, AEStronglyMeasurable h (volume.restrict (Icc 0 1)) →
      (∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) → β * objective d h ≤ 1)
    (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb) :
    ∃ z : ℝ, 0 ≤ z ∧
      β * gainsFromTrade μs μb - β * d * sellerMean μs ≤ gain μs μb z := by
  set T := β * gainsFromTrade μs μb - β * d * sellerMean μs with hT_def
  by_cases hT : T ≤ 0
  · exact ⟨0, le_rfl, hT.trans (gain_nonneg μs μb 0)⟩
  push Not at hT
  have hM : 0 ≤ sellerMean μs := integral_nonneg_of_ae hs0
  -- the buyer has positive mean, so the cutoff exists
  have hL0 : 0 < tailIntegral μb 0 := by
    apply tailIntegral_zero_pos_of_gainsFromTrade_pos hbint hs0
    by_contra hG
    push Not at hG
    have : T ≤ 0 := by
      rw [hT_def]
      nlinarith [mul_nonneg hβ (neg_nonneg.mpr hG), mul_nonneg (mul_nonneg hβ hd.le) hM]
    linarith
  obtain ⟨s₀, hs₀, hcut⟩ := exists_cutoff μb hbint hd hL0
  have hc : IsCutoff μb d s₀ := ⟨hd, hs₀, hcut⟩
  exact exists_price_of_cutoff hβ hc
    (hJ _ cutControl_aestronglyMeasurable (fun t _ => cutControl_mem_Icc t)) hs0 hsint hbint hT

theorem initialState_pos {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) : 0 < initialState C := by
  unfold initialState
  apply mul_pos (div_pos (pow_pos (by linarith [hC.1]) 2) (by linarith [hC.2])) (Real.exp_pos _)

/-- **Theorem A, guarantee direction.** For the maximizing curvature `C_*` with
`S(C_*) = 1 + τ(C_*)`, every independent pair of nonnegative finite-mean value laws admits a
posted price whose welfare is at least `β_* = 1/S(C_*)` times first-best welfare. -/
theorem theoremA_guarantee {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C)
    (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb) :
    ∃ z : ℝ, 0 ≤ z ∧
      (optimalValue C)⁻¹ * (sellerMean μs + gainsFromTrade μs μb) ≤
        sellerMean μs + gain μs μb z := by
  have hd : 0 < initialState C := initialState_pos hC
  have hS : 0 < optimalValue C := by linarith [one_le_optimalValue hC]
  set β := (optimalValue C)⁻¹ with hβ_def
  have hβ : 0 ≤ β := (inv_pos.mpr hS).le
  have hJ : ∀ h : ℝ → ℝ, AEStronglyMeasurable h (volume.restrict (Icc 0 1)) →
      (∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) → β * objective (initialState C) h ≤ 1 := by
    intro h hmeas hbox
    have := objective_le_optimalValue hd hC rfl hmeas hbox
    rw [hβ_def, inv_mul_le_iff₀ hS, mul_one]
    exact this
  obtain ⟨z, hz, hgain⟩ := exists_price_of_variational_bound hβ hd hJ hs0 hsint hbint
  refine ⟨z, hz, ?_⟩
  have hβS : β * optimalValue C = 1 := by rw [hβ_def]; exact inv_mul_cancel₀ hS.ne'
  have hβS' : β * (1 + initialState C) = 1 := by rw [← hroot]; exact hβS
  have hβd : β * initialState C = 1 - β := by linear_combination hβS'
  linear_combination hgain + sellerMean μs * hβd

end Main

end FixedPrice
