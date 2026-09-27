import FixedPrice.BuyerTail

/-! The price density of Lemma 9.1 in unnormalized coordinates. For a cutoff `s₀` with
`L(s₀) = d s₀`, the normalized control `h(t) = H(s₀(1-t))` has state `L(s₀(1-t))/s₀`, and the
price density `q(z) = β [H/L + (d² s₀ - K)/L²]` on `[0, s₀]` integrates to `β J_d(h)`. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- `K(z) = ∫_z^{s₀} H²`. -/
def secondTail (μ : Measure ℝ) (s₀ z : ℝ) : ℝ := ∫ u in z..s₀, (survival μ u) ^ 2

/-- The bracket `H/L + (d² s₀ - K)/L²`; the price density is `β` times it. -/
def priceBracket (μ : Measure ℝ) (d s₀ z : ℝ) : ℝ :=
  survival μ z / tailIntegral μ z + (d ^ 2 * s₀ - secondTail μ s₀ z) / (tailIntegral μ z) ^ 2

def priceDensity (β : ℝ) (μ : Measure ℝ) (d s₀ z : ℝ) : ℝ := β * priceBracket μ d s₀ z

/-- The normalized control `t ↦ H(s₀(1 - t))`. -/
def cutControl (μ : Measure ℝ) (s₀ t : ℝ) : ℝ := survival μ (s₀ * (1 - t))

/-- A cutoff of the buyer law: `L(s₀) = d s₀` with `d, s₀ > 0`. -/
structure IsCutoff (μ : Measure ℝ) (d s₀ : ℝ) : Prop where
  hd : 0 < d
  pos : 0 < s₀
  eq : tailIntegral μ s₀ = d * s₀

section Cutoff

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {d s₀ : ℝ}

theorem survival_sq_antitone : Antitone (fun u => (survival μ u) ^ 2) :=
  fun _ _ hab => pow_le_pow_left₀ (survival_nonneg μ _) (survival_antitone μ hab) 2

theorem survival_sq_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun u => (survival μ u) ^ 2) volume a b :=
  (survival_sq_antitone (μ := μ)).intervalIntegrable

theorem IsCutoff.tailIntegral_ge (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    {z : ℝ} (hz : z ≤ s₀) : d * s₀ ≤ tailIntegral μ z := by
  rw [← hc.eq]
  exact tailIntegral_antitone μ hint hz

theorem IsCutoff.tailIntegral_pos (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    {z : ℝ} (hz : z ≤ s₀) : 0 < tailIntegral μ z :=
  lt_of_lt_of_le (mul_pos hc.hd hc.pos) (hc.tailIntegral_ge hint hz)

theorem IsCutoff.survival_pos (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    {z : ℝ} (hz : z ≤ s₀) : 0 < survival μ z :=
  lt_of_lt_of_le (survival_pos_of_tailIntegral_pos μ (hc.tailIntegral_pos hint le_rfl))
    (survival_antitone μ hz)

theorem secondTail_sub {z w : ℝ} (hzw : z ≤ w) (hw : w ≤ s₀) :
    secondTail μ s₀ z - secondTail μ s₀ w = ∫ u in z..w, (survival μ u) ^ 2 := by
  unfold secondTail
  rw [← intervalIntegral.integral_add_adjacent_intervals (survival_sq_intervalIntegrable z w)
    (survival_sq_intervalIntegrable w s₀)]
  ring

omit [IsProbabilityMeasure μ] in
theorem secondTail_nonneg {z : ℝ} (hz : z ≤ s₀) : 0 ≤ secondTail μ s₀ z :=
  intervalIntegral.integral_nonneg hz (fun _ _ => sq_nonneg _)

theorem secondTail_le_length {z : ℝ} (hz : z ≤ s₀) : secondTail μ s₀ z ≤ s₀ - z := by
  unfold secondTail
  calc (∫ u in z..s₀, (survival μ u) ^ 2) ≤ ∫ _u in z..s₀, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hz (survival_sq_intervalIntegrable z s₀)
          intervalIntegrable_const
        intro u _
        exact pow_le_one₀ (survival_nonneg μ u) (survival_le_one μ u)
    _ = s₀ - z := by simp

theorem secondTail_lipschitz : LipschitzWith 1 (secondTail μ s₀) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  have key : ∀ z w : ℝ, z ≤ w → secondTail μ s₀ z - secondTail μ s₀ w ≤ w - z ∧
      0 ≤ secondTail μ s₀ z - secondTail μ s₀ w := by
    intro z w hzw
    have hsub : secondTail μ s₀ z - secondTail μ s₀ w = ∫ u in z..w, (survival μ u) ^ 2 := by
      unfold secondTail
      rw [← intervalIntegral.integral_add_adjacent_intervals (survival_sq_intervalIntegrable z w)
        (survival_sq_intervalIntegrable w s₀)]
      ring
    rw [hsub]
    constructor
    · calc (∫ u in z..w, (survival μ u) ^ 2) ≤ ∫ _u in z..w, (1 : ℝ) := by
            apply intervalIntegral.integral_mono_on hzw (survival_sq_intervalIntegrable z w)
              intervalIntegrable_const
            intro u _
            exact pow_le_one₀ (survival_nonneg μ u) (survival_le_one μ u)
        _ = w - z := by simp
    · exact intervalIntegral.integral_nonneg hzw (fun u _ => sq_nonneg _)
  rcases le_total z w with hzw | hwz
  · obtain ⟨h1, h2⟩ := key z w hzw
    rw [abs_of_nonneg h2, abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨h1, h2⟩ := key w z hwz
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem secondTail_continuous : Continuous (secondTail μ s₀) :=
  (secondTail_lipschitz (μ := μ) (s₀ := s₀)).continuous

/-- `K(z) ≤ H(z) (L(z) - d s₀)` on `[0, s₀]`. -/
theorem IsCutoff.secondTail_le (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    {z : ℝ} (hz : z ≤ s₀) :
    secondTail μ s₀ z ≤ survival μ z * (tailIntegral μ z - d * s₀) := by
  rw [← hc.eq, tailIntegral_sub μ hint hz, ← intervalIntegral.integral_const_mul]
  unfold secondTail
  apply intervalIntegral.integral_mono_on hz (survival_sq_intervalIntegrable z s₀)
  · exact (survival_antitone μ).intervalIntegrable.const_mul _
  · intro u hu
    have h1 := survival_antitone μ hu.1
    have h2 := survival_nonneg μ u
    nlinarith

theorem IsCutoff.priceBracket_nonneg (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    {z : ℝ} (hz : z ≤ s₀) : 0 ≤ priceBracket μ d s₀ z := by
  have hL := hc.tailIntegral_pos hint hz
  have hK := hc.secondTail_le hint hz
  have hH := survival_nonneg μ z
  unfold priceBracket
  rw [div_add_div _ _ (ne_of_gt hL) (ne_of_gt (pow_pos hL 2))]
  apply div_nonneg _ (mul_pos hL (pow_pos hL 2)).le
  have hds : 0 < d * s₀ := mul_pos hc.hd hc.pos
  have h1 : 0 ≤ survival μ z * tailIntegral μ z + d ^ 2 * s₀ - secondTail μ s₀ z := by
    nlinarith [hK, mul_nonneg hH hds.le, mul_pos (pow_pos hc.hd 2) hc.pos]
  nlinarith [mul_nonneg hL.le h1]

theorem IsCutoff.priceDensity_nonneg {β : ℝ} (hβ : 0 ≤ β) (hc : IsCutoff μ d s₀)
    (hint : Integrable (fun v => v) μ) {z : ℝ} (hz : z ≤ s₀) : 0 ≤ priceDensity β μ d s₀ z :=
  mul_nonneg hβ (hc.priceBracket_nonneg hint hz)

theorem measurable_priceBracket (hint : Integrable (fun v => v) μ) :
    Measurable (priceBracket μ d s₀) := by
  unfold priceBracket
  have hH := survival_measurable μ
  have hL := (tailIntegral_continuous μ hint).measurable
  have hK := (secondTail_continuous (μ := μ) (s₀ := s₀)).measurable
  exact (hH.div hL).add ((measurable_const.sub hK).div (hL.pow_const 2))

/-- The bracket is bounded on `[0, s₀]`, hence integrable there. -/
theorem IsCutoff.priceBracket_intervalIntegrable (hc : IsCutoff μ d s₀)
    (hint : Integrable (fun v => v) μ) :
    IntervalIntegrable (priceBracket μ d s₀) volume 0 s₀ := by
  have hds : 0 < d * s₀ := mul_pos hc.hd hc.pos
  set M : ℝ := 1 / (d * s₀) + (d ^ 2 * s₀ + s₀) / (d * s₀) ^ 2 with hM
  rw [intervalIntegrable_iff, uIoc_of_le hc.pos.le]
  apply Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
    (measurable_priceBracket hint).aestronglyMeasurable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with z hz
  have hL := hc.tailIntegral_ge hint hz.2
  have hLpos := hc.tailIntegral_pos hint hz.2
  have hK0 := secondTail_nonneg (μ := μ) hz.2
  have hK1 := secondTail_le_length (μ := μ) hz.2
  rw [Real.norm_eq_abs, abs_of_nonneg (hc.priceBracket_nonneg hint hz.2)]
  unfold priceBracket
  apply add_le_add
  · calc survival μ z / tailIntegral μ z ≤ 1 / tailIntegral μ z :=
          div_le_div_of_nonneg_right (survival_le_one μ z) hLpos.le
      _ ≤ 1 / (d * s₀) := div_le_div_of_nonneg_left zero_le_one hds hL
  · calc (d ^ 2 * s₀ - secondTail μ s₀ z) / (tailIntegral μ z) ^ 2
        ≤ (d ^ 2 * s₀ + s₀) / (tailIntegral μ z) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (pow_pos hLpos 2).le
          linarith [hz.1]
      _ ≤ (d ^ 2 * s₀ + s₀) / (d * s₀) ^ 2 := by
          apply div_le_div_of_nonneg_left
            (add_nonneg (mul_nonneg (sq_nonneg d) hc.pos.le) hc.pos.le) (pow_pos hds 2)
          exact pow_le_pow_left₀ hds.le hL 2

/-! ### The normalized control -/

theorem cutControl_measurable : Measurable (cutControl μ s₀) :=
  (survival_measurable μ).comp (measurable_const.mul (measurable_const.sub measurable_id))

theorem cutControl_mem_Icc (t : ℝ) : cutControl μ s₀ t ∈ Icc (0 : ℝ) 1 :=
  ⟨survival_nonneg μ _, survival_le_one μ _⟩

theorem cutControl_aestronglyMeasurable :
    AEStronglyMeasurable (cutControl μ s₀) (volume.restrict (Icc 0 1)) :=
  (cutControl_measurable (μ := μ) (s₀ := s₀)).aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
theorem cutControl_eq (t : ℝ) : cutControl μ s₀ t = survival μ (s₀ - s₀ * t) := by
  unfold cutControl
  rw [mul_sub, mul_one]

theorem IsCutoff.state_cutControl (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    state d (cutControl μ s₀) t = tailIntegral μ (s₀ * (1 - t)) / s₀ := by
  have hs₀ := hc.pos
  unfold state
  simp_rw [cutControl_eq]
  rw [intervalIntegral.integral_comp_sub_mul (survival μ) (ne_of_gt hs₀) s₀]
  simp only [mul_zero, sub_zero, smul_eq_mul]
  have hle : s₀ - s₀ * t ≤ s₀ := by nlinarith [ht.1]
  rw [← tailIntegral_sub μ hint hle, hc.eq, show s₀ * (1 - t) = s₀ - s₀ * t by ring]
  field_simp
  try ring

theorem IsCutoff.secondMoment_cutControl (hc : IsCutoff μ d s₀) {t : ℝ} :
    secondMoment (cutControl μ s₀) t = secondTail μ s₀ (s₀ * (1 - t)) / s₀ := by
  have hs₀ := hc.pos
  unfold secondMoment secondTail
  simp_rw [cutControl_eq]
  rw [intervalIntegral.integral_comp_sub_mul (fun u => (survival μ u) ^ 2) (ne_of_gt hs₀) s₀]
  simp only [mul_zero, sub_zero, smul_eq_mul, mul_sub, mul_one]
  try field_simp

/-- The objective of the normalized control is the integral of the price bracket. -/
theorem IsCutoff.objective_cutControl (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ) :
    objective d (cutControl μ s₀) = ∫ z in (0 : ℝ)..s₀, priceBracket μ d s₀ z := by
  have hs₀ := hc.pos
  unfold objective
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
      cutControl μ s₀ t / state d (cutControl μ s₀) t +
        (d ^ 2 - secondMoment (cutControl μ s₀) t) / state d (cutControl μ s₀) t ^ 2 =
      s₀ * priceBracket μ d s₀ (s₀ - s₀ * t) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one] at ht
    rw [hc.state_cutControl hint ht', hc.secondMoment_cutControl, cutControl_eq]
    have hz : s₀ * (1 - t) ≤ s₀ := by nlinarith [ht'.1]
    have hL := hc.tailIntegral_pos hint hz
    unfold priceBracket
    rw [mul_sub, mul_one] at hL ⊢
    field_simp
    try ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_mul (priceBracket μ d s₀) (ne_of_gt hs₀) s₀]
  simp only [mul_zero, sub_zero, mul_one, sub_self, smul_eq_mul]
  try field_simp

theorem IsCutoff.priceDensity_integral (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    (β : ℝ) :
    (∫ z in (0 : ℝ)..s₀, priceDensity β μ d s₀ z) = β * objective d (cutControl μ s₀) := by
  unfold priceDensity
  rw [intervalIntegral.integral_const_mul, hc.objective_cutControl hint]

end Cutoff

end FixedPrice
