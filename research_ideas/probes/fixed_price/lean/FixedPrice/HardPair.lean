import FixedPrice.HardSeller

/-! Lemma 9.2 (bounded hard pairs). For the buyer and the equalizing seller built from `H`,
with `T = T(1)` and `J = J_d(H(1 - ·))`,
`M = 1 - d² T`, `Γ(z) ≤ d + η d² T` at every price, and `G = d J + d M`
(equivalently `G = d + d J - d³ T`), which is (40). The gain at a price is computed from the
general formula `Γ(z) = L_b(z) F_s(z) + μ_b[z, ∞) E(z - V_s)_+`. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

section GainFormula

variable {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

theorem integrable_max_sub_left (hsint : Integrable (fun s => s) μs) (z : ℝ) :
    Integrable (fun s => max (z - s) 0) μs := by
  apply Integrable.mono' ((integrable_const |z|).add hsint.norm)
  · exact ((continuous_const.sub continuous_id).max continuous_const).aestronglyMeasurable
  · filter_upwards with s
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (le_max_right _ _)]
    rcases le_or_gt (z - s) 0 with h | h
    · rw [max_eq_right h]; positivity
    · rw [max_eq_left h.le]
      linarith [abs_nonneg z, abs_nonneg s, le_abs_self z, neg_abs_le s]

/-- `Γ(z) = L_b(z) μ_s(-∞, z] + μ_b[z, ∞) E(z - V_s)_+`. -/
theorem gain_eq_formula (hsint : Integrable (fun s => s) μs)
    (hbint : Integrable (fun b => b) μb) (z : ℝ) :
    gain μs μb z = tailIntegral μb z * μs.real (Iic z) +
      μb.real (Ici z) * ∫ s, max (z - s) 0 ∂μs := by
  have hinner : ∀ s, (∫ b, (if s ≤ z ∧ z ≤ b then b - s else 0) ∂μb) =
      tailIntegral μb z * (Iic z).indicator (fun _ => (1 : ℝ)) s +
        μb.real (Ici z) * max (z - s) 0 := by
    intro s
    by_cases hs : s ≤ z
    · have hpt : (fun b => if s ≤ z ∧ z ≤ b then b - s else 0) =
          fun b => max (b - z) 0 + (z - s) * (Ici z).indicator (fun _ => (1 : ℝ)) b := by
        funext b
        by_cases hb : z ≤ b
        · rw [if_pos ⟨hs, hb⟩, max_eq_left (sub_nonneg.mpr hb),
            Set.indicator_of_mem (mem_Ici.mpr hb)]
          ring
        · push Not at hb
          rw [if_neg (fun h => absurd h.2 (not_le.mpr hb)), max_eq_right (by linarith),
            Set.indicator_of_notMem (by simpa using hb)]
          ring
      rw [hpt, integral_add (integrable_max_sub μb hbint z)
        (((integrable_const _).indicator measurableSet_Ici).const_mul _), integral_const_mul,
        integral_indicator_const _ measurableSet_Ici, Set.indicator_of_mem (mem_Iic.mpr hs),
        max_eq_left (sub_nonneg.mpr hs)]
      simp only [smul_eq_mul, mul_one]
      unfold tailIntegral
      ring
    · push Not at hs
      have h0 : (fun b => if s ≤ z ∧ z ≤ b then b - s else (0 : ℝ)) = fun _ => 0 := by
        funext b
        rw [if_neg (fun h => absurd h.1 (not_le.mpr hs))]
      rw [h0, integral_zero, Set.indicator_of_notMem (by simpa using hs),
        max_eq_right (by linarith)]
      ring
  unfold gain
  simp_rw [hinner]
  rw [integral_add (((integrable_const _).indicator measurableSet_Iic).const_mul _)
    ((integrable_max_sub_left hsint z).const_mul _), integral_const_mul, integral_const_mul,
    integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one]

omit [IsProbabilityMeasure μb] in
/-- `Λ(z) = L_b(z) μ_s(-∞, z) + H_b(z) E(z - V_s)_+`. -/
theorem lowerGain_eq_formula (hsint : Integrable (fun s => s) μs) (z : ℝ) :
    lowerGain μs μb z = tailIntegral μb z * μs.real (Iio z) +
      survival μb z * ∫ s, max (z - s) 0 ∂μs := by
  have hpt : (fun s => if s < z then tailIntegral μb z + (z - s) * survival μb z else 0) =
      fun s => tailIntegral μb z * (Iio z).indicator (fun _ => (1 : ℝ)) s +
        survival μb z * max (z - s) 0 := by
    funext s
    by_cases hs : s < z
    · rw [if_pos hs, Set.indicator_of_mem (mem_Iio.mpr hs), max_eq_left (by linarith)]
      ring
    · push Not at hs
      rw [if_neg (not_lt.mpr hs), Set.indicator_of_notMem (by simpa using hs),
        max_eq_right (by linarith)]
      ring
  unfold lowerGain
  rw [hpt, integral_add (((integrable_const _).indicator measurableSet_Iio).const_mul _)
    ((integrable_max_sub_left hsint z).const_mul _), integral_const_mul, integral_const_mul,
    integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_one]

/-- `E(z - V)_+ = ∫_0^z μ(-∞, u] du` for a nonnegative law and `z ≥ 0`. -/
theorem integral_max_sub_left_eq (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) {z : ℝ} (hz : 0 ≤ z) :
    (∫ s, max (z - s) 0 ∂μs) = ∫ u in (0 : ℝ)..z, μs.real (Iic u) := by
  have hpt : (fun s => max (z - s) 0) = fun s => z - s + max (s - z) 0 := by
    funext s
    rcases le_total s z with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  have hsub := tailIntegral_sub μs hsint hz
  have h0 := tailIntegral_zero_eq μs hs0
  have hsurv : ∀ u, μs.real (Iic u) = 1 - survival μs u := by
    intro u
    unfold survival
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
    ring
  have hi1 : Integrable (fun s => z - s) μs := (integrable_const z).sub hsint
  rw [hpt, integral_add hi1 (integrable_max_sub μs hsint z),
    integral_sub (integrable_const z) hsint, integral_const_prob]
  simp_rw [hsurv]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (survival_antitone μs).intervalIntegrable, ← hsub, h0]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  unfold tailIntegral
  ring

end GainFormula

section Pair

variable {d η : ℝ} {H : ℝ → ℝ}

/-- `E(z - V_s)_+ = d L(z) T(z)` on `[0, 1]`. -/
theorem HardPairData.seller_leftTail (P : HardPairData d η H) {z : ℝ} (hz : 0 ≤ z)
    (hz1 : z ≤ 1) :
    (∫ s, max (z - s) 0 ∂P.sellerLaw) = d * tailL d H z * timeT d H z := by
  rw [integral_max_sub_left_eq P.seller_nonneg P.seller_integrable hz,
    ← P.integral_sellerFormula hz hz1]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (1 : ℝ)] with u hne hu
  rw [uIoc_of_le hz] at hu
  have hu1 : u < 1 := lt_of_le_of_ne (hu.2.trans hz1) hne
  rw [P.seller_Iic]
  simp [sellerCDF, not_lt.mpr hu.1.le, hu1]

theorem HardPairData.buyer_tail_eq_tailL (P : HardPairData d η H) {z : ℝ} (hz : 0 ≤ z)
    (hz1 : z ≤ 1) : tailIntegral P.buyerLaw z = tailL d H z :=
  P.buyer_tail_eq_of_le_one hz hz1

theorem HardPairData.isCutoff (P : HardPairData d η H) : IsCutoff P.buyerLaw d 1 :=
  ⟨P.hd, zero_lt_one, by rw [P.buyer_tail_eq_tailL zero_le_one le_rfl, tailL_one, mul_one]⟩

/-- `M = 1 - d² T(1)`. -/
theorem HardPairData.sellerMean_eq (P : HardPairData d η H) :
    sellerMean P.sellerLaw = 1 - d ^ 2 * timeT d H 1 := by
  have h := P.seller_leftTail zero_le_one le_rfl
  rw [tailL_one] at h
  have hae : (fun s => max (1 - s) 0) =ᵐ[P.sellerLaw] fun s => 1 - s := by
    filter_upwards [P.seller_ae_mem] with s hs
    exact max_eq_left (by linarith [hs.2])
  rw [integral_congr_ae hae, integral_sub (integrable_const 1) P.seller_integrable,
    integral_const_prob] at h
  unfold sellerMean
  nlinarith

theorem HardPairData.timeT_one_bounds (P : HardPairData d η H) :
    0 ≤ d ^ 2 * timeT d H 1 ∧ d ^ 2 * timeT d H 1 ≤ 1 := by
  have h1 := P.timeT_le zero_le_one le_rfl
  have h0 := P.timeT_nonneg zero_le_one
  have hd2 := pow_pos P.hd 2
  refine ⟨mul_nonneg hd2.le h0, ?_⟩
  calc d ^ 2 * timeT d H 1 ≤ d ^ 2 * (1 / d ^ 2) := mul_le_mul_of_nonneg_left h1 hd2.le
    _ = 1 := mul_one_div_cancel hd2.ne'

/-- On `[0, 1)` the gain equals `d` up to the correction `(μ_b[z,∞) - H(z)) d L T`. -/
theorem HardPairData.gain_of_mem (P : HardPairData d η H) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    gain P.sellerLaw P.buyerLaw z = d := by
  rw [gain_eq_formula P.seller_integrable P.buyer_integrable, P.seller_Iic,
    P.seller_leftTail hz hz1.le, P.buyer_tail_eq_tailL hz hz1.le]
  have hsc : sellerCDF d H z = sellerFormula d H z := by
    simp [sellerCDF, not_lt.mpr hz, hz1]
  rw [hsc]
  have hn := (P.tailL_pos hz1.le).ne'
  rcases eq_or_lt_of_le hz with h0 | h0
  · subst h0
    rw [timeT_zero, P.sellerFormula_zero]
    field_simp
    ring
  · rw [P.buyer_Ici_of_mem h0 (hz1.trans P.one_lt_buyerAtom)]
    unfold sellerFormula
    field_simp
    ring

theorem HardPairData.lowerGain_of_mem (P : HardPairData d η H) {z : ℝ} (hz : 0 < z)
    (hz1 : z < 1) : lowerGain P.sellerLaw P.buyerLaw z = d := by
  rw [lowerGain_eq_formula P.seller_integrable, P.seller_Iio_of_mem hz hz1,
    P.seller_leftTail hz.le hz1.le, P.buyer_tail_eq_tailL hz.le hz1.le,
    P.buyer_survival_eq hz.le (hz1.trans P.one_lt_buyerAtom)]
  have hn := (P.tailL_pos hz1.le).ne'
  unfold sellerFormula
  field_simp
  ring

/-- `Γ(z) ≤ d + η d² T(1)` at every price. -/
theorem HardPairData.gain_le (P : HardPairData d η H) (z : ℝ) :
    gain P.sellerLaw P.buyerLaw z ≤ d + η * (d ^ 2 * timeT d H 1) := by
  have hT := P.timeT_one_bounds
  have hbase : d ≤ d + η * (d ^ 2 * timeT d H 1) := by
    have := mul_nonneg P.hη.le hT.1
    linarith
  have hR := P.one_lt_buyerAtom
  rcases lt_or_ge z 0 with hz | hz
  · rw [gain_eq_formula P.seller_integrable P.buyer_integrable, P.seller_Iic]
    have hc : sellerCDF d H z = 0 := by simp [sellerCDF, hz]
    have hphi : (∫ s, max (z - s) 0 ∂P.sellerLaw) = 0 := by
      have hae : (fun s => max (z - s) 0) =ᵐ[P.sellerLaw] fun _ => 0 := by
        filter_upwards [P.seller_nonneg] with s hs
        exact max_eq_right (by linarith)
      rw [integral_congr_ae hae, integral_zero]
    rw [hc, hphi]
    linarith [P.hd]
  rcases lt_or_ge z 1 with hz1 | hz1
  · rw [P.gain_of_mem hz hz1]
    exact hbase
  rcases le_or_gt z (buyerAtom d η) with hzR | hzR
  · rw [gain_eq_formula P.seller_integrable P.buyer_integrable, P.seller_Iic,
      P.buyer_tail_eq_of_one_le hz1 hzR]
    have hc : sellerCDF d H z = 1 := by
      simp [sellerCDF, not_lt.mpr hz, not_lt.mpr hz1]
    have hIci : P.buyerLaw.real (Ici z) = η := by
      rcases eq_or_lt_of_le hz1 with h | h
      · rw [← h]; exact P.buyer_Ici_one
      rcases eq_or_lt_of_le hzR with h' | h'
      · rw [h']; exact P.buyer_Ici_atom
      · rw [P.buyer_Ici_of_mem (zero_lt_one.trans h) h', P.clampH_of_ge_one h.le]
    have hphi : (∫ s, max (z - s) 0 ∂P.sellerLaw) = z - sellerMean P.sellerLaw := by
      have hae : (fun s => max (z - s) 0) =ᵐ[P.sellerLaw] fun s => z - s := by
        filter_upwards [P.seller_ae_mem] with s hs
        exact max_eq_left (by linarith [hs.2])
      rw [integral_congr_ae hae, integral_sub (integrable_const z) P.seller_integrable,
        integral_const_prob]
      rfl
    rw [hc, hIci, hphi, P.sellerMean_eq]
    unfold buyerAtom
    field_simp [P.hη.ne']
    ring_nf
    exact le_refl _
  · rw [gain_eq_formula P.seller_integrable P.buyer_integrable, P.buyer_tail_of_ge hzR.le,
      P.buyer_Ici_of_gt hzR]
    simp only [zero_mul, zero_add]
    linarith [P.hd]

/-- `G = d J + d M`, with `J = J_d(H(1 - ·))` the objective of the buyer's normalized
control; with `M = 1 - d² T` this is the third identity in (40). -/
theorem HardPairData.gainsFromTrade_eq (P : HardPairData d η H) :
    gainsFromTrade P.sellerLaw P.buyerLaw =
      d * objective d (cutControl P.buyerLaw 1) + d * sellerMean P.sellerLaw := by
  have hc := P.isCutoff
  have hF := hc.integral_priceDensity_lowerGain (μs := P.sellerLaw) (β := 1) P.buyer_integrable
    P.seller_integrable P.seller_nonneg
  have hleft : (∫ z in Ioc 0 1, priceDensity 1 P.buyerLaw d 1 z *
      lowerGain P.sellerLaw P.buyerLaw z) = d * objective d (cutControl P.buyerLaw 1) := by
    have hae : ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        priceDensity 1 P.buyerLaw d 1 z * lowerGain P.sellerLaw P.buyerLaw z =
          d * priceDensity 1 P.buyerLaw d 1 z := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [volume.ae_ne (1 : ℝ)] with z hne hz
      rw [P.lowerGain_of_mem hz.1 (lt_of_le_of_ne hz.2 hne)]
      ring
    rw [integral_congr_ae hae, integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      hc.priceDensity_integral P.buyer_integrable 1, one_mul]
  have hright : (∫ s, (if s ≤ 1 then 1 * (tailIntegral P.buyerLaw s - d * s) else 0)
      ∂P.sellerLaw) = gainsFromTrade P.sellerLaw P.buyerLaw - d * sellerMean P.sellerLaw := by
    have hae : (fun s => if s ≤ 1 then 1 * (tailIntegral P.buyerLaw s - d * s) else 0)
        =ᵐ[P.sellerLaw] fun s => tailIntegral P.buyerLaw s - d * s := by
      filter_upwards [P.seller_ae_mem] with s hs
      rw [if_pos hs.2, one_mul]
    rw [integral_congr_ae hae, integral_sub
      (integrable_tailIntegral_seller P.buyer_integrable P.seller_nonneg)
      (P.seller_integrable.const_mul d), integral_const_mul]
    rfl
  rw [hleft, hright] at hF
  linarith

/-- `d ≤ M + G`: first-best welfare is at least `L_b(1) = d`. -/
theorem HardPairData.d_le_welfare (P : HardPairData d η H) :
    d ≤ sellerMean P.sellerLaw + gainsFromTrade P.sellerLaw P.buyerLaw := by
  have hM : 0 ≤ sellerMean P.sellerLaw := integral_nonneg_of_ae P.seller_nonneg
  have hG : d ≤ gainsFromTrade P.sellerLaw P.buyerLaw := by
    rw [gainsFromTrade_eq_integral_tail]
    have hLint := integrable_tailIntegral_seller P.buyer_integrable P.seller_nonneg
    calc d = ∫ _s, d ∂P.sellerLaw := (integral_const_prob d).symm
      _ ≤ ∫ s, tailIntegral P.buyerLaw s ∂P.sellerLaw := by
        apply integral_mono_ae (integrable_const d) hLint
        filter_upwards [P.seller_ae_mem] with s hs
        have := tailIntegral_antitone P.buyerLaw P.buyer_integrable hs.2
        rw [P.buyer_tail_eq_tailL zero_le_one le_rfl, tailL_one] at this
        exact this
  linarith

/-- **(41)**: at every price, `(M + Γ(z)) - β (M + G) ≤ d (1 - β J) + η d² T` whenever
`β (1 + d) = 1`. -/
theorem HardPairData.welfare_gap_le (P : HardPairData d η H) {β : ℝ} (hβ : β * (1 + d) = 1)
    (z : ℝ) :
    (sellerMean P.sellerLaw + gain P.sellerLaw P.buyerLaw z) -
        β * (sellerMean P.sellerLaw + gainsFromTrade P.sellerLaw P.buyerLaw) ≤
      d * (1 - β * objective d (cutControl P.buyerLaw 1)) + η * (d ^ 2 * timeT d H 1) := by
  have hg := P.gain_le z
  rw [P.gainsFromTrade_eq]
  have hM := P.sellerMean_eq
  have : β * (sellerMean P.sellerLaw + (d * objective d (cutControl P.buyerLaw 1) +
      d * sellerMean P.sellerLaw)) =
      sellerMean P.sellerLaw * (β * (1 + d)) + β * d * objective d (cutControl P.buyerLaw 1) := by
    ring
  rw [this, hβ]
  nlinarith

/-- The buyer's normalized control is `H(1 - ·)` on `[0, 1]`. -/
theorem HardPairData.cutControl_eq (P : HardPairData d η H) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cutControl P.buyerLaw 1 t = H (1 - t) := by
  unfold cutControl
  rw [one_mul, P.buyer_survival_eq (by linarith [ht.2])
    (lt_of_le_of_lt (by linarith [ht.1]) P.one_lt_buyerAtom),
    clampH_eq ⟨by linarith [ht.2], by linarith [ht.1]⟩]

end Pair

end FixedPrice
