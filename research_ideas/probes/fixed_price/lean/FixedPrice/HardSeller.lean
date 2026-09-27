import FixedPrice.HardBuyer

/-! The equalizing seller of Lemma 9.2: on `[0, 1)` its distribution function is
`F_s = d (1/L - H T)`, with `L(s) = d + ∫_s^1 H` and `T(s) = ∫_0^s L^{-2}`, and the remaining
mass sits at one. The identity `∫_0^z F_s = d L(z) T(z)` is equation (42). -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- `L(s) = d + ∫_s^1 H`. -/
def tailL (d : ℝ) (H : ℝ → ℝ) (s : ℝ) : ℝ := d + ∫ u in s..1, clampH H u

/-- `T(s) = ∫_0^s L^{-2}`. -/
def timeT (d : ℝ) (H : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, (tailL d H u ^ 2)⁻¹

/-- `d (1/L - H T)`. -/
def sellerFormula (d : ℝ) (H : ℝ → ℝ) (s : ℝ) : ℝ :=
  d * ((tailL d H s)⁻¹ - clampH H s * timeT d H s)

/-- The seller's distribution function. -/
def sellerCDF (d : ℝ) (H : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s < 0 then 0 else if s < 1 then sellerFormula d H s else 1

section Seller

variable {d η : ℝ} {H : ℝ → ℝ}

theorem HardPairData.tailL_hasDerivAt (P : HardPairData d η H) (s : ℝ) :
    HasDerivAt (tailL d H) (-clampH H s) s := by
  have hc := P.clampH_continuous
  have h := intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable s 1)
    (hc.stronglyMeasurableAtFilter volume (𝓝 s)) hc.continuousAt
  exact h.const_add d

theorem HardPairData.tailL_continuous (P : HardPairData d η H) : Continuous (tailL d H) :=
  continuous_iff_continuousAt.mpr fun s => (P.tailL_hasDerivAt s).continuousAt

theorem HardPairData.tailL_ge (P : HardPairData d η H) {s : ℝ} (hs : s ≤ 1) : d ≤ tailL d H s := by
  unfold tailL
  have := intervalIntegral.integral_nonneg (μ := volume) hs fun u _ => (P.clampH_pos u).le
  linarith

theorem HardPairData.tailL_pos (P : HardPairData d η H) {s : ℝ} (hs : s ≤ 1) : 0 < tailL d H s :=
  P.hd.trans_le (P.tailL_ge hs)

theorem tailL_one (d : ℝ) (H : ℝ → ℝ) : tailL d H 1 = d := by simp [tailL]

theorem HardPairData.invSq_continuousOn (P : HardPairData d η H) :
    ContinuousOn (fun u => (tailL d H u ^ 2)⁻¹) (Iic 1) :=
  (P.tailL_continuous.continuousOn.pow 2).inv₀ fun u hu => pow_ne_zero 2 (P.tailL_pos hu).ne'

theorem HardPairData.invSq_intervalIntegrable (P : HardPairData d η H) {a b : ℝ}
    (ha : a ≤ 1) (hb : b ≤ 1) :
    IntervalIntegrable (fun u => (tailL d H u ^ 2)⁻¹) volume a b :=
  (P.invSq_continuousOn.mono fun u hu => by
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hu; exact hu.2.trans hb
    · rw [uIcc_of_ge h] at hu; exact hu.2.trans ha).intervalIntegrable

theorem HardPairData.timeT_hasDerivAt (P : HardPairData d η H) {s : ℝ} (hs : s < 1) :
    HasDerivAt (timeT d H) (tailL d H s ^ 2)⁻¹ s := by
  have hm : Measurable (fun u => (tailL d H u ^ 2)⁻¹) :=
    (P.tailL_continuous.measurable.pow_const 2).inv
  have hc : ContinuousAt (fun u => (tailL d H u ^ 2)⁻¹) s :=
    P.invSq_continuousOn.continuousAt (Iic_mem_nhds hs)
  exact intervalIntegral.integral_hasDerivAt_right
    (P.invSq_intervalIntegrable zero_le_one hs.le)
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hc

theorem HardPairData.timeT_continuousOn (P : HardPairData d η H) :
    ContinuousOn (timeT d H) (Iic 1) := by
  intro s hs
  rcases eq_or_lt_of_le (show s ≤ 1 from hs) with h1 | h1
  · subst h1
    have hc := intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ))
      (P.invSq_intervalIntegrable zero_le_one le_rfl)
      (by rw [uIcc_of_le zero_le_one]; exact ⟨le_rfl, zero_le_one⟩)
    have hw := hc 1 (by rw [uIcc_of_le zero_le_one]; exact ⟨zero_le_one, le_rfl⟩)
    rw [uIcc_of_le zero_le_one] at hw
    exact hw.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE zero_lt_one)
  · exact (P.timeT_hasDerivAt h1).continuousAt.continuousWithinAt

theorem HardPairData.timeT_nonneg (P : HardPairData d η H) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ timeT d H s :=
  intervalIntegral.integral_nonneg hs fun u _ => inv_nonneg.mpr (sq_nonneg _)

theorem timeT_zero (d : ℝ) (H : ℝ → ℝ) : timeT d H 0 = 0 := by simp [timeT]

theorem HardPairData.timeT_le (P : HardPairData d η H) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    timeT d H s ≤ s / d ^ 2 := by
  unfold timeT
  calc (∫ u in (0 : ℝ)..s, (tailL d H u ^ 2)⁻¹) ≤ ∫ _u in (0 : ℝ)..s, (d ^ 2)⁻¹ :=
        intervalIntegral.integral_mono_on hs (P.invSq_intervalIntegrable zero_le_one hs1)
          intervalIntegrable_const fun u hu =>
            inv_anti₀ (pow_pos P.hd 2) (pow_le_pow_left₀ P.hd.le (P.tailL_ge (hu.2.trans hs1)) 2)
    _ = s / d ^ 2 := by simp [div_eq_mul_inv]

/-- `1/L(s') - 1/L(s) = ∫_s^{s'} H/L²`. -/
theorem HardPairData.inv_tailL_sub (P : HardPairData d η H) {s s' : ℝ} (hs : s ≤ s')
    (hs' : s' ≤ 1) :
    (tailL d H s')⁻¹ - (tailL d H s)⁻¹ = ∫ u in s..s', clampH H u * (tailL d H u ^ 2)⁻¹ := by
  have hder : ∀ u ∈ uIcc s s', HasDerivAt (fun v => (tailL d H v)⁻¹)
      (clampH H u * (tailL d H u ^ 2)⁻¹) u := by
    intro u hu
    rw [uIcc_of_le hs] at hu
    have hn := (P.tailL_pos (hu.2.trans hs')).ne'
    convert (P.tailL_hasDerivAt u).inv hn using 1
    field_simp
  have hint : IntervalIntegrable (fun u => clampH H u * (tailL d H u ^ 2)⁻¹) volume s s' :=
    (P.clampH_continuous.continuousOn.mul (P.invSq_continuousOn.mono fun u hu => by
      rw [uIcc_of_le hs] at hu; exact hu.2.trans hs')).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]

theorem HardPairData.timeT_sub (P : HardPairData d η H) {s s' : ℝ} (hs : s ≤ 1) (hs' : s' ≤ 1) :
    timeT d H s' - timeT d H s = ∫ u in s..s', (tailL d H u ^ 2)⁻¹ := by
  unfold timeT
  rw [intervalIntegral.integral_interval_sub_left (P.invSq_intervalIntegrable zero_le_one hs')
    (P.invSq_intervalIntegrable zero_le_one hs)]

/-- The seller formula is nondecreasing on `[0, 1]`. -/
theorem HardPairData.sellerFormula_mono (P : HardPairData d η H) {s s' : ℝ} (hs0 : 0 ≤ s)
    (hss' : s ≤ s') (hs' : s' ≤ 1) : sellerFormula d H s ≤ sellerFormula d H s' := by
  have h1 := P.inv_tailL_sub hss' hs'
  have h2 := P.timeT_sub (hss'.trans hs') hs'
  have hint : IntervalIntegrable (fun u => (tailL d H u ^ 2)⁻¹) volume s s' :=
    P.invSq_intervalIntegrable (hss'.trans hs') hs'
  have hint' : IntervalIntegrable (fun u => clampH H u * (tailL d H u ^ 2)⁻¹) volume s s' :=
    (P.clampH_continuous.continuousOn.mul (P.invSq_continuousOn.mono fun u hu => by
      rw [uIcc_of_le hss'] at hu; exact hu.2.trans hs')).intervalIntegrable
  have h3 : clampH H s' * (timeT d H s' - timeT d H s) ≤
      ∫ u in s..s', clampH H u * (tailL d H u ^ 2)⁻¹ := by
    rw [h2, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hss' (hint.const_mul _) hint'
    intro u hu
    exact mul_le_mul_of_nonneg_right (P.clampH_antitone hu.2) (inv_nonneg.mpr (sq_nonneg _))
  have hT := P.timeT_nonneg hs0
  have hH := P.clampH_antitone hss'
  unfold sellerFormula
  apply mul_le_mul_of_nonneg_left _ P.hd.le
  nlinarith [mul_le_mul_of_nonneg_right hH hT]

theorem HardPairData.sellerFormula_zero (P : HardPairData d η H) :
    sellerFormula d H 0 = d * (tailL d H 0)⁻¹ := by
  simp [sellerFormula, timeT_zero]

theorem HardPairData.sellerFormula_zero_pos (P : HardPairData d η H) : 0 < sellerFormula d H 0 := by
  rw [P.sellerFormula_zero]
  exact mul_pos P.hd (inv_pos.mpr (P.tailL_pos zero_le_one))

theorem HardPairData.sellerFormula_one (P : HardPairData d η H) :
    sellerFormula d H 1 = 1 - d * η * timeT d H 1 := by
  unfold sellerFormula
  rw [tailL_one, P.clampH_of_ge_one le_rfl]
  field_simp [P.hd.ne']

theorem HardPairData.sellerFormula_le_one (P : HardPairData d η H) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : sellerFormula d H s ≤ 1 := by
  have h := P.sellerFormula_mono hs0 hs1 le_rfl
  rw [P.sellerFormula_one] at h
  have := mul_nonneg (mul_nonneg P.hd.le P.hη.le) (P.timeT_nonneg zero_le_one)
  linarith

theorem HardPairData.sellerFormula_nonneg (P : HardPairData d η H) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : 0 ≤ sellerFormula d H s :=
  P.sellerFormula_zero_pos.le.trans (P.sellerFormula_mono le_rfl hs0 hs1)

theorem HardPairData.sellerFormula_continuousOn (P : HardPairData d η H) :
    ContinuousOn (sellerFormula d H) (Iic 1) := by
  unfold sellerFormula
  apply continuousOn_const.mul
  apply ContinuousOn.sub
  · exact P.tailL_continuous.continuousOn.inv₀ fun u hu => (P.tailL_pos hu).ne'
  · exact P.clampH_continuous.continuousOn.mul P.timeT_continuousOn

theorem HardPairData.sellerCDF_nonneg (P : HardPairData d η H) (z : ℝ) : 0 ≤ sellerCDF d H z := by
  unfold sellerCDF
  split_ifs with h1 h2
  · exact le_rfl
  · exact P.sellerFormula_nonneg (not_lt.mp h1) h2.le
  · exact zero_le_one

theorem HardPairData.sellerCDF_le_one (P : HardPairData d η H) (z : ℝ) : sellerCDF d H z ≤ 1 := by
  unfold sellerCDF
  split_ifs with h1 h2
  · exact zero_le_one
  · exact P.sellerFormula_le_one (not_lt.mp h1) h2.le
  · exact le_rfl

theorem HardPairData.sellerCDF_mono (P : HardPairData d η H) : Monotone (sellerCDF d H) := by
  intro x y hxy
  by_cases hx0 : x < 0
  · have : sellerCDF d H x = 0 := by simp [sellerCDF, hx0]
    rw [this]
    exact P.sellerCDF_nonneg y
  by_cases hy1 : 1 ≤ y
  · have : sellerCDF d H y = 1 := by
      simp [sellerCDF, not_lt.mpr (zero_le_one.trans hy1), not_lt.mpr hy1]
    rw [this]
    exact P.sellerCDF_le_one x
  push Not at hx0 hy1
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
  have hy0 : 0 ≤ y := hx0.trans hxy
  simp only [sellerCDF, not_lt.mpr hx0, not_lt.mpr hy0, hx1, hy1, if_false, if_true]
  exact P.sellerFormula_mono hx0 hxy hy1.le

theorem HardPairData.sellerCDF_rightCont (P : HardPairData d η H) (x : ℝ) :
    ContinuousWithinAt (sellerCDF d H) (Ici x) x := by
  rcases lt_or_ge x 0 with hx | hx
  · apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with y hy
      simp [sellerCDF, show y < 0 from hy]
    · simp [sellerCDF, hx]
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hc : ContinuousAt (sellerFormula d H) x :=
      P.sellerFormula_continuousOn.continuousAt (Iic_mem_nhds hx1)
    apply hc.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hx1)] with y hy hy1
      simp only [sellerCDF, show ¬ y < 0 from not_lt.mpr (hx.trans hy), if_false,
        show y < 1 from hy1, if_true]
    · simp [sellerCDF, not_lt.mpr hx, hx1]
  · apply (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : x ≤ y := hy
      simp [sellerCDF, not_lt.mpr (hx.trans hy'), not_lt.mpr (hx1.trans hy')]
    · simp [sellerCDF, not_lt.mpr hx, not_lt.mpr hx1]

/-- The seller's Stieltjes function. -/
def HardPairData.sellerStieltjes (P : HardPairData d η H) : StieltjesFunction ℝ :=
  ⟨sellerCDF d H, P.sellerCDF_mono, P.sellerCDF_rightCont⟩

/-- The seller's value law. -/
def HardPairData.sellerLaw (P : HardPairData d η H) : Measure ℝ := P.sellerStieltjes.measure

theorem HardPairData.sellerStieltjes_apply (P : HardPairData d η H) :
    (P.sellerStieltjes : ℝ → ℝ) = sellerCDF d H := rfl

theorem HardPairData.seller_tendsto_bot (P : HardPairData d η H) :
    Tendsto P.sellerStieltjes atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot 0] with z hz
  show (0 : ℝ) = sellerCDF d H z
  simp [sellerCDF, hz]

theorem HardPairData.seller_tendsto_top (P : HardPairData d η H) :
    Tendsto P.sellerStieltjes atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with z hz
  show (1 : ℝ) = sellerCDF d H z
  simp [sellerCDF, not_lt.mpr (zero_le_one.trans hz), not_lt.mpr hz]

instance HardPairData.sellerLaw_isProb (P : HardPairData d η H) :
    IsProbabilityMeasure P.sellerLaw :=
  P.sellerStieltjes.isProbabilityMeasure P.seller_tendsto_bot P.seller_tendsto_top

theorem HardPairData.seller_Iic (P : HardPairData d η H) (z : ℝ) :
    P.sellerLaw.real (Iic z) = sellerCDF d H z := by
  unfold HardPairData.sellerLaw
  rw [measureReal_def, P.sellerStieltjes.measure_Iic P.seller_tendsto_bot z,
    P.sellerStieltjes_apply, sub_zero, ENNReal.toReal_ofReal (P.sellerCDF_nonneg z)]

theorem HardPairData.seller_Iio_of_mem (P : HardPairData d η H) {z : ℝ} (hz : 0 < z)
    (hz1 : z < 1) : P.sellerLaw.real (Iio z) = sellerFormula d H z := by
  unfold HardPairData.sellerLaw
  have hc : ContinuousAt (sellerCDF d H) z := by
    apply (P.sellerFormula_continuousOn.continuousAt (Iic_mem_nhds hz1)).congr
    filter_upwards [Ioi_mem_nhds hz, Iio_mem_nhds hz1] with y hy hy1
    simp [sellerCDF, not_lt.mpr (le_of_lt (mem_Ioi.mp hy)), mem_Iio.mp hy1]
  rw [measureReal_def, P.sellerStieltjes.measure_Iio P.seller_tendsto_bot z,
    P.sellerStieltjes_apply, sub_zero, hc.continuousWithinAt.leftLim_eq,
    ENNReal.toReal_ofReal (P.sellerCDF_nonneg z)]
  simp [sellerCDF, not_lt.mpr hz.le, hz1]

theorem HardPairData.seller_ae_mem (P : HardPairData d η H) :
    ∀ᵐ s ∂P.sellerLaw, s ∈ Icc (0 : ℝ) 1 := by
  have hlow : P.sellerLaw (Iio 0) = 0 := by
    unfold HardPairData.sellerLaw
    rw [P.sellerStieltjes.measure_Iio P.seller_tendsto_bot 0, sub_zero, ENNReal.ofReal_eq_zero]
    apply le_of_eq
    refine leftLim_eq_of_tendsto (NeBot.ne inferInstance) ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    show (0 : ℝ) = sellerCDF d H z
    simp [sellerCDF, show z < 0 from hz]
  have hhigh : P.sellerLaw (Ioi 1) = 0 := by
    unfold HardPairData.sellerLaw
    have h1 : sellerCDF d H 1 = 1 := by
      unfold sellerCDF
      norm_num
    rw [P.sellerStieltjes.measure_Ioi P.seller_tendsto_top 1, P.sellerStieltjes_apply, h1,
      sub_self, ENNReal.ofReal_zero]
  have hu : (Icc (0 : ℝ) 1)ᶜ = Iio 0 ∪ Ioi 1 := by
    ext b
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  rw [ae_iff]
  simp only [← mem_compl_iff (s := Icc (0 : ℝ) 1), setOf_mem_eq, hu]
  exact measure_union_null hlow hhigh

theorem HardPairData.seller_nonneg (P : HardPairData d η H) : ∀ᵐ s ∂P.sellerLaw, 0 ≤ s := by
  filter_upwards [P.seller_ae_mem] with s hs
  exact hs.1

theorem HardPairData.seller_integrable (P : HardPairData d η H) :
    Integrable (fun s => s) P.sellerLaw := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact measurable_id.aestronglyMeasurable
  · filter_upwards [P.seller_ae_mem] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2

/-- Equation (42), first identity: `∫_0^z F_s = d L(z) T(z)` on `[0, 1]`. -/
theorem HardPairData.integral_sellerFormula (P : HardPairData d η H) {z : ℝ} (hz : 0 ≤ z)
    (hz1 : z ≤ 1) :
    (∫ u in (0 : ℝ)..z, sellerFormula d H u) = d * tailL d H z * timeT d H z := by
  have hder : ∀ u ∈ Ioo (0 : ℝ) z, HasDerivAt (fun v => d * tailL d H v * timeT d H v)
      (sellerFormula d H u) u := by
    intro u hu
    have hu1 : u < 1 := lt_of_lt_of_le hu.2 hz1
    have hn := (P.tailL_pos hu1.le).ne'
    convert ((P.tailL_hasDerivAt u).const_mul d).mul (P.timeT_hasDerivAt hu1) using 1
    unfold sellerFormula
    field_simp
    ring
  have hcont : ContinuousOn (fun v => d * tailL d H v * timeT d H v) (Icc 0 z) :=
    ((continuousOn_const.mul P.tailL_continuous.continuousOn).mul
      P.timeT_continuousOn).mono fun v hv => hv.2.trans hz1
  have hint : IntervalIntegrable (sellerFormula d H) volume 0 z :=
    (P.sellerFormula_continuousOn.mono fun v hv => by
      rw [uIcc_of_le hz] at hv; exact hv.2.trans hz1).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz hcont hder hint, timeT_zero]
  ring

end Seller

end FixedPrice
