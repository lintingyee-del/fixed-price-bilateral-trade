import FixedPrice.Strict
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! The buyer of the bounded hard pairs, Lemma 9.2: survival function `H` on `[0, 1]`,
equal to `η = H(1)` on `[1, R)` with `R = 1 + d/η`, and zero from `R` on. The law is the
Stieltjes measure of `1 - survival`. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- The hypotheses of Lemma 9.2 on the buyer's survival function on `[0, 1]`. -/
structure HardPairData (d η : ℝ) (H : ℝ → ℝ) : Prop where
  hd : 0 < d
  hη : 0 < η
  hη1 : η ≤ 1
  cont : ContinuousOn H (Icc 0 1)
  anti : AntitoneOn H (Icc 0 1)
  one : H 1 = η
  le_one : ∀ s ∈ Icc (0 : ℝ) 1, H s ≤ 1

/-- `H` extended by constants outside `[0, 1]`. -/
def clampH (H : ℝ → ℝ) (s : ℝ) : ℝ := H (max 0 (min s 1))

/-- The remote atom `R_η = 1 + d/η`. -/
def buyerAtom (d η : ℝ) : ℝ := 1 + d / η

/-- The buyer's distribution function. -/
def buyerCDF (d η : ℝ) (H : ℝ → ℝ) (z : ℝ) : ℝ :=
  if z < 0 then 0 else if z < buyerAtom d η then 1 - clampH H z else 1

section Data

variable {d η : ℝ} {H : ℝ → ℝ}

theorem clamp_mem (s : ℝ) : max 0 (min s 1) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clampH_eq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : clampH H s = H s := by
  unfold clampH
  rw [min_eq_left hs.2, max_eq_right hs.1]

theorem clampH_of_one_le {s : ℝ} (hs : 1 ≤ s) : clampH H s = H 1 := by
  unfold clampH
  rw [min_eq_right hs, max_eq_right zero_le_one]

theorem clampH_of_nonpos {s : ℝ} (hs : s ≤ 0) : clampH H s = H 0 := by
  unfold clampH
  rw [max_eq_left (le_trans (min_le_left _ _) hs)]

theorem HardPairData.clampH_continuous (P : HardPairData d η H) : Continuous (clampH H) :=
  P.cont.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) clamp_mem

theorem HardPairData.clampH_antitone (P : HardPairData d η H) : Antitone (clampH H) := by
  intro x y hxy
  unfold clampH
  exact P.anti (clamp_mem x) (clamp_mem y)
    (max_le_max le_rfl (min_le_min hxy le_rfl))

theorem HardPairData.clampH_le_one (P : HardPairData d η H) (s : ℝ) : clampH H s ≤ 1 :=
  P.le_one _ (clamp_mem s)

theorem HardPairData.clampH_ge (P : HardPairData d η H) (s : ℝ) : η ≤ clampH H s := by
  rw [← P.one, ← clampH_eq (H := H) (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)]
  rcases le_total s 1 with h | h
  · exact P.clampH_antitone h
  · rw [clampH_of_one_le h, clampH_eq (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)]

theorem HardPairData.clampH_pos (P : HardPairData d η H) (s : ℝ) : 0 < clampH H s :=
  P.hη.trans_le (P.clampH_ge s)

theorem HardPairData.clampH_of_ge_one (P : HardPairData d η H) {s : ℝ} (hs : 1 ≤ s) :
    clampH H s = η := by
  rw [clampH_of_one_le hs, P.one]

theorem HardPairData.one_lt_buyerAtom (P : HardPairData d η H) : 1 < buyerAtom d η := by
  unfold buyerAtom
  have := div_pos P.hd P.hη
  linarith

theorem HardPairData.buyerCDF_mono (P : HardPairData d η H) : Monotone (buyerCDF d η H) := by
  intro x y hxy
  have hle := P.clampH_le_one
  have hge := P.clampH_pos
  unfold buyerCDF
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> first
    | linarith [hle y, hge x]
    | linarith [P.clampH_antitone hxy]

theorem HardPairData.buyerCDF_rightCont (P : HardPairData d η H) (x : ℝ) :
    ContinuousWithinAt (buyerCDF d η H) (Ici x) x := by
  have hR := P.one_lt_buyerAtom
  rcases lt_or_ge x 0 with hx | hx
  · apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with y hy
      simp [buyerCDF, show y < 0 from hy]
    · simp [buyerCDF, hx]
  rcases lt_or_ge x (buyerAtom d η) with hxR | hxR
  · have hc : ContinuousAt (fun z => 1 - clampH H z) x :=
      (continuous_const.sub P.clampH_continuous).continuousAt
    apply hc.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hxR)] with y hy hyR
      simp only [buyerCDF, show ¬ y < 0 from not_lt.mpr (hx.trans hy), if_false,
        show y < buyerAtom d η from hyR, if_true]
    · simp [buyerCDF, not_lt.mpr hx, hxR]
  · apply (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : x ≤ y := hy
      simp [buyerCDF, not_lt.mpr (hx.trans hy'), not_lt.mpr (hxR.trans hy')]
    · simp [buyerCDF, not_lt.mpr hx, not_lt.mpr hxR]

/-- The buyer's Stieltjes function. -/
def HardPairData.buyerStieltjes (P : HardPairData d η H) : StieltjesFunction ℝ :=
  ⟨buyerCDF d η H, P.buyerCDF_mono, P.buyerCDF_rightCont⟩

/-- The buyer's value law. -/
def HardPairData.buyerLaw (P : HardPairData d η H) : Measure ℝ := P.buyerStieltjes.measure

theorem HardPairData.buyer_tendsto_bot (P : HardPairData d η H) :
    Tendsto P.buyerStieltjes atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot 0] with z hz
  show (0 : ℝ) = buyerCDF d η H z
  simp [buyerCDF, hz]

theorem HardPairData.buyer_tendsto_top (P : HardPairData d η H) :
    Tendsto P.buyerStieltjes atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (buyerAtom d η)] with z hz
  show (1 : ℝ) = buyerCDF d η H z
  have hz0 : ¬ z < 0 := not_lt.mpr ((zero_le_one.trans P.one_lt_buyerAtom.le).trans hz)
  simp [buyerCDF, hz0, not_lt.mpr hz]

theorem HardPairData.buyerStieltjes_apply (P : HardPairData d η H) :
    (P.buyerStieltjes : ℝ → ℝ) = buyerCDF d η H := rfl

instance HardPairData.buyerLaw_isProb (P : HardPairData d η H) :
    IsProbabilityMeasure P.buyerLaw :=
  P.buyerStieltjes.isProbabilityMeasure P.buyer_tendsto_bot P.buyer_tendsto_top

theorem HardPairData.buyerCDF_le_one (P : HardPairData d η H) (z : ℝ) : buyerCDF d η H z ≤ 1 := by
  unfold buyerCDF
  split_ifs <;> linarith [P.clampH_pos z]

theorem HardPairData.buyerCDF_nonneg (P : HardPairData d η H) (z : ℝ) : 0 ≤ buyerCDF d η H z := by
  unfold buyerCDF
  split_ifs <;> linarith [P.clampH_le_one z]

theorem HardPairData.buyer_survival (P : HardPairData d η H) (z : ℝ) :
    survival P.buyerLaw z = 1 - buyerCDF d η H z := by
  unfold survival HardPairData.buyerLaw
  rw [measureReal_def, P.buyerStieltjes.measure_Ioi P.buyer_tendsto_top z, P.buyerStieltjes_apply,
    ENNReal.toReal_ofReal (by linarith [P.buyerCDF_le_one z])]

/-- On `[0, R)` the survival function is `clampH H`. -/
theorem HardPairData.buyer_survival_eq (P : HardPairData d η H) {z : ℝ} (hz : 0 ≤ z)
    (hzR : z < buyerAtom d η) : survival P.buyerLaw z = clampH H z := by
  rw [P.buyer_survival]
  simp [buyerCDF, not_lt.mpr hz, hzR]

theorem HardPairData.buyer_survival_of_ge (P : HardPairData d η H) {z : ℝ}
    (hz : buyerAtom d η ≤ z) : survival P.buyerLaw z = 0 := by
  rw [P.buyer_survival]
  have hz0 : ¬ z < 0 := not_lt.mpr ((zero_le_one.trans P.one_lt_buyerAtom.le).trans hz)
  simp [buyerCDF, hz0, not_lt.mpr hz]

theorem HardPairData.buyer_ae_mem (P : HardPairData d η H) :
    ∀ᵐ b ∂P.buyerLaw, b ∈ Icc (0 : ℝ) (buyerAtom d η) := by
  have hlow : P.buyerLaw (Iio 0) = 0 := by
    unfold HardPairData.buyerLaw
    rw [P.buyerStieltjes.measure_Iio P.buyer_tendsto_bot 0, sub_zero, ENNReal.ofReal_eq_zero]
    apply le_of_eq
    refine leftLim_eq_of_tendsto (NeBot.ne inferInstance) ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    show (0 : ℝ) = buyerCDF d η H z
    simp [buyerCDF, show z < 0 from hz]
  have hhigh : P.buyerLaw (Ioi (buyerAtom d η)) = 0 := by
    have := P.buyer_survival_of_ge (le_refl (buyerAtom d η))
    unfold survival at this
    rwa [measureReal_eq_zero_iff] at this
  have hu : (Icc (0 : ℝ) (buyerAtom d η))ᶜ = Iio 0 ∪ Ioi (buyerAtom d η) := by
    ext b
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  rw [ae_iff]
  simp only [← mem_compl_iff (s := Icc (0 : ℝ) (buyerAtom d η)), setOf_mem_eq, hu]
  exact measure_union_null hlow hhigh

theorem HardPairData.buyer_nonneg (P : HardPairData d η H) : ∀ᵐ b ∂P.buyerLaw, 0 ≤ b := by
  filter_upwards [P.buyer_ae_mem] with b hb
  exact hb.1

theorem HardPairData.buyer_integrable (P : HardPairData d η H) :
    Integrable (fun b => b) P.buyerLaw := by
  apply Integrable.mono' (integrable_const (buyerAtom d η))
  · exact measurable_id.aestronglyMeasurable
  · filter_upwards [P.buyer_ae_mem] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2

theorem HardPairData.buyer_tail_atom (P : HardPairData d η H) :
    tailIntegral P.buyerLaw (buyerAtom d η) = 0 := by
  unfold tailIntegral
  have : ∀ᵐ b ∂P.buyerLaw, max (b - buyerAtom d η) 0 = 0 := by
    filter_upwards [P.buyer_ae_mem] with b hb
    exact max_eq_right (by linarith [hb.2])
  rw [integral_congr_ae this]
  simp

/-- The buyer's tail integral on `[0, R]`: `L(z) = ∫_z^R clampH H`. -/
theorem HardPairData.buyer_tail_eq (P : HardPairData d η H) {z : ℝ} (hz : 0 ≤ z)
    (hzR : z ≤ buyerAtom d η) :
    tailIntegral P.buyerLaw z = ∫ u in z..buyerAtom d η, clampH H u := by
  have hsub := tailIntegral_sub P.buyerLaw P.buyer_integrable hzR
  rw [P.buyer_tail_atom, sub_zero] at hsub
  rw [hsub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (buyerAtom d η)] with u hne hu
  rw [uIoc_of_le hzR] at hu
  exact P.buyer_survival_eq (hz.trans hu.1.le) (lt_of_le_of_ne hu.2 hne)

/-- `∫_1^R clampH H = d`. -/
theorem HardPairData.integral_clamp_one_atom (P : HardPairData d η H) :
    (∫ u in (1 : ℝ)..buyerAtom d η, clampH H u) = d := by
  have hR := P.one_lt_buyerAtom
  rw [intervalIntegral.integral_congr (g := fun _ => η) (fun u hu => by
    rw [uIcc_of_le hR.le] at hu
    exact P.clampH_of_ge_one hu.1)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  unfold buyerAtom
  field_simp [P.hη.ne']
  ring

/-- On `[0, 1]` the buyer's tail integral is `d + ∫_z^1 H`. -/
theorem HardPairData.buyer_tail_eq_of_le_one (P : HardPairData d η H) {z : ℝ} (hz : 0 ≤ z)
    (hz1 : z ≤ 1) : tailIntegral P.buyerLaw z = d + ∫ u in z..1, clampH H u := by
  have hR := P.one_lt_buyerAtom
  rw [P.buyer_tail_eq hz (hz1.trans hR.le),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1)
      (P.clampH_continuous.intervalIntegrable _ _) (P.clampH_continuous.intervalIntegrable _ _),
    P.integral_clamp_one_atom]
  ring

/-- On `[1, R]` the buyer's tail integral is `η (R - z)`. -/
theorem HardPairData.buyer_tail_eq_of_one_le (P : HardPairData d η H) {z : ℝ} (hz : 1 ≤ z)
    (hzR : z ≤ buyerAtom d η) : tailIntegral P.buyerLaw z = η * (buyerAtom d η - z) := by
  rw [P.buyer_tail_eq (zero_le_one.trans hz) hzR,
    intervalIntegral.integral_congr (g := fun _ => η) (fun u hu => by
      rw [uIcc_of_le hzR] at hu
      exact P.clampH_of_ge_one (hz.trans hu.1))]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem HardPairData.buyer_tail_of_ge (P : HardPairData d η H) {z : ℝ}
    (hz : buyerAtom d η ≤ z) : tailIntegral P.buyerLaw z = 0 :=
  le_antisymm (P.buyer_tail_atom ▸ tailIntegral_antitone P.buyerLaw P.buyer_integrable hz)
    (tailIntegral_nonneg _ _)

/-- `μ_b([z, ∞))` for the inclusive trade rule. -/
theorem HardPairData.buyer_Ici (P : HardPairData d η H) (z : ℝ) :
    P.buyerLaw.real (Ici z) = 1 - leftLim (buyerCDF d η H) z := by
  unfold HardPairData.buyerLaw
  rw [measureReal_def, P.buyerStieltjes.measure_Ici P.buyer_tendsto_top z, P.buyerStieltjes_apply,
    ENNReal.toReal_ofReal]
  · have := P.buyerStieltjes.mono.leftLim_le (le_refl z)
    have h1 := P.buyerCDF_le_one z
    change leftLim (buyerCDF d η H) z ≤ buyerCDF d η H z at this
    linarith

theorem HardPairData.buyer_Ici_of_mem (P : HardPairData d η H) {z : ℝ} (hz : 0 < z)
    (hzR : z < buyerAtom d η) : P.buyerLaw.real (Ici z) = clampH H z := by
  rw [P.buyer_Ici]
  have hc : ContinuousAt (buyerCDF d η H) z := by
    have hc' : ContinuousAt (fun y => 1 - clampH H y) z :=
      (continuous_const.sub P.clampH_continuous).continuousAt
    apply hc'.congr
    filter_upwards [Ioi_mem_nhds hz, Iio_mem_nhds hzR] with y hy hyR
    simp [buyerCDF, not_lt.mpr (le_of_lt (mem_Ioi.mp hy)), mem_Iio.mp hyR]
  rw [hc.continuousWithinAt.leftLim_eq]
  simp [buyerCDF, not_lt.mpr hz.le, hzR]

theorem HardPairData.buyer_Ici_atom (P : HardPairData d η H) :
    P.buyerLaw.real (Ici (buyerAtom d η)) = η := by
  have hR := P.one_lt_buyerAtom
  rw [P.buyer_Ici]
  have hlim : leftLim (buyerCDF d η H) (buyerAtom d η) = 1 - η := by
    refine leftLim_eq_of_tendsto (NeBot.ne inferInstance) ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hR)] with y hy hy1
    have hy' : y < buyerAtom d η := hy
    have hy1' : 1 < y := hy1
    simp [buyerCDF, not_lt.mpr (zero_le_one.trans hy1'.le), hy', P.clampH_of_ge_one hy1'.le]
  rw [hlim]
  ring

theorem HardPairData.buyer_Ici_of_gt (P : HardPairData d η H) {z : ℝ}
    (hz : buyerAtom d η < z) : P.buyerLaw.real (Ici z) = 0 := by
  have h1 : P.buyerLaw.real (Ici z) ≤ survival P.buyerLaw (buyerAtom d η) := by
    unfold survival
    exact measureReal_mono (fun b hb => lt_of_lt_of_le hz hb)
  rw [P.buyer_survival_of_ge le_rfl] at h1
  exact le_antisymm h1 measureReal_nonneg

theorem HardPairData.buyer_Ici_one (P : HardPairData d η H) :
    P.buyerLaw.real (Ici 1) = η := by
  rw [P.buyer_Ici_of_mem zero_lt_one P.one_lt_buyerAtom, P.clampH_of_ge_one le_rfl]

end Data

end FixedPrice
