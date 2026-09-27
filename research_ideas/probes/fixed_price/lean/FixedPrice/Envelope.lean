import FixedPrice.Model
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section

open Set MeasureTheory
open scoped Interval Topology

namespace FixedPrice

def branchDefect (C y : ℝ) : ℝ := 2 * C - 1 + C * (1 - C) * y

theorem endParameter_eq (C : ℝ) (hC : C ≠ 0) (hC1 : 1 - C ≠ 0) :
    endParameter C = 1 / C - 1 / (1 - C) := by
  unfold endParameter
  field_simp
  ring

theorem endParameter_strictAnti : StrictAntiOn endParameter (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  rw [endParameter_eq a (ne_of_gt ha.1) (ne_of_gt (sub_pos.mpr ha.2)),
    endParameter_eq b (ne_of_gt hb.1) (ne_of_gt (sub_pos.mpr hb.2))]
  have h1 := one_div_lt_one_div_of_lt ha.1 hab
  have h2 := one_div_lt_one_div_of_lt (sub_pos.mpr hb.2) (show 1 - b < 1 - a by linarith)
  linarith

theorem branchDefect_eq (C y : ℝ) (hC : C ≠ 0) (hC1 : 1 - C ≠ 0) :
    branchDefect C y = C * (1 - C) * (y - endParameter C) := by
  unfold branchDefect endParameter
  field_simp
  ring

/-- The envelope sign on the entire positive branch. The upper part C>=1/2
is included; no restriction of the comparison to (1/4,1/2) is made. -/
theorem branchDefect_sign {Y : ℝ → ℝ} {Cstar Cbar : ℝ}
    (hstar : Cstar ∈ Ioo (0 : ℝ) (1 / 2)) (hbar : Cstar < Cbar)
    (hYmono : MonotoneOn Y (Ioo 0 Cbar))
    (hYpos : ∀ C ∈ Ioo 0 Cbar, 0 < Y C)
    (hcap : ∀ C ∈ Ioo 0 Cbar, C * Y C < 1)
    (hcontact : Y Cstar = endParameter Cstar) :
    (∀ C ∈ Ioo 0 Cstar, branchDefect C (Y C) < 0) ∧
    branchDefect Cstar (Y Cstar) = 0 ∧
    (∀ C ∈ Ioo Cstar Cbar, 0 < branchDefect C (Y C)) := by
  have hstarMem : Cstar ∈ Ioo 0 Cbar := ⟨hstar.1, hbar⟩
  have hstar1 : Cstar < 1 := by linarith [hstar.2]
  constructor
  · intro C hC
    have hCbar : C ∈ Ioo 0 Cbar := ⟨hC.1, hC.2.trans hbar⟩
    have hC1 : C < 1 := hC.2.trans hstar1
    have hYe : Y C < endParameter C := lt_of_le_of_lt
      (by simpa [hcontact] using hYmono hCbar hstarMem hC.2.le)
      (endParameter_strictAnti ⟨hC.1, hC1⟩ ⟨hstar.1, hstar1⟩ hC.2)
    rw [branchDefect_eq C (Y C) (ne_of_gt hC.1) (ne_of_gt (sub_pos.mpr hC1))]
    exact mul_neg_of_pos_of_neg (mul_pos hC.1 (sub_pos.mpr hC1)) (sub_neg.mpr hYe)
  constructor
  · rw [branchDefect_eq Cstar (Y Cstar) (ne_of_gt hstar.1)
      (ne_of_gt (sub_pos.mpr hstar1)), hcontact, sub_self, mul_zero]
  · intro C hC
    have hCpos : 0 < C := hstar.1.trans hC.1
    have hCbar : C ∈ Ioo 0 Cbar := ⟨hCpos, hC.2⟩
    by_cases hChalf : C < 1 / 2
    · have hC1 : C < 1 := by linarith
      have hYe : endParameter C < Y C := lt_of_lt_of_le
        (endParameter_strictAnti ⟨hstar.1, hstar1⟩ ⟨hCpos, hC1⟩ hC.1)
        (by simpa [hcontact] using hYmono hstarMem hCbar hC.1.le)
      rw [branchDefect_eq C (Y C) (ne_of_gt hCpos) (ne_of_gt (sub_pos.mpr hC1))]
      exact mul_pos (mul_pos hCpos (sub_pos.mpr hC1)) (sub_pos.mpr hYe)
    · have hhalf : 1 / 2 ≤ C := le_of_not_gt hChalf
      have hy := hYpos C hCbar
      have hc := hcap C hCbar
      unfold branchDefect
      by_cases hC1 : C < 1
      · have hp := mul_pos (mul_pos hCpos (sub_pos.mpr hC1)) hy
        nlinarith
      · have hn : (1 - C) * (C * Y C - 1) ≥ 0 :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        nlinarith

def envelopeWeight (Y U : ℝ → ℝ) (C : ℝ) : ℝ :=
  (Y C + U C) / (1 - C * Y C) ^ 2

/-- The FTC part of G2, including uniqueness of the global maximum.
Its derivative and branch hypotheses must still be established for the
implicit contact branch before this theorem applies to the manuscript. -/
theorem endpointEnvelope_calibration {Y U Phi : ℝ → ℝ} {Cstar Cbar : ℝ}
    (hstar : Cstar ∈ Ioo (0 : ℝ) (1 / 2)) (hbar : Cstar < Cbar)
    (hYmono : MonotoneOn Y (Ioo 0 Cbar))
    (hYcont : ContinuousOn Y (Ioo 0 Cbar)) (hUcont : ContinuousOn U (Ioo 0 Cbar))
    (hYpos : ∀ C ∈ Ioo 0 Cbar, 0 < Y C)
    (hUnn : ∀ C ∈ Ioo 0 Cbar, 0 ≤ U C)
    (hcap : ∀ C ∈ Ioo 0 Cbar, C * Y C < 1)
    (hcontact : Y Cstar = endParameter Cstar)
    (hPhi : ∀ C ∈ Ioo 0 Cbar,
      HasDerivAt Phi (-envelopeWeight Y U C * branchDefect C (Y C)) C)
    {C : ℝ} (hC : C ∈ Ioo 0 Cbar) :
    Phi Cstar - Phi C = ∫ u in min C Cstar..max C Cstar,
      (Y u + U u) * |branchDefect u (Y u)| / (1 - u * Y u) ^ 2 ∧
    Phi C ≤ Phi Cstar ∧ (Phi C = Phi Cstar ↔ C = Cstar) := by
  have hs : Cstar ∈ Ioo 0 Cbar := ⟨hstar.1, hbar⟩
  obtain ⟨hneg, hzero, hpos⟩ := branchDefect_sign hstar hbar hYmono hYpos hcap hcontact
  have hwpos (u : ℝ) (hu : u ∈ Ioo 0 Cbar) : 0 < envelopeWeight Y U u := by
    exact div_pos (add_pos_of_pos_of_nonneg (hYpos u hu) (hUnn u hu))
      (sq_pos_of_pos (sub_pos.mpr (hcap u hu)))
  have hwcont : ContinuousOn (envelopeWeight Y U) (Ioo 0 Cbar) := by
    exact (hYcont.add hUcont).div
      ((continuousOn_const.sub (continuousOn_id.mul hYcont)).pow 2)
      (fun u hu => pow_ne_zero 2 (ne_of_gt (sub_pos.mpr (hcap u hu))))
  have hbcont : ContinuousOn (fun u => branchDefect u (Y u)) (Ioo 0 Cbar) := by
    exact ((continuousOn_id.const_mul 2).sub continuousOn_const).add
      ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul hYcont)
  have hfcont : ContinuousOn Phi (Ioo 0 Cbar) :=
    fun u hu => (hPhi u hu).continuousAt.continuousWithinAt
  have hdiffcont := hwcont.neg.mul hbcont
  have hsub {a b : ℝ} (ha : a ∈ Ioo 0 Cbar) (hb : b ∈ Ioo 0 Cbar) :
      Icc a b ⊆ Ioo 0 Cbar := fun u hu => ⟨ha.1.trans_le hu.1, hu.2.trans_lt hb.2⟩
  have hstrict : C ≠ Cstar → Phi C < Phi Cstar := by
    intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm : StrictMonoOn Phi (Icc C Cstar) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc C Cstar) (hfcont.mono (hsub hC hs))
        intro u hu
        have hu' : u ∈ Ioo C Cstar := by simpa only [interior_Icc] using hu
        have huDom := hsub hC hs (Ioo_subset_Icc_self hu')
        rw [(hPhi u huDom).deriv]
        exact mul_pos_of_neg_of_neg (neg_neg_of_pos (hwpos u huDom))
          (hneg u ⟨hC.1.trans hu'.1, hu'.2⟩)
      exact hm ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
    · have hm : StrictAntiOn Phi (Icc Cstar C) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc Cstar C) (hfcont.mono (hsub hs hC))
        intro u hu
        have hu' : u ∈ Ioo Cstar C := by simpa only [interior_Icc] using hu
        have huDom := hsub hs hC (Ioo_subset_Icc_self hu')
        rw [(hPhi u huDom).deriv]
        exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hwpos u huDom))
          (hpos u ⟨hu'.1, hu'.2.trans hC.2⟩)
      exact hm ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt
  refine ⟨?_, ?_, ?_⟩
  · rcases le_total C Cstar with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
      have hint := (hdiffcont.mono (hsub hC hs)).intervalIntegrable_of_Icc (μ := volume) hle
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => hPhi u (hsub hC hs (by simpa [uIcc_of_le hle] using hu))) hint
      rw [← hFTC]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc C Cstar := by simpa [uIcc_of_le hle] using hu
      have hb : branchDefect u (Y u) ≤ 0 := by
        rcases hu'.2.eq_or_lt with heq | hlt
        · simpa [heq] using hzero.le
        · exact (hneg u ⟨hC.1.trans_le hu'.1, hlt⟩).le
      dsimp only
      rw [abs_of_nonpos hb]
      unfold envelopeWeight
      ring
    · rw [min_eq_right hle, max_eq_left hle]
      have hint := (hdiffcont.mono (hsub hs hC)).intervalIntegrable_of_Icc (μ := volume) hle
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => hPhi u (hsub hs hC (by simpa [uIcc_of_le hle] using hu))) hint
      have hflip : Phi Cstar - Phi C = -(Phi C - Phi Cstar) := by ring
      rw [hflip, ← hFTC, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc Cstar C := by simpa [uIcc_of_le hle] using hu
      have hb : 0 ≤ branchDefect u (Y u) := by
        rcases hu'.1.eq_or_lt with heq | hlt
        · simpa [← heq] using hzero.ge
        · exact (hpos u ⟨hlt, hu'.2.trans_lt hC.2⟩).le
      dsimp only
      rw [abs_of_nonneg hb]
      unfold envelopeWeight
      ring
  · by_cases heq : C = Cstar
    · simp [heq]
    · exact (hstrict heq).le
  · constructor
    · intro heq
      by_contra hne
      exact (ne_of_lt (hstrict hne)) heq
    · rintro rfl
      rfl

end FixedPrice
