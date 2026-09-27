import FixedPrice.Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

def expRemainder (v : ℝ) : ℝ := Real.exp (-2 * v) - 1 + 2 * v

theorem expRemainder_nonneg (v : ℝ) : 0 ≤ expRemainder v := by
  have h := Real.add_one_le_exp (-2 * v)
  unfold expRemainder
  linarith

theorem expRemainder_pos {v : ℝ} (hv : v ≠ 0) : 0 < expRemainder v := by
  have h := Real.add_one_lt_exp (show -2 * v ≠ 0 by exact mul_ne_zero (by norm_num) hv)
  unfold expRemainder
  linarith

theorem expRemainder_eq_zero_iff (v : ℝ) : expRemainder v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact (ne_of_gt (expRemainder_pos hv)) h
  · rintro rfl
    simp [expRemainder]

theorem gapIntegrand_nonneg {ell v Q : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hc : Q a * v a ≤ 0) : 0 ≤ gapIntegrand ell v Q a := by
  have hsq := mul_nonneg ha (sq_nonneg (deriv v a))
  have hexp := mul_nonneg (Real.exp_pos (-2 * ell a)).le (expRemainder_nonneg (v a))
  change 0 ≤ a * deriv v a ^ 2 + Real.exp (-2 * ell a) * expRemainder (v a) -
    2 * Q a * v a
  nlinarith

theorem gapIntegrand_zero_imp {ell v Q : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hc : Q a * v a ≤ 0) (hzero : gapIntegrand ell v Q a = 0) :
    v a = 0 := by
  by_contra hv
  have hsq := mul_nonneg ha (sq_nonneg (deriv v a))
  have hexp := mul_pos (Real.exp_pos (-2 * ell a)) (expRemainder_pos hv)
  change a * deriv v a ^ 2 + Real.exp (-2 * ell a) * expRemainder (v a) -
    2 * Q a * v a = 0 at hzero
  nlinarith

theorem gapIntegral_nonneg {ell v Q : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hc : ∀ a ∈ Icc 0 R, Q a * v a ≤ 0) :
    0 ≤ ∫ a in 0..R, gapIntegrand ell v Q a := by
  exact intervalIntegral.integral_nonneg hR fun a ha => gapIntegrand_nonneg ha.1 (hc a ha)

/-- The integration-by-parts step in G1. Absolute continuity permits measurable
controls and piecewise smooth reference curves; no pointwise derivative at a join is assumed. -/
theorem logEnergy_gap_identity {d R : ℝ} {ell v : ℝ → ℝ}
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval (fun a => a * deriv ell a) 0 R)
    (hellSq : IntervalIntegrable (fun a => a * (deriv ell a) ^ 2) volume 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R)
    (hv0 : v 0 = 0) (hvR : v R = 0) :
    logEnergy d R ell - logEnergy d R (fun a => ell a + v a) =
      ∫ a in 0..R, gapIntegrand ell v
        (fun a => Real.exp (-2 * ell a) + deriv (fun b => b * deriv ell b) a) a := by
  let w : ℝ → ℝ := fun a => a * deriv ell a
  let e : ℝ → ℝ := fun a => Real.exp (-2 * ell a)
  let pot : ℝ → ℝ := fun a => e a * (Real.exp (-2 * v a) - 1)
  have he : ContinuousOn e (uIcc 0 R) :=
    Real.continuous_exp.comp_continuousOn (hell.continuousOn.const_mul (-2))
  have hpot : IntervalIntegrable pot volume 0 R :=
    (he.mul ((Real.continuous_exp.comp_continuousOn
      (hv.continuousOn.const_mul (-2))).sub continuousOn_const)).intervalIntegrable
  have hcross : IntervalIntegrable (fun a => w a * deriv v a) volume 0 R :=
    hv.intervalIntegrable_deriv.continuousOn_mul hw.continuousOn
  have hdual : IntervalIntegrable (fun a => deriv w a * v a) volume 0 R :=
    hw.intervalIntegrable_deriv.mul_continuousOn hv.continuousOn
  have hbase : IntervalIntegrable (fun a => d ^ 2 - e a - a * deriv ell a ^ 2) volume 0 R :=
    (continuousOn_const.sub he).intervalIntegrable.sub hellSq
  have hdelta : IntervalIntegrable
      (fun a => a * deriv v a ^ 2 + pot a + 2 * (w a * deriv v a)) volume 0 R :=
    (hvSq.add hpot).add (hcross.const_mul 2)
  have hderiv : ∀ᵐ a, a ∈ uIcc 0 R →
      deriv (fun b => ell b + v b) a = deriv ell a + deriv v a := by
    filter_upwards [hell.ae_differentiableAt, hv.ae_differentiableAt] with a ha hb hab
    exact ((ha hab).hasDerivAt.add (hb hab).hasDerivAt).deriv
  have hexp (a : ℝ) : Real.exp (-2 * (ell a + v a)) = e a * Real.exp (-2 * v a) := by
    rw [show -2 * (ell a + v a) = -2 * ell a + -2 * v a by ring, Real.exp_add]
  have hnew : (∫ a in 0..R,
      d ^ 2 - Real.exp (-2 * (ell a + v a)) - a * deriv (fun b => ell b + v b) a ^ 2) =
      (∫ a in 0..R, d ^ 2 - e a - a * deriv ell a ^ 2) -
        ∫ a in 0..R, a * deriv v a ^ 2 + pot a + 2 * (w a * deriv v a) := by
    rw [← intervalIntegral.integral_sub hbase hdelta]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with a ha hab
    rw [ha (uIoc_subset_uIcc hab), hexp]
    dsimp [pot, w]
    ring
  have hibp : (∫ a in 0..R, w a * deriv v a) = -(∫ a in 0..R, deriv w a * v a) := by
    simpa [hv0, hvR] using hw.integral_mul_deriv_eq_deriv_mul hv
  have hgap : (∫ a in 0..R, gapIntegrand ell v
        (fun a => e a + deriv w a) a) =
      (∫ a in 0..R, a * deriv v a ^ 2) + (∫ a in 0..R, pot a) -
        2 * ∫ a in 0..R, deriv w a * v a := by
    calc
      _ = ∫ a in 0..R, (a * deriv v a ^ 2 + pot a) - 2 * (deriv w a * v a) := by
        apply intervalIntegral.integral_congr
        intro a _
        dsimp [gapIntegrand, pot, e]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hvSq.add hpot) (hdual.const_mul 2),
          intervalIntegral.integral_add hvSq hpot, intervalIntegral.integral_const_mul]
  change logEnergy d R ell - logEnergy d R (fun a => ell a + v a) =
    ∫ a in 0..R, gapIntegrand ell v (fun a => e a + deriv w a) a
  rw [hgap]
  unfold logEnergy
  dsimp only
  rw [hnew, hv0, add_zero, intervalIntegral.integral_add (hvSq.add hpot) (hcross.const_mul 2),
    intervalIntegral.integral_add hvSq hpot, intervalIntegral.integral_const_mul, hibp]
  dsimp [e]
  ring

theorem gapIntegral_zero_imp {ell v Q : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv : ContinuousOn v (Icc 0 R))
    (hc : ∀ a ∈ Icc 0 R, Q a * v a ≤ 0)
    (hi : IntervalIntegrable (gapIntegrand ell v Q) volume 0 R)
    (hz : (∫ a in 0..R, gapIntegrand ell v Q a) = 0) :
    EqOn v (fun _ => 0) (Icc 0 R) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] gapIntegrand ell v Q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact gapIntegrand_nonneg ha.1.le (hc a ⟨ha.1.le, ha.2⟩)
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hR.le hnn hi).mp hz
  have hvAE : v =ᵐ[volume.restrict (Ioc 0 R)] (fun _ => 0) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with a ha hab
    exact gapIntegrand_zero_imp hab.1.le (hc a ⟨hab.1.le, hab.2⟩) ha
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hvAE
  exact Measure.eqOn_Icc_of_ae_eq volume hR.ne hvAE hv continuousOn_const

theorem logEnergy_congr {d R : ℝ} (hR : 0 < R) {f g : ℝ → ℝ}
    (hfg : EqOn f g (Icc 0 R)) : logEnergy d R f = logEnergy d R g := by
  have h0 := hfg (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl, hR.le⟩)
  unfold logEnergy
  rw [h0]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ a : ℝ, a ≠ R := volume.ae_ne R
  filter_upwards [hne] with a ha hab
  have ham : a ∈ Ioc 0 R := by simpa [uIoc_of_le hR.le] using hab
  have hao : a ∈ Ioo 0 R := ⟨ham.1, lt_of_le_of_ne ham.2 ha⟩
  have hd := (hfg.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hao
  rw [hfg (Ioo_subset_Icc_self hao), hd]

theorem gapIntegrand_intervalIntegrable {R : ℝ} {ell v : ℝ → ℝ}
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval (fun a => a * deriv ell a) 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R) :
    IntervalIntegrable (gapIntegrand ell v
      (fun a => Real.exp (-2 * ell a) + deriv (fun b => b * deriv ell b) a)) volume 0 R := by
  have he : ContinuousOn (fun a => Real.exp (-2 * ell a)) (uIcc 0 R) :=
    Real.continuous_exp.comp_continuousOn (hell.continuousOn.const_mul (-2))
  have hev : ContinuousOn (fun a => Real.exp (-2 * v a)) (uIcc 0 R) :=
    Real.continuous_exp.comp_continuousOn (hv.continuousOn.const_mul (-2))
  have hrem := (he.mul ((hev.sub (continuousOn_const (c := (1 : ℝ)))).add
    (hv.continuousOn.const_mul 2))).intervalIntegrable (μ := volume)
  have hq := (he.intervalIntegrable.add hw.intervalIntegrable_deriv).mul_continuousOn hv.continuousOn
  convert (hvSq.add hrem).sub (hq.const_mul 2) using 1
  funext a
  simp only [gapIntegrand, Pi.mul_apply, Pi.add_apply, mul_assoc]

/-- Fixed-endpoint optimality, including the pointwise equality case.
The assumptions are regularity and the contact sign, not a presumed gap identity. -/
theorem fixedEndpoint_calibration {d R : ℝ} {ell v : ℝ → ℝ}
    (hR : 0 < R)
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval (fun a => a * deriv ell a) 0 R)
    (hellSq : IntervalIntegrable (fun a => a * (deriv ell a) ^ 2) volume 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R)
    (hv0 : v 0 = 0) (hvR : v R = 0)
    (hc : ∀ a ∈ Icc 0 R,
      (Real.exp (-2 * ell a) + deriv (fun b => b * deriv ell b) a) * v a ≤ 0) :
    logEnergy d R (fun a => ell a + v a) ≤ logEnergy d R ell ∧
      (logEnergy d R (fun a => ell a + v a) = logEnergy d R ell ↔
        EqOn v (fun _ => 0) (Icc 0 R)) := by
  have hid := logEnergy_gap_identity hell hv hw hellSq hvSq hv0 hvR (d := d)
  have hnn := gapIntegral_nonneg (ell := ell) hR.le hc
  constructor
  · linarith
  constructor
  · intro heq
    have hi := gapIntegrand_intervalIntegrable hell hv hw hvSq
    apply gapIntegral_zero_imp hR (by simpa [uIcc_of_le hR.le] using hv.continuousOn) hc hi
    linarith
  · intro heq
    apply logEnergy_congr hR
    intro a ha
    simp only [heq ha, add_zero]

end FixedPrice
