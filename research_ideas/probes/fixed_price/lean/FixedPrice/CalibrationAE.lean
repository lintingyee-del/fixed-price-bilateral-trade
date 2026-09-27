import FixedPrice.Calibration

/-! The fixed-endpoint calibration with an explicit weight `w` in place of `a * ell'`.
The weight only has to agree with `a * ell'` almost everywhere and the contact sign
only has to hold almost everywhere, so a reference curve with `C^1` joins can be
used without proving differentiability at the joins. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

theorem logEnergy_gap_identity_weight {d R : ℝ} {ell v w : ℝ → ℝ}
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval w 0 R)
    (hw_ae : ∀ᵐ a, a ∈ Ι (0 : ℝ) R → w a = a * deriv ell a)
    (hellSq : IntervalIntegrable (fun a => a * (deriv ell a) ^ 2) volume 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R)
    (hv0 : v 0 = 0) (hvR : v R = 0) :
    logEnergy d R ell - logEnergy d R (fun a => ell a + v a) =
      ∫ a in 0..R, gapIntegrand ell v
        (fun a => Real.exp (-2 * ell a) + deriv w a) a := by
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
    filter_upwards [hderiv, hw_ae] with a ha hwa hab
    rw [ha (uIoc_subset_uIcc hab), hexp, hwa hab]
    dsimp [pot]
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

/-- The fixed-endpoint bound from an almost-everywhere contact sign. -/
theorem logEnergy_le_of_weight_calibration {d R : ℝ} {ell v w : ℝ → ℝ} (hR : 0 ≤ R)
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval w 0 R)
    (hw_ae : ∀ᵐ a, a ∈ Ι (0 : ℝ) R → w a = a * deriv ell a)
    (hellSq : IntervalIntegrable (fun a => a * (deriv ell a) ^ 2) volume 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R)
    (hv0 : v 0 = 0) (hvR : v R = 0)
    (hc : ∀ᵐ a, a ∈ Icc (0 : ℝ) R →
      (Real.exp (-2 * ell a) + deriv w a) * v a ≤ 0) :
    logEnergy d R (fun a => ell a + v a) ≤ logEnergy d R ell := by
  have hgap := logEnergy_gap_identity_weight (d := d) hell hv hw hw_ae hellSq hvSq hv0 hvR
  have hnn : 0 ≤ ∫ a in 0..R, gapIntegrand ell v
      (fun a => Real.exp (-2 * ell a) + deriv w a) a := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hR
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hc] with a hca ha
    exact gapIntegrand_nonneg ha.1 (hca ha)
  linarith

theorem gapIntegrand_weight_intervalIntegrable {R : ℝ} {ell v w : ℝ → ℝ}
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval w 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R) :
    IntervalIntegrable (gapIntegrand ell v
      (fun a => Real.exp (-2 * ell a) + deriv w a)) volume 0 R := by
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

/-- The equality case of the fixed-endpoint bound: equal energies force `v = 0`. -/
theorem eqOn_zero_of_weight_calibration {d R : ℝ} {ell v w : ℝ → ℝ} (hR : 0 < R)
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval w 0 R)
    (hw_ae : ∀ᵐ a, a ∈ Ι (0 : ℝ) R → w a = a * deriv ell a)
    (hellSq : IntervalIntegrable (fun a => a * (deriv ell a) ^ 2) volume 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R)
    (hv0 : v 0 = 0) (hvR : v R = 0)
    (hc : ∀ᵐ a, a ∈ Icc (0 : ℝ) R →
      (Real.exp (-2 * ell a) + deriv w a) * v a ≤ 0)
    (heq : logEnergy d R (fun a => ell a + v a) = logEnergy d R ell) :
    EqOn v (fun _ => 0) (Icc 0 R) := by
  have hgap := logEnergy_gap_identity_weight (d := d) hell hv hw hw_ae hellSq hvSq hv0 hvR
  have hi := gapIntegrand_weight_intervalIntegrable hell hv hw hvSq
  have hz : (∫ a in 0..R, gapIntegrand ell v
      (fun a => Real.exp (-2 * ell a) + deriv w a) a) = 0 := by linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)]
      gapIntegrand ell v (fun a => Real.exp (-2 * ell a) + deriv w a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hc] with a ha hca
    exact gapIntegrand_nonneg ha.1.le (hca ⟨ha.1.le, ha.2⟩)
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hR.le hnn hi).mp hz
  have hvAE : v =ᵐ[volume.restrict (Ioc 0 R)] (fun _ => 0) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hc]
      with a ha hab hca
    exact gapIntegrand_zero_imp hab.1.le (hca ⟨hab.1.le, hab.2⟩) ha
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hvAE
  exact Measure.eqOn_Icc_of_ae_eq volume hR.ne hvAE
    (by simpa [uIcc_of_le hR.le] using hv.continuousOn) continuousOn_const

end FixedPrice
