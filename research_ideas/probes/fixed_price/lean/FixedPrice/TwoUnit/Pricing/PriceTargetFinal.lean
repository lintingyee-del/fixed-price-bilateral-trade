import FixedPrice.TwoUnit.Pricing.PriceTargetRealized

/-!
# Theorem E, package B, part 4: the realized price meets the target; part (iii)

* The gain at `s` depends only on the mass at `s` and on `(s, b̄]`.
* The realized potential at any seller cost `s ≥ 0` is at least the potential of `ϖ` at
  `min s b̄` (beyond `b̄` the difference is `dw - min {dw, ϖ(b̄)} ≥ 0`).
* Hence the realized price meets the target at every ordered seller pair (certified field
  `ordered_farkas` at the clipped pair), and its restriction to `(b̄, ∞)` is `βd` times Lebesgue
  measure on `(b̄, b̄ + ϖ(b̄)/d)`: both measures give `(a, c]` the mass
  `βd (min c M - max a b̄)_+`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section Congr

variable {bbar : ℝ} {μ : Measure ℝ}

theorem gainFromMass_congr {ϖ₁ ϖ₂ : ℝ → ℝ} {s : ℝ} (hs : ϖ₁ s = ϖ₂ s)
    (h : ∀ t ∈ Ioc s bbar, ϖ₁ t = ϖ₂ t) :
    gainFromMass bbar μ ϖ₁ s = gainFromMass bbar μ ϖ₂ s := by
  have hk : kernelIntegral bbar μ ϖ₁ s = kernelIntegral bbar μ ϖ₂ s := by
    unfold kernelIntegral
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [h t ht]
  unfold gainFromMass
  rw [hs, hk]

theorem kernelIntegral_of_le {ϖ : ℝ → ℝ} {s : ℝ} (h : bbar ≤ s) :
    kernelIntegral bbar μ ϖ s = 0 := by
  unfold kernelIntegral
  rw [Ioc_eq_empty (not_lt.mpr h), Measure.restrict_empty, integral_zero_measure]

end Congr

section RealizedTarget

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d β : ℝ} {ϖ : ℝ → ℝ}

/-- The realized potential dominates the potential at the clipped seller cost. -/
theorem sellerPotential_ext_ge (hB : IsBuyerBodies bbar law) (hd : 0 < d)
    (hϖ : IsCumulativeMass bbar ϖ) (i : Fin 2) {s : ℝ} (hs : 0 ≤ s) :
    sellerPotential bbar (law i) d ϖ (min s bbar) ≤
      sellerPotential bbar (law i) d (extendedMass bbar d ϖ) s := by
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  have hb := bbar_nonneg_of_bodies hB
  rcases le_or_gt s bbar with hsb | hsb
  · rw [min_eq_left hsb]
    unfold sellerPotential
    rw [gainFromMass_congr (ϖ₁ := extendedMass bbar d ϖ) (ϖ₂ := ϖ)
      (extendedMass_of_mem ⟨hs, hsb⟩) (fun t ht => extendedMass_of_mem ⟨hs.trans ht.1.le, ht.2⟩)]
  · rw [min_eq_right hsb.le]
    unfold sellerPotential gainFromMass
    rw [kernelIntegral_of_le le_rfl, kernelIntegral_of_le hsb.le, Lbar_eq_one_of_le' hsupp le_rfl,
      Lbar_eq_one_of_le' hsupp hsb.le, extendedMass_of_ge hb hd hϖ hsb.le]
    have h1 : d * (bbar + ϖ bbar / d - s) ≤ d * max (bbar + ϖ bbar / d - s) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hd.le
    have h2 : d * (bbar + ϖ bbar / d - s) = ϖ bbar - d * (s - bbar) := by field_simp; ring
    linarith

/-- The realized price meets the price target at every ordered seller pair. -/
theorem realizedPrice_priceTarget (cert : PricingScalarCertificates)
    (hB : IsBuyerBodies bbar law) (hd : 0 < d) (hβ : 0 ≤ β) (hβ1 : β * ϖ 0 ≤ 1) {ϑ : ℝ → ℝ}
    (hϑ : ϑ ∈ compensationClass bbar) (hF : IsFeasibleMass bbar law d ϑ ϖ) :
    PriceTarget law d β (realizedPrice bbar d β ϖ) := by
  have hb := bbar_nonneg_of_bodies hB
  have hcum := hF.cumulative
  have hP := isBoundedPriceLaw_realizedPrice hb hd hcum hβ hβ1
  haveI := hP.isProbability
  intro s hs0 hs01
  have hgain : ∀ i : Fin 2, ∀ t, 0 ≤ t →
      ∫ z, gainKernel (law i) t z ∂(realizedPrice bbar d β ϖ) =
        β * gainFromMass bbar (law i) (extendedMass bbar d ϖ) t := by
    intro i t ht
    haveI := hB.isProbability i
    have hsupp := hB.supported i
    rw [integral_gainKernel' hsupp _ t,
      gainFromMass_congr (ϖ₂ := fun u => β * extendedMass bbar d ϖ u)
        (realizedPrice_real_Ioi hb hd hcum hβ ht)
        (fun u hu => realizedPrice_real_Ioi hb hd hcum hβ (ht.trans hu.1.le))]
    exact gainFromMass_const_mul hsupp
      (goodMass_of_antitoneOn hsupp fun x _ y _ hxy => extendedMass_antitone hb hd hcum hxy) β t
  simp only [Fin.sum_univ_two]
  rw [hgain 0 (s 0) hs0, hgain 1 (s 1) (hs0.trans hs01)]
  have hm0 : min (s 0) bbar ∈ Icc 0 bbar := ⟨le_min hs0 hb, min_le_right _ _⟩
  have hm1 : min (s 1) bbar ∈ Icc 0 bbar := ⟨le_min (hs0.trans hs01) hb, min_le_right _ _⟩
  have hm01 : min (s 0) bbar ≤ min (s 1) bbar := min_le_min_right _ hs01
  have c0 := hF.potential_ge 0 _ hm0
  have c1 := hF.potential_ge 1 _ hm1
  rw [compSign_zero] at c0
  rw [compSign_one, one_mul] at c1
  have hmono := (show IsCompensation bbar ϑ from hϑ).monotoneOn hm0 hm1 hm01
  have hsum := cert.ordered_farkas (sellerPotential bbar (law 0) d ϖ (min (s 0) bbar))
    (sellerPotential bbar (law 1) d ϖ (min (s 1) bbar)) (ϑ (min (s 0) bbar))
    (ϑ (min (s 1) bbar)) (by linarith) (by linarith) (by linarith)
  have e0 := sellerPotential_ext_ge hB hd hcum 0 hs0
  have e1 := sellerPotential_ext_ge hB hd hcum 1 (hs0.trans hs01)
  have hS : 0 ≤ sellerPotential bbar (law 0) d (extendedMass bbar d ϖ) (s 0) +
      sellerPotential bbar (law 1) d (extendedMass bbar d ϖ) (s 1) := by linarith
  unfold sellerPotential at hS
  have hprod := mul_nonneg hβ hS
  linarith

/-- `max (M - x) 0 - max (M - c) 0 = max (min c M - x) 0` for `x < c`. -/
theorem max_sub_max_eq {M x c : ℝ} (hxc : x < c) :
    max (M - x) 0 - max (M - c) 0 = max (min c M - x) 0 := by
  rcases le_total M x with h1 | h1
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), min_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring
  rcases le_total M c with h2 | h2
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), min_eq_right h2,
      max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), min_eq_left h2,
      max_eq_left (by linarith)]
    ring

/-- Above `b̄` the realized price is the density `βd` on `(b̄, b̄ + ϖ(b̄)/d)`. -/
theorem realizedPrice_restrict (hB : IsBuyerBodies bbar law) (hd : 0 < d) (hβ : 0 ≤ β)
    (hβ1 : β * ϖ 0 ≤ 1) (hϖ : IsCumulativeMass bbar ϖ) :
    (realizedPrice bbar d β ϖ).restrict (Ioi bbar) =
      ENNReal.ofReal (β * d) • (volume : Measure ℝ).restrict (Ioo bbar (bbar + ϖ bbar / d)) := by
  have hb := bbar_nonneg_of_bodies hB
  have hP := isBoundedPriceLaw_realizedPrice hb hd hϖ hβ hβ1
  haveI := hP.isProbability
  set M := bbar + ϖ bbar / d with hM
  refine Measure.ext_of_Ioc _ _ fun a c _ => ?_
  rw [Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioi, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Ioc, smul_eq_mul]
  set x := a ⊔ bbar with hx
  have hxb : bbar ≤ x := le_sup_right
  have hx0 : 0 ≤ x := hb.trans hxb
  have hL : realizedPrice bbar d β ϖ (Ioc x c) =
      ENNReal.ofReal (β * (extendedMass bbar d ϖ x - extendedMass bbar d ϖ c)) := by
    rw [realizedPrice_eq hb hd hϖ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      extMeasure_Ioc, Measure.dirac_apply' _ measurableSet_Ioc,
      indicator_of_notMem (show (0 : ℝ) ∉ Ioc x c from fun h => absurd h.1 (not_lt.mpr hx0)),
      smul_eq_mul, smul_eq_mul, ENNReal.ofReal_mul hβ]
    simp
  have hR : (volume : Measure ℝ) (Ioc a c ∩ Ioo bbar M) = ENNReal.ofReal (c ⊓ M - x) := by
    have hae : (Ioc a c ∩ Ioo bbar M : Set ℝ) =ᵐ[volume] (Ioc a c ∩ Ioc bbar M : Set ℝ) :=
      (EventuallyEq.refl _ _).inter Ioo_ae_eq_Ioc
    rw [measure_congr hae, Ioc_inter_Ioc, Real.volume_Ioc]
  rw [hL, hR, ← ENNReal.ofReal_mul (by positivity)]
  rcases le_or_gt c x with hcx | hxc
  · have h1 : extendedMass bbar d ϖ x ≤ extendedMass bbar d ϖ c :=
      extendedMass_antitone hb hd hϖ hcx
    rw [ENNReal.ofReal_of_nonpos (by nlinarith), ENNReal.ofReal_of_nonpos]
    have : c ⊓ M - x ≤ 0 := by linarith [min_le_left c M]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  · rw [extendedMass_of_ge hb hd hϖ hxb, extendedMass_of_ge hb hd hϖ (hxb.trans hxc.le),
      ← mul_sub, max_sub_max_eq hxc]
    rcases le_or_gt 0 (c ⊓ M - x) with hy | hy
    · rw [max_eq_left hy]; ring_nf
    · rw [max_eq_right hy.le, mul_zero, mul_zero, ENNReal.ofReal_zero,
        ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hy.le)]

end RealizedTarget

end FixedPrice.TwoUnit.Pricing
