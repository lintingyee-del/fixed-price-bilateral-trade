import FixedPrice.TwoUnit.Pricing.RoundingBasic

/-!
# Theorem E, package D, part 2: independence of `b̄` and part (iv)

* **Gap G1.** For bodies supported on `[0, b]` and `b ≤ b'` the potentials computed on `[0, b]`
  and on `[0, b']` agree (the kernel is `∫ (t - s)_+ ϖ(t) dμ` either way). Restricting a feasible
  pair from `[0, b']` to `[0, b]` gives `𝒥_b ≤ 𝒥_{b'}`; extending mass and compensation
  constantly above `b` (where `L̄ = 1`, the kernel vanishes and the potential grows at rate `d`)
  gives `𝒥_{b'} ≤ 𝒥_b`.
* **Part (iv).** An optimal rounded least mass plus `δ` is feasible for the bodies with the same
  compensation, so `𝒥 ≤ 𝒥^δ + δ`. The rounded bodies are an ordered finite-support pair on the
  same interval, which gives the equality of suprema (in `[0, ∞]`).
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Pricing

section Bound

variable {b b' : ℝ}

theorem supp_mono {μ : Measure ℝ} (hsupp : μ (Icc 0 b)ᶜ = 0) (hbb' : b ≤ b') :
    μ (Icc 0 b')ᶜ = 0 :=
  measure_mono_null (compl_subset_compl.mpr (Icc_subset_Icc_right hbb')) hsupp

theorem isBuyerBodies_mono {law : Fin 2 → Measure ℝ} (hB : IsBuyerBodies b law)
    (hbb' : b ≤ b') : IsBuyerBodies b' law :=
  ⟨hB.isProbability, fun i => supp_mono (hB.supported i) hbb'⟩

/-- The potentials do not depend on the interval containing the body. -/
theorem sellerPotential_bound_eq {μ : Measure ℝ} (hsupp : μ (Icc 0 b)ᶜ = 0) (hbb' : b ≤ b')
    (d : ℝ) (ϖ : ℝ → ℝ) (s : ℝ) :
    sellerPotential b' μ d ϖ s = sellerPotential b μ d ϖ s := by
  unfold sellerPotential gainFromMass
  rw [kernelIntegral_eq_integral_max (supp_mono hsupp hbb'), kernelIntegral_eq_integral_max hsupp]

/-! ### Restriction from `[0, b']` to `[0, b]` -/

theorem IsCumulativeMass.restrictBound {ϖ : ℝ → ℝ} (h : IsCumulativeMass b' ϖ)
    (hbb' : b ≤ b') : IsCumulativeMass b ϖ :=
  ⟨fun s hs => h.nonneg s ⟨hs.1, hs.2.trans hbb'⟩, h.antitoneOn.mono (Icc_subset_Icc_right hbb'),
    fun s hs => (h.rightContinuous s ⟨hs.1, hs.2.trans hbb'⟩).mono (Icc_subset_Icc_right hbb')⟩

theorem IsCompensation.restrictBound {ϑ : ℝ → ℝ} (h : IsCompensation b' ϑ) (hbb' : b ≤ b') :
    IsCompensation b ϑ := by
  obtain ⟨C, hC⟩ := h.bounded
  exact ⟨⟨C, fun s hs => hC s ⟨hs.1, hs.2.trans hbb'⟩⟩,
    h.monotoneOn.mono (Icc_subset_Icc_right hbb'),
    fun s hs => (h.rightContinuous s ⟨hs.1, hs.2.trans hbb'⟩).mono (Icc_subset_Icc_right hbb')⟩

theorem IsFeasibleMass.restrictBound {law : Fin 2 → Measure ℝ} {d : ℝ} {ϑ ϖ : ℝ → ℝ}
    (h : IsFeasibleMass b' law d ϑ ϖ) (hB : IsBuyerBodies b law) (hbb' : b ≤ b') :
    IsFeasibleMass b law d ϑ ϖ :=
  ⟨h.cumulative.restrictBound hbb', fun i s hs => by
    rw [← sellerPotential_bound_eq (hB.supported i) hbb']
    exact h.potential_ge i s ⟨hs.1, hs.2.trans hbb'⟩⟩

/-! ### Constant extension from `[0, b]` to `[0, b']` -/

theorem continuousWithinAt_extend {f : ℝ → ℝ} (hb : 0 ≤ b)
    (hf : ∀ s ∈ Icc 0 b, ContinuousWithinAt f (Icc s b) s) :
    ∀ s ∈ Icc 0 b', ContinuousWithinAt (fun t => f (min t b)) (Icc s b') s := by
  intro s hs
  have hs0 : min s b ∈ Icc 0 b := ⟨le_min hs.1 hb, min_le_right _ _⟩
  have hmaps : MapsTo (fun t => min t b) (Icc s b') (Icc (min s b) b) :=
    fun t ht => ⟨min_le_min_right _ ht.1, min_le_right _ _⟩
  have hg : Continuous fun t : ℝ => min t b := continuous_id.min continuous_const
  exact ContinuousWithinAt.comp (f := fun t => min t b) (x := s) (hf _ hs0)
    hg.continuousWithinAt hmaps

theorem IsCumulativeMass.extendBound {ϖ : ℝ → ℝ} (h : IsCumulativeMass b ϖ) (hb : 0 ≤ b) :
    IsCumulativeMass b' (fun t => ϖ (min t b)) :=
  ⟨fun _ hs => h.nonneg _ ⟨le_min hs.1 hb, min_le_right _ _⟩,
    fun _ hx _ hy hxy => h.antitoneOn ⟨le_min hx.1 hb, min_le_right _ _⟩
      ⟨le_min hy.1 hb, min_le_right _ _⟩ (min_le_min_right _ hxy),
    continuousWithinAt_extend hb h.rightContinuous⟩

theorem IsCompensation.extendBound {ϑ : ℝ → ℝ} (h : IsCompensation b ϑ) (hb : 0 ≤ b) :
    IsCompensation b' (fun t => ϑ (min t b)) := by
  obtain ⟨C, hC⟩ := h.bounded
  exact ⟨⟨C, fun _ hs => hC _ ⟨le_min hs.1 hb, min_le_right _ _⟩⟩,
    fun _ hx _ hy hxy => h.monotoneOn ⟨le_min hx.1 hb, min_le_right _ _⟩
      ⟨le_min hy.1 hb, min_le_right _ _⟩ (min_le_min_right _ hxy),
    continuousWithinAt_extend hb h.rightContinuous⟩

theorem IsFeasibleMass.extendBound {law : Fin 2 → Measure ℝ} {d : ℝ} {ϑ ϖ : ℝ → ℝ}
    (h : IsFeasibleMass b law d ϑ ϖ) (hB : IsBuyerBodies b law) (hbb' : b ≤ b') (hd : 0 < d) :
    IsFeasibleMass b' law d (fun t => ϑ (min t b)) (fun t => ϖ (min t b)) := by
  have hb := bbar_nonneg_of_bodies hB
  refine ⟨h.cumulative.extendBound hb, fun i s hs => ?_⟩
  have hsupp := hB.supported i
  rw [sellerPotential_bound_eq hsupp hbb']
  rcases le_or_gt s b with hsb | hsb
  · -- inside `[0, b]` the extension agrees with `ϖ` at `s` and on `(s, b]`
    have hg : sellerPotential b (law i) d (fun t => ϖ (min t b)) s =
        sellerPotential b (law i) d ϖ s := by
      unfold sellerPotential
      rw [gainFromMass_congr (ϖ₂ := ϖ) (show ϖ (min s b) = ϖ s by rw [min_eq_left hsb])
        (fun t ht => show ϖ (min t b) = ϖ t by rw [min_eq_left ht.2])]
    rw [hg]
    show compSign i * ϑ (min s b) ≤ _
    rw [min_eq_left hsb]
    exact h.potential_ge i s ⟨hs.1, hsb⟩
  · -- beyond `b`: `L̄ = 1`, the kernel vanishes, and the potential grows at rate `d`
    have hpb := h.potential_ge i b ⟨hb, le_rfl⟩
    have e1 : sellerPotential b (law i) d (fun t => ϖ (min t b)) s = d * s - 1 + ϖ b := by
      unfold sellerPotential gainFromMass
      simp only [Lbar_eq_one_of_le' hsupp hsb.le, kernelIntegral_of_le hsb.le,
        min_eq_right hsb.le]
      ring
    have e2 : sellerPotential b (law i) d ϖ b = d * b - 1 + ϖ b := by
      unfold sellerPotential gainFromMass
      simp only [Lbar_eq_one_of_le' hsupp le_rfl, kernelIntegral_of_le le_rfl]
      ring
    rw [e1]
    rw [e2] at hpb
    show compSign i * ϑ (min s b) ≤ _
    rw [min_eq_right hsb.le]
    have := mul_le_mul_of_nonneg_left hsb.le hd.le
    linarith

/-- **Gap G1.** `𝒥` does not depend on the interval `[0, b̄]` containing the bodies. -/
theorem pricingValue_eq_of_bound_le' (cert : PricingScalarCertificates)
    {law : Fin 2 → Measure ℝ} (hB : IsBuyerBodies b law) (hbb' : b ≤ b') {d : ℝ} (hd : 0 < d) :
    pricingValue b' law d = pricingValue b law d := by
  have hb := bbar_nonneg_of_bodies hB
  have hB' := isBuyerBodies_mono hB hbb'
  apply le_antisymm
  · obtain ⟨⟨ϑ, hϑ, hopt⟩, -⟩ := pricingValue_isLeast' cert hB hd
    have hF := leastMass_isFeasible' cert hB hd hϑ
    have hϑ' : (fun t => ϑ (min t b)) ∈ compensationClass b' :=
      (show IsCompensation b ϑ from hϑ).extendBound hb
    have hF' := hF.extendBound hB hbb' hd
    have h1 := leastMass_le_of_isFeasible' cert hB' hd hϑ' hF' 0 ⟨le_rfl, hb.trans hbb'⟩
    have h2 := pricingValue_le cert hB' hd hϑ'
    have h3 : leastMass b law d ϑ 0 = pricingValue b law d := hopt
    simp only [min_eq_left hb] at h1
    linarith
  · obtain ⟨⟨ϑ, hϑ, hopt⟩, -⟩ := pricingValue_isLeast' cert hB' hd
    have hF' := leastMass_isFeasible' cert hB' hd hϑ
    have hϑb : ϑ ∈ compensationClass b := (show IsCompensation b' ϑ from hϑ).restrictBound hbb'
    have hF := hF'.restrictBound hB hbb'
    have h1 := leastMass_le_of_isFeasible' cert hB hd hϑb hF 0 ⟨le_rfl, hb⟩
    have h2 := pricingValue_le cert hB hd hϑb
    have h3 : leastMass b' law d ϑ 0 = pricingValue b' law d := hopt
    linarith

end Bound

section PartIV

variable {d δ : ℝ}

/-- **Theorem E (iv), inequality.** -/
theorem theoremE_part_iv' (cert : PricingScalarCertificates) (P : OrderedBuyerPair)
    (hd : 0 < d) (hδ : 0 < δ) :
    P.value d ≤ pricingValue P.bbar (roundedLaw δ P.law) d + δ := by
  have hBδ := (roundedLaw_spec' P hδ).1
  obtain ⟨⟨ϑ, hϑ, hopt⟩, -⟩ := pricingValue_isLeast' cert hBδ hd
  have hFδ := leastMass_isFeasible' cert hBδ hd hϑ
  have hF := isFeasibleMass_add_of_rounded cert P.bodies hδ hFδ
  have hb := bbar_nonneg_of_bodies P.bodies
  have h1 := leastMass_le_of_isFeasible' cert P.bodies hd hϑ hF 0 ⟨le_rfl, hb⟩
  have h2 := pricingValue_le cert P.bodies hd hϑ
  have h3 : leastMass P.bbar (roundedLaw δ P.law) d ϑ 0 =
      pricingValue P.bbar (roundedLaw δ P.law) d := hopt
  show pricingValue P.bbar P.law d ≤ _
  linarith

/-- **Theorem E (iv), last sentence.** -/
theorem theoremE_part_iv_sup' (cert : PricingScalarCertificates) (hd : 0 < d) :
    ⨆ P : OrderedBuyerPair, ENNReal.ofReal (P.value d) =
      ⨆ P : {P : OrderedBuyerPair // P.HasFiniteSupport}, ENNReal.ofReal (P.1.value d) := by
  apply le_antisymm
  · refine iSup_le fun P => ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hδ : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
    obtain ⟨hBδ, hord, hfin⟩ := roundedLaw_spec' P hδ
    let Pδ : OrderedBuyerPair := ⟨P.bbar, roundedLaw ε P.law, hBδ, hord⟩
    have hPδ : Pδ.HasFiniteSupport := hfin
    have h : P.value d ≤ Pδ.value d + ε := theoremE_part_iv' cert P hd hδ
    calc ENNReal.ofReal (P.value d) ≤ ENNReal.ofReal (Pδ.value d + ε) := ENNReal.ofReal_le_ofReal h
      _ ≤ ENNReal.ofReal (Pδ.value d) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (Pδ.value d) + ε := by rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ (⨆ P : {P : OrderedBuyerPair // P.HasFiniteSupport}, ENNReal.ofReal (P.1.value d)) +
            ε := by
          gcongr
          exact le_iSup (fun P : {P : OrderedBuyerPair // P.HasFiniteSupport} =>
            ENNReal.ofReal (P.1.value d)) ⟨Pδ, hPδ⟩
  · exact iSup_le fun P => le_iSup (fun P : OrderedBuyerPair => ENNReal.ofReal (P.value d)) P.1

end PartIV

end FixedPrice.TwoUnit.Pricing
