import FixedPrice.TwoUnit.Pricing.PriceTargetFinal

/-!
# Theorem E, package D, part 1: rounded buyer bodies

* `x ↦ δ⌊x/δ⌋` is monotone and measurable, with `0 ≤ δ⌊x/δ⌋ ≤ x < δ⌊x/δ⌋ + δ` for `x ≥ 0`.
* The rounded bodies form an ordered pair on the same interval `[0, b̄]` with finite support
  (gap G3). The preimage of `(s, ∞)` is the closed ray `[(⌊s/δ⌋+1)δ, ∞)`, and the order of the
  pair passes from open to closed rays by continuity of the measures.
* `0 ≤ L̄ - L̄^δ ≤ δ` (certified pointwise field `rounded_stopLoss`), and the gain against the
  rounded law is at most the gain against the law: in the gain form
  `G^ϖ(s) = ϖ(s) + ∫_{(s,b̄]} (t-s)(ϖ(s)-ϖ(t)) dμ` the integrand is nondecreasing in `t`.
* A mass feasible for the rounded bodies becomes feasible for the bodies after adding `δ`
  (certified field `tail_repair`).
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section RoundDown

variable {δ : ℝ}

theorem roundDown_le (hδ : 0 < δ) (x : ℝ) : roundDown δ x ≤ x := by
  unfold roundDown
  have h := mul_le_mul_of_nonneg_left (Int.floor_le (x / δ)) hδ.le
  have e : δ * (x / δ) = x := by field_simp
  linarith

theorem lt_roundDown_add (hδ : 0 < δ) (x : ℝ) : x < roundDown δ x + δ := by
  unfold roundDown
  have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x / δ))
  linarith

theorem roundDown_nonneg (hδ : 0 < δ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ roundDown δ x :=
  mul_nonneg hδ.le (by exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hx hδ.le))

theorem roundDown_mono (hδ : 0 < δ) : Monotone (roundDown δ) := fun _ _ hxy =>
  mul_le_mul_of_nonneg_left
    (Int.cast_le.mpr (Int.floor_mono (div_le_div_of_nonneg_right hxy hδ.le))) hδ.le

theorem measurable_roundDown (hδ : 0 < δ) : Measurable (roundDown δ) :=
  (roundDown_mono hδ).measurable

theorem roundDown_mem_Icc (hδ : 0 < δ) {bbar x : ℝ} (hx : x ∈ Icc 0 bbar) :
    roundDown δ x ∈ Icc 0 bbar :=
  ⟨roundDown_nonneg hδ hx.1, (roundDown_le hδ x).trans hx.2⟩

/-- The preimage of an open ray is a closed ray. -/
theorem roundDown_preimage_Ioi (hδ : 0 < δ) (s : ℝ) :
    roundDown δ ⁻¹' Ioi s = Ici (((⌊s / δ⌋ : ℝ) + 1) * δ) := by
  ext x
  simp only [mem_preimage, mem_Ioi, mem_Ici, roundDown]
  constructor
  · intro h
    have h1 : s / δ < (⌊x / δ⌋ : ℝ) := by rw [div_lt_iff₀ hδ]; linarith
    have h2 : ⌊s / δ⌋ < ⌊x / δ⌋ := Int.floor_lt.mpr h1
    have h3 : ((⌊s / δ⌋ : ℝ) + 1) ≤ x / δ := Int.lt_floor_iff.mp h2
    exact (le_div_iff₀ hδ).mp h3
  · intro h
    have h3 : ((⌊s / δ⌋ : ℝ) + 1) ≤ x / δ := (le_div_iff₀ hδ).mpr h
    have h2 : ⌊s / δ⌋ < ⌊x / δ⌋ := Int.lt_floor_iff.mpr h3
    have h1 : s / δ < (⌊x / δ⌋ : ℝ) := Int.floor_lt.mp h2
    rw [div_lt_iff₀ hδ] at h1
    linarith

end RoundDown

/-- An order of open-ray masses passes to closed rays. -/
theorem measure_Ici_le_of_forall_Ioi {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ s, μ (Ioi s) ≤ ν (Ioi s)) (a : ℝ) : μ (Ici a) ≤ ν (Ici a) := by
  have hI : Ici a = ⋂ n : ℕ, Ioi (a - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [mem_Ici, mem_iInter, mem_Ioi]
    constructor
    · intro hx n
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hx
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      have := hx n
      linarith
  have hanti : Antitone fun n : ℕ => Ioi (a - 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply Ioi_subset_Ioi
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have tμ := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => measurableSet_Ioi.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have tν := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => measurableSet_Ioi.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hI]
  exact le_of_tendsto_of_tendsto' tμ tν fun n => h _

section RoundedLaw

variable {δ : ℝ} {bbar : ℝ}

theorem rounded_supported {μ : Measure ℝ} (hsupp : μ (Icc 0 bbar)ᶜ = 0) (hδ : 0 < δ) :
    (μ.map (roundDown δ)) (Icc 0 bbar)ᶜ = 0 := by
  rw [Measure.map_apply (measurable_roundDown hδ) measurableSet_Icc.compl]
  exact measure_mono_null (fun x hx hmem => hx (roundDown_mem_Icc hδ hmem)) hsupp

/-- **Gap G3.** The rounded bodies form an ordered pair on `[0, b̄]` with finite support. -/
theorem roundedLaw_spec' (P : OrderedBuyerPair) (hδ : 0 < δ) :
    IsBuyerBodies P.bbar (roundedLaw δ P.law) ∧
    (∀ s : ℝ, roundedLaw δ P.law 1 (Ioi s) ≤ roundedLaw δ P.law 0 (Ioi s)) ∧
    ∃ S : Finset ℝ, ∀ i, roundedLaw δ P.law i (↑S)ᶜ = 0 := by
  have hr := measurable_roundDown hδ
  refine ⟨⟨fun i => ?_, fun i => rounded_supported (P.bodies.supported i) hδ⟩, fun s => ?_,
    ⟨(Finset.Icc 0 ⌊P.bbar / δ⌋).image (fun k : ℤ => δ * (k : ℝ)), fun i => ?_⟩⟩
  · haveI := P.bodies.isProbability i
    exact Measure.isProbabilityMeasure_map hr.aemeasurable
  · haveI := P.bodies.isProbability 0
    haveI := P.bodies.isProbability 1
    simp only [roundedLaw]
    rw [Measure.map_apply hr measurableSet_Ioi, Measure.map_apply hr measurableSet_Ioi,
      roundDown_preimage_Ioi hδ]
    exact measure_Ici_le_of_forall_Ioi P.ordered _
  · simp only [roundedLaw]
    rw [Measure.map_apply hr (Finset.measurableSet _).compl]
    refine measure_mono_null ?_ (P.bodies.supported i)
    intro x hx hmem
    refine hx (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⌊x / δ⌋, Finset.mem_Icc.mpr
      ⟨Int.floor_nonneg.mpr (div_nonneg hmem.1 hδ.le),
        Int.floor_mono (div_le_div_of_nonneg_right hmem.2 hδ.le)⟩, rfl⟩))

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem Lbar_map (hδ : 0 < δ) (s : ℝ) :
    Lbar (μ.map (roundDown δ)) s = 1 + ∫ x, max (roundDown δ x - s) 0 ∂μ := by
  unfold Lbar
  rw [integral_map (measurable_roundDown hδ).aemeasurable
    (show AEStronglyMeasurable (fun y : ℝ => max (y - s) 0) (μ.map (roundDown δ)) from
      ((continuous_sub_right s).max continuous_const).aestronglyMeasurable)]

/-- `0 ≤ L̄(s) - L̄^δ(s) ≤ δ`, from the certified pointwise field `rounded_stopLoss`. -/
theorem Lbar_sub_rounded (cert : PricingScalarCertificates) (hsupp : μ (Icc 0 bbar)ᶜ = 0)
    (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ Lbar μ s - Lbar (μ.map (roundDown δ)) s ∧ Lbar μ s - Lbar (μ.map (roundDown δ)) s ≤ δ := by
  have hb := bbar_nonneg_of_supp hsupp
  rw [Lbar_map hδ]
  unfold Lbar
  have hi1 := integrable_max_sub hsupp s
  have hi2 : Integrable (fun x => max (roundDown δ x - s) 0) μ :=
    integrable_of_bdd_on_supp hsupp
      (((measurable_roundDown hδ).sub_const s).max measurable_const).aestronglyMeasurable
      (fun x hx => abs_max_sub_le (roundDown δ x) s hb (roundDown_mem_Icc hδ hx))
  have hdiff : 1 + ∫ x, max (x - s) 0 ∂μ - (1 + ∫ x, max (roundDown δ x - s) 0 ∂μ) =
      ∫ x, (max (x - s) 0 - max (roundDown δ x - s) 0) ∂μ := by
    rw [integral_sub hi1 hi2]; ring
  rw [hdiff]
  have hpt : ∀ᵐ x ∂μ, 0 ≤ max (x - s) 0 - max (roundDown δ x - s) 0 ∧
      max (x - s) 0 - max (roundDown δ x - s) 0 ≤ δ := by
    filter_upwards [ae_mem_Icc_of_supp hsupp] with x hx
    have h := cert.rounded_stopLoss (roundDown δ x) x δ s (roundDown_nonneg hδ hx.1)
      (roundDown_le hδ x) (by linarith [lt_roundDown_add hδ x]) hδ hs
    rw [max_comm 0 (x - s), max_comm 0 (roundDown δ x - s)] at h
    exact h
  constructor
  · exact integral_nonneg_of_ae (hpt.mono fun x h => h.1)
  · have hint : Integrable (fun x => max (x - s) 0 - max (roundDown δ x - s) 0) μ := hi1.sub hi2
    calc ∫ x, (max (x - s) 0 - max (roundDown δ x - s) 0) ∂μ ≤ ∫ _, δ ∂μ :=
          integral_mono_ae hint (integrable_const δ) (hpt.mono fun x h => h.2)
      _ = δ := by rw [integral_const, probReal_univ, one_smul]

/-- The gain against the rounded law is at most the gain against the law. -/
theorem gainFromMass_rounded_le (hsupp : μ (Icc 0 bbar)ᶜ = 0) (hδ : 0 < δ) {ϖ : ℝ → ℝ}
    (hϖ : IsCumulativeMass bbar ϖ) {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    gainFromMass bbar (μ.map (roundDown δ)) ϖ s ≤ gainFromMass bbar μ ϖ s := by
  have hb := bbar_nonneg_of_supp hsupp
  have hr := measurable_roundDown hδ
  have hsuppδ := rounded_supported hsupp hδ
  haveI : IsProbabilityMeasure (μ.map (roundDown δ)) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  rw [gainFromMass_eq' hsuppδ (goodMass_of_antitoneOn hsuppδ hϖ.antitoneOn),
    gainFromMass_eq' hsupp (goodMass_of_antitoneOn hsupp hϖ.antitoneOn)]
  set F : ℝ → ℝ := (Ioc s bbar).indicator (fun t => (t - s) * (ϖ s - ϖ t)) with hF
  have hset : ∀ ν : Measure ℝ,
      ∫ t in Ioc s bbar, (t - s) * (ϖ s - ϖ t) ∂ν = ∫ t, F t ∂ν := fun ν =>
    (integral_indicator measurableSet_Ioc).symm
  rw [hset, hset]
  -- `F` is nonnegative and nondecreasing on `[0, b̄]`
  have hFnn : ∀ v ∈ Icc 0 bbar, 0 ≤ F v := by
    intro v hv
    simp only [hF, indicator, mem_Ioc]
    split_ifs with h
    · exact mul_nonneg (by linarith [h.1]) (by linarith [hϖ.antitoneOn hs hv h.1.le])
    · exact le_rfl
  have hFmono : ∀ u ∈ Icc 0 bbar, ∀ v ∈ Icc 0 bbar, u ≤ v → F u ≤ F v := by
    intro u hu v hv huv
    by_cases hsu : s < u
    · have hsv : s < v := hsu.trans_le huv
      simp only [hF, indicator, mem_Ioc]
      rw [if_pos ⟨hsu, hu.2⟩, if_pos ⟨hsv, hv.2⟩]
      have h1 : ϖ u ≤ ϖ s := hϖ.antitoneOn hs hu hsu.le
      have h2 : ϖ v ≤ ϖ u := hϖ.antitoneOn hu hv huv
      exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    · have : F u = 0 := by
        simp only [hF, indicator, mem_Ioc]
        rw [if_neg (fun h => hsu h.1)]
      rw [this]
      exact hFnn v hv
  -- measurability and integrability
  have hFaesm : ∀ ν : Measure ℝ, ν (Icc 0 bbar)ᶜ = 0 → AEStronglyMeasurable F ν := fun ν hν =>
    ((measurable_id.sub_const s).aestronglyMeasurable.mul
      (aestronglyMeasurable_const.sub (aestronglyMeasurable_of_antitoneOn hν hϖ.antitoneOn))).indicator
      measurableSet_Ioc
  have hbd : ∀ v ∈ Icc 0 bbar, ‖F v‖ ≤ F bbar := fun v hv => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn v hv)]
    exact hFmono v hv bbar ⟨hb, le_rfl⟩ hv.2
  have hi1 : Integrable (fun x => F (roundDown δ x)) μ := by
    refine Integrable.of_bound ((hFaesm _ hsuppδ).comp_aemeasurable hr.aemeasurable) (F bbar) ?_
    filter_upwards [ae_mem_Icc_of_supp hsupp] with x hx
    exact hbd _ (roundDown_mem_Icc hδ hx)
  have hi2 : Integrable F μ := by
    refine Integrable.of_bound (hFaesm _ hsupp) (F bbar) ?_
    filter_upwards [ae_mem_Icc_of_supp hsupp] with x hx
    exact hbd x hx
  rw [integral_map hr.aemeasurable (hFaesm _ hsuppδ)]
  have hle : ∫ x, F (roundDown δ x) ∂μ ≤ ∫ x, F x ∂μ := by
    refine integral_mono_ae hi1 hi2 ?_
    filter_upwards [ae_mem_Icc_of_supp hsupp] with x hx
    exact hFmono _ (roundDown_mem_Icc hδ hx) x hx (roundDown_le hδ x)
  linarith

end RoundedLaw

section Shift

variable {δ bbar d : ℝ} {law : Fin 2 → Measure ℝ}

/-- A mass feasible for the rounded bodies, plus `δ`, is feasible for the bodies with the same
compensation (certified field `tail_repair`). -/
theorem isFeasibleMass_add_of_rounded (cert : PricingScalarCertificates)
    (hB : IsBuyerBodies bbar law) (hδ : 0 < δ) {ϑ ϖ : ℝ → ℝ}
    (hF : IsFeasibleMass bbar (roundedLaw δ law) d ϑ ϖ) :
    IsFeasibleMass bbar law d ϑ (fun t => ϖ t + δ) := by
  have hcum := hF.cumulative
  refine ⟨⟨fun s hs => by linarith [hcum.nonneg s hs], fun a ha c hc hac => ?_,
    fun s hs => (hcum.rightContinuous s hs).add continuousWithinAt_const⟩, fun i s hs => ?_⟩
  · show ϖ c + δ ≤ ϖ a + δ
    linarith [hcum.antitoneOn ha hc hac]
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  have h0 := hF.potential_ge i s hs
  rw [sellerPotential_add_const' hsupp (goodMass_of_antitoneOn hsupp hcum.antitoneOn) d δ s]
  have hL := Lbar_sub_rounded cert hsupp hδ hs.1
  have hG := gainFromMass_rounded_le hsupp hδ hcum hs
  have htr := cert.tail_repair _ _ δ hL.1 hL.2 (sub_nonneg.mpr hG)
  have e : sellerPotential bbar (roundedLaw δ law i) d ϖ s =
      d * s - Lbar ((law i).map (roundDown δ)) s +
        gainFromMass bbar ((law i).map (roundDown δ)) ϖ s := rfl
  rw [e] at h0
  unfold sellerPotential
  linarith

end Shift

end FixedPrice.TwoUnit.Pricing
