import FixedPrice.Sharpness

/-! **Theorem A** in full. Over independent pairs of nonnegative finite-mean value laws with
positive first-best welfare, the best fixed-price welfare ratio
`(M + sup_{z ≥ 0} Γ(z)) / (M + G)` has infimum `β_* = 1/S(C_*)`, where `C_*` is the unique
root of (44) in `(1/4, 1/2)`; the infimum is not attained, and bounded hard pairs approach it
at the linear rate of Proposition 13.1. The decimal enclosure of `β_*` is computed outside Lean. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- The model of Section 3: independent nonnegative values with
`0 < E max{V_s, V_b} = M + G < ∞`. -/
structure AdmissiblePair (μs μb : Measure ℝ) : Prop where
  probS : IsProbabilityMeasure μs
  probB : IsProbabilityMeasure μb
  nonnegS : ∀ᵐ s ∂μs, 0 ≤ s
  nonnegB : ∀ᵐ b ∂μb, 0 ≤ b
  intS : Integrable (fun s => s) μs
  intB : Integrable (fun b => b) μb
  pos : 0 < sellerMean μs + gainsFromTrade μs μb

/-- The best fixed-price welfare ratio `(M + Γ_max)/(M + G)`, `Γ_max = sup_{z ≥ 0} Γ(z)`. -/
def fixedPriceRatio (μs μb : Measure ℝ) : ℝ :=
  (sellerMean μs + ⨆ z : Ici (0 : ℝ), gain μs μb z) / (sellerMean μs + gainsFromTrade μs μb)

section Ratio

variable {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

theorem gain_le_gainsFromTrade (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb) (z : ℝ) :
    gain μs μb z ≤ gainsFromTrade μs μb := by
  rw [gainsFromTrade_eq_integral_tail]
  apply integral_mono (integrable_inner_gain μs μb hbint hsint z)
    (integrable_tailIntegral_seller hbint hs0)
  intro s
  apply integral_mono (integrable_tradeGain μb hbint s z) (integrable_max_sub μb hbint s)
  intro b
  simp only
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem gain_bddAbove (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb) :
    BddAbove (range fun z : Ici (0 : ℝ) => gain μs μb z) :=
  ⟨gainsFromTrade μs μb, by
    rintro _ ⟨z, rfl⟩
    exact gain_le_gainsFromTrade hs0 hsint hbint z⟩

/-- A price with welfare above `β (M + G)` puts the best ratio above `β`. -/
theorem lt_fixedPriceRatio {β : ℝ} (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb)
    (hpos : 0 < sellerMean μs + gainsFromTrade μs μb) {z : ℝ} (hz : 0 ≤ z)
    (h : β * (sellerMean μs + gainsFromTrade μs μb) < sellerMean μs + gain μs μb z) :
    β < fixedPriceRatio μs μb := by
  unfold fixedPriceRatio
  rw [lt_div_iff₀ hpos]
  have := le_ciSup (gain_bddAbove hs0 hsint hbint) (⟨z, hz⟩ : Ici (0 : ℝ))
  linarith

omit [IsProbabilityMeasure μs] [IsProbabilityMeasure μb] in
/-- A bound at every price bounds the best ratio. -/
theorem fixedPriceRatio_le {e : ℝ} (hpos : 0 < sellerMean μs + gainsFromTrade μs μb)
    (h : ∀ z : ℝ, 0 ≤ z →
      sellerMean μs + gain μs μb z ≤ e * (sellerMean μs + gainsFromTrade μs μb)) :
    fixedPriceRatio μs μb ≤ e := by
  unfold fixedPriceRatio
  rw [div_le_iff₀ hpos]
  have : (⨆ z : Ici (0 : ℝ), gain μs μb z) ≤
      e * (sellerMean μs + gainsFromTrade μs μb) - sellerMean μs := by
    apply ciSup_le
    intro z
    have := h z z.2
    linarith
  linarith

end Ratio

/-- The hard pair is admissible, with seller values in `[0, 1]` and buyer values in `[0, R_η]`. -/
theorem hardPair_admissible {d η : ℝ} {H : ℝ → ℝ} (P : HardPairData d η H) :
    AdmissiblePair P.sellerLaw P.buyerLaw where
  probS := inferInstance
  probB := inferInstance
  nonnegS := P.seller_nonneg
  nonnegB := P.buyer_nonneg
  intS := P.seller_integrable
  intB := P.buyer_integrable
  pos := P.hd.trans_le P.d_le_welfare

/-- **Proposition 13.1 (finite-tail error).** At a root `C` of (44) with `d = τ(C)`, the hard
pair at `η ∈ (0, 1]` has best ratio `r_η` with
`0 < r_η - β_* ≤ η (β_* L_err(d) + 1/d)`. -/
theorem proposition_finiteTail {C η : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) (hη : η ∈ Ioc (0 : ℝ) 1) :
    let P := hardPairData (initialState_pos hC) hC rfl hη
    0 < fixedPriceRatio P.sellerLaw P.buyerLaw - (optimalValue C)⁻¹ ∧
      fixedPriceRatio P.sellerLaw P.buyerLaw - (optimalValue C)⁻¹ ≤
        η * ((optimalValue C)⁻¹ * perturbConst (initialState C) + 1 / initialState C) := by
  intro P
  have A := hardPair_admissible P
  constructor
  · obtain ⟨z, hz, hlt⟩ := theoremA_strict hC hroot A.nonnegS A.intS A.intB A.pos
    have := lt_fixedPriceRatio A.nonnegS A.intS A.intB A.pos hz hlt
    linarith
  · have := fixedPriceRatio_le A.pos fun z _ =>
      hardPair_welfare_le (initialState_pos hC) hC rfl hroot hη z
    linarith

/-- **Theorem A.** Let `C_*` be the root of (44) and `β_* = 1/S(C_*)`. Every admissible pair
has best fixed-price welfare ratio strictly above `β_*`; for every `ε > 0` a bounded hard pair
has ratio below `β_* + ε`; hence `β_*` is the infimum over admissible pairs. -/
theorem theoremA {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) :
    (∀ μs μb : Measure ℝ, AdmissiblePair μs μb → (optimalValue C)⁻¹ < fixedPriceRatio μs μb) ∧
    (∀ ε > 0, ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧
      (∀ᵐ s ∂μs, s ∈ Icc (0 : ℝ) 1) ∧ (∃ R : ℝ, ∀ᵐ b ∂μb, b ∈ Icc (0 : ℝ) R) ∧
      fixedPriceRatio μs μb < (optimalValue C)⁻¹ + ε) ∧
    IsGLB {r | ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧ fixedPriceRatio μs μb = r}
      (optimalValue C)⁻¹ := by
  have hstrict : ∀ μs μb : Measure ℝ, AdmissiblePair μs μb →
      (optimalValue C)⁻¹ < fixedPriceRatio μs μb := by
    intro μs μb A
    haveI := A.probS
    haveI := A.probB
    obtain ⟨z, hz, hlt⟩ := theoremA_strict hC hroot A.nonnegS A.intS A.intB A.pos
    exact lt_fixedPriceRatio A.nonnegS A.intS A.intB A.pos hz hlt
  have hsharp : ∀ ε > 0, ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧
      (∀ᵐ s ∂μs, s ∈ Icc (0 : ℝ) 1) ∧ (∃ R : ℝ, ∀ᵐ b ∂μb, b ∈ Icc (0 : ℝ) R) ∧
      fixedPriceRatio μs μb < (optimalValue C)⁻¹ + ε := by
    intro ε hε
    set d := initialState C with hd_def
    have hd : 0 < d := initialState_pos hC
    set K := (optimalValue C)⁻¹ * perturbConst d + 1 / d with hK_def
    have hβ : 0 < (optimalValue C)⁻¹ := inv_pos.mpr (by linarith [one_lt_optimalValue hC])
    have hK : 0 < K := by
      have : 0 ≤ perturbConst d := by unfold perturbConst; positivity
      have : 0 < 1 / d := one_div_pos.mpr hd
      positivity
    set η := min 1 (ε / (2 * K)) with hη_def
    have hη : η ∈ Ioc (0 : ℝ) 1 := ⟨lt_min zero_lt_one (by positivity), min_le_left _ _⟩
    have hηK : η * K < ε := by
      calc η * K ≤ ε / (2 * K) * K := mul_le_mul_of_nonneg_right (min_le_right _ _) hK.le
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    have hP := proposition_finiteTail hC hroot hη
    set P := hardPairData hd hC rfl hη
    refine ⟨P.sellerLaw, P.buyerLaw, hardPair_admissible P, P.seller_ae_mem,
      ⟨buyerAtom d η, P.buyer_ae_mem⟩, ?_⟩
    linarith [hP.2]
  refine ⟨hstrict, hsharp, ?_, ?_⟩
  · rintro r ⟨μs, μb, A, rfl⟩
    exact (hstrict μs μb A).le
  · intro b hb
    by_contra hlt
    push Not at hlt
    obtain ⟨μs, μb, A, -, -, hr⟩ := hsharp (b - (optimalValue C)⁻¹) (by linarith)
    have := hb ⟨μs, μb, A, rfl⟩
    linarith

/-- The constant of Theorem A exists and is unique. -/
theorem theoremA_constant :
    ∃! C : ℝ, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ optimalValue C = 1 + initialState C :=
  existsUnique_root

end FixedPrice
