import FixedPrice.DSICClass
import FixedPrice.Smoothing

/-! **Corollary 11.3.** For measurable dominant-strategy mechanisms on the nonnegative reports
with `s φ ≤ pay ≤ b φ`, allowing the mechanism to depend on the prior pair, the optimal
universal welfare guarantee is `β_*`. The ceiling uses a bounded hard pair of Theorem A,
smooths it (Lemma 11.1) into an absolutely continuous pair on `(0, Λ)²`, and applies the
welfare bound of Proposition 11.2 to the restriction of the mechanism to `(0, Λ)`. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- **Corollary 11.3, ceiling.** For every `ε > 0` there is an admissible, absolutely continuous
pair on `(0, Λ)²` on which every mechanism of `DSICOn Λ` has welfare below `β_* + ε` times
first-best welfare. -/
theorem dsic_ceiling {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) {ε : ℝ} (hε : 0 < ε) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧ μs ≪ volume ∧ μb ≪ volume ∧
      (∀ᵐ s ∂μs, s ∈ Ioo 0 Λ) ∧ (∀ᵐ b ∂μb, b ∈ Ioo 0 Λ) ∧
      ∀ φ pay : ℝ → ℝ → ℝ, DSICOn Λ φ pay →
        mechWelfare (μs.prod μb) φ < ((optimalValue C)⁻¹ + ε) * firstBest (μs.prod μb) := by
  obtain ⟨-, hsharp, -⟩ := theoremA hC hroot
  obtain ⟨μs, μb, A, hs1, ⟨R, hbR⟩, hr⟩ := hsharp (ε / 2) (by linarith)
  haveI := A.probS
  haveI := A.probB
  set β := (optimalValue C)⁻¹ with hβ_def
  have hβ : 0 < β := inv_pos.mpr (by linarith [one_lt_optimalValue hC])
  set Λ := max 1 R + 1 with hΛ_def
  have hΛ : 0 < Λ := by have := le_max_left 1 R; linarith
  have hsΛ : ∀ᵐ s ∂μs, s ∈ Icc 0 Λ :=
    hs1.mono fun s hs => ⟨hs.1, hs.2.trans (by linarith [le_max_left 1 R])⟩
  have hbΛ : ∀ᵐ b ∂μb, b ∈ Icc 0 Λ :=
    hbR.mono fun b hb => ⟨hb.1, hb.2.trans (by linarith [le_max_right 1 R])⟩
  set W := sellerMean μs + gainsFromTrade μs μb with hW_def
  have hW : 0 < W := A.pos
  set Gm := ⨆ z : Ici (0 : ℝ), gain μs μb z with hGm
  have hr' : sellerMean μs + Gm < (β + ε / 2) * W := by
    unfold fixedPriceRatio at hr
    rwa [div_lt_iff₀ hW] at hr
  set η := ε * W / (2 * (1 + β + ε)) with hη_def
  have hη : 0 < η := by positivity
  have hηW : η < W := by
    rw [hη_def, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨μs', μb', hP1, hP2, hac1, hac2, hsupp1, hsupp2, hfb, hprice⟩ :=
    lemma_smoothing hΛ hsΛ hbΛ hη
  have hint : ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∀ᵐ x ∂ν, x ∈ Ioo 0 Λ) →
      Integrable (fun x => x) ν := by
    intro ν _ h
    refine Integrable.of_bound measurable_id.aestronglyMeasurable Λ ?_
    filter_upwards [h] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hx.1]
    exact hx.2.le
  have hsint' := hint μs' hP1 hsupp1
  have hbint' := hint μb' hP2 hsupp2
  have hfb' : W - η ≤ firstBest (μs'.prod μb') := by
    have := (abs_le.mp hfb).1
    linarith
  have A' : AdmissiblePair μs' μb' :=
    { probS := hP1
      probB := hP2
      nonnegS := hsupp1.mono fun s hs => hs.1.le
      nonnegB := hsupp2.mono fun b hb => hb.1.le
      intS := hsint'
      intB := hbint'
      pos := by
        haveI := hP1
        haveI := hP2
        rw [← firstBest_prod hsint' hbint']
        linarith }
  refine ⟨Λ, hΛ, μs', μb', A', hac1, hac2, hsupp1, hsupp2, ?_⟩
  intro φ pay M
  haveI := hP1
  haveI := hP2
  have hac : μs'.prod μb' ≪ volume := by
    rw [Measure.volume_eq_prod]
    exact hac1.prod hac2
  have hsupp : ∀ᵐ p ∂(μs'.prod μb'), p ∈ Ioo 0 Λ ×ˢ Ioo 0 Λ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsupp1,
      Measure.quasiMeasurePreserving_snd.ae hsupp2] with p h1 h2
    exact ⟨h1, h2⟩
  have h1 := M.mechWelfare_le (μs'.prod μb') hac hsupp
  have h2 : ⨆ z : ℝ, jointPriceWelfare (μs'.prod μb') z ≤ sellerMean μs + Gm + η :=
    ciSup_le hprice
  have key : (β + ε / 2) * W + η ≤ (β + ε) * (W - η) := by
    have : η * (1 + β + ε) = ε * W / 2 := by
      rw [hη_def]
      field_simp
    nlinarith
  calc mechWelfare (μs'.prod μb') φ ≤ sellerMean μs + Gm + η := h1.trans h2
    _ < (β + ε / 2) * W + η := by linarith
    _ ≤ (β + ε) * (W - η) := key
    _ ≤ (β + ε) * firstBest (μs'.prod μb') :=
        mul_le_mul_of_nonneg_left hfb' (by positivity)

/-- Measurable dominant-strategy mechanisms on the nonnegative reports. -/
def DSICMech : Type :=
  {m : (ℝ → ℝ → ℝ) × (ℝ → ℝ → ℝ) // DSICNonneg m.1 m.2 ∧ Measurable (uncurry m.1)}

instance : Nonempty DSICMech := ⟨⟨(fpAlloc 0, fpPay 0), fixedPrice_dsic 0, measurable_fpAlloc 0⟩⟩

/-- The best welfare ratio a measurable dominant-strategy mechanism attains on the pair. -/
def dsicRatio (μs μb : Measure ℝ) : ℝ :=
  ⨆ M : DSICMech, mechWelfare (μs.prod μb) M.1.1 / firstBest (μs.prod μb)

/-- Mechanism welfare never exceeds first-best welfare. -/
theorem mechWelfare_le_firstBest {μs μb : Measure ℝ} (A : AdmissiblePair μs μb)
    {φ pay : ℝ → ℝ → ℝ} (M : DSICNonneg φ pay) (hφ : Measurable (uncurry φ)) :
    mechWelfare (μs.prod μb) φ ≤ firstBest (μs.prod μb) := by
  haveI := A.probS
  haveI := A.probB
  have hnn : ∀ᵐ p ∂(μs.prod μb), 0 ≤ p.1 ∧ 0 ≤ p.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae A.nonnegS,
      Measure.quasiMeasurePreserving_snd.ae A.nonnegB] with p h1 h2
    exact ⟨h1, h2⟩
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) (μs.prod μb) := A.intS.comp_fst μb
  have h2 : Integrable (fun p : ℝ × ℝ => p.2) (μs.prod μb) := A.intB.comp_snd μs
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 + (p.2 - p.1) * φ p.1 p.2) :=
    measurable_fst.add ((measurable_snd.sub measurable_fst).mul hφ)
  have hmint : Integrable (fun p : ℝ × ℝ => p.1 + (p.2 - p.1) * φ p.1 p.2) (μs.prod μb) := by
    refine Integrable.mono' ((h1.norm.add h1.norm).add h2.norm) hmeas.aestronglyMeasurable ?_
    filter_upwards [hnn] with p hp
    have h0 := M.nonneg p.1 hp.1 p.2 hp.2
    have h1' := M.le_one p.1 hp.1 p.2 hp.2
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg hp.1, abs_of_nonneg hp.2]
    rw [abs_le]
    constructor <;> nlinarith
  have hfint : Integrable (fun p : ℝ × ℝ => max p.1 p.2) (μs.prod μb) := by
    refine Integrable.mono' (h1.norm.add h2.norm)
      (measurable_fst.max measurable_snd).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_le]
    constructor
    · linarith [neg_abs_le p.1, le_max_left p.1 p.2, abs_nonneg p.2]
    · exact max_le (by linarith [le_abs_self p.1, abs_nonneg p.2])
        (by linarith [le_abs_self p.2, abs_nonneg p.1])
  unfold mechWelfare firstBest
  apply integral_mono_ae hmint hfint
  filter_upwards [hnn] with p hp
  have h0 := M.nonneg p.1 hp.1 p.2 hp.2
  have h1' := M.le_one p.1 hp.1 p.2 hp.2
  rcases le_total p.1 p.2 with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

theorem dsicRatio_bddAbove {μs μb : Measure ℝ} (A : AdmissiblePair μs μb) :
    BddAbove (range fun M : DSICMech => mechWelfare (μs.prod μb) M.1.1 / firstBest (μs.prod μb)) := by
  haveI := A.probS
  haveI := A.probB
  have hpos : 0 < firstBest (μs.prod μb) := by
    rw [firstBest_prod A.intS A.intB]
    exact A.pos
  refine ⟨1, ?_⟩
  rintro _ ⟨M, rfl⟩
  rw [div_le_one hpos]
  exact mechWelfare_le_firstBest A M.2.1 M.2.2

/-- **Corollary 11.3 (exact dominant-strategy guarantee).** Over admissible pairs, the best
welfare ratio of measurable dominant-strategy mechanisms, chosen separately for each pair,
has infimum `β_*`; every pair is strictly above it, and absolutely continuous pairs on bounded
report intervals come arbitrarily close even for mechanisms that are only required to be
dominant-strategy on the support interval. -/
theorem corollary_dsic {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) :
    (∀ μs μb : Measure ℝ, AdmissiblePair μs μb → (optimalValue C)⁻¹ < dsicRatio μs μb) ∧
    (∀ ε > 0, ∃ Λ : ℝ, 0 < Λ ∧ ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧
      μs ≪ volume ∧ μb ≪ volume ∧ (∀ᵐ s ∂μs, s ∈ Ioo 0 Λ) ∧ (∀ᵐ b ∂μb, b ∈ Ioo 0 Λ) ∧
      ∀ φ pay : ℝ → ℝ → ℝ, DSICOn Λ φ pay →
        mechWelfare (μs.prod μb) φ < ((optimalValue C)⁻¹ + ε) * firstBest (μs.prod μb)) ∧
    IsGLB {r | ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧ dsicRatio μs μb = r}
      (optimalValue C)⁻¹ := by
  have hlow : ∀ μs μb : Measure ℝ, AdmissiblePair μs μb →
      (optimalValue C)⁻¹ < dsicRatio μs μb := by
    intro μs μb A
    haveI := A.probS
    haveI := A.probB
    have hpos : 0 < firstBest (μs.prod μb) := by
      rw [firstBest_prod A.intS A.intB]
      exact A.pos
    obtain ⟨z, -, hM, hmeas, hlt⟩ := dsic_guarantee hC hroot A
    have := le_ciSup (dsicRatio_bddAbove A) ⟨(fpAlloc z, fpPay z), hM, hmeas⟩
    have hdiv : (optimalValue C)⁻¹ < mechWelfare (μs.prod μb) (fpAlloc z) / firstBest (μs.prod μb) := by
      rw [lt_div_iff₀ hpos]
      linarith
    exact hdiv.trans_le this
  have hceil := fun ε (hε : 0 < ε) => dsic_ceiling hC hroot hε
  refine ⟨hlow, hceil, ?_, ?_⟩
  · rintro r ⟨μs, μb, A, rfl⟩
    exact (hlow μs μb A).le
  · intro b hb
    by_contra hlt
    push Not at hlt
    obtain ⟨Λ, -, μs, μb, A, -, -, -, -, hM⟩ := hceil ((b - (optimalValue C)⁻¹) / 2) (by linarith)
    haveI := A.probS
    haveI := A.probB
    have hpos : 0 < firstBest (μs.prod μb) := by
      rw [firstBest_prod A.intS A.intB]
      exact A.pos
    have hle : dsicRatio μs μb ≤ (optimalValue C)⁻¹ + (b - (optimalValue C)⁻¹) / 2 := by
      apply ciSup_le
      intro M
      rw [div_le_iff₀ hpos]
      exact (hM M.1.1 M.1.2 (M.2.1.restrict Λ)).le
    have := hb ⟨μs, μb, A, rfl⟩
    linarith

end FixedPrice
