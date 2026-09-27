import FixedPrice.TwoUnit.Pricing.OperatorLeast

/-!
# Theorem E, work package A: kernel and operator (part (i))

Owner: package A (see `blueprints/theoremE.md`). This file exports proofs of the statements that
`Statements.lean` tags `[A]`. Each export `<name>_proof` has as its type the statement
`<Name>Statement` fixed in `Statements.lean`, so the proof cannot drift from the statement.
Downstream packages import this file and use the `_proof` names; while an export is still an
unproved stub they can already build on it.

Package A adds its internal lemmas above the exports (or in further files it owns, named
`Operator*.lean`). It must not re-prove any field of `PricingScalarCertificates`; use `cert`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-! ### Exports -/

theorem self_add_Lbar_proof : SelfAddLbarStatement := by
  intro bbar μ _ hsupp s
  exact self_add_Lbar' hsupp s

theorem potential_ge_iff_operator_le_proof : PotentialGeIffOperatorLeStatement := by
  intro cert bbar law hB d hd ϑ hϑ ϖ hϖ₀ hϖ
  exact potential_ge_iff_operator_le' cert hB hd hϑ hϖ₀ hϖ

theorem one_le_Lbar_proof : OneLeLbarStatement := fun μ s => one_le_Lbar' μ s

theorem Lbar_le_one_add_proof : LbarLeOneAddStatement := by
  intro bbar μ _ hsupp s hs
  exact Lbar_le_one_add' hsupp hs

theorem Lbar_eq_one_of_le_proof : LbarEqOneOfLeStatement := by
  intro bbar μ _ hsupp s hs
  exact Lbar_eq_one_of_le' hsupp hs

theorem Lbar_lipschitz_proof : LbarLipschitzStatement := by
  intro bbar μ _ hsupp
  exact Lbar_lipschitz' hsupp

theorem kernelIntegral_const_proof : KernelIntegralConstStatement := by
  intro bbar μ _ hsupp c s
  exact kernelIntegral_const' hsupp c s

theorem kernelIntegral_mono_proof : KernelIntegralMonoStatement := by
  intro bbar μ _ hsupp ϖ ϖ' hϖ hϖ' s _ hle
  exact kernelIntegral_mono_of_le hsupp (goodMass_of_antitoneOn hsupp hϖ)
    (goodMass_of_antitoneOn hsupp hϖ') hle

theorem kernelIntegral_continuousOn_proof : KernelIntegralContinuousOnStatement := by
  intro bbar μ _ hsupp ϖ hϖ
  exact (continuous_kernelIntegral hsupp (goodMass_of_antitoneOn hsupp hϖ)).continuousOn

theorem gainFromMass_eq_proof : GainFromMassEqStatement := by
  intro bbar μ _ hsupp ϖ hϖ s _
  exact gainFromMass_eq' hsupp (goodMass_of_antitoneOn hsupp hϖ) s

theorem sellerPotential_convexComb_proof : SellerPotentialConvexCombStatement := by
  intro bbar μ _ hsupp ϖ₁ ϖ₂ hϖ₁ hϖ₂ a d₁ d₂ s _
  exact sellerPotential_convexComb' hsupp (goodMass_of_antitoneOn hsupp hϖ₁)
    (goodMass_of_antitoneOn hsupp hϖ₂) a d₁ d₂ s

theorem sellerPotential_add_const_proof : SellerPotentialAddConstStatement := by
  intro bbar μ _ hsupp ϖ hϖ d c s _
  exact sellerPotential_add_const' hsupp (goodMass_of_antitoneOn hsupp hϖ) d c s

theorem leastMass_isFeasible_proof : LeastMassIsFeasibleStatement := by
  intro bbar cert law hB d hd ϑ hϑ
  exact leastMass_isFeasible' cert hB hd hϑ

theorem leastMass_le_of_isFeasible_proof : LeastMassLeOfIsFeasibleStatement := by
  intro bbar cert law hB d hd ϑ hϑ ϖ hϖ
  exact leastMass_le_of_isFeasible' cert hB hd hϑ hϖ

theorem theoremE_part_i_proof : TheoremEPartIStatement := by
  intro cert P d hd ϑ hϑ
  have hB := P.bodies
  have hb := bbar_nonneg_of_bodies hB
  have hϑc : IsCompensation P.bbar ϑ := hϑ
  obtain ⟨C, hC⟩ := hϑc.bounded
  have h0mem : (0 : ℝ) ∈ Icc 0 P.bbar := ⟨le_rfl, hb⟩
  refine ⟨leastMass_isBoundedOn cert hB hd hC,
    fun s hs => leastMass_isFixedPt cert hB hd hC hs,
    fun ϖ hϖb hfix => fixedPt_eq_leastMass cert hB hd hC hϖb hfix,
    leastMass_isFeasible' cert hB hd hϑ,
    fun ϖ hϖ => leastMass_le_of_isFeasible' cert hB hd hϑ hϖ, ?_, ?_, ?_⟩
  · intro ϖ₁ ϖ₂ hm₁ hm₂ hb₁ hb₂ E hE s hs
    have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 0 h0mem)
    exact abs_pricingOperator_sub_le hB hd ⟨C, hC⟩ cert (goodMass2_of_measurable hm₁ hb₁)
      (goodMass2_of_measurable hm₂ hb₂) hE0 hE hs
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hq0 : 0 ≤ P.bbar / (1 + P.bbar) := by positivity
    have hq1 : P.bbar / (1 + P.bbar) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hlim : Tendsto (fun n : ℕ => (P.bbar / (1 + P.bbar)) ^ n *
        leastMass P.bbar P.law d ϑ 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
        (leastMass P.bbar P.law d ϑ 0)
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn x hx
    rw [Real.dist_eq, abs_sub_comm]
    exact (iter_rate cert hB hd hC n x hx).trans_lt hn
  · intro n s hs
    exact iter_rate cert hB hd hC n s hs

end FixedPrice.TwoUnit.Pricing
