import FixedPrice.TwoUnit.Pricing.PriceTargetWelfare

/-!
# Theorem E, work package B: gain representation and the price target (part (iii))

Owner: package B (see `blueprints/theoremE.md`). Exports proofs of the statements that
`Statements.lean` tags `[B]`, each `<name>_proof` with type `<Name>Statement`. The proofs live in
`PriceTargetGain` (survival functions, gain representation), `PriceTargetReverse` (a price meeting
the target forces `β𝒥 ≤ 1`), `PriceTargetRealized` (the realized price as a measure),
`PriceTargetFinal` (the realized price meets the target; its tail above `b̄`) and
`PriceTargetWelfare` (the welfare clause); they use the internal lemmas of packages A and C.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-! ### Exports -/

theorem isCumulativeMass_of_price_proof : IsCumulativeMassOfPriceStatement := by
  intro bbar π₀ _ _ tail htail
  exact isCumulativeMass_of_price' π₀ htail

theorem integral_gainKernel_eq_gainFromMass_proof :
    IntegralGainKernelEqGainFromMassStatement := by
  intro bbar μ _ hsupp π _ s _
  exact integral_gainKernel' hsupp π s

theorem theoremE_part_iii_proof : TheoremEPartIIIStatement := by
  intro cert P d β hd hβ₀ _
  constructor
  · rintro ⟨π, hπ, htarget⟩
    exact le_one_of_priceTarget cert P.bodies hd hβ₀ hπ htarget
  · intro hβJ
    obtain ⟨⟨ϑ, hϑ, hopt⟩, -⟩ := pricingValue_isLeast' cert P.bodies hd
    have hb := bbar_nonneg_of_bodies P.bodies
    have hF := leastMass_isFeasible' cert P.bodies hd hϑ
    have h1 : β * leastMass P.bbar P.law d ϑ 0 ≤ 1 := by
      rw [show leastMass P.bbar P.law d ϑ 0 = P.value d from hopt]; exact hβJ
    exact ⟨realizedPrice P.bbar d β (leastMass P.bbar P.law d ϑ),
      isBoundedPriceLaw_realizedPrice hb hd hF.cumulative hβ₀.le h1,
      realizedPrice_priceTarget cert P.bodies hd hβ₀.le h1 hϑ hF⟩

theorem theoremE_part_iii_welfare_proof : TheoremEPartIIIWelfareStatement := by
  intro P β hβ₀ _ π hπ htarget ν _ hν hνb
  exact welfare_of_priceTarget P.bodies hβ₀ hπ htarget ν hν hνb

theorem realizedPrice_spec_proof : RealizedPriceSpecStatement := by
  intro cert P d β hd hβ₀ _ ϑ hϑ hopt hβJ
  have hb := bbar_nonneg_of_bodies P.bodies
  have hF := leastMass_isFeasible' cert P.bodies hd hϑ
  have h1 : β * leastMass P.bbar P.law d ϑ 0 ≤ 1 := by rw [hopt]; exact hβJ
  refine ⟨isBoundedPriceLaw_realizedPrice hb hd hF.cumulative hβ₀.le h1,
    realizedPrice_priceTarget cert P.bodies hd hβ₀.le h1 hϑ hF, fun t ht => ?_,
    realizedPrice_restrict P.bodies hd hβ₀.le h1 hF.cumulative⟩
  rw [realizedPrice_real_Ioi hb hd hF.cumulative hβ₀.le ht.1, extendedMass_of_mem ht]

end FixedPrice.TwoUnit.Pricing
