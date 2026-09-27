import FixedPrice.TwoUnit.Pricing.AttainmentLimit

/-!
# Theorem E, work package C: canonical compensation, convexity, attainment (part (ii))

Owner: package C (see `blueprints/theoremE.md`). Exports proofs of the statements that
`Statements.lean` tags `[C]`, each `<name>_proof` with type `<Name>Statement`. Uses package A
only through the `_proof` exports of `Operator.lean`. Internal lemmas go above the exports or
into further files named `Attainment*.lean`; integrability facts that package A proves
internally (blueprint A2, A6) are re-proved here as local copies. Fields of
`PricingScalarCertificates` are used through `cert`, never re-proved.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-! ### Exports -/

theorem orderedSum_ge_of_compensation_proof : OrderedSumGeOfCompensationStatement := by
  intro _ bbar law d ϑ ϖ hϑ hψ s₁ s₂ h1 h12 h2
  exact orderedSum_ge' hϑ hψ h1 h12 h2

theorem canonicalCompensation_spec_proof : CanonicalCompensationSpecStatement := by
  intro _ bbar law hB d _ ϖ hϖ hsum
  exact canonicalCompensation_spec' hB hϖ hsum

theorem pricingValue_isLeast_proof : PricingValueIsLeastStatement := by
  intro bbar cert law hB d hd
  exact pricingValue_isLeast' cert hB hd

theorem theoremE_part_ii_proof : TheoremEPartIIStatement := by
  intro cert P
  exact ⟨leastMass_convexOn cert P.bodies, fun d hd => pricingValue_isLeast' cert P.bodies hd⟩

end FixedPrice.TwoUnit.Pricing
