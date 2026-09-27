import FixedPrice.TwoUnit.Pricing.RoundingValue

/-!
# Theorem E, work package D: rounding, finite support, independence of `b̄` (part (iv))

Owner: package D (see `blueprints/theoremE.md`). Exports proofs of the statements that
`Statements.lean` tags `[D]`, each `<name>_proof` with type `<Name>Statement`. The proofs live in
`RoundingBasic` (rounded bodies, `0 ≤ L̄ - L̄^δ ≤ δ`, the gain comparison, the `+δ` repair) and
`RoundingValue` (independence of `b̄`, part (iv)); they use the internal lemmas of packages A
and C. The pointwise rounding inequalities are fields of `PricingScalarCertificates`
(`rounded_stopLoss`, `tail_repair`) and are used through `cert`, never re-proved.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-! ### Exports -/

theorem roundedLaw_spec_proof : RoundedLawSpecStatement := by
  intro P δ hδ
  exact roundedLaw_spec' P hδ

theorem pricingValue_eq_of_bound_le_proof : PricingValueEqOfBoundLeStatement := by
  intro cert b b' law hB hbb' d hd
  exact pricingValue_eq_of_bound_le' cert hB hbb' hd

theorem theoremE_part_iv_proof : TheoremEPartIVStatement := by
  intro cert P d δ hd hδ
  exact theoremE_part_iv' cert P hd hδ

theorem theoremE_part_iv_sup_proof : TheoremEPartIVSupStatement := by
  intro cert d hd
  exact theoremE_part_iv_sup' cert hd

end FixedPrice.TwoUnit.Pricing
