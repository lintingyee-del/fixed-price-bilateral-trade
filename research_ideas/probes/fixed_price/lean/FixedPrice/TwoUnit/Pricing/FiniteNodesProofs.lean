import FixedPrice.TwoUnit.Pricing.FiniteNodesCover

/-!
# Finite-node recurrence, work package E (secondary target)

Owner: package E (see `blueprints/theoremE.md`). Exports proofs of the claims stated in
`FiniteNodes.lean`, each `<name>_proof` with type `<Name>Statement`. The proofs live in
`FiniteNodesBasic` (node laws, cells, the backward pass and its leastness), `FiniteNodesAffine`
(piecewise affine and convex value) and `FiniteNodesCover` (slopes between nodes, jumps at nodes,
ordered potential sums); they use a few kernel lemmas of package A (`one_le_Lbar'`) and the sign
lemmas of package C. The node step facts are fields of `NodeScalarCertificates` (and the obstacle
identity and the ordered Farkas step are fields of `PricingScalarCertificates`); they are used
through the certificate arguments, never re-proved.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing.NodeData

/-! ### Exports -/

theorem nodeMass_last_proof : NodeMassLastStatement := by
  intro n D d ϑ
  exact D.nodeMass_last' d ϑ

theorem nodeMass_backward_proof : NodeMassBackwardStatement := by
  intro n D d ϑ j hj
  exact D.nodeMass_backward' d ϑ hj

theorem nodeMass_isLeastSolution_proof : NodeMassIsLeastSolutionStatement := by
  intro n cert D d _ ϑ _
  exact D.nodeMass_isLeastSolution' cert d ϑ

theorem nodeValue_convex_piecewiseAffine_proof : NodeValueConvexPiecewiseAffineStatement := by
  intro n _ D
  exact D.nodeValue_convex_piecewiseAffine'

theorem stepMass_eq_on_cell_proof : StepMassEqOnCellStatement := by
  intro n D w j hj
  exact ⟨D.stepMass_node w hj, fun hjn s hs => D.stepMass_of_cell (D.inCell_Ico hjn hs) w⟩

theorem priceBody_spec_proof : PriceBodySpecStatement := by
  intro n D w _ hwa
  exact D.priceBody_spec' hwa

theorem sellerPotential_hasDerivAt_between_nodes_proof :
    SellerPotentialHasDerivAtBetweenNodesStatement := by
  intro n D d hd w hw₀ hwa i j hj s hs
  exact D.sellerPotential_hasDerivAt' hd hw₀ hwa i hj hs

theorem sellerPotential_jump_at_node_proof : SellerPotentialJumpAtNodeStatement := by
  intro n D d w i j hj₁ hj
  exact D.sellerPotential_jump' d w i hj₁ hj

theorem nodeSolution_orderedSum_nonneg_proof : NodeSolutionOrderedSumNonnegStatement := by
  intro n cert _ D d hd ϑ hϑ w hw hbudget s₁ s₂ h₁ h₁₂
  exact D.nodeSolution_orderedSum_nonneg' cert hd hϑ hw hbudget s₁ s₂ h₁ h₁₂

end FixedPrice.TwoUnit.Pricing.NodeData
