import FixedPrice.TwoUnit.Family.Basic
import FixedPrice.TwoUnit.Family.Compactness
import FixedPrice.TwoUnit.Family.Shape
import FixedPrice.TwoUnit.Family.Boundary
import FixedPrice.TwoUnit.Family.Stationary
import FixedPrice.TwoUnit.Family.Domain
import FixedPrice.TwoUnit.Family.Reconstruction
import FixedPrice.TwoUnit.Family.Witness
import FixedPrice.TwoUnit.Family.Realization
import FixedPrice.TwoUnit.Family.OfFinite
import FixedPrice.TwoUnit.Family.Assembly

/-!
# The two-unit family: end-to-end results (coordinator file)

Chains the export theorems of the six work packages into Proposition `prop:2fam-optimum` and its
lemmas, under the machine-certified hypotheses `FamilyNumerics` and `FamilyIdentities` only.
Every package export is proved; `#print axioms` of each theorem below shows `propext`,
`Classical.choice` and `Quot.sound` only (2026-09-26). The `lean` credential for the family names
the two hypothesis structures. `lem:2fam-shape` needs neither (`shape_holds`).
-/

namespace FixedPrice.TwoUnit.Family

/-- The shared foundations of work package A. -/
theorem foundations (hI : FamilyIdentities) :
    ClassBasicsStatement ∧ PositivityStatement ∧ ComparisonStatement ∧ SeqCompactStatement :=
  ⟨class_basics_proof, positivity_proof hI class_basics_proof,
    comparison_proof hI class_basics_proof, seq_compact_proof class_basics_proof⟩

/-- **Lemma `lem:2fam-compact`**, end to end. -/
theorem lem_2fam_compact (hN : FamilyNumerics) (hI : FamilyIdentities) : CompactStatement := by
  obtain ⟨hCB, hPos, hCmp, hSeq⟩ := foundations hI
  exact lem_2fam_compact_proof hN hI hCB hPos hCmp hSeq small_mass_mono_proof

/-- **Lemma `lem:2fam-shape`**, end to end. -/
theorem lem_2fam_shape (hI : FamilyIdentities) : ShapeStatement :=
  lem_2fam_shape_proof hI class_basics_proof

/-- **Lemma `lem:2fam-boundary`**, end to end. -/
theorem lem_2fam_boundary (hN : FamilyNumerics) (hI : FamilyIdentities) : BoundaryStatement := by
  obtain ⟨hCB, hPos, hCmp, -⟩ := foundations hI
  exact lem_2fam_boundary_proof hN hI hCB hPos hCmp (lem_2fam_compact hN hI)
    (lem_2fam_shape hI) (globalMax_energyMinimizer_proof hCmp) (affine_functionals_proof hI hCB)

/-- **Lemma `lem:2fam-domain`**, end to end. -/
theorem lem_2fam_domain (hN : FamilyNumerics) (hI : FamilyIdentities) : DomainStatement :=
  lem_2fam_domain_proof hN hI

/-- The at-most-one half of `lem:2fam-cover`, end to end. -/
theorem cover_atMostOne (hN : FamilyNumerics) (hI : FamilyIdentities) :
    CoverAtMostOneStatement := by
  have hDom := lem_2fam_domain hN hI
  have hConn := connI_eq_connJ_proof
  exact cover_atMostOne_proof hN hI hDom (phys_to_coverRoot_proof hN hI hDom hConn)
    (quadratures_proof hI class_basics_proof) hConn

/-- **Lemma `lem:2fam-cover`**, end to end. -/
theorem lem_2fam_cover (hN : FamilyNumerics) (hI : FamilyIdentities) : CoverStatement :=
  lem_2fam_cover_of hN (lem_2fam_domain hN hI)
    (reconstruction_proof hN hI connI_eq_connJ_proof) (cover_atMostOne hN hI)

/-- **Lemma `lem:2fam-witness`**, end to end. -/
theorem lem_2fam_witness (hN : FamilyNumerics) : WitnessStatement :=
  lem_2fam_witness_of hN polygon_curve_proof

/-- **Lemma `lem:2fam-realization`**, end to end. -/
theorem lem_2fam_realization (hI : FamilyIdentities) : RealizationStatement :=
  lem_2fam_realization_of (realization_escaping_proof hI class_basics_proof)

/-- **The finite model is the special case of the general model**, end to end. -/
theorem ofFinite_spec : OfFiniteStatement :=
  ofFinite_spec_proof

/-- **Proposition `prop:2fam-optimum`**, under the machine-certified hypotheses only. -/
theorem prop_2fam_optimum (hN : FamilyNumerics) (hI : FamilyIdentities) : OptimumStatement := by
  obtain ⟨hCB, hPos, hCmp, hSeq⟩ := foundations hI
  have hComp := lem_2fam_compact hN hI
  have hGM := globalMax_energyMinimizer_proof hCmp
  have hQ := quadratures_proof hI hCB
  exact prop_2fam_optimum_of_proof hN hI hPos hCmp hComp
    (ratio_attained_proof hCB hPos hSeq hComp) (lem_2fam_shape hI) hGM
    (lem_2fam_boundary hN hI) (endpoint_slopes_proof hCB)
    (stationary_reduction_proof hI hCB hQ) (cover_atMostOne hN hI) (lem_2fam_witness hN)
    (realization_escaping_proof hI hCB)

/-- **Proposition `prop:2fam-optimum`, "Self-consistency"**, end to end. -/
theorem self_consistency (hN : FamilyNumerics) (hI : FamilyIdentities) :
    SelfConsistencyStatement := by
  obtain ⟨hCB, hPos, hCmp, hSeq⟩ := foundations hI
  have hComp := lem_2fam_compact hN hI
  have hQ := quadratures_proof hI hCB
  exact self_consistency_of_proof hN hI hPos hCmp hComp
    (ratio_attained_proof hCB hPos hSeq hComp) (lem_2fam_boundary hN hI)
    (stationary_reduction_proof hI hCB hQ) (cover_atMostOne hN hI) (lem_2fam_witness hN) hQ

end FixedPrice.TwoUnit.Family
