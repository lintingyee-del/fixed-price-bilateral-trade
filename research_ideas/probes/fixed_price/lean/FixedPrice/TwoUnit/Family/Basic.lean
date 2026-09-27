import FixedPrice.TwoUnit.Family.BasicFTC

/-!
# Work package A, part 1: foundations (export theorems)

Owned by work package A. Each theorem proves one statement of `Statements.lean` with the frozen
signature below. The proofs live in `BasicClass` (parameters, class members, derivative bounds)
and `BasicFTC` (integrals, positivity, comparison, moving endpoints). Certified facts enter only
through `FamilyNumerics` and `FamilyIdentities` and are not re-derived. Blueprint:
`lean/blueprints/family.md`, sections 2 and 3.1.

Some injected hypotheses are not needed by these proofs (positivity and the comparison are proved
from the class directly), so the unused-variables linter is off for this file.
-/

set_option linter.unusedVariables false

namespace FixedPrice.TwoUnit.Family

/-- `ClassBasicsStatement`: continuity, `P ≥ p_f`, `h_f ≤ P' ≤ 1` a.e., `(log P)' = P'/P` a.e.,
integrability of the integrands of `T_f`, `Q_f`, `E_f`, `s_f' = P⁻²`, and the moving-endpoint
lemma. -/
theorem class_basics_proof : ClassBasicsStatement := class_basics'

/-- `PositivityStatement` (proof of `lem:2fam-compact`, the parameter bounds). -/
theorem positivity_proof (hI : FamilyIdentities) (hCB : ClassBasicsStatement) :
    PositivityStatement := fun _ _ hP => hP.positivity'

/-- `ComparisonStatement` (`(eq:2fam-comparison)` on the class and its ratio form). -/
theorem comparison_proof (hI : FamilyIdentities) (hCB : ClassBasicsStatement) :
    ComparisonStatement := fun _ _ _ hP hβ => hP.comparison' hI hβ

/-- `GlobalMaxEnergyStatement`: a global maximizer of `K_f` minimizes `E_f` at its parameters. -/
theorem globalMax_energyMinimizer_proof (hCmp : ComparisonStatement) :
    GlobalMaxEnergyStatement := by
  intro β θ P hβ _ hmax
  refine ⟨hmax.1, fun Q hQ => ?_⟩
  have hK := hmax.2 θ Q hQ
  rw [(hCmp β θ Q hQ hβ).2.1, (hCmp β θ P hmax.1 hβ).2.1] at hK
  linarith

end FixedPrice.TwoUnit.Family
