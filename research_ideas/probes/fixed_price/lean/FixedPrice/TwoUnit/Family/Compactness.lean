import FixedPrice.TwoUnit.Family.SeqCompactLimit

/-!
# Work package A, part 2: compactness (export theorems)

Owned by work package A. Each theorem proves one statement of `Statements.lean` with the frozen
signature below. The proofs live in `CompactnessBounds` (the parameter bounds of
`lem:2fam-compact`), `CompactnessAttain` (attainment on the compact region) and `SeqCompactExt`,
`SeqCompactDeriv`, `SeqCompactLimit` (the compact extension). Blueprint:
`lean/blueprints/family.md`, section 3.1.

Some injected hypotheses are not needed by these proofs, so the unused-variables linter is off
for this file.
-/

set_option linter.unusedVariables false

namespace FixedPrice.TwoUnit.Family

/-- `SeqCompactStatement`: the compact extension in the proof of `lem:2fam-compact`. -/
theorem seq_compact_proof (hCB : ClassBasicsStatement) : SeqCompactStatement := seq_compact'

/-- `SmallMassMonoStatement`: `smallMassBound` increases on `(0, 1/32]` (proof of
`lem:2fam-compact`; the certificate checks only a point value, so this is a Lean target). -/
theorem small_mass_mono_proof : SmallMassMonoStatement := small_mass_mono'

/-- `CompactStatement` (`lem:2fam-compact`). -/
theorem lem_2fam_compact_proof (hN : FamilyNumerics) (hI : FamilyIdentities)
    (hCB : ClassBasicsStatement) (hPos : PositivityStatement) (hCmp : ComparisonStatement)
    (hSeq : SeqCompactStatement) (hSM : SmallMassMonoStatement) : CompactStatement :=
  fun _ hβ0 hβ => ⟨fun _ _ hP hR => region_bounds hN hI hβ0 hβ hP hR,
    exists_globalMaxK hN hI hSeq hβ0 hβ⟩

/-- `RatioAttainedStatement` (proof of `prop:2fam-optimum`, "Attainment"). -/
theorem ratio_attained_proof (hCB : ClassBasicsStatement) (hPos : PositivityStatement)
    (hSeq : SeqCompactStatement) (hComp : CompactStatement) : RatioAttainedStatement :=
  exists_globalMinR hSeq (hComp (3 / 4) (by norm_num) le_rfl).1

end FixedPrice.TwoUnit.Family
