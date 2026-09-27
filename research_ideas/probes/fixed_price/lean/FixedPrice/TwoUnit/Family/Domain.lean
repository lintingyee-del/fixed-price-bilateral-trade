import FixedPrice.TwoUnit.Family.Statements
import FixedPrice.TwoUnit.Family.DomainCalc

/-!
# Work package D, part 2: `lem:2fam-domain` (export theorem)

Owned by work package D. The theorem proves `DomainStatement` and keeps exactly the signature
below.

The machine-checked inputs are the eleven identities `FamilyIdentities.branch_*` and the seven
constants `FamilyNumerics.branch_positive_constants` (`branch_monotonicity.py`, ledger
`fp_ext_k2_branch_positive_factors_20260913`). Everything else is Lean work, in
`DomainCalc.lean`: the sign case split on `∂_p C_f`, the bounds `-2/e < χ' < 0`, the positivity of
the slack and increment terms, the monotone-factor lower bounds of the three coefficients on
`0 < t ≤ 1/5`, `37/100 ≤ d ≤ 3/8`, the chain of ratio bounds that excludes `t ≤ 1/5`, the
monotonicity of `largeTBound`, and the identification of `∂_p 𝒜_f` (the `deriv` of the
closed-form residual, with the root `q_r` differentiated as the inverse of
`C(q) = v²q(1-q)/(v²-q²)`) with the certified expression `R_p = 1/p² + 2(d+t)/p³ + f_C C_p`.
-/

namespace FixedPrice.TwoUnit.Family

/-- `DomainStatement` (`lem:2fam-domain`). -/
theorem lem_2fam_domain_proof (hN : FamilyNumerics) (hI : FamilyIdentities) :
    DomainStatement := by
  refine ⟨fun d hd1 hd2 t p hs => ?_, fun d hd t p ht htp hp1 => ?_⟩
  · exact PkgD.domain_t_bounds hd1 hd2 hs.t_pos hs.t_lt_p hs.p_lt_one hs.alg hs.qR_lt_qL
      hs.qL_lt_one hN.branch_positive_constants hI.branch_small_t_expansion hI.branch_Pl_ratio
      hI.branch_lambda_delta hI.branch_ordered_phase hI.branch_large_t
  · exact PkgD.deriv_algResidual_pos hd ht htp hp1 hI.branch_C_p hI.branch_C_p_gap hI.branch_f_C
      hI.branch_f_C_gap hI.branch_den hI.branch_R_p

end FixedPrice.TwoUnit.Family
