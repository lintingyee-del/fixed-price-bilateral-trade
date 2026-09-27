import FixedPrice.TwoUnit.Family.Statements
import FixedPrice.TwoUnit.Family.StationaryAlg
import FixedPrice.TwoUnit.Family.StationaryArc
import FixedPrice.TwoUnit.Family.StationaryReduction

/-!
# Work package D, part 1: the stationary system (export theorems)

Owned by work package D. Each theorem proves one statement of `Statements.lean` and keeps exactly
the signature below. Blueprint: `lean/blueprints/family.md`, section 3.4. The other files of
package D are `Domain.lean`, `Reconstruction.lean` and `Witness.lean`; the helper files are
`DomainCalc.lean`, `StationaryAlg.lean`, `StationaryArc.lean` and `StationaryReduction.lean`.
-/

namespace FixedPrice.TwoUnit.Family

/-- `QuadratureStatement` (`(eq:2fam-quadratures)`). -/
theorem quadratures_proof (hI : FamilyIdentities) (hCB : ClassBasicsStatement) :
    QuadratureStatement :=
  PkgD.quadratures hI hCB

/-- `ReductionStatement`: an interior three-arc stationary curve is a physical stationary point
(this includes the derivation of the connection equation, paper gap G9). -/
theorem stationary_reduction_proof (hI : FamilyIdentities) (hCB : ClassBasicsStatement)
    (hQ : QuadratureStatement) : ReductionStatement := by
  -- `hQ` is not needed: the free-arc integrals are computed directly in `StationaryArc.lean`.
  exact PkgD.reduction hI hCB

/-- `ConnectionArctanStatement`: `ℐ_f` in the arctan form when `C_f > 1/4`. -/
theorem connI_eq_connJ_proof : ConnectionArctanStatement := by
  intro d t p hC
  unfold Elim.connI Elim.connJ Elim.Dq
  exact PkgD.integral_inv_quadratic _ _ _ hC

/-- `PhysToCoverRootStatement`: physical stationary points are cover roots. -/
theorem phys_to_coverRoot_proof (hN : FamilyNumerics) (hI : FamilyIdentities)
    (hDom : DomainStatement) (hConn : ConnectionArctanStatement) :
    PhysToCoverRootStatement := by
  -- `hI` is not needed: the identities enter through `hDom` and the cover fields of `hN`.
  intro β hβ t p hs
  have hd := PkgD.dOf_pos hβ
  obtain ⟨hd1, hd2⟩ := PkgD.dOf_domain hβ
  obtain ⟨ht1, ht2⟩ := hDom.1 (dOf β) hd1 hd2 t p hs
  have hPl := PkgD.Pl_le_one hd hs
  have hC := hN.cover_C (coverMonotonicity_of_domain hDom) β hβ t p ht1.le ht2.le hs.t_lt_p
    hs.p_lt_one.le hs.alg hPl hs.qR_lt_qL.le
  refine ⟨ht1.le, ht2.le, hs.t_lt_p, hs.p_lt_one.le, hs.alg, hPl, hs.qR_lt_qL.le, hC, ?_⟩
  have h := hs.conn
  unfold Elim.connection at h
  unfold Elim.connectionArctan
  rw [← hConn _ _ _ hC]
  linarith

/-- `CoverAtMostOneStatement`: the uniqueness half of `lem:2fam-cover` and the lower-endpoint
sign. -/
theorem cover_atMostOne_proof (hN : FamilyNumerics) (hI : FamilyIdentities)
    (hDom : DomainStatement) (hA : PhysToCoverRootStatement) (hQ : QuadratureStatement)
    (hConn : ConnectionArctanStatement) : CoverAtMostOneStatement := by
  have hCM := coverMonotonicity_of_domain hDom
  refine ⟨fun β hβ t p t' p' hs hs' =>
    hN.cover_unique hCM β hβ t p t' p' (hA β hβ t p hs) (hA β hβ t' p' hs'), ?_⟩
  intro t p hs P hP hTA
  have hβ := PkgD.βlo_mem
  have hd := PkgD.dOf_pos hβ
  have hroot := hA βlo hβ t p hs
  have hneg := hN.lower_endpoint_sign hCM t p hroot
  have hf := PkgD.physFacts hd hs
  obtain ⟨hT, -, hG⟩ :=
    hQ (dOf βlo) (Elim.params (dOf βlo) t p) P _ _ _ hd hP hTA hs.c_lt_ξl hs.ξr_lt_ξ₀
  have hlog := PkgD.log_ratio_eq_connI hI hd hs
  have hJ := hConn _ _ _ hroot.C_gt
  have hGJ : Gf (Elim.params (dOf βlo) t p) P = Elim.GJ (dOf βlo) t p := by
    rw [hG]
    unfold quadG Elim.GJ
    rw [hlog, hJ]
    rfl
  have hMJ : Mf (Elim.params (dOf βlo) t p) P = Elim.M (dOf βlo) t p := by
    unfold Mf
    rw [hT]
    unfold quadT Elim.M Elim.T
    rw [PkgD.line₁_ξl, PkgD.line₂_ξr hf.v_pos.ne' hf.h_pos.ne' (by linarith [hf.qR_lt_one]),
      PkgD.params_h hf.v_pos.ne' hf.h_pos.ne']
    have hq : Elim.h (dOf βlo) t p * Elim.ξr (dOf βlo) t p / Elim.Pr (dOf βlo) t p
        = Elim.qR (dOf βlo) t p := by
      unfold Elim.ξr
      field_simp [hf.h_pos.ne', hf.Pr_pos.ne']
    rw [hq]
    show NF t * (aF t p + _ - vF t / Elim.h (dOf βlo) t p) = _
    congr 2
    simp only [one_div]
    rfl
  unfold Elim.comparisonJ at hneg
  rw [hGJ, hMJ]
  exact hneg

end FixedPrice.TwoUnit.Family
