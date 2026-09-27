import FixedPrice.TwoUnit.Family.BoundaryBasic
import FixedPrice.TwoUnit.Family.BoundaryVarCases

/-!
# Work package C: outer variations (export theorems)

Owned by work package C. Each theorem proves one statement of `Statements.lean` and keeps exactly
the signature below. Blueprint:
`lean/blueprints/family.md`, section 3.3 (the envelope coefficients are directional derivatives
along admissible outer variations, see `EnvelopeCoeffs`).

Proof of `lem_2fam_boundary_proof` (helper files `BoundaryVar*.lean`, namespace `PkgC`): both
cases give a global maximizer of `K_f` with `R_f ≤ β_f`; `lem:2fam-compact` at `3/4` gives
`p_f < 1`, and the certified bound `R_f ≥ 73/100` on the two affine boundaries excludes an
entirely affine curve, so the minimizer of `lem:2fam-shape` is three-arc. The competitors are
the curve plus a multiple of a cubic Hermite bump continued by its tangents; they stay in the
class, and differentiating `K_f` along them gives, with the certified envelope identities,
positive contacts, `t_f < p_f`, and the three stationarity equations.
-/

namespace FixedPrice.TwoUnit.Family

/-- `EndpointSlopesStatement`: positive contacts give the endpoint slopes `1, h_f`. -/
theorem endpoint_slopes_proof (hCB : ClassBasicsStatement) : EndpointSlopesStatement :=
  endpoint_slopes'

/-- `AffineFunctionalsStatement`: the entirely affine curves have the functionals
`(eq:2fam-affine-boundaries)`. -/
theorem affine_functionals_proof (hI : FamilyIdentities) (hCB : ClassBasicsStatement) :
    AffineFunctionalsStatement :=
  affine_functionals' hI

/-- `BoundaryStatement` (`lem:2fam-boundary`). -/
theorem lem_2fam_boundary_proof (hN : FamilyNumerics) (hI : FamilyIdentities)
    (hCB : ClassBasicsStatement) (hPos : PositivityStatement) (hCmp : ComparisonStatement)
    (hComp : CompactStatement) (hShape : ShapeStatement) (hGM : GlobalMaxEnergyStatement)
    (hAff : AffineFunctionalsStatement) : BoundaryStatement := by
  intro β hβI θ P hcase
  have hβhi : β ≤ βhi := hβI.2
  have hβ : 0 < β := by
    have : (0 : ℝ) < βlo := by unfold βlo; norm_num
    linarith [hβI.1]
  have hβ34 : βhi < 73 / 100 := by unfold βhi; norm_num
  have hβ1 : β < 1 := by linarith
  -- both cases give a global maximizer of `K_f` with `R_f ≤ β`
  obtain ⟨hmaxK, hRβ⟩ : IsGlobalMaxK β θ P ∧ Rf θ P ≤ β := by
    rcases hcase with ⟨hmax, hK⟩ | ⟨hmin, hR⟩
    · refine ⟨hmax, ?_⟩
      obtain ⟨-, -, hKr⟩ := hCmp β θ P hmax.1 hβ
      obtain ⟨hN0, hM0, hG2, -⟩ := hPos θ P hmax.1
      rw [hKr] at hK
      have hpos : 0 < (Mf θ P + Gf θ P) / θ.N := div_pos (by linarith) hN0
      have h1 : 0 < 1 - Rf θ P / β := by
        by_contra h
        linarith [mul_nonpos_of_nonneg_of_nonpos hpos.le (not_lt.1 h)]
      have h2 : Rf θ P / β < 1 := by linarith
      exact ((div_lt_one hβ).1 h2).le
    · refine ⟨⟨hmin.1, fun θ' P' hP' => ?_⟩, hR.le⟩
      obtain ⟨-, -, hKr⟩ := hCmp β θ P hmin.1 hβ
      obtain ⟨-, -, hKr'⟩ := hCmp β θ' P' hP' hβ
      obtain ⟨hN0, hM0, hG2, -⟩ := hPos θ' P' hP'
      have hpos : 0 ≤ (Mf θ' P' + Gf θ' P') / θ'.N := (div_pos (by linarith) hN0).le
      have h1 : 1 - Rf θ' P' / β ≤ 0 := by
        have := hmin.2 θ' P' hP'
        rw [hR] at this
        have : 1 ≤ Rf θ' P' / β := (one_le_div hβ).2 this
        linarith
      rw [hKr, hKr', hR, div_self hβ.ne', sub_self, mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hpos h1
  have hP : InClass θ P := hmaxK.1
  have hadm := hP.admissible
  -- `p_f < 1` (`lem:2fam-compact`)
  have hp1 : θ.p < 1 :=
    ((hComp (3 / 4) (by norm_num) le_rfl).1 θ P hP (by linarith)).2.2.2
  -- the curve minimizes `E_f` at its parameters and is three-arc
  have hEM := hGM β θ P hβ hβ1 hmaxK
  obtain ⟨-, -, hdich, hc0⟩ := hShape β θ hβ hβ1 ⟨P, hP⟩
  have hnotAff : ¬ EntirelyAffine θ P := by
    obtain ⟨-, hM0, hG2, -⟩ := hPos θ P hP
    have hMG : 0 < Mf θ P + Gf θ P := by linarith
    have hR73 : ¬ 73 / 100 * (Mf θ P + Gf θ P) ≤ Mf θ P + 2 := by
      intro h
      have : 73 / 100 ≤ Rf θ P := by unfold Rf; rw [le_div_iff₀ hMG]; linarith
      linarith
    rintro (hl | hr)
    · obtain ⟨hM', hG'⟩ := (hAff θ P hP).1 hl hp1
      have hc := hN.affine_left θ.t θ.p hadm.t_pos hadm.t_lt_one hadm.t_le_p hp1
      rw [← hM', ← hG'] at hc
      exact hR73 hc
    · obtain ⟨hep, hM', hG'⟩ := (hAff θ P hP).2 hr hp1
      have hc := hN.affine_right θ.t θ.p hadm.t_pos hadm.t_lt_one hep hp1
      rw [← hM', ← hG'] at hc
      exact hR73 hc
  obtain ⟨ξl, ξr, C, hA3⟩ := (hdich P hEM).resolve_left hnotAff
  have ha : 0 < ξl := by
    rcases lt_or_eq_of_le hadm.c_nonneg with hc | hc
    · exact hc.trans_le hA3.c_le
    · exact hc0 hc.symm P hEM hnotAff ξl ξr C hA3
  -- the end slopes of the free arc and the data at the maximum
  obtain ⟨La, hLa_h, hLa_1, hLa_lim, hLa_der, hLa_one, hLeft⟩ := PkgC.arc_left hP hA3
  obtain ⟨Lb, hLb_h, hLb_1, hLb_lim, hLb_der, hLb_eq, hRight⟩ := PkgC.arc_right hP hA3
  have hM : PkgC.MaxData β θ P ξl ξr C La Lb :=
    ⟨hβ, hβ1, hP, hmaxK.2, hA3, ha, hp1, hLa_h, hLa_1, hLa_lim, hLa_der, hLa_one, hLeft,
      hLb_h, hLb_1, hLb_lim, hLb_der, hLb_eq, hRight⟩
  -- both contacts have positive length, `t_f < p_f`, and the three derivatives vanish
  have hr := PkgC.final_contact_pos hM hI
  have hl : θ.c < ξl := by
    rcases lt_or_eq_of_le hadm.c_nonneg with hc | hc
    · exact PkgC.initial_contact_pos hM hI hc
    · rw [← hc]; exact ha
  have htp : θ.t < θ.p := by
    rcases lt_or_eq_of_le hadm.t_le_p with h | h
    · exact h
    · exact (PkgC.not_face hM hI hr hl h).elim
  exact ⟨htp, hp1, ξl, ξr, C, hA3, hl, hr, PkgC.statP_zero hM hI hr hl htp,
    PkgC.statH_zero hM hI hr hl, PkgC.statT_zero hM hI hr hl htp⟩

end FixedPrice.TwoUnit.Family
