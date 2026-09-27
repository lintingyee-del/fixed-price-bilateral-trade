import FixedPrice.TwoUnit.Family.AssemblyBasic

/-!
# Work package F: assembly (export theorems)

Owned by work package F. Each theorem proves one statement of `Statements.lean` from the injected
statements with the frozen signature below; helpers in `AssemblyBasic`. Blueprint:
`lean/blueprints/family.md`, section 2 (nodes F1, F2).

* The lower trial value: if `r_fam ≤ βlo`, a positive maximum of `K_f` at `βlo` (or the minimum
  itself when `r_fam = βlo`) is a physical stationary curve, and the certified lower-endpoint sign
  gives `K_f < 0` there.
* Attainment and uniqueness: the witness gives `R_f < βhi < 3/4`, so the minimum is attained; two
  minimizers are physical stationary points at `β = r_fam`, hence have the same parameters (at
  most one stationary point), and as energy minimizers at these parameters they coincide.
* Self-consistency: a second curve with `R_f < β` would give a positive maximum of `K_f`, a
  stationary point equal to the given one; the quadratures then give the two curves the same
  `K_f`, but one has `K_f > 0` and the other `K_f = 0`.

Some injected hypotheses are not needed, so the unused-variables linter is off for this file.
-/

set_option linter.unusedVariables false

open Set Filter
open scoped Topology

namespace FixedPrice.TwoUnit.Family

/-- The proof of `prop:2fam-optimum` from the lemmas and interfaces. -/
theorem prop_2fam_optimum_of_proof (hN : FamilyNumerics) (hI : FamilyIdentities)
    (hPos : PositivityStatement) (hCmp : ComparisonStatement)
    (hComp : CompactStatement) (hAtt : RatioAttainedStatement)
    (hShape : ShapeStatement) (hGM : GlobalMaxEnergyStatement)
    (hBd : BoundaryStatement) (hES : EndpointSlopesStatement)
    (hRed : ReductionStatement) (hCov : CoverAtMostOneStatement)
    (hWit : WitnessStatement) (hReal : RealizationEscapingStatement) :
    OptimumStatement := by
  obtain ⟨θw, Pw, -, hPw, -, hRw⟩ := hWit
  obtain ⟨θ, P, hmin, hRθ⟩ := hAtt ⟨θw, Pw, hPw, hRw.trans βhi_lt⟩
  have hP := hmin.1
  have hlt_hi : rFam < βhi := by rw [← hRθ]; exact (hmin.2 θw Pw hPw).trans_lt hRw
  -- the lower trial value
  have hlo : βlo < rFam := by
    by_contra hle
    push Not at hle
    have hβlo : βlo ∈ Icc βlo βhi := ⟨le_rfl, βlo_lt_βhi.le⟩
    obtain ⟨hb0, hb1, hb34⟩ := mem_trial_bounds hβlo
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hK : 0 < Kf βlo θ P := (Kf_pos_iff hPos hCmp hb0 hP).mpr (hRθ ▸ hlt)
      obtain ⟨θ₁, P₁, hmax, hK₁, -⟩ := (hComp βlo hb0 hb34).2 ⟨θ, P, hP, hK⟩
      obtain ⟨hPS, htr, hTA⟩ :=
        stationary_of_extremal hBd hRed hβlo (Or.inl ⟨hmax, hK₁⟩) hmax.1
      have hP₁ := htr (fun x => InClass x P₁) hmax.1
      have hK₁' := htr (fun x => 0 < Kf βlo x P₁) hK₁
      have := Kf_neg_of_num hb0 hP₁ (hCov.2 θ₁.t θ₁.p hPS P₁ hP₁ hTA)
      linarith
    · obtain ⟨hPS, htr, hTA⟩ :=
        stationary_of_extremal hBd hRed hβlo (Or.inr ⟨hmin, hRθ.trans heq⟩) hP
      have hP' := htr (fun x => InClass x P) hP
      have hR' := htr (fun x => Rf x P = βlo) (hRθ.trans heq)
      have hneg := Kf_neg_of_num hb0 hP' (hCov.2 θ.t θ.p hPS P hP' hTA)
      have := (Kf_neg_iff hPos hCmp hb0 hP').mp hneg
      linarith
  have hβ : rFam ∈ Icc βlo βhi := ⟨hlo.le, hlt_hi.le⟩
  obtain ⟨hb0, hb1, -⟩ := mem_trial_bounds hβ
  -- minimizers maximize `K_f` at `β = r_fam`
  have hminR : ∀ θ' P', InClass θ' P' → Rf θ' P' = rFam → IsGlobalMinR θ' P' :=
    fun θ' P' hP' hR' => ⟨hP', fun θ'' P'' hP'' => hR' ▸ rFam_le hPos hP''⟩
  have hmaxK : ∀ θ' P', InClass θ' P' → Rf θ' P' = rFam → IsGlobalMaxK rFam θ' P' :=
    fun θ' P' hP' hR' => ⟨hP', fun θ'' P'' hP'' => by
      rw [(Kf_eq_zero_iff hPos hCmp hb0 hP').mpr hR']
      exact Kf_le_zero_of_le hPos hCmp hb0 hP'' (rFam_le hPos hP'')⟩
  -- uniqueness
  have huniq : ∀ θ' P', InClass θ' P' → Rf θ' P' = rFam →
      θ' = θ ∧ EqOn P' P (Icc θ.c θ.ξ₀) := by
    intro θ' P' hP' hR'
    obtain ⟨hPS', htr', -⟩ :=
      stationary_of_extremal hBd hRed hβ (Or.inr ⟨hminR θ' P' hP' hR', hR'⟩) hP'
    obtain ⟨hPS₀, htr₀, -⟩ := stationary_of_extremal hBd hRed hβ (Or.inr ⟨hmin, hRθ⟩) hP
    obtain ⟨h1, h2⟩ := hCov.1 rFam hβ θ'.t θ'.p θ.t θ.p hPS' hPS₀
    have hθeq : θ' = θ := by
      have e' := htr' (fun x => x = θ') rfl
      have e₀ := htr₀ (fun x => x = θ) rfl
      rw [← e', ← e₀, h1, h2]
    subst hθeq
    have hE' := hGM rFam θ' P' hb0 hb1 (hmaxK θ' P' hP' hR')
    have hE₀ := hGM rFam θ' P hb0 hb1 (hmaxK θ' P hP hRθ)
    exact ⟨rfl, (hShape rFam θ' hb0 hb1 ⟨P, hP⟩).2.1 P' P hE' hE₀⟩
  -- the shape of the minimizer
  obtain ⟨-, -, ξl, ξr, C, hTA, hcl, hrξ, -, -, -⟩ := hBd rFam hβ θ P (Or.inr ⟨hmin, hRθ⟩)
  -- the endpoint-slope subclass has the same infimum
  have hslopes : rFamSlopes = rFam := by
    have hES' := hES (dOf rFam) θ P ξl ξr C hP hTA hcl hrξ
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨θ, P, hP, hES', hRθ⟩
      rintro r ⟨θ', P', hP', -, rfl⟩
      exact R_nonneg hPos hP'
    · refine le_csInf ⟨rFam, θ, P, hP, hES', hRθ⟩ ?_
      rintro r ⟨θ', P', hP', -, rfl⟩
      exact rFam_le hPos hP'
  obtain ⟨I, hIv, hesc, hlaw, hM, hG, hbest, hratio⟩ := hReal θ P hP
  rw [hRθ] at hratio
  exact ⟨⟨θ, P, hP, hRθ, huniq,
    ⟨ξl, ξr, C, hTA.C_pos, hcl, hTA.l_lt_r, hrξ, hTA.left_contact, hTA.right_contact,
      hTA.strictConcave, hTA.smooth, hTA.euler⟩,
    ⟨I, hIv, hesc, hlaw, hM, hG, hbest, hratio⟩⟩, hslopes, hlo, hlt_hi⟩

/-- The self-consistency characterization in the proof of `prop:2fam-optimum`. The quadratures
determine `K_f` of a three-arc curve from its contact data, which rules out a second stationary
curve with `K_f > 0` at the same point. -/
theorem self_consistency_of_proof (hN : FamilyNumerics) (hI : FamilyIdentities)
    (hPos : PositivityStatement) (hCmp : ComparisonStatement)
    (hComp : CompactStatement) (hAtt : RatioAttainedStatement)
    (hBd : BoundaryStatement) (hRed : ReductionStatement) (hCov : CoverAtMostOneStatement)
    (hWit : WitnessStatement) (hQ : QuadratureStatement) : SelfConsistencyStatement := by
  intro β hβ t p hPS P hP hTA hK0
  obtain ⟨hb0, hb1, hb34⟩ := mem_trial_bounds hβ
  have hd := dOf_pos hb0 hb1
  have hRs : Rf (Elim.params (dOf β) t p) P = β := (Kf_eq_zero_iff hPos hCmp hb0 hP).mp hK0
  have hge : ∀ θ' P', InClass θ' P' → β ≤ Rf θ' P' := by
    intro θ' P' hP'
    by_contra hlt
    push Not at hlt
    have hK' : 0 < Kf β θ' P' := (Kf_pos_iff hPos hCmp hb0 hP').mpr hlt
    obtain ⟨θ₁, P₁, hmax, hK₁, -⟩ := (hComp β hb0 hb34).2 ⟨θ', P', hP', hK'⟩
    obtain ⟨hPS₁, htr, hTA₁⟩ := stationary_of_extremal hBd hRed hβ (Or.inl ⟨hmax, hK₁⟩) hmax.1
    obtain ⟨h1, h2⟩ := hCov.1 β hβ θ₁.t θ₁.p t p hPS₁ hPS
    have hP₁ := htr (fun x => InClass x P₁) hmax.1
    have hK₁' := htr (fun x => 0 < Kf β x P₁) hK₁
    rw [h1, h2] at hP₁ hTA₁ hK₁'
    -- the quadratures give both curves the same `T_f` and `Q_f`, hence the same `K_f`
    obtain ⟨hT₁, hQ₁, -⟩ := hQ (dOf β) _ P₁ _ _ _ hd hP₁ hTA₁ hPS.c_lt_ξl hPS.ξr_lt_ξ₀
    obtain ⟨hTs, hQs, -⟩ := hQ (dOf β) _ P _ _ _ hd hP hTA hPS.c_lt_ξl hPS.ξr_lt_ξ₀
    have hKeq : Kf β (Elim.params (dOf β) t p) P₁ = Kf β (Elim.params (dOf β) t p) P := by
      unfold Kf Gf Mf; rw [hT₁, hQ₁, hTs, hQs]
    linarith
  refine ⟨⟨hP, fun θ' P' hP' => by rw [hRs]; exact hge θ' P' hP'⟩, le_antisymm ?_ ?_⟩
  · exact le_csInf ⟨_, _, P, hP, rfl⟩ fun r ⟨θ', P', hP', hr⟩ => hr ▸ hge θ' P' hP'
  · exact hRs ▸ rFam_le hPos hP

end FixedPrice.TwoUnit.Family
