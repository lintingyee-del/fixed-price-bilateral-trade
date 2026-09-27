import FixedPrice.TwoUnit.Family.Statements
import FixedPrice.TwoUnit.Family.ReconstructionCurve

/-!
# Work package D, part 3: reconstructing the curve (export theorem)

Owned by work package D. The theorem proves `ReconstructionStatement` ("Reconstructing the curve"
in the proof of `lem:2fam-cover`) and keeps exactly the signature below. The margins of the root
strip are the certified field `FamilyNumerics.physical_box`; `𝒟 > 0` everywhere follows from
`C_f > 1/4` and `FamilyIdentities.quadratic_complete_square`; the connection equation in the
arctan form (a cover root) gives `log(ξ_r/ξ_ℓ) = ℐ_f`; and the recovered curve is the closed-form
three-arc curve of `ReconstructionCurve.lean`. (The discriminant of `q_r` is positive for
`0 < v < 1`, `DomainCalc.disc_pos`.)
-/

noncomputable section
open Real Set Filter Topology

namespace FixedPrice.TwoUnit.Family

namespace PkgD

/-- The positivity facts of `PhysFacts` from the certified margins. -/
lemma physFacts_of_margins {d t p : ℝ} (hd : 0 < d) (hM : PhysicalMargins d t p)
    (hDq : ∀ u, 0 < Elim.Dq (Elim.C d t p) u) : PhysFacts d t p := by
  have ht := hM.t_pos
  have htp := hM.t_lt_p
  have hp1 := hM.p_lt_one
  have hp : 0 < p := ht.trans htp
  have hc : 0 < cF t p := by unfold cF; linarith
  have hξl : 0 < Elim.ξl d t p := hc.trans hM.c_lt_ξl
  have hξr : 0 < Elim.ξr d t p := hξl.trans hM.ξl_lt_ξr
  have hqR1 : Elim.qR d t p < 1 := hM.qR_lt_qL.trans hM.qL_lt_one
  refine ⟨hd, hp, by unfold δF; linarith, by unfold eF; linarith, by rw [vF_eq]; linarith,
    by rw [vF_eq]; linarith, hc, Pl_pos hd ht hp, hξl, hξr, hξr.trans hM.ξr_lt_ξ₀,
    by linarith [hM.C_gt], hM.qR_pos, hqR1, hM.qL_lt_one, hDq _, hDq _, hM.h_pos, ?_⟩
  unfold Elim.Pr
  have : 0 < 1 - Elim.qR d t p := by linarith
  have : 0 < eF t := by unfold eF; linarith
  positivity

/-- The recovered class curve with the three-arc shape. -/
theorem recovered_curve (hI : FamilyIdentities) {d t p : ℝ} (hd : 0 < d)
    (hM : PhysicalMargins d t p) (hf : PhysFacts d t p)
    (hlog : Real.log (Elim.ξr d t p / Elim.ξl d t p) = Elim.connJ d t p) :
    ∃ P, InClass (Elim.params d t p) P ∧
      ThreeArc d (Elim.params d t p) P (Elim.ξl d t p) (Elim.ξr d t p) (Elim.C d t p) := by
  set θ := Elim.params d t p with hθ
  have hC : 1 / 4 < Elim.C d t p := hM.C_gt
  set A : ArcParams := ⟨d, Elim.C d t p, Elim.ξl d t p,
    arctan ((Elim.qL d t p - 1 / 2) / √(Elim.C d t p - 1 / 4))⟩ with hA
  have hAd : A.d = d := rfl
  have hAC : A.C = Elim.C d t p := rfl
  have hAw : A.w = √(Elim.C d t p - 1 / 4) := rfl
  have hw := ArcParams.w_pos (A := A) hC
  have hlr : Elim.ξl d t p < Elim.ξr d t p := hM.ξl_lt_ξr
  have hξl := hf.ξl_pos
  have hξr := hf.ξr_pos
  have hθh : θ.h = Elim.h d t p := params_h hf.v_pos.ne' hf.h_pos.ne'
  -- the angle at the contacts
  have hφl : A.φ (Elim.ξl d t p) = arctan ((Elim.qL d t p - 1 / 2) / A.w) := by
    show A.φ₀ - A.w * (Real.log (Elim.ξl d t p) - Real.log (Elim.ξl d t p)) = _
    rw [sub_self, mul_zero, sub_zero]
    rfl
  have hφr : A.φ (Elim.ξr d t p) = arctan ((Elim.qR d t p - 1 / 2) / A.w) := by
    show A.φ₀ - A.w * (Real.log (Elim.ξr d t p) - Real.log (Elim.ξl d t p)) = _
    rw [← Real.log_div hξr.ne' hξl.ne', hlog]
    unfold Elim.connJ
    rw [← hAw]
    show arctan ((Elim.qL d t p - 1 / 2) / A.w) - A.w * ((arctan ((Elim.qL d t p - 1 / 2) / A.w)
      - arctan ((Elim.qR d t p - 1 / 2) / A.w)) / A.w) = _
    field_simp
    ring
  -- the arc at the contacts
  obtain ⟨hFl0, hF1l0⟩ :=
    ArcParams.F_of_arctan (A := A) hI.quadratic_complete_square hd hC hξl hφl
  obtain ⟨hFr0, hF1r0⟩ :=
    ArcParams.F_of_arctan (A := A) hI.quadratic_complete_square hd hC hξr hφr
  have hDL : Elim.Dq (Elim.C d t p) (Elim.qL d t p) = d * Elim.ξl d t p / Elim.Pl d t p ^ 2 :=
    hI.left_endpoint_D (Elim.Pl d t p) (δF t p) d hf.Pl_pos.ne'
  have hDR : Elim.ξr d t p = Elim.Pr d t p ^ 2 * Elim.Dq (Elim.C d t p) (Elim.qR d t p) / d :=
    hI.right_endpoint_ξ (Elim.qR d t p) (eF t) d (Elim.C d t p) hf.qR_pos.ne'
      (by linarith [hf.qR_lt_one]) hf.e_pos.ne' hd.ne' hf.DqR_pos.ne'
  have hFl : A.F (Elim.ξl d t p) = Elim.ξl d t p + θ.δ := by
    rw [hFl0]
    have : d * Elim.ξl d t p / (Elim.qL d t p ^ 2 - Elim.qL d t p + Elim.C d t p)
        = Elim.Pl d t p ^ 2 := by
      have h1 : Elim.qL d t p ^ 2 - Elim.qL d t p + Elim.C d t p
          = d * Elim.ξl d t p / Elim.Pl d t p ^ 2 := hDL
      rw [h1]
      field_simp [hf.Pl_pos.ne', hξl.ne', hd.ne']
    rw [hAd, hAC, this, Real.sqrt_sq hf.Pl_pos.le]
    show Elim.Pl d t p = Elim.Pl d t p - δF t p + δF t p
    ring
  have hF1l : A.F1 (Elim.ξl d t p) = 1 := by
    rw [hF1l0, hFl]
    show Elim.ξl d t p / Elim.Pl d t p * (Elim.Pl d t p - δF t p + δF t p) / Elim.ξl d t p = 1
    field_simp [hf.Pl_pos.ne', hξl.ne']
    ring
  have hPr_eq : θ.h * Elim.ξr d t p + θ.e = Elim.Pr d t p :=
    line₂_ξr hf.v_pos.ne' hf.h_pos.ne' (by linarith [hf.qR_lt_one])
  have hFr : A.F (Elim.ξr d t p) = θ.h * Elim.ξr d t p + θ.e := by
    rw [hFr0, hPr_eq]
    have : d * Elim.ξr d t p / (Elim.qR d t p ^ 2 - Elim.qR d t p + Elim.C d t p)
        = Elim.Pr d t p ^ 2 := by
      have h1 : Elim.qR d t p ^ 2 - Elim.qR d t p + Elim.C d t p
          = Elim.Dq (Elim.C d t p) (Elim.qR d t p) := rfl
      rw [h1]
      have h2 := hf.DqR_pos
      rw [hDR]
      field_simp [hd.ne', h2.ne']
    rw [hAd, hAC, this, Real.sqrt_sq hf.Pr_pos.le]
  have hF1r : A.F1 (Elim.ξr d t p) = θ.h := by
    rw [hF1r0, hFr, hPr_eq, hθh]
    show Elim.qR d t p * Elim.Pr d t p / (Elim.qR d t p * Elim.Pr d t p / Elim.h d t p)
      = Elim.h d t p
    field_simp [hf.qR_pos.ne', hf.Pr_pos.ne', hf.h_pos.ne']
  -- the arc is positive and its slope decreases on `[ξ_ℓ, ξ_r]`
  have hcos : ∀ ξ ∈ Icc (Elim.ξl d t p) (Elim.ξr d t p), 0 < cos (A.φ ξ) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := hξl.trans_le hξ.1
    apply cos_pos_of_mem_Ioo
    constructor
    · have := ArcParams.φ_antitone (A := A) hC hξ0 hξ.2
      rw [hφr] at this
      linarith [neg_pi_div_two_lt_arctan ((Elim.qR d t p - 1 / 2) / A.w)]
    · have := ArcParams.φ_antitone (A := A) hC hξl hξ.1
      rw [hφl] at this
      linarith [arctan_lt_pi_div_two ((Elim.qL d t p - 1 / 2) / A.w)]
  have hFpos : ∀ ξ ∈ Icc (Elim.ξl d t p) (Elim.ξr d t p), 0 < A.F ξ := by
    intro ξ hξ
    have hξ0 : 0 < ξ := hξl.trans_le hξ.1
    unfold ArcParams.F
    have := ArcParams.K_pos (A := A) hd hC
    have := Real.sqrt_pos.2 hξ0
    have := hcos ξ hξ
    positivity
  have hF1anti : StrictAntiOn A.F1 (Icc (Elim.ξl d t p) (Elim.ξr d t p)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro x hx
      exact (ArcParams.hasDerivAt_F1 (A := A) hC (hξl.trans_le hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hξl.trans hx.1
      rw [(ArcParams.hasDerivAt_F1 (A := A) hC hx0).deriv]
      have := hFpos x (Ioo_subset_Icc_self hx)
      have : 0 < A.C := by linarith
      have : 0 < A.C * A.F x / x ^ 2 := by positivity
      rw [neg_mul, neg_div]
      linarith
  have hup : ∀ ξ ∈ Ioo (Elim.ξl d t p) (Elim.ξr d t p), A.F1 ξ ≤ 1 := by
    intro ξ hξ
    rw [← hF1l]
    exact (hF1anti ⟨le_rfl, hlr.le⟩ (Ioo_subset_Icc_self hξ) hξ.1).le
  have hlow : ∀ ξ ∈ Ioo (Elim.ξl d t p) (Elim.ξr d t p), θ.h ≤ A.F1 ξ := by
    intro ξ hξ
    rw [← hF1r]
    exact (hF1anti (Ioo_subset_Icc_self hξ) ⟨hlr.le, le_rfl⟩ hξ.2).le
  have hh1 : θ.h ≤ 1 := by rw [hθh]; exact hM.h_lt_one.le
  have hh0 : 0 < θ.h := by rw [hθh]; exact hf.h_pos
  -- the glued curve
  set P := glue (Elim.ξl d t p) (Elim.ξr d t p) θ.δ θ.h θ.e A.F with hPdef
  have hFd : ∀ ξ ∈ Icc (Elim.ξl d t p) (Elim.ξr d t p), HasDerivAt A.F (A.F1 ξ) ξ :=
    fun ξ hξ => ArcParams.hasDerivAt_F (hξl.trans_le hξ.1)
  have hPd : ∀ ξ, HasDerivAt P (glueD (Elim.ξl d t p) (Elim.ξr d t p) θ.h A.F1 ξ) ξ :=
    glue_hasDerivAt hlr hFd hFl hFr hF1l hF1r
  have hderivP : deriv P = glueD (Elim.ξl d t p) (Elim.ξr d t p) θ.h A.F1 :=
    glue_deriv hlr hFd hFl hFr hF1l hF1r
  have hdiffP : Differentiable ℝ P := fun ξ => (hPd ξ).differentiableAt
  have hanti : Antitone (glueD (Elim.ξl d t p) (Elim.ξr d t p) θ.h A.F1) :=
    glueD_antitone hlr (hF1anti.antitoneOn.mono Ioo_subset_Icc_self) hup hlow hh1
  have hconc : ConcaveOn ℝ univ P :=
    Antitone.concaveOn_univ_of_deriv hdiffP (by rw [hderivP]; exact hanti)
  have hbound : ∀ ξ, 0 ≤ glueD (Elim.ξl d t p) (Elim.ξr d t p) θ.h A.F1 ξ ∧
      glueD (Elim.ξl d t p) (Elim.ξr d t p) θ.h A.F1 ξ ≤ 1 := by
    intro ξ
    rcases le_or_gt ξ (Elim.ξl d t p) with h1 | h1
    · rw [glueD_eq_left h1]; norm_num
    rcases lt_or_ge ξ (Elim.ξr d t p) with h2 | h2
    · rw [glueD_eq_mid h1 h2]
      exact ⟨hh0.le.trans (hlow ξ ⟨h1, h2⟩), hup ξ ⟨h1, h2⟩⟩
    · rw [glueD_eq_right hlr h2]; exact ⟨hh0.le, hh1⟩
  have hlip : LipschitzWith 1 P := by
    apply lipschitzWith_of_nnnorm_deriv_le hdiffP
    intro ξ
    rw [hderivP, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one, abs_le]
    obtain ⟨h1, h2⟩ := hbound ξ
    constructor <;> linarith
  have hfitl : HasDerivAt P 1 (Elim.ξl d t p) := by
    have := hPd (Elim.ξl d t p); rwa [glueD_eq_left le_rfl] at this
  have hfitr : HasDerivAt P θ.h (Elim.ξr d t p) := by
    have := hPd (Elim.ξr d t p); rwa [glueD_eq_right hlr le_rfl] at this
  have hc : 0 < θ.c := hf.c_pos
  have hcl : θ.c < Elim.ξl d t p := hM.c_lt_ξl
  have hrξ₀ : Elim.ξr d t p < θ.ξ₀ := hM.ξr_lt_ξ₀
  have hξ₀ : 0 < θ.ξ₀ := hf.ξ₀_pos
  refine ⟨P, ⟨⟨hM.t_pos, ?_, hM.t_lt_p.le, hM.p_lt_one.le, hξ₀, (hcl.trans (hlr.trans hrξ₀)).le⟩,
    ?_, hconc.subset (subset_univ _) (convex_Icc _ _), ⟨1, hlip.lipschitzOnWith⟩, ?_, ?_, ?_⟩,
    ⟨hcl.le, hlr, hrξ₀.le, by linarith, fun ξ hξ => glue_eq_left hξ.2,
      fun ξ hξ => glue_eq_right hlr hξ.1, fun _ => hfitl, fun _ => hfitr, ?_, ?_, ?_, ?_⟩⟩
  · exact hM.t_lt_p.trans hM.p_lt_one
  · -- positivity
    intro ξ hξ
    rw [hPdef]
    rcases le_or_gt ξ (Elim.ξl d t p) with h1 | h1
    · rw [glue_eq_left h1]
      have : 0 < θ.δ := hf.δ_pos
      linarith [hξ.1]
    rcases lt_or_ge ξ (Elim.ξr d t p) with h2 | h2
    · rw [glue_eq_mid h1 h2]; exact hFpos ξ ⟨h1.le, h2.le⟩
    · rw [glue_eq_right hlr h2]
      have : 0 < θ.e := hf.e_pos
      have : 0 < ξ := hc.trans_le hξ.1
      positivity
  · -- left end
    rw [hPdef, glue_eq_left hcl.le, c_add_δ]
  · -- right end
    rw [hPdef, glue_eq_right hlr hrξ₀.le]
    exact line₂_ξ₀ hξ₀.ne'
  · -- obstacle: both obstacles are tangent lines of the concave curve
    intro ξ _
    apply le_min
    · have := ConcaveOn.le_tangent hconc hfitl ξ
      rw [hPdef, glue_eq_left le_rfl] at this
      show P ξ ≤ ξ + θ.δ
      rw [hPdef]
      linarith
    · have := ConcaveOn.le_tangent hconc hfitr ξ
      rw [hPdef, glue_eq_right hlr le_rfl] at this
      show P ξ ≤ θ.h * ξ + θ.e
      rw [hPdef]
      linarith
  · -- smoothness on the free interval
    have hsm : ContDiffOn ℝ 2 A.F (Ioo (Elim.ξl d t p) (Elim.ξr d t p)) :=
      fun x hx => (ArcParams.contDiffAt_F (A := A) (hξl.trans hx.1)).contDiffWithinAt
    exact hsm.congr (fun x hx => by rw [hPdef]; exact glue_eq_mid hx.1 hx.2)
  · -- the Euler equation
    intro ξ hξ
    have hξ0 : 0 < ξ := hξl.trans hξ.1
    rw [hderivP]
    have heq : glueD (Elim.ξl d t p) (Elim.ξr d t p) θ.h A.F1 =ᶠ[𝓝 ξ] A.F1 := by
      filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with x hx using glueD_eq_mid hx.1 hx.2
    rw [heq.deriv_eq, (ArcParams.hasDerivAt_F1 (A := A) hC hξ0).deriv, hPdef,
      glue_eq_mid hξ.1 hξ.2]
    rw [hAC]
    field_simp
    ring
  · -- the first integral
    intro ξ hξ
    have hξ0 : 0 < ξ := hξl.trans hξ.1
    rw [hderivP, glueD_eq_mid hξ.1 hξ.2, hPdef, glue_eq_mid hξ.1 hξ.2]
    exact ArcParams.first_integral (A := A) hd hC hξ0
  · -- strict concavity on the free interval
    have hsc : StrictConcaveOn ℝ (Icc (Elim.ξl d t p) (Elim.ξr d t p)) A.F := by
      apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
      · intro x hx
        exact (ArcParams.hasDerivAt_F (A := A) (hξl.trans_le hx.1)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := hξl.trans hx.1
        have heq : deriv A.F =ᶠ[𝓝 x] A.F1 := by
          filter_upwards [Ioi_mem_nhds hx0] with y hy using (ArcParams.hasDerivAt_F hy).deriv
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
        rw [heq.deriv_eq, (ArcParams.hasDerivAt_F1 (A := A) hC hx0).deriv]
        have := hFpos x (Ioo_subset_Icc_self hx)
        have : 0 < A.C := by linarith
        have : 0 < A.C * A.F x / x ^ 2 := by positivity
        rw [neg_mul, neg_div]
        linarith
    refine hsc.congr fun x hx => ?_
    rw [hPdef]
    rcases eq_or_lt_of_le hx.1 with h1 | h1
    · subst h1; rw [glue_eq_left le_rfl, hFl]
    rcases eq_or_lt_of_le hx.2 with h2 | h2
    · subst h2; rw [glue_eq_right hlr le_rfl, hFr]
    · rw [glue_eq_mid h1 h2]

end PkgD

/-- `ReconstructionStatement`: a cover root in the certified strip is a physical stationary
point. -/
theorem reconstruction_proof (hN : FamilyNumerics) (hI : FamilyIdentities)
    (hConn : ConnectionArctanStatement) : ReconstructionStatement := by
  intro β hβ t p ht hp hroot
  have hd := PkgD.dOf_pos hβ
  have hM := hN.physical_box β hβ t ht p hp
  have hDq : ∀ u, 0 < Elim.Dq (Elim.C (dOf β) t p) u := fun u => by
    rw [hI.quadratic_complete_square]
    nlinarith [sq_nonneg (u - 1 / 2), hM.C_gt]
  have hf := PkgD.physFacts_of_margins hd hM hDq
  have hJ := hConn _ _ _ hM.C_gt
  have hconn : Elim.connection (dOf β) t p = 0 := by
    have h := hroot.conn
    unfold Elim.connectionArctan at h
    unfold Elim.connection
    rw [hJ]
    linarith
  have hlog : Real.log (Elim.ξr (dOf β) t p / Elim.ξl (dOf β) t p) = Elim.connJ (dOf β) t p := by
    have := PkgD.connection_eq hI hf
    rw [hconn] at this
    rw [← hJ]
    linarith
  exact ⟨hM.t_pos, hM.t_lt_p, hM.p_lt_one, hroot.alg, hconn, hM.c_lt_ξl, hM.ξl_lt_ξr,
    hM.ξr_lt_ξ₀, hM.qR_pos, hM.qR_lt_qL, hM.qL_lt_one, fun u _ => hDq u,
    PkgD.recovered_curve hI hd hM hf hlog⟩

end FixedPrice.TwoUnit.Family
