import FixedPrice.TwoUnit.Family.Statements
import FixedPrice.TwoUnit.Family.DomainCalc

/-!
# Work package D: algebra of the eliminated stationary system (helper for `Stationary.lean`)

* `integral_inv_quadratic`: `∫_a^b du/(u² - u + C)` in the arctan form when `C > 1/4`
  (this gives `ConnectionArctanStatement`);
* the trial range of `d_f = (1 - β)/β` on `[18227/25000, 729081/10⁶]`;
* consequences of `PhysStationary`: positivity of the eliminated data, `P_ℓ ≤ 1` (the obstacle at
  the initial contact), the recovered `h_f`, `P_r`, `ξ_r` and the curve data at the recovered
  parameters, and `log(ξ_r/ξ_ℓ) = ℐ_f` from the connection equation.
-/

noncomputable section
open Real Set Filter Topology

namespace FixedPrice.TwoUnit.Family

namespace PkgD

/-- `∫_a^b du/(u² - u + C) = (arctan((b - 1/2)/w) - arctan((a - 1/2)/w))/w`, `w = √(C - 1/4)`,
when `C > 1/4`. -/
lemma integral_inv_quadratic (C a b : ℝ) (hC : 1 / 4 < C) :
    ∫ u in a..b, (u ^ 2 - u + C)⁻¹
      = (arctan ((b - 1 / 2) / √(C - 1 / 4)) - arctan ((a - 1 / 2) / √(C - 1 / 4)))
        / √(C - 1 / 4) := by
  have hw : 0 < √(C - 1 / 4) := Real.sqrt_pos.2 (by linarith)
  have hw2 : √(C - 1 / 4) ^ 2 = C - 1 / 4 := Real.sq_sqrt (by linarith)
  set w := √(C - 1 / 4) with hwdef
  have hD : ∀ u : ℝ, 0 < u ^ 2 - u + C := fun u => by nlinarith [sq_nonneg (u - 1 / 2)]
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u => arctan ((u - 1 / 2) / w) / w)
      (u ^ 2 - u + C)⁻¹ u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (u - 1 / 2) / w) (1 / w) u :=
      ((hasDerivAt_id u).sub_const _).div_const w
    have h3 := h1.arctan.div_const w
    convert h3 using 1
    have hkey : 1 / (1 + ((u - 1 / 2) / w) ^ 2) * (1 / w) / w = (w ^ 2 + (u - 1 / 2) ^ 2)⁻¹ := by
      field_simp
    rw [hkey]
    congr 1
    rw [hw2]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)]
  · ring
  · exact (Continuous.inv₀ (by fun_prop) (fun u => (hD u).ne')).intervalIntegrable _ _

/-- The trial range of `d_f`: `β ∈ [18227/25000, 729081/10⁶]` gives
`d_f ∈ [270919/729081, 6773/18227]`. -/
lemma dOf_mem {β : ℝ} (hβ : β ∈ Icc βlo βhi) :
    270919 / 729081 ≤ dOf β ∧ dOf β ≤ 6773 / 18227 := by
  obtain ⟨h1, h2⟩ := hβ
  unfold βlo at h1
  unfold βhi at h2
  have hβ0 : 0 < β := by linarith
  unfold dOf
  constructor
  · rw [le_div_iff₀ hβ0]; norm_num at h2 ⊢; linarith
  · rw [div_le_iff₀ hβ0]; linarith

lemma dOf_pos {β : ℝ} (hβ : β ∈ Icc βlo βhi) : 0 < dOf β :=
  lt_of_lt_of_le (by norm_num) (dOf_mem hβ).1

lemma dOf_domain {β : ℝ} (hβ : β ∈ Icc βlo βhi) : 37 / 100 ≤ dOf β ∧ dOf β ≤ 3 / 8 :=
  ⟨le_trans (by norm_num) (dOf_mem hβ).1, le_trans (dOf_mem hβ).2 (by norm_num)⟩

lemma βlo_mem : βlo ∈ Icc βlo βhi := ⟨le_rfl, by unfold βlo βhi; norm_num⟩

/-- Positivity facts of a physical stationary point. -/
structure PhysFacts (d t p : ℝ) : Prop where
  d_pos : 0 < d
  p_pos : 0 < p
  δ_pos : 0 < δF t p
  e_pos : 0 < eF t
  v_pos : 0 < vF t
  v_lt : vF t < 1 / 2
  c_pos : 0 < cF t p
  Pl_pos : 0 < Elim.Pl d t p
  ξl_pos : 0 < Elim.ξl d t p
  ξr_pos : 0 < Elim.ξr d t p
  ξ₀_pos : 0 < Elim.ξ₀ d t p
  C_pos : 0 < Elim.C d t p
  qR_pos : 0 < Elim.qR d t p
  qR_lt_one : Elim.qR d t p < 1
  qL_lt_one : Elim.qL d t p < 1
  DqR_pos : 0 < Elim.Dq (Elim.C d t p) (Elim.qR d t p)
  DqL_pos : 0 < Elim.Dq (Elim.C d t p) (Elim.qL d t p)
  h_pos : 0 < Elim.h d t p
  Pr_pos : 0 < Elim.Pr d t p

lemma physFacts {d t p : ℝ} (hd : 0 < d) (hs : PhysStationary d t p) : PhysFacts d t p := by
  have ht := hs.t_pos
  have htp := hs.t_lt_p
  have hp1 := hs.p_lt_one
  have hp : 0 < p := ht.trans htp
  have hδ : 0 < δF t p := by unfold δF; linarith
  have he : 0 < eF t := by unfold eF; linarith
  have hv : 0 < vF t := by rw [vF_eq]; linarith
  have hv2 : vF t < 1 / 2 := by rw [vF_eq]; linarith
  have hc : 0 < cF t p := by unfold cF; linarith
  have hPl := Pl_pos hd ht hp
  have hξl : 0 < Elim.ξl d t p := hc.trans hs.c_lt_ξl
  have hξr : 0 < Elim.ξr d t p := hξl.trans hs.ξl_lt_ξr
  have hξ₀ : 0 < Elim.ξ₀ d t p := hξr.trans hs.ξr_lt_ξ₀
  have hC := C_pos hd ht htp
  have hqR := hs.qR_pos
  have hqL1 := hs.qL_lt_one
  have hqR1 : Elim.qR d t p < 1 := hs.qR_lt_qL.trans hqL1
  have hDR := hs.D_pos _ ⟨le_rfl, hs.qR_lt_qL.le⟩
  have hDL := hs.D_pos _ ⟨hs.qR_lt_qL.le, le_rfl⟩
  have hh : 0 < Elim.h d t p := by
    unfold Elim.h
    have : 0 < 1 - Elim.qR d t p := by linarith
    positivity
  have hPr : 0 < Elim.Pr d t p := by
    unfold Elim.Pr
    have : 0 < 1 - Elim.qR d t p := by linarith
    positivity
  exact ⟨hd, hp, hδ, he, hv, hv2, hc, hPl, hξl, hξr, hξ₀, hC, hqR, hqR1, hqL1, hDR, hDL, hh, hPr⟩

/-- The recovered parameters: `θ.h = h_f` at `θ = (t, p, ξ₀(d,t,p))`. -/
lemma params_h {d t p : ℝ} (hv : vF t ≠ 0) (hh : Elim.h d t p ≠ 0) :
    (Elim.params d t p).h = Elim.h d t p := by
  show vF t / (vF t / Elim.h d t p) = Elim.h d t p
  field_simp

/-- `P_r = h_f ξ_r + e_f` at the recovered data (`P_r (1 - q_r) = e_f`). -/
lemma line₂_ξr {d t p : ℝ} (hv : vF t ≠ 0) (hh : Elim.h d t p ≠ 0)
    (hq1 : Elim.qR d t p ≠ 1) :
    (Elim.params d t p).line₂ (Elim.ξr d t p) = Elim.Pr d t p := by
  have h1 : 1 - Elim.qR d t p ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  show (Elim.params d t p).h * Elim.ξr d t p + eF t = Elim.Pr d t p
  rw [params_h hv hh]
  unfold Elim.ξr Elim.Pr
  field_simp
  ring

/-- `P_ℓ = ξ_ℓ + δ_f`. -/
lemma line₁_ξl (d t p : ℝ) : (Elim.params d t p).line₁ (Elim.ξl d t p) = Elim.Pl d t p := by
  show Elim.ξl d t p + δF t p = Elim.Pl d t p
  unfold Elim.ξl; ring

/-- At a physical stationary point, `P_ℓ ≤ 1`: the recovered class curve meets the first obstacle
at `ξ_ℓ` and lies below the second obstacle, which is at most `1` on `[c_f, ξ₀]`. -/
lemma Pl_le_one {d t p : ℝ} (hd : 0 < d) (hs : PhysStationary d t p) : Elim.Pl d t p ≤ 1 := by
  have hf := physFacts hd hs
  obtain ⟨P, hP, hA⟩ := hs.curve
  set θ := Elim.params d t p with hθ
  have hmem : Elim.ξl d t p ∈ Icc θ.c θ.ξ₀ := ⟨hA.c_le, (hA.l_lt_r.trans_le hA.r_le).le⟩
  have h1 : P (Elim.ξl d t p) = θ.line₁ (Elim.ξl d t p) := hA.left_contact _ ⟨hA.c_le, le_rfl⟩
  have h2 := hP.obstacle _ hmem
  have h3 : θ.U (Elim.ξl d t p) ≤ θ.line₂ (Elim.ξl d t p) := min_le_right _ _
  rw [h1, line₁_ξl] at h2
  have hθh : θ.h = Elim.h d t p := params_h hf.v_pos.ne' hf.h_pos.ne'
  have h4 : θ.line₂ (Elim.ξl d t p) ≤ 1 := by
    show θ.h * Elim.ξl d t p + eF t ≤ 1
    have hξ : Elim.ξl d t p ≤ Elim.ξ₀ d t p := hmem.2
    have : θ.h * Elim.ξ₀ d t p = vF t := by
      rw [hθh]; unfold Elim.ξ₀; field_simp [hf.h_pos.ne']
    have hv : vF t + eF t = 1 := by unfold vF; ring
    have h5 : θ.h * Elim.ξl d t p ≤ θ.h * Elim.ξ₀ d t p :=
      mul_le_mul_of_nonneg_left hξ (by rw [hθh]; exact hf.h_pos.le)
    linarith
  linarith

/-- The connection residual in terms of `ℐ_f` and the recovered contacts:
`ℱ_f = (ℐ_f - log(ξ_r/ξ_ℓ))/2` (`left_endpoint_D`, `right_endpoint_ξ`, and
`1 - q_ℓ = δ/P_ℓ`, `1 - q_r = e/P_r`). -/
lemma connection_eq (hI : FamilyIdentities) {d t p : ℝ} (hf : PhysFacts d t p) :
    Elim.connection d t p
      = (Elim.connI d t p - Real.log (Elim.ξr d t p / Elim.ξl d t p)) / 2 := by
  have hd := hf.d_pos
  unfold Elim.connection
  -- the left end: `1 - q_ℓ = δ/P_ℓ`, `𝒟(q_ℓ) = d ξ_ℓ/P_ℓ²`
  have hDL : Elim.Dq (Elim.C d t p) (Elim.qL d t p) = d * Elim.ξl d t p / Elim.Pl d t p ^ 2 :=
    hI.left_endpoint_D (Elim.Pl d t p) (δF t p) d hf.Pl_pos.ne'
  have h1L : 1 - Elim.qL d t p = δF t p / Elim.Pl d t p := by
    unfold Elim.qL Elim.ξl; field_simp [hf.Pl_pos.ne']; ring
  -- the right end: `1 - q_r = e/P_r`, `ξ_r = P_r² 𝒟(q_r)/d`
  have hDR : Elim.ξr d t p = Elim.Pr d t p ^ 2 * Elim.Dq (Elim.C d t p) (Elim.qR d t p) / d :=
    hI.right_endpoint_ξ (Elim.qR d t p) (eF t) d (Elim.C d t p) hf.qR_pos.ne'
      (by linarith [hf.qR_lt_one]) hf.e_pos.ne' hd.ne' hf.DqR_pos.ne'
  have h1R : 1 - Elim.qR d t p = eF t / Elim.Pr d t p := by
    have hq1 : 1 - Elim.qR d t p ≠ 0 := by linarith [hf.qR_lt_one]
    unfold Elim.Pr; field_simp [hf.e_pos.ne']
  have hDR' : Elim.Dq (Elim.C d t p) (Elim.qR d t p) = d * Elim.ξr d t p / Elim.Pr d t p ^ 2 := by
    rw [hDR]; field_simp [hf.Pr_pos.ne']
  rw [h1L, h1R, hDL, hDR']
  have hPl := hf.Pl_pos
  have hPr := hf.Pr_pos
  have hξl := hf.ξl_pos
  have hξr := hf.ξr_pos
  have hδ := hf.δ_pos
  have he := hf.e_pos
  rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- The connection equation of a physical stationary point says `log(ξ_r/ξ_ℓ) = ℐ_f`. -/
lemma log_ratio_eq_connI (hI : FamilyIdentities) {d t p : ℝ} (hd : 0 < d)
    (hs : PhysStationary d t p) :
    Real.log (Elim.ξr d t p / Elim.ξl d t p) = Elim.connI d t p := by
  have h := connection_eq hI (physFacts hd hs)
  rw [hs.conn] at h
  linarith

end PkgD

end FixedPrice.TwoUnit.Family
