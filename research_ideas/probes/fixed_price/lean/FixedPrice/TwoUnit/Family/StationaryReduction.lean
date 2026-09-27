import FixedPrice.TwoUnit.Family.StationaryArc

/-!
# Work package D: the stationary reduction (helper for `Stationary.lean`)

An interior three-arc stationary curve gives a physical stationary point whose recovery formulas
reproduce its data (`ReductionStatement`, paper gap G9): `statP = 0` fixes `P_ℓ`, the first
integral at `ξ_ℓ` fixes `C_f`, the first integral at `ξ_r` and `statH = 0` put
`q_r = h ξ_r/P_r` on the quadratic `v²𝒟(q) = C q²` (`h_stationarity`), and
`C(v² - q_r²) = v² q_r (1 - q_r) > 0` gives `q_r < v`, which identifies it with the closed-form
root; `statT = 0` is `𝒜_f = 0` (`t_stationarity`); the substitution `u = ω(ξ)` on the free arc
gives `log(ξ_r/ξ_ℓ) = ℐ_f`, i.e. the connection equation.
-/

noncomputable section
open Real Set Filter Topology MeasureTheory

namespace FixedPrice.TwoUnit.Family

namespace PkgD

/-- `ReductionStatement`. -/
theorem reduction (hI : FamilyIdentities) (hCB : ClassBasicsStatement) : ReductionStatement := by
  intro d θ P ξl ξr C hd hP hA hl hr htp hp1 hsP hsH hsT
  obtain ⟨ht, ht1, hp, hc, hδ, he, hv, hξ₀, hh⟩ := params_signs hP
  have hF := freeArc_of hCB hP hA hl hr
  have hlr := hA.l_lt_r
  have hC := hA.C_pos
  have hPl : P ξl = θ.line₁ ξl := hA.left_contact ξl ⟨hA.c_le, le_rfl⟩
  have hPr : P ξr = θ.line₂ ξr := hA.right_contact ξr ⟨le_rfl, hA.r_le⟩
  have hξl0 : 0 < ξl := hc.trans_lt hl
  have hξr0 : 0 < ξr := hξl0.trans hlr
  have hl1 : 0 < θ.line₁ ξl := by show 0 < ξl + θ.δ; linarith
  have hr1 : 0 < θ.line₂ ξr := by rw [← hPr]; exact hF.pos ξr ⟨hlr.le, le_rfl⟩
  have hv_def : θ.v = (1 - θ.t) / 2 := vF_eq θ.t
  have hv2 : θ.v < 1 / 2 := by rw [hv_def]; linarith
  have hev : θ.e = 1 - θ.v := by linarith [v_add_e θ]
  -- `P_ℓ` from `statP = 0`
  have hPlE : Elim.Pl d θ.t θ.p = θ.line₁ ξl := by
    have hg : (δF θ.t θ.p + d) / (θ.t + d) = (θ.line₁ ξl / θ.p) ^ 2 := by
      unfold statP at hsP
      have h1 : (θ.δ + d) / θ.line₁ ξl ^ 2 = (θ.t + d) / θ.p ^ 2 := by linarith
      show (θ.δ + d) / (θ.t + d) = (θ.line₁ ξl / θ.p) ^ 2
      have htd : 0 < θ.t + d := by linarith
      field_simp at h1 ⊢
      linarith
    unfold Elim.Pl
    rw [hg, Real.sqrt_sq (by positivity)]
    field_simp
  have hξlE : Elim.ξl d θ.t θ.p = ξl := by
    unfold Elim.ξl
    rw [hPlE]
    show ξl + θ.δ - θ.δ = ξl
    ring
  -- `C_f` from the first integral at `ξ_ℓ`
  have hCE : Elim.C d θ.t θ.p = C := by
    have hfi := hF.first_integral_a
    rw [hPl] at hfi
    unfold Elim.C
    rw [hξlE, hPlE]
    have hl1' : θ.line₁ ξl = ξl + θ.δ := rfl
    show (θ.δ + d) * ξl / θ.line₁ ξl ^ 2 = C
    rw [div_eq_iff (by positivity)]
    field_simp at hfi
    rw [hl1'] at hfi ⊢
    nlinarith [hfi]
  -- the right contact slope `q = h ξ_r/P_r`
  set q := ξr * θ.h / θ.line₂ ξr with hqdef
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one hr1]
    show ξr * θ.h < θ.h * ξr + θ.e
    linarith
  have hPrq : θ.line₂ ξr = θ.e / (1 - q) := by
    have : (1 - q) ≠ 0 := by linarith
    rw [eq_div_iff this, hqdef]
    show (θ.h * ξr + θ.e) * (1 - ξr * θ.h / (θ.h * ξr + θ.e)) = θ.e
    have : θ.h * ξr + θ.e ≠ 0 := hr1.ne'
    field_simp
    ring
  have hDq : Elim.Dq C q = d * ξr / θ.line₂ ξr ^ 2 := by
    have := hF.Dq_ω_b
    rw [hPr] at this
    unfold Elim.Dq
    rw [hqdef]
    linarith
  have hDq0 : 0 < Elim.Dq C q := by rw [hDq]; positivity
  have hh_eq : θ.h = d * q * (1 - q) / (θ.e * Elim.Dq C q) := by
    rw [hDq, hqdef]
    have h1 : 1 - ξr * θ.h / θ.line₂ ξr = θ.e / θ.line₂ ξr := by
      show 1 - ξr * θ.h / (θ.h * ξr + θ.e) = θ.e / (θ.h * ξr + θ.e)
      have : θ.h * ξr + θ.e ≠ 0 := hr1.ne'
      field_simp
      ring
    rw [h1]
    field_simp
  -- `statH = 0` puts `q` on the quadratic `v²𝒟(q) = C q²`
  have hroot : θ.v ^ 2 * Elim.Dq C q = C * q ^ 2 := by
    have hHs := hI.h_stationarity q θ.v d C θ.e θ.h (θ.line₂ ξr) hq0.ne' hq1.ne he.ne' hd.ne'
      hDq0.ne' hev hh_eq hPrq
    have hkey : -θ.v ^ 2 * θ.h + 2 * (θ.h * θ.e + d)
        * (1 / θ.line₂ ξr - 1 + θ.e * (1 - 1 / θ.line₂ ξr ^ 2) / 2)
        = θ.h ^ 2 * statH d θ (θ.line₂ ξr) := by
      unfold statH
      rw [← h_mul_ξ₀ hξ₀.ne']
      field_simp
    rw [hsH, mul_zero] at hkey
    rw [hkey] at hHs
    have hne : θ.e * Elim.Dq C q ≠ 0 := by positivity
    rw [eq_comm, div_eq_zero_iff] at hHs
    rcases hHs with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hd.ne'
      · linarith
    · exact absurd h hne
  -- `q < v`, hence `q = q_r`
  have hqv : q < θ.v := by
    have h1 : C * (θ.v ^ 2 - q ^ 2) = θ.v ^ 2 * q * (1 - q) := by
      unfold Elim.Dq at hroot; linear_combination hroot
    have h2 : 0 < θ.v ^ 2 * q * (1 - q) := by
      have : 0 < 1 - q := by linarith
      positivity
    have h3 : 0 < θ.v ^ 2 - q ^ 2 := by
      by_contra hc'; push Not at hc'
      have := mul_nonpos_of_nonneg_of_nonpos hC.le hc'
      linarith
    nlinarith
  have hqE : Elim.qR d θ.t θ.p = q := by
    rw [qR_eq, hCE]
    have := qClosed_unique hv hv2 hC hq0 hqv (by unfold Elim.Dq at hroot; exact hroot)
    exact this.symm
  -- the recovered parameters
  have hhE : Elim.h d θ.t θ.p = θ.h := by
    unfold Elim.h
    rw [hqE, hCE, hh_eq]
    rfl
  have hPrE : Elim.Pr d θ.t θ.p = θ.line₂ ξr := by
    unfold Elim.Pr
    rw [hqE, hPrq]
    rfl
  have hξrE : Elim.ξr d θ.t θ.p = ξr := by
    unfold Elim.ξr
    rw [hqE, hPrE, hhE, hqdef]
    field_simp
  have hξ₀E : Elim.ξ₀ d θ.t θ.p = θ.ξ₀ := by
    unfold Elim.ξ₀
    rw [hhE]
    show θ.v / (θ.v / θ.ξ₀) = θ.ξ₀
    field_simp
  have hqLE : Elim.qL d θ.t θ.p = ξl * 1 / P ξl := by
    unfold Elim.qL
    rw [hξlE, hPlE, hPl, mul_one]
  -- `statT = 0` is `𝒜_f = 0`
  have halg : Elim.algResidual d θ.t θ.p = 0 := by
    have hTs := hI.t_stationarity q θ.v d C θ.t θ.p θ.e θ.h (θ.line₂ ξr) hq0.ne' hq1.ne
      he.ne' hd.ne' hDq0.ne' (by positivity) ht.ne' hp.ne' hev hh_eq hPrq hroot
    have hkey : -Elim.γ d θ.t θ.p - θ.v + (θ.h * θ.e + d) / θ.h * (1 / θ.line₂ ξr ^ 2 - 1)
        = 2 * statT d θ (θ.line₁ ξl) (θ.line₂ ξr) - statP d θ (θ.line₁ ξl) := by
      unfold statT statP Elim.γ
      rw [← h_mul_ξ₀ hξ₀.ne']
      field_simp
      ring
    rw [hsT, hsP] at hkey
    unfold Elim.algResidual
    rw [hqE]
    show -Elim.γ d θ.t θ.p + θ.v * (θ.v - q) / (θ.e * (θ.v + q)) = 0
    linarith
  -- the positivity facts at the recovered point
  have hDqL : 0 < Elim.Dq (Elim.C d θ.t θ.p) (Elim.qL d θ.t θ.p) := by
    rw [hCE, hqLE]
    have := hF.Dq_ω_a
    unfold Elim.Dq
    rw [this]
    have := hF.pos ξl ⟨le_rfl, hlr.le⟩
    positivity
  have hfacts : PhysFacts d θ.t θ.p := by
    refine ⟨hd, hp, hδ, he, hv, hv2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDqL, ?_, ?_⟩
    · show 0 < cF θ.t θ.p; unfold cF; linarith
    · rw [hPlE]; exact hl1
    · rw [hξlE]; exact hξl0
    · rw [hξrE]; exact hξr0
    · rw [hξ₀E]; exact hξ₀
    · rw [hCE]; exact hC
    · rw [hqE]; exact hq0
    · rw [hqE]; exact hq1
    · rw [hqLE, hPl]
      rw [div_lt_one hl1]
      show ξl * 1 < ξl + θ.δ
      linarith
    · rw [hCE, hqE]; exact hDq0
    · rw [hhE]; exact hh
    · rw [hPrE]; exact hr1
  -- the connection equation (substitution `u = ω(ξ)`)
  have hconn : Elim.connection d θ.t θ.p = 0 := by
    rw [connection_eq hI hfacts]
    have hlog := hF.log_ratio hd hI.omega_derivative
    rw [hPr] at hlog
    unfold Elim.connI
    rw [hξrE, hξlE, hlog, hqE, hqLE, hCE]
    unfold Elim.Dq
    rw [hqdef]
    ring
  have hθ : Elim.params d θ.t θ.p = θ := by
    unfold Elim.params
    rw [hξ₀E]
  have hqRL : Elim.qR d θ.t θ.p < Elim.qL d θ.t θ.p := by
    rw [hqE, hqLE]
    have := hF.ω_lt hd hI.omega_derivative
    rw [hPr] at this
    exact this
  refine ⟨⟨ht, htp, hp1, halg, hconn, ?_, ?_, ?_, ?_, hqRL, hfacts.qL_lt_one, ?_, ?_⟩,
    hξ₀E.symm, hξlE.symm, hξrE.symm, hCE.symm⟩
  · rw [hξlE]; exact hl
  · rw [hξlE, hξrE]; exact hlr
  · rw [hξrE, hξ₀E]; exact hr
  · exact hfacts.qR_pos
  · intro u hu
    rw [hqE, hqLE] at hu
    have hpos := hF.Dq_pos_Icc hd hI.omega_derivative
    rw [hPr] at hpos
    rw [hCE]
    unfold Elim.Dq
    exact hpos u hu
  · rw [hθ, hξlE, hξrE, hCE]
    exact ⟨P, hP, hA⟩

end PkgD

end FixedPrice.TwoUnit.Family
