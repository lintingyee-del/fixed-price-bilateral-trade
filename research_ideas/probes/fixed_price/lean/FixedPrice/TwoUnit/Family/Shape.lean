import FixedPrice.TwoUnit.Family.Statements
import FixedPrice.TwoUnit.Family.ShapeGlobal

/-!
# Work package B: the fixed-endpoint energy minimizer (export theorem)

Owned by work package B. The theorem proves `ShapeStatement` (`lem:2fam-shape`) and keeps exactly
the signature below. Blueprint: `lean/blueprints/family.md`, section 3.2.

Proof (helper files `Shape*.lean`, namespace `Relaxed`). With `z = log P` and `w = √ξ z'`, the
energy is `J(w) = ‖w‖² + d ∫ e^{-2z}` on `L²(c_f, ξ₀]`, and the class becomes the closed convex
set `log p_f ≤ z ≤ log U_f` (`ShapeSpace`). `J` is uniformly convex there, so it has a unique
minimizer (`ShapeExist`); a class member `P` gives `w_P` with `J(w_P) = E_f(P)` (`ShapeClass`).
Trapezoid variations (`ShapeVar`, `ShapeTrap`, `ShapeTwoPoint`) give, at Lebesgue points, that
`ω + dF` (`ω = ξz'`, `F = ∫ e^{-2z}`) is nondecreasing where pushing down is allowed and
nonincreasing where pushing up is allowed. The lower obstacle is never active inside
(`ShapeLower`), so `ω + dF` is nondecreasing everywhere and constant on free stretches. There
`ω = K - dF` is continuous, the endpoint comparisons give `0 < ω < 1`, and
`C = ω - ω² + dξe^{-2z}` is a positive constant: the Euler equation and first integral hold and
the curve is strictly concave (`ShapeArc`, `ShapeODE`). A strictly concave stretch cannot touch
the same affine obstacle at both ends, so there is one free stretch, with `line₁` before and
`line₂` after (`ShapeComp`); the contacts are smooth and a corner of `U_f` cannot be followed
(`ShapeFit`). The candidate `P* = e^z` is therefore a three-arc or entirely affine class member
with `E_f(P*) = J(w)` (`ShapeGlobal`), which gives existence; uniqueness of the relaxed minimizer
gives uniqueness. If `c_f = 0`, the first integral `d = ξP'² - PP' + CP²/ξ` with `P ≥ p_f` and
bounded `P'` rules out a free stretch starting at `0`.
-/

namespace FixedPrice.TwoUnit.Family

open Set Filter Topology Relaxed

namespace Relaxed

/-- `ThreeArc` depends only on the values on the curve interval. -/
theorem threeArc_congr {d : ℝ} {θ : Params} {P Q : ℝ → ℝ} {ξl ξr C : ℝ}
    (hT : ThreeArc d θ Q ξl ξr C) (hEq : EqOn P Q (Icc θ.c θ.ξ₀)) : ThreeArc d θ P ξl ξr C := by
  have hin : ∀ ξ ∈ Ioo θ.c θ.ξ₀, P =ᶠ[𝓝 ξ] Q := fun ξ hξ => by
    filter_upwards [Icc_mem_nhds hξ.1 hξ.2] with t ht using hEq ht
  have hmid : ∀ ξ ∈ Ioo ξl ξr, ξ ∈ Ioo θ.c θ.ξ₀ := fun ξ hξ =>
    ⟨lt_of_le_of_lt hT.c_le hξ.1, lt_of_lt_of_le hξ.2 hT.r_le⟩
  exact { c_le := hT.c_le
          l_lt_r := hT.l_lt_r
          r_le := hT.r_le
          C_pos := hT.C_pos
          left_contact := fun ξ hξ =>
            (hEq ⟨hξ.1, hξ.2.trans (hT.l_lt_r.le.trans hT.r_le)⟩).trans (hT.left_contact ξ hξ)
          right_contact := fun ξ hξ =>
            (hEq ⟨hT.c_le.trans (hT.l_lt_r.le.trans hξ.1), hξ.2⟩).trans (hT.right_contact ξ hξ)
          fit_left := fun h => (hT.fit_left h).congr_of_eventuallyEq
            (hin ξl ⟨h, lt_of_lt_of_le hT.l_lt_r hT.r_le⟩)
          fit_right := fun h => (hT.fit_right h).congr_of_eventuallyEq
            (hin ξr ⟨lt_of_le_of_lt hT.c_le hT.l_lt_r, h⟩)
          smooth := hT.smooth.congr fun x hx => hEq (Ioo_subset_Icc_self (hmid x hx))
          euler := fun ξ hξ => by
            have h1 := hin ξ (hmid ξ hξ)
            rw [h1.deriv.deriv_eq, hEq (Ioo_subset_Icc_self (hmid ξ hξ))]
            exact hT.euler ξ hξ
          first_integral := fun ξ hξ => by
            have h1 := hin ξ (hmid ξ hξ)
            rw [h1.deriv_eq, hEq (Ioo_subset_Icc_self (hmid ξ hξ))]
            exact hT.first_integral ξ hξ
          strictConcave := hT.strictConcave.congr fun x hx =>
            (hEq ⟨hT.c_le.trans hx.1, hx.2.trans hT.r_le⟩).symm }

/-- With `c_f = 0`, no three-arc decomposition of a class member starts its free stretch at `0`:
the first integral would make `CP²/ξ` bounded. -/
theorem left_pos_of_c_zero {β : ℝ} (hβ : 0 < dOf β) {θ : Params} (hc0 : θ.c = 0) {P : ℝ → ℝ}
    (hP : InClass θ P) {ξl ξr C : ℝ} (hT : ThreeArc (dOf β) θ P ξl ξr C) : 0 < ξl := by
  by_contra hle
  push_neg at hle
  have hξl : ξl = 0 := le_antisymm hle (hc0 ▸ hT.c_le)
  obtain ⟨K, hK⟩ := hP.lipschitz
  have hpp := hP.admissible.p_pos
  have hr0 : 0 < ξr := hξl ▸ hT.l_lt_r
  have hC := hT.C_pos
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hden : 0 < 2 * (dOf β + K + 1) := by positivity
  have hq : 0 < C * θ.p ^ 2 / (2 * (dOf β + K + 1)) := by positivity
  have hξ0 : 0 < Min.min (ξr / 2) (C * θ.p ^ 2 / (2 * (dOf β + K + 1))) :=
    lt_min (by linarith) hq
  have hm1 := min_le_left (ξr / 2) (C * θ.p ^ 2 / (2 * (dOf β + K + 1)))
  have hm2 := min_le_right (ξr / 2) (C * θ.p ^ 2 / (2 * (dOf β + K + 1)))
  set ξ := Min.min (ξr / 2) (C * θ.p ^ 2 / (2 * (dOf β + K + 1)))
  have hξmem : ξ ∈ Ioo ξl ξr := ⟨by rw [hξl]; exact hξ0, by linarith⟩
  have hξI : ξ ∈ Ioo θ.c θ.ξ₀ := ⟨by rw [hc0]; exact hξ0, by linarith [hT.r_le]⟩
  have hFI := hT.first_integral ξ hξmem
  have hder : ‖deriv P ξ‖ ≤ K := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hξI.1 hξI.2) hK
  rw [Real.norm_eq_abs] at hder
  have hPξ := hP.le_one (Ioo_subset_Icc_self hξI)
  have hpξ := hP.p_le (Ioo_subset_Icc_self hξI)
  have h1 : P ξ * deriv P ξ ≤ K := by
    calc P ξ * deriv P ξ ≤ |P ξ * deriv P ξ| := le_abs_self _
      _ = |P ξ| * |deriv P ξ| := abs_mul _ _
      _ ≤ 1 * K := mul_le_mul (by rw [abs_of_pos (hpp.trans_le hpξ)]; exact hPξ) hder
          (abs_nonneg _) zero_le_one
      _ = K := one_mul _
  have h2 : C * θ.p ^ 2 / ξ ≤ C * P ξ ^ 2 / ξ :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpp.le hpξ 2) hC.le) hξ0.le
  have h3 : 2 * (dOf β + K + 1) ≤ C * θ.p ^ 2 / ξ := by
    rw [le_div_iff₀ hξ0]
    rw [le_div_iff₀ hden] at hm2
    linarith
  have h4 : 0 ≤ ξ * deriv P ξ ^ 2 := by positivity
  linarith

end Relaxed

/-- `ShapeStatement` (`lem:2fam-shape`), with no hypotheses: the proof uses neither the
certified identities nor the class basics. -/
theorem shape_holds : ShapeStatement := by
  intro β θ hβ0 hβ1 hne
  obtain ⟨P₀, hP₀⟩ := hne
  have hd : 0 < dOf β := by unfold dOf; exact div_pos (by linarith) hβ0
  have hθ := hP₀.admissible
  rcases eq_or_lt_of_le hθ.c_le_ξ₀ with hdeg | hcξ
  · -- the degenerate face: the curve interval is a point
    have hpt : ∀ ξ ∈ Icc θ.c θ.ξ₀, ξ = θ.c := fun ξ hξ =>
      le_antisymm (hξ.2.trans hdeg.symm.le) hξ.1
    have hE : ∀ P, Ef β θ P = 0 := fun P => by
      unfold Ef; rw [hdeg]; exact intervalIntegral.integral_same
    have hEA : ∀ P, InClass θ P → EntirelyAffine θ P := fun P hP =>
      Or.inl fun ξ hξ => by rw [hpt ξ hξ, hP.left_end, Params.line₁_c]
    refine ⟨⟨P₀, hP₀, fun Q _ => by rw [hE, hE]⟩, fun P Q hP hQ ξ hξ => ?_,
      fun P hP => Or.inl (hEA P hP.1), fun _ P hP hna => absurd (hEA P hP.1) hna⟩
    rw [hpt ξ hξ, hP.1.left_end, hQ.1.left_end]
  · -- the relaxed minimizer and the candidate
    have hline₂c : θ.p ≤ θ.line₂ θ.c := by
      have := hP₀.le_line₂ ⟨le_rfl, hθ.c_le_ξ₀⟩
      rwa [hP₀.left_end] at this
    have hline₁ξ₀ : 1 ≤ θ.line₁ θ.ξ₀ := by
      have := hP₀.le_line₁ ⟨hθ.c_le_ξ₀, le_rfl⟩
      rwa [hP₀.right_end] at this
    have hWne : (W θ).Nonempty := ⟨wP hP₀, wP_mem hP₀⟩
    obtain ⟨w, hw, hmin⟩ := exists_minimizer (dOf β) hθ hd.le hWne
    have S : Setting θ (dOf β) w := ⟨hθ, hd, hw, hmin, hcξ, hline₂c, hline₁ξ₀⟩
    obtain ⟨hPin, hshape⟩ := S.shape_Pstar
    have hEstar : Ef β θ (Pstar θ w) = J θ (dOf β) w := by
      rw [← J_wP hPin β, S.wP_Pstar hPin]
    have hPmin : IsEnergyMinimizer β θ (Pstar θ w) :=
      ⟨hPin, fun Q hQ => by rw [hEstar, ← J_wP hQ β]; exact hmin _ (wP_mem hQ)⟩
    have huniq : ∀ P, IsEnergyMinimizer β θ P → EqOn P (Pstar θ w) (Icc θ.c θ.ξ₀) := by
      intro P hP ξ hξ
      have hJ : ∀ v ∈ W θ, J θ (dOf β) (wP hP.1) ≤ J θ (dOf β) v := fun v hv => by
        rw [J_wP hP.1 β]
        calc Ef β θ P ≤ Ef β θ (Pstar θ w) := hP.2 _ hPin
          _ = J θ (dOf β) w := hEstar
          _ ≤ J θ (dOf β) v := hmin v hv
      have heq : wP hP.1 = w := minimizer_unique (dOf β) hθ hd.le (wP_mem hP.1) hw hJ hmin
      rcases eq_or_lt_of_le hξ.1 with h | h
      · rw [← h, hP.1.left_end, Pstar_c]
      · have hξ0 : 0 < ξ := lt_of_le_of_lt hθ.c_nonneg h
        have h1 := zfun_wP hP.1 hξ hξ0
        rw [heq] at h1
        rw [Pstar_of_lt w h, h1, Real.exp_log (hP.1.pos' hξ)]
    refine ⟨⟨_, hPmin⟩, fun P Q hP hQ => (huniq P hP).trans (huniq Q hQ).symm, ?_, ?_⟩
    · intro P hP
      have hEq := huniq P hP
      rcases hshape with hA | ⟨a, b, C, hT⟩
      · left
        rcases hA with h | h
        · exact Or.inl fun ξ hξ => by rw [hEq hξ, h ξ hξ]
        · exact Or.inr fun ξ hξ => by rw [hEq hξ, h ξ hξ]
      · exact Or.inr ⟨a, b, C, threeArc_congr hT hEq⟩
    · intro hc0 P hP _ ξl ξr C hT
      exact left_pos_of_c_zero hd hc0 hP.1 hT

/-- `ShapeStatement` (`lem:2fam-shape`). The hypotheses are part of the frozen signature and are
not used (see `shape_holds`). -/
theorem lem_2fam_shape_proof (hI : FamilyIdentities) (hCB : ClassBasicsStatement) :
    ShapeStatement :=
  shape_holds

end FixedPrice.TwoUnit.Family
