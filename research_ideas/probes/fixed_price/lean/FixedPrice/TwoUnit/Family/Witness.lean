import FixedPrice.TwoUnit.Family.Statements
import FixedPrice.TwoUnit.Family.WitnessPoly

/-!
# Work package D, part 4: the rational polygon (export theorem)

Owned by work package D. The theorem proves `PolygonCurveStatement` (exact segment integration of
a valid rational polygon) and keeps exactly the signature below. `lem_2fam_witness_of` in
`Statements.lean` turns it and the certified polygon into `WitnessStatement`. The polygon analysis
(segment lines, concavity, the segment integrals) is in `WitnessPoly.lean`.
-/

noncomputable section
open Set

namespace FixedPrice.TwoUnit.Family

namespace PkgD

/-- The polygon data as real sequences satisfy `SegData`. -/
lemma polygon_segData (D : PolygonData) (hV : D.Valid) :
    SegData D.n (fun j => (D.X j : ℝ)) (fun j => (D.Y j : ℝ)) (fun j => (D.slope j : ℝ)) where
  x_lt j hj := by exact_mod_cast hV.X_strictMono j hj
  y_pos j hj := by exact_mod_cast hV.Y_pos j hj
  slope j _ := by
    simp only [PolygonData.slope]
    push_cast
    rfl
  anti j hj := by exact_mod_cast hV.slope_antitone j hj

/-- Exact segment integration of a valid rational polygon. -/
theorem polygon_curve (D : PolygonData) (hV : D.Valid) :
    InClass D.params D.curve ∧ IsRationalConcavePolygon D.curve D.params.c D.params.ξ₀ ∧
      Rf D.params D.curve = (D.segmentRatio : ℝ) := by
  have hD := polygon_segData D hV
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, x = fun j => (D.X j : ℝ) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, y = fun j => (D.Y j : ℝ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun j => (D.slope j : ℝ) := ⟨_, rfl⟩
  rw [← hx, ← hy, ← hs] at hD
  have hcurve : D.curve = segMin D.n x y s := by subst hx hy hs; rfl
  have ht : (0 : ℝ) < D.t := by exact_mod_cast hV.t_pos
  have ht1 : (D.t : ℝ) < 1 := by exact_mod_cast hV.t_lt_one
  have htp : (D.t : ℝ) < D.p := by exact_mod_cast hV.t_lt_p
  have hp1 : (D.p : ℝ) < 1 := by exact_mod_cast hV.p_lt_one
  have hp : (0 : ℝ) < D.p := ht.trans htp
  have hx0 : x 0 = D.params.c := by
    rw [hx]
    show ((D.X 0 : ℚ) : ℝ) = cF (D.t : ℝ) D.p
    rw [hV.X_zero]; unfold cF; push_cast; ring
  have hxn : x (D.n + 1) = D.params.ξ₀ := by
    rw [hx]
    show ((D.X (D.n + 1) : ℚ) : ℝ) = D.ξ₀
    rw [hV.X_last]
  have hy0 : y 0 = D.params.p := by
    rw [hy]
    show ((D.Y 0 : ℚ) : ℝ) = D.p
    rw [hV.Y_zero]
  have hyn : y (D.n + 1) = 1 := by
    rw [hy]
    show ((D.Y (D.n + 1) : ℚ) : ℝ) = 1
    rw [hV.Y_last]; push_cast; rfl
  have hs0 : s 0 = 1 := by
    rw [hs]
    show ((D.slope 0 : ℚ) : ℝ) = 1
    rw [hV.slope_first]; push_cast; rfl
  have hsn : s D.n = D.params.h := by
    rw [hs]
    show ((D.slope D.n : ℚ) : ℝ) = vF (D.t : ℝ) / D.ξ₀
    rw [hV.slope_last]; unfold vF eF; push_cast; ring
  have hspos : ∀ j ≤ D.n, 0 < s j := fun j hj => by
    rw [hs]
    show (0 : ℝ) < (D.slope j : ℝ)
    exact_mod_cast hV.slope_pos j hj
  have hs1 : ∀ j ≤ D.n, |s j| ≤ 1 := fun j hj => by
    rw [abs_of_pos (hspos j hj), ← hs0]; exact hD.s_anti (Nat.zero_le j) hj
  have hc : 0 < D.params.c := by
    show 0 < cF (D.t : ℝ) D.p
    unfold cF; linarith
  have hcξ : D.params.c < D.params.ξ₀ := by
    rw [← hx0, ← hxn]
    exact lt_of_lt_of_le (hD.x_lt 0 (Nat.zero_le _)) (hD.x_mono (by omega) le_rfl)
  have hξ₀ : 0 < D.params.ξ₀ := hc.trans hcξ
  -- class membership
  have hclass : InClass D.params D.curve := by
    refine ⟨⟨ht, ht1, htp.le, hp1.le, hξ₀, hcξ.le⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ξ hξ
      rw [hcurve]
      rw [← hx0, ← hxn] at hξ
      exact hD.pos hξ
    · rw [hcurve]; exact SegData.concaveOn _ (convex_Icc _ _)
    · rw [hcurve]; exact ⟨1, (SegData.lipschitz hs1).lipschitzOnWith⟩
    · rw [hcurve, ← hx0, hD.segMin_vertex (Nat.zero_le _), hy0]
    · rw [hcurve, ← hxn, hD.segMin_vertex le_rfl, hyn]
    · intro ξ _
      rw [hcurve]
      apply le_min
      · have h1 := SegData.segMin_le (n := D.n) (x := x) (y := y) (s := s) 0 (Nat.zero_le _) ξ
        have hl : segLine x y s 0 ξ = D.params.line₁ ξ := by
          unfold segLine
          rw [hs0, hx0, hy0]
          show 1 * (ξ - cF (D.t : ℝ) D.p) + D.p = ξ + δF (D.t : ℝ) D.p
          unfold cF δF; ring
        linarith
      · have h1 := SegData.segMin_le (n := D.n) (x := x) (y := y) (s := s) D.n le_rfl ξ
        have hl : segLine x y s D.n ξ = D.params.line₂ ξ := by
          rw [SegData.line_step D.n (x (D.n + 1)) ξ, hD.line_right le_rfl, hyn, hsn, hxn]
          show 1 + D.params.h * (ξ - D.params.ξ₀) = D.params.h * ξ + D.params.e
          have hhξ : D.params.h * D.params.ξ₀ = D.params.v := by
            show D.params.v / D.params.ξ₀ * D.params.ξ₀ = D.params.v
            field_simp
          have hve : D.params.v + D.params.e = 1 := by
            show vF (D.t : ℝ) + eF (D.t : ℝ) = 1
            unfold vF; ring
          linear_combination (-1 : ℝ) * hve - hhξ
        linarith
  -- the rational polygon form
  have hpoly : IsRationalConcavePolygon D.curve D.params.c D.params.ξ₀ := by
    refine ⟨⟨(D.p - D.t) / 2, D.ξ₀, ?_, rfl⟩, D.n, fun j => D.slope j,
      fun j => D.Y j - D.slope j * D.X j, ?_⟩
    · show cF (D.t : ℝ) D.p = (((D.p - D.t) / 2 : ℚ) : ℝ)
      unfold cF; push_cast; ring
    · intro ξ _
      show (Finset.range (D.n + 1)).inf' Finset.nonempty_range_add_one
          (fun j => (D.slope j : ℝ) * (ξ - D.X j) + D.Y j) = _
      apply le_antisymm
      · apply Finset.le_inf'
        intro i _
        refine (Finset.inf'_le _ (Finset.mem_range.2 i.isLt)).trans (le_of_eq ?_)
        push_cast; ring
      · apply Finset.le_inf'
        intro j hj
        refine (Finset.inf'_le _
          (Finset.mem_univ (⟨j, Finset.mem_range.1 hj⟩ : Fin (D.n + 1)))).trans (le_of_eq ?_)
        push_cast; ring
  -- the functionals by segment integration
  have hT : Tf D.params D.curve = ((∑ j ∈ Finset.range (D.n + 1), D.ds j : ℚ) : ℝ) := by
    unfold Tf
    rw [hcurve, ← hx0, ← hxn, hD.integral_inv_sq]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [hx, hy]
    simp only [PolygonData.ds]
    push_cast
    rfl
  have hQ : Qf D.params D.curve = -Real.log D.params.p
      - ((∑ j ∈ Finset.range (D.n + 1),
          (D.Y j - D.X j * D.slope j) * D.slope j * D.ds j : ℚ) : ℝ) := by
    unfold Qf
    rw [hcurve, ← hx0, ← hxn, hD.integral_grad, hyn, hy0, Real.log_one]
    push_cast
    have hsum : ∑ j ∈ Finset.range (D.n + 1), (y j - x j * s j) * s j * ((x (j + 1) - x j)
        / (y j * y (j + 1)))
        = ∑ j ∈ Finset.range (D.n + 1), ((D.Y j : ℝ) - D.X j * D.slope j) * D.slope j * D.ds j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hx, hy, hs]
      simp only [PolygonData.ds]
      push_cast
      rfl
    rw [hsum]
    ring
  have hM : Mf D.params D.curve = (D.segmentM : ℝ) := by
    unfold Mf PolygonData.segmentM PolygonData.Nq PolygonData.aq
    rw [hT]
    push_cast
    show NF (D.t : ℝ) * (aF (D.t : ℝ) D.p + _ - D.ξ₀) = _
    unfold NF aF cF
    ring
  have hG : Gf D.params D.curve = (D.segmentG : ℝ) := by
    unfold Gf PolygonData.segmentG PolygonData.Nq PolygonData.mq PolygonData.aq
    rw [hQ]
    push_cast
    show 2 + 2 * mF (D.t : ℝ) * aF (D.t : ℝ) D.p - NF (D.t : ℝ) * Real.log D.p
        - NF (D.t : ℝ) * (-Real.log D.p - _) = _
    unfold mF aF NF cF
    have hsum : ∑ i ∈ Finset.range (D.n + 1), 2 / (1 + (D.t : ℝ))
          * ((D.Y i : ℝ) - D.X i * D.slope i) * D.slope i * D.ds i
        = 2 / (1 + (D.t : ℝ)) * ∑ i ∈ Finset.range (D.n + 1),
          ((D.Y i : ℝ) - D.X i * D.slope i) * D.slope i * D.ds i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    ring
  refine ⟨hclass, hpoly, ?_⟩
  unfold Rf PolygonData.segmentRatio
  rw [hM, hG]
  push_cast
  rfl

end PkgD

/-- `PolygonCurveStatement`. -/
theorem polygon_curve_proof : PolygonCurveStatement :=
  fun D hV => PkgD.polygon_curve D hV

end FixedPrice.TwoUnit.Family
