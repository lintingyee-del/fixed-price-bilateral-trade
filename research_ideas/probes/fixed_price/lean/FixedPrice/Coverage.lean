import FixedPrice.ReferenceParameters
import FixedPrice.BranchRoot

/-! Every endpoint below the cap is reached by the reference branch: for each
denominator value `D` with `d < D/(1-D)` there is a physical contact point with
`denominator C Y = D`. The argument moves along the curve `C = (D-1+y)/y^2`,
on which the denominator at the contact parameter is `D` by construction, and
uses the blow-up of the primitive near the double root. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

theorem continuousAt_curvature {D y : ℝ} (hy : y ≠ 0) :
    ContinuousAt (curvatureAtEndpoint D) y := by
  unfold curvatureAtEndpoint
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  exact pow_ne_zero 2 hy

theorem continuousAt_contactLog_pair {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    ContinuousAt (fun q : ℝ × ℝ => contactLog q.1 q.2) (C, y) :=
  (hasStrictFDerivAt_contactLog hy hD).continuousAt

/-- The contact function along the fixed-denominator curve. -/
def curveContact (D y : ℝ) : ℝ := contactLog (curvatureAtEndpoint D y) y

theorem curvature_lower_endpoint (D : ℝ) : curvatureAtEndpoint D (1 - D) = 0 := by
  simp [curvatureAtEndpoint]

theorem continuousAt_curveContact {D y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator (curvatureAtEndpoint D y) r) :
    ContinuousAt (curveContact D) y := by
  have hc := continuousAt_contactLog_pair hy hD
  have hpair : ContinuousAt (fun z => (curvatureAtEndpoint D z, z)) y :=
    (continuousAt_curvature (ne_of_gt hy)).prodMk continuousAt_id
  exact ContinuousAt.comp (f := fun z => (curvatureAtEndpoint D z, z)) hc hpair

/-- Along the fixed-denominator curve the contact function is continuous on the
closed physical parameter interval, including the left endpoint where `C = 0`. -/
theorem continuousOn_curveContact {D y₁ : ℝ} (hD : D ∈ Ioo (0 : ℝ) 1)
    (hy₁ : y₁ < 2 + 2 * Real.sqrt D) :
    ContinuousOn (curveContact D) (Icc (1 - D) y₁) := by
  intro y hy
  apply ContinuousAt.continuousWithinAt
  have hypos : 0 < y := by linarith [hy.1, hD.2]
  rcases eq_or_lt_of_le hy.1 with heq | hlt
  · subst heq
    apply continuousAt_curveContact hypos
    intro r hr
    rw [curvature_lower_endpoint]
    simp only [denominator, zero_mul, add_zero]
    linarith [hr.2, hD.1]
  · exact continuousAt_curveContact hypos
      (curvature_physical hD hlt (lt_of_le_of_lt hy.2 hy₁)).2.2

theorem exists_branch_point {d D : ℝ} (hd : 0 < d) (hD : D ∈ Ioo (0 : ℝ) 1)
    (hdD : d * (1 - D) < D) :
    ∃ C y : ℝ, 0 < C ∧ IsBranchRoot d C y ∧ denominator C y = D := by
  set q := Real.sqrt D with hq_def
  have hq : 0 < q := Real.sqrt_pos.mpr hD.1
  have hq1 : q < 1 := by
    rw [hq_def, Real.sqrt_lt' one_pos]
    simpa using hD.2
  set s₀ : ℝ := 1 / (1 + q) with hs₀_def
  have hs₀ : 0 < s₀ := div_pos one_pos (by linarith)
  have hs₀1 : s₀ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set K : ℝ := (1 + q) ^ 2 + 1 with hK_def
  have hK : 0 < K := by positivity
  set L : ℝ := |Real.log d| + 1 with hL_def
  have hL : 0 < L := by positivity
  set ε : ℝ := min (min (s₀ / 2) ((1 - s₀) / 2)) (min (1 / 2) (1 / (K * L))) / 2 with hε_def
  have hε : 0 < ε := by
    apply div_pos _ two_pos
    apply lt_min (lt_min (by linarith) (by linarith))
    exact lt_min (by norm_num) (div_pos one_pos (mul_pos hK hL))
  have hε_le₁ : ε ≤ s₀ / 2 / 2 := by
    apply div_le_div_of_nonneg_right _ two_pos.le
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hε_le₂ : ε ≤ (1 - s₀) / 2 / 2 := by
    apply div_le_div_of_nonneg_right _ two_pos.le
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hε_le₃ : ε ≤ 1 / 2 / 2 := by
    apply div_le_div_of_nonneg_right _ two_pos.le
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hε_le₄ : ε ≤ 1 / (K * L) / 2 := by
    apply div_le_div_of_nonneg_right _ two_pos.le
    exact (min_le_right _ _).trans (min_le_right _ _)
  have he1 : ε < 1 := by linarith
  have hel : ε < (1 / (1 + Real.sqrt D)) / 2 := by rw [← hq_def, ← hs₀_def]; linarith
  have her : ε < (1 - 1 / (1 + Real.sqrt D)) / 2 := by rw [← hq_def, ← hs₀_def]; linarith
  have hprim := primitive_lower_near_boundary hD hε he1 hel her
  rw [← hq_def, ← hK_def] at hprim
  set y₁ : ℝ := 2 + 2 * q - ε ^ 2 with hy₁_def
  have hε2 : ε ^ 2 < 1 := by nlinarith
  have hy₁_gt : 1 < y₁ := by rw [hy₁_def]; nlinarith
  have hy₁_lt : y₁ < 2 + 2 * Real.sqrt D := by
    rw [hy₁_def, ← hq_def]; nlinarith [sq_pos_of_pos hε]
  have hy₀ : 1 - D < y₁ := by linarith [hD.1]
  -- the contact value at the far endpoint is below `log d`
  have hlarge : 2 * (|Real.log d| + 1) ≤ primitive (curvatureAtEndpoint D y₁) y₁ := by
    refine le_trans ?_ hprim
    have hKe : K * ε ≤ 1 / (2 * L) := by
      have := mul_le_mul_of_nonneg_left hε_le₄ hK.le
      calc K * ε ≤ K * (1 / (K * L) / 2) := this
        _ = 1 / (2 * L) := by field_simp
    have hpos : 0 < K * ε := mul_pos hK hε
    have h1 : 2 / (1 / (2 * L)) ≤ 2 / (K * ε) :=
      div_le_div_of_nonneg_left (by norm_num) hpos hKe
    have h2 : 2 / (1 / (2 * L)) = 4 * L := by
      rw [div_div_eq_mul_div, div_one]; ring
    have h3 : 2 * (|Real.log d| + 1) = 2 * L := by rw [hL_def]
    linarith
  have hfar : curveContact D y₁ < Real.log d := by
    unfold curveContact contactLog
    rw [denominator_curvature_endpoint (ne_of_gt (by linarith))]
    have hlogD : Real.log D < 0 := Real.log_neg hD.1 hD.2
    have hlogy : 0 < Real.log y₁ := Real.log_pos hy₁_gt
    have habs : -|Real.log d| ≤ Real.log d := neg_abs_le _
    linarith
  have hnear : Real.log d < curveContact D (1 - D) := by
    unfold curveContact
    rw [contactLog_curvature_lower hD]
    apply Real.log_lt_log hd
    rw [lt_div_iff₀ (by linarith [hD.2])]
    exact hdD
  have hcont := continuousOn_curveContact hD hy₁_lt
  have hivt := intermediate_value_Icc' hy₀.le hcont
  obtain ⟨y, hy, hyval⟩ := hivt ⟨hfar.le, hnear.le⟩
  have hy_ne₀ : y ≠ 1 - D := by
    rintro rfl
    exact absurd hyval (ne_of_gt hnear)
  have hy_ne₁ : y ≠ y₁ := by
    rintro rfl
    exact absurd hyval (ne_of_lt hfar)
  have hy_lo : 1 - D < y := lt_of_le_of_ne hy.1 (Ne.symm hy_ne₀)
  have hy_hi : y < 2 + 2 * Real.sqrt D := lt_of_lt_of_le (lt_of_le_of_ne hy.2 hy_ne₁) hy₁_lt.le
  obtain ⟨hCpos, hCy, hphys⟩ := curvature_physical hD hy_lo hy_hi
  refine ⟨curvatureAtEndpoint D y, y, hCpos, ⟨?_, hCy, hphys, hyval⟩, ?_⟩
  · linarith [hD.2]
  · exact denominator_curvature_endpoint (ne_of_gt (by linarith [hD.2]))

end FixedPrice
