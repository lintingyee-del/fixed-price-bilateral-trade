import FixedPrice.EndpointDerivative
import FixedPrice.BranchRoot

/-! The scalar curve of Section 3: `S(C) = C (2 + I(C))` is strictly decreasing and
`τ(C) = C²/(1-2C) e^{-I(C)/2}` is strictly increasing on `(1/4, 1/2)`, equation (7), and the
root equation (44) `S(C) = 1 + τ(C)` has exactly one solution there. The boundary behaviour (8)
is replaced by two explicit evaluations, at `C = 101/400` and `C = 49/100`. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

theorem hasDerivAt_endParameter {C : ℝ} (hC0 : C ≠ 0) (hC1 : 1 - C ≠ 0) :
    HasDerivAt endParameter (-(1 / C ^ 2) - 1 / (1 - C) ^ 2) C := by
  have h := (((hasDerivAt_id C).const_mul 2).const_sub 1).div
    ((hasDerivAt_id C).mul ((hasDerivAt_id C).const_sub 1)) (mul_ne_zero hC0 hC1)
  convert h using 1
  simp only [Pi.mul_apply, id_eq, mul_one]
  field_simp
  ring

/-- The derivative of `I(C) = I_C(y_e(C))`. -/
def scalarDerivI (C : ℝ) : ℝ :=
  -secondPrimitive C (endParameter C) +
    (-(1 / C ^ 2) - 1 / (1 - C) ^ 2) / denominator C (endParameter C)

theorem hasDerivAt_scalarI {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt (fun x => primitive x (endParameter x)) (scalarDerivI C) C := by
  have hC0 : C ≠ 0 := ne_of_gt (by linarith [hC.1])
  have hC1 : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have hY := hasDerivAt_endParameter hC0 hC1
  have hy := endParameter_pos hC
  have hD : ∀ r ∈ Icc (0 : ℝ) (endParameter C), 0 < denominator C r :=
    fun r _ => denominator_pos hC.1 r
  have hn := ne_of_gt (hD (endParameter C) ⟨hy.le, le_rfl⟩)
  have hcl := contactLog_deriv_along_branch hY hy hD
  have hden := hasDerivAt_denominator_along hY
  have hsum := ((hden.log hn).sub ((hY.log (ne_of_gt hy)).const_mul 2)).sub (hcl.const_mul 2)
  have heq : (fun x => primitive x (endParameter x)) = fun x =>
      Real.log (denominator x (endParameter x)) - 2 * Real.log (endParameter x) -
        2 * contactLog x (endParameter x) := by
    funext x
    unfold contactLog
    ring
  rw [heq]
  convert hsum using 1
  unfold scalarDerivI contactDerivativeC contactDerivativeY
  generalize endParameter C = y at hy hn ⊢
  field_simp [hn, ne_of_gt hy]
  unfold denominator
  ring

theorem scalarDerivI_neg {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) : scalarDerivI C < 0 := by
  have hy := endParameter_pos hC
  have hn := denominator_pos hC.1 (endParameter C)
  have hZ := secondPrimitive_nonneg (C := C) hy.le
  have hC0 : 0 < C := by linarith [hC.1]
  have hC1 : 0 < 1 - C := by linarith [hC.2]
  have hq : -(1 / C ^ 2) - 1 / (1 - C) ^ 2 < 0 := by
    have := one_div_pos.mpr (pow_pos hC0 2)
    have := one_div_pos.mpr (pow_pos hC1 2)
    linarith
  unfold scalarDerivI
  have := div_neg_of_neg_of_pos hq hn
  linarith

theorem primitive_endParameter_pos {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    0 < primitive C (endParameter C) := by
  have hy := endParameter_pos hC
  unfold primitive
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact ((continuous_denominator C).inv₀
      (fun r => ne_of_gt (denominator_pos hC.1 r))).intervalIntegrable _ _
  · intro r _
    exact inv_pos.mpr (denominator_pos hC.1 r)
  · exact hy

/-- Equation (7): `(4C - 1) S'(C) = (2C - 1) I(C) + 8C - 6`. -/
theorem hasDerivAt_optimalValue {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt optimalValue
      (((2 * C - 1) * primitive C (endParameter C) + 8 * C - 6) / (4 * C - 1)) C := by
  have hI := hasDerivAt_scalarI hC
  have hS := (hasDerivAt_id C).mul (hI.const_add 2)
  have hC0 : C ≠ 0 := ne_of_gt (by linarith [hC.1])
  have hC1 : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have h4 : 4 * C - 1 ≠ 0 := ne_of_gt (by linarith [hC.1])
  have hy := endParameter_pos hC
  have hD : ∀ r ∈ Icc (0 : ℝ) (endParameter C), 0 < denominator C r :=
    fun r _ => denominator_pos hC.1 r
  have hn := ne_of_gt (hD (endParameter C) ⟨hy.le, le_rfl⟩)
  have hid := primitive_secondPrimitive_identity hy.le hD
  have hDe : denominator C (endParameter C) = C ^ 2 / (1 - C) ^ 2 :=
    denominator_endParameter hC0 hC1
  convert hS using 1
  unfold scalarDerivI
  simp only [id_eq, one_mul]
  have hZ : secondPrimitive C (endParameter C) =
      (2 * primitive C (endParameter C) +
        endParameter C * (endParameter C - 2) / denominator C (endParameter C)) / (4 * C - 1) := by
    rw [eq_div_iff h4, mul_comm]
    exact hid
  rw [hZ, hDe]
  generalize primitive C (endParameter C) = I
  have hy_def : endParameter C = (1 - 2 * C) / (C * (1 - C)) := rfl
  have h4' : C * 4 - 1 ≠ 0 := by rwa [mul_comm]
  rw [hy_def]
  field_simp
  ring

theorem hasDerivAt_optimalValue_neg {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    ((2 * C - 1) * primitive C (endParameter C) + 8 * C - 6) / (4 * C - 1) < 0 := by
  have hI := primitive_endParameter_pos hC
  apply div_neg_of_neg_of_pos _ (by linarith [hC.1])
  nlinarith [hC.1, hC.2]

theorem optimalValue_strictAntiOn : StrictAntiOn optimalValue (Ioo (1 / 4 : ℝ) (1 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro C hC
    exact (hasDerivAt_optimalValue hC).continuousAt.continuousWithinAt
  · intro C hC
    rw [interior_Ioo] at hC
    rw [(hasDerivAt_optimalValue hC).deriv]
    exact hasDerivAt_optimalValue_neg hC

theorem hasDerivAt_initialState {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt initialState
      ((2 * C * (1 - 2 * C) + 2 * C ^ 2) / (1 - 2 * C) ^ 2 *
          Real.exp (-(primitive C (endParameter C)) / 2) +
        C ^ 2 / (1 - 2 * C) * (Real.exp (-(primitive C (endParameter C)) / 2) *
          (-(scalarDerivI C) / 2))) C := by
  have h2 : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have hc := ((hasDerivAt_id C).pow 2).div (((hasDerivAt_id C).const_mul 2).const_sub 1) h2
  have he := (((hasDerivAt_scalarI hC).neg).div_const 2).exp
  convert hc.mul he using 1
  simp only [Pi.pow_apply, Pi.div_apply, id_eq, Nat.cast_ofNat, Pi.neg_apply]
  field_simp
  ring

theorem initialState_strictMonoOn : StrictMonoOn initialState (Ioo (1 / 4 : ℝ) (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro C hC
    exact (hasDerivAt_initialState hC).continuousAt.continuousWithinAt
  · intro C hC
    rw [interior_Ioo] at hC
    rw [(hasDerivAt_initialState hC).deriv]
    have hC0 : 0 < C := by linarith [hC.1]
    have h2 : 0 < 1 - 2 * C := by linarith [hC.2]
    have hI' := scalarDerivI_neg hC
    have he := Real.exp_pos (-(primitive C (endParameter C)) / 2)
    have hA : 0 < (2 * C * (1 - 2 * C) + 2 * C ^ 2) / (1 - 2 * C) ^ 2 :=
      div_pos (by nlinarith) (pow_pos h2 2)
    have hB : 0 < C ^ 2 / (1 - 2 * C) := div_pos (pow_pos hC0 2) h2
    have := mul_pos hA he
    have := mul_pos hB (mul_pos he (by linarith : 0 < -(scalarDerivI C) / 2))
    linarith

/-- Near `C = 1/4` the integral `I(C)` is large. -/
theorem primitive_endParameter_ge_ten :
    10 ≤ primitive (101 / 400) (endParameter (101 / 400)) := by
  set C : ℝ := 101 / 400 with hC_def
  have hC : 1 / 4 < C := by norm_num [hC_def]
  have hye : (2 : ℝ) ≤ endParameter C := by
    unfold endParameter
    rw [hC_def]
    norm_num
  have hcont : Continuous (fun r => (denominator C r)⁻¹) :=
    (continuous_denominator C).inv₀ (fun r => ne_of_gt (denominator_pos hC r))
  have hi := fun a b => hcont.intervalIntegrable (μ := volume) a b
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (9 / 5)) (hi (9 / 5) (endParameter C))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hi (9 / 5) 2) (hi 2 (endParameter C))
  have hnn1 : 0 ≤ ∫ r in (0 : ℝ)..9 / 5, (denominator C r)⁻¹ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun r _ => (inv_pos.mpr (denominator_pos hC r)).le)
  have hnn2 : 0 ≤ ∫ r in (2 : ℝ)..endParameter C, (denominator C r)⁻¹ :=
    intervalIntegral.integral_nonneg hye (fun r _ => (inv_pos.mpr (denominator_pos hC r)).le)
  have hmid : (10 : ℝ) ≤ ∫ r in (9 / 5 : ℝ)..2, (denominator C r)⁻¹ := by
    have hle : ∫ _r in (9 / 5 : ℝ)..2, (50 : ℝ) ≤ ∫ r in (9 / 5 : ℝ)..2, (denominator C r)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const (hi _ _)
      intro r hr
      have hDr := denominator_pos hC r
      rw [le_inv_comm₀ (by norm_num) hDr]
      unfold denominator
      rw [hC_def]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)]
    have hval : ∫ _r in (9 / 5 : ℝ)..2, (50 : ℝ) = 10 := by norm_num
    linarith
  unfold primitive
  linarith

theorem primitive_endParameter_le_small :
    primitive (49 / 100) (endParameter (49 / 100)) ≤ 400 / 2499 := by
  set C : ℝ := 49 / 100 with hC_def
  have hC : 1 / 4 < C := by norm_num [hC_def]
  have hye : endParameter C = 200 / 2499 := by
    unfold endParameter
    rw [hC_def]
    norm_num
  have hcont : Continuous (fun r => (denominator C r)⁻¹) :=
    (continuous_denominator C).inv₀ (fun r => ne_of_gt (denominator_pos hC r))
  have hle : ∫ r in (0 : ℝ)..endParameter C, (denominator C r)⁻¹ ≤
      ∫ _r in (0 : ℝ)..endParameter C, (2 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by rw [hye]; norm_num) (hcont.intervalIntegrable _ _)
      intervalIntegrable_const
    intro r hr
    rw [hye] at hr
    have hDr := denominator_pos hC r
    rw [inv_le_comm₀ hDr (by norm_num)]
    unfold denominator
    rw [hC_def]
    nlinarith [hr.1, hr.2, sq_nonneg r]
  have hval : ∫ _r in (0 : ℝ)..endParameter C, (2 : ℝ) = 400 / 2499 := by
    rw [hye]
    norm_num
  unfold primitive
  linarith

/-- The root equation (44) has exactly one solution in `(1/4, 1/2)`. -/
theorem existsUnique_root :
    ∃! C : ℝ, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ optimalValue C = 1 + initialState C := by
  set f : ℝ → ℝ := fun C => optimalValue C - 1 - initialState C with hf_def
  have hsub : Icc (101 / 400 : ℝ) (49 / 100) ⊆ Ioo (1 / 4) (1 / 2) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcont : ContinuousOn f (Icc (101 / 400 : ℝ) (49 / 100)) := by
    intro x hx
    have hx' := hsub hx
    exact (((hasDerivAt_optimalValue hx').continuousAt.sub continuousAt_const).sub
      (hasDerivAt_initialState hx').continuousAt).continuousWithinAt
  have hfa : 0 ≤ f (101 / 400) := by
    have hI := primitive_endParameter_ge_ten
    have hτ : initialState (101 / 400) ≤ 1 := by
      unfold initialState
      have he : Real.exp (-primitive (101 / 400) (endParameter (101 / 400)) / 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have hc : (0 : ℝ) ≤ (101 / 400) ^ 2 / (1 - 2 * (101 / 400)) := by norm_num
      calc (101 / 400 : ℝ) ^ 2 / (1 - 2 * (101 / 400)) *
            Real.exp (-primitive (101 / 400) (endParameter (101 / 400)) / 2)
          ≤ (101 / 400) ^ 2 / (1 - 2 * (101 / 400)) * 1 := mul_le_mul_of_nonneg_left he hc
        _ ≤ 1 := by norm_num
    simp only [hf_def, optimalValue]
    nlinarith
  have hfb : f (49 / 100) ≤ 0 := by
    have hI := primitive_endParameter_le_small
    have hI0 := primitive_endParameter_pos (C := 49 / 100) ⟨by norm_num, by norm_num⟩
    have hτ : 10 ≤ initialState (49 / 100) := by
      unfold initialState
      have he : 1 - primitive (49 / 100) (endParameter (49 / 100)) / 2 ≤
          Real.exp (-primitive (49 / 100) (endParameter (49 / 100)) / 2) := by
        have := Real.add_one_le_exp (-primitive (49 / 100) (endParameter (49 / 100)) / 2)
        linarith
      have hc : (49 / 100 : ℝ) ^ 2 / (1 - 2 * (49 / 100)) = 2401 / 200 := by norm_num
      rw [hc]
      nlinarith
    simp only [hf_def, optimalValue]
    nlinarith
  obtain ⟨C, hC, hfC⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨hfb, hfa⟩
  refine ⟨C, ⟨hsub hC, by simp only [hf_def] at hfC; linarith⟩, ?_⟩
  rintro C' ⟨hC', hroot'⟩
  have hroot : optimalValue C = 1 + initialState C := by simp only [hf_def] at hfC; linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := optimalValue_strictAntiOn hC' (hsub hC) hlt
    have h2 := initialState_strictMonoOn hC' (hsub hC) hlt
    linarith
  · have h1 := optimalValue_strictAntiOn (hsub hC) hC' hgt
    have h2 := initialState_strictMonoOn (hsub hC) hC' hgt
    linarith

end FixedPrice
