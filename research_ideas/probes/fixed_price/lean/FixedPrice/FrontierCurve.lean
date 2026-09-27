import FixedPrice.ScalarCurve
import FixedPrice.Strict

/-! The scalar curve at its ends, equation (8), and the tangent parameter
`κ(C) = τ(C)(S(C) + u)/u`, `u = 1 - 2C`, of Theorem B: `I(C) → ∞` and `τ → 0` as `C ↓ 1/4`,
`S → 1` and `τ → ∞` as `C ↑ 1/2`; `I' = -2(CI + 2)/(C(4C - 1))` and `τ'/τ = -S'/u`;
`κ` is a strictly increasing bijection of `(1/4, 1/2)` onto `(0, ∞)`. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace FixedPrice

/-- `I(C) = I_C(y_e(C))`. -/
def scalarI (C : ℝ) : ℝ := primitive C (endParameter C)

/-- The tangent slope `κ(C) = τ(C)(S(C) + u)/u`, `u = 1 - 2C`, equation (51). -/
def kappaOf (C : ℝ) : ℝ := initialState C * (optimalValue C + (1 - 2 * C)) / (1 - 2 * C)

section Derivatives

variable {C : ℝ}

theorem scalarDerivI_eq (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    scalarDerivI C = -2 * (C * scalarI C + 2) / (C * (4 * C - 1)) := by
  have hC0 : C ≠ 0 := ne_of_gt (by linarith [hC.1])
  have hC1 : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have h4 : 4 * C - 1 ≠ 0 := ne_of_gt (by linarith [hC.1])
  have h4' : C * 4 - 1 ≠ 0 := by rwa [mul_comm]
  have hy := endParameter_pos hC
  have hD : ∀ r ∈ Icc (0 : ℝ) (endParameter C), 0 < denominator C r :=
    fun r _ => denominator_pos hC.1 r
  have hid := primitive_secondPrimitive_identity hy.le hD
  have hDe : denominator C (endParameter C) = C ^ 2 / (1 - C) ^ 2 :=
    denominator_endParameter hC0 hC1
  have hZ : secondPrimitive C (endParameter C) =
      (2 * primitive C (endParameter C) +
        endParameter C * (endParameter C - 2) / denominator C (endParameter C)) / (4 * C - 1) := by
    rw [eq_div_iff h4, mul_comm]
    exact hid
  unfold scalarDerivI scalarI
  rw [hZ, hDe]
  generalize primitive C (endParameter C) = I
  have hy_def : endParameter C = (1 - 2 * C) / (C * (1 - C)) := rfl
  rw [hy_def]
  field_simp
  ring

/-- `(4C - 1) S' = (2C - 1) I + 8C - 6`, with `I` named. -/
theorem hasDerivAt_optimalValue' (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt optimalValue (((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1)) C :=
  hasDerivAt_optimalValue hC

/-- `τ' = -τ S'/u`, the last identity of (7). -/
theorem hasDerivAt_initialState' (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt initialState
      (-(initialState C) * (((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1)) /
        (1 - 2 * C)) C := by
  have h := hasDerivAt_initialState hC
  convert h using 1
  rw [scalarDerivI_eq hC]
  have hC0 : C ≠ 0 := ne_of_gt (by linarith [hC.1])
  have h2 : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have h4 : 4 * C - 1 ≠ 0 := ne_of_gt (by linarith [hC.1])
  have h4' : C * 4 - 1 ≠ 0 := by rwa [mul_comm]
  have h2' : 1 - C * 2 ≠ 0 := by rwa [mul_comm]
  unfold initialState scalarI
  field_simp
  ring

theorem optimalValue_deriv_neg (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    ((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1) < 0 :=
  hasDerivAt_optimalValue_neg hC

theorem hasDerivAt_kappaOf (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt kappaOf
      (initialState C * optimalValue C *
        (2 - ((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1)) / (1 - 2 * C) ^ 2) C := by
  set σ := ((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1) with hσ
  have h2 : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have hτ := hasDerivAt_initialState' hC
  have hS := hasDerivAt_optimalValue' hC
  have hu : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) C := by
    simpa using ((hasDerivAt_id C).const_mul 2).const_sub 1
  have h := (hτ.mul (hS.add hu)).div hu h2
  convert h using 1
  rw [← hσ]
  simp only [Pi.add_apply, Pi.mul_apply]
  field_simp
  ring

theorem kappaOf_deriv_pos (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    0 < initialState C * optimalValue C *
        (2 - ((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1)) / (1 - 2 * C) ^ 2 := by
  have hτ := initialState_pos hC
  have hS : 0 < optimalValue C := by linarith [one_lt_optimalValue hC]
  have hσ := optimalValue_deriv_neg hC
  have h2 : 0 < 1 - 2 * C := by linarith [hC.2]
  apply div_pos _ (pow_pos h2 2)
  exact mul_pos (mul_pos hτ hS) (by linarith)

theorem kappaOf_strictMonoOn : StrictMonoOn kappaOf (Ioo (1 / 4 : ℝ) (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro C hC
    exact (hasDerivAt_kappaOf hC).continuousAt.continuousWithinAt
  · intro C hC
    rw [interior_Ioo] at hC
    rw [(hasDerivAt_kappaOf hC).deriv]
    exact kappaOf_deriv_pos hC

theorem kappaOf_pos (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) : 0 < kappaOf C := by
  have hτ := initialState_pos hC
  have hS : 0 < optimalValue C := by linarith [one_lt_optimalValue hC]
  have h2 : 0 < 1 - 2 * C := by linarith [hC.2]
  unfold kappaOf
  positivity

theorem optimalValue_continuousOn : ContinuousOn optimalValue (Ioo (1 / 4 : ℝ) (1 / 2)) :=
  fun _ hC => (hasDerivAt_optimalValue hC).continuousAt.continuousWithinAt

theorem initialState_continuousOn : ContinuousOn initialState (Ioo (1 / 4 : ℝ) (1 / 2)) :=
  fun _ hC => (hasDerivAt_initialState hC).continuousAt.continuousWithinAt

theorem kappaOf_continuousOn : ContinuousOn kappaOf (Ioo (1 / 4 : ℝ) (1 / 2)) :=
  fun _ hC => (hasDerivAt_kappaOf hC).continuousAt.continuousWithinAt

theorem scalarI_continuousOn : ContinuousOn scalarI (Ioo (1 / 4 : ℝ) (1 / 2)) :=
  fun _ hC => (hasDerivAt_scalarI hC).continuousAt.continuousWithinAt

end Derivatives

section Ends

theorem denominator_eq_square (C r : ℝ) :
    denominator C r = (1 - r / 2) ^ 2 + (C - 1 / 4) * r ^ 2 := by
  unfold denominator
  ring

theorem scalarI_pos {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) : 0 < scalarI C :=
  primitive_endParameter_pos hC

/-- (8), left end: `I(C) → ∞` as `C ↓ 1/4`. -/
theorem scalarI_tendsto_left : Tendsto scalarI (𝓝[>] (1 / 4)) atTop := by
  rw [tendsto_atTop]
  intro M
  set M' := max M 2 with hM'
  have hM'2 : 2 ≤ M' := le_max_right _ _
  set w := 2 / M' with hw
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 := by rw [hw, div_le_one (by linarith)]; exact hM'2
  set δ := min (1 / 25) (w ^ 2 / 16) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 1 / 4 + δ by linarith)] with C hCm
  have hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
    ⟨hCm.1, by linarith [hCm.2, min_le_left (1 / 25 : ℝ) (w ^ 2 / 16)]⟩
  set ε := C - 1 / 4 with hε
  have hε0 : 0 < ε := by linarith [hCm.1]
  have hεw : ε ≤ w ^ 2 / 16 := by linarith [hCm.2, min_le_right (1 / 25 : ℝ) (w ^ 2 / 16)]
  have hC29 : C ≤ 29 / 100 := by linarith [hCm.2, min_le_left (1 / 25 : ℝ) (w ^ 2 / 16)]
  have hye : (2 : ℝ) ≤ endParameter C := by
    have hC0 : 0 < C := by linarith
    have hC1 : 0 < 1 - C := by linarith
    unfold endParameter
    rw [le_div_iff₀ (mul_pos hC0 hC1)]
    nlinarith
  have hcont : Continuous (fun r => (denominator C r)⁻¹) :=
    (continuous_denominator C).inv₀ (fun r => ne_of_gt (denominator_pos hC.1 r))
  have hi := fun a b => hcont.intervalIntegrable (μ := volume) a b
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 - w)) (hi (2 - w) (endParameter C))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (hi (2 - w) 2) (hi 2 (endParameter C))
  have hn1 : 0 ≤ ∫ r in (0 : ℝ)..2 - w, (denominator C r)⁻¹ :=
    intervalIntegral.integral_nonneg (by linarith) (fun r _ => (inv_pos.mpr (denominator_pos hC.1 r)).le)
  have hn2 : 0 ≤ ∫ r in (2 : ℝ)..endParameter C, (denominator C r)⁻¹ :=
    intervalIntegral.integral_nonneg hye (fun r _ => (inv_pos.mpr (denominator_pos hC.1 r)).le)
  have hmid : M' ≤ ∫ r in (2 - w : ℝ)..2, (denominator C r)⁻¹ := by
    have hle : ∫ _r in (2 - w : ℝ)..2, (2 / w ^ 2 : ℝ) ≤ ∫ r in (2 - w : ℝ)..2, (denominator C r)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hi _ _)
      intro r hr
      have hDr := denominator_pos hC.1 r
      rw [le_inv_comm₀ (by positivity) hDr, inv_div, denominator_eq_square]
      have h1 : (1 - r / 2) ^ 2 ≤ w ^ 2 / 4 := by
        have ha : 0 ≤ 1 - r / 2 := by linarith [hr.2]
        have hb : 1 - r / 2 ≤ w / 2 := by linarith [hr.1]
        nlinarith
      have h2 : (C - 1 / 4) * r ^ 2 ≤ w ^ 2 / 4 := by
        have hr2 : r ^ 2 ≤ 4 := by nlinarith [hr.1, hr.2]
        have : (C - 1 / 4) * r ^ 2 ≤ (w ^ 2 / 16) * 4 :=
          mul_le_mul hεw hr2 (sq_nonneg r) (by positivity)
        linarith
      linarith
    have hval : ∫ _r in (2 - w : ℝ)..2, (2 / w ^ 2 : ℝ) = M' := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      rw [hw]
      field_simp
      ring
    linarith
  have : M' ≤ scalarI C := by
    unfold scalarI primitive
    linarith
  exact (le_max_left M 2).trans this

/-- (8), left end: `S(C) → ∞`. -/
theorem optimalValue_tendsto_left : Tendsto optimalValue (𝓝[>] (1 / 4)) atTop := by
  apply tendsto_atTop_mono' _ _ (scalarI_tendsto_left.atTop_div_const (show (0 : ℝ) < 4 by norm_num))
  filter_upwards [Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with C hC
  have hI := scalarI_pos hC
  unfold optimalValue
  change scalarI C / 4 ≤ C * (2 + scalarI C)
  nlinarith [hC.1]

/-- (8), left end: `τ(C) → 0`. -/
theorem initialState_tendsto_left : Tendsto initialState (𝓝[>] (1 / 4)) (𝓝 0) := by
  have hexp : Tendsto (fun C => Real.exp (-scalarI C / 2)) (𝓝[>] (1 / 4)) (𝓝 0) := by
    have : Tendsto (fun C => -scalarI C / 2) (𝓝[>] (1 / 4)) atBot := by
      have h := scalarI_tendsto_left.atTop_div_const (show (0 : ℝ) < 2 by norm_num)
      refine (tendsto_neg_atTop_atBot.comp h).congr ?_
      intro C
      simp [Function.comp, neg_div]
    exact Real.tendsto_exp_atBot.comp this
  have hpre : Tendsto (fun C : ℝ => C ^ 2 / (1 - 2 * C)) (𝓝[>] (1 / 4)) (𝓝 ((1 / 4) ^ 2 / (1 - 2 * (1 / 4)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((continuous_pow 2).continuousAt.div (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
      (by norm_num)).tendsto
  have := hpre.mul hexp
  rw [mul_zero] at this
  apply this.congr'
  filter_upwards with C
  unfold initialState scalarI
  ring_nf

theorem endParameter_le_of_near_half {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hC' : 9 / 20 ≤ C) : endParameter C ≤ 1 / 2 := by
  have hC0 : 0 < C := by linarith [hC.1]
  have hC1 : 0 < 1 - C := by linarith [hC.2]
  unfold endParameter
  rw [div_le_iff₀ (mul_pos hC0 hC1)]
  nlinarith [hC.2]

theorem scalarI_le_two_endParameter {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hy : endParameter C ≤ 1 / 2) : scalarI C ≤ 2 * endParameter C := by
  have hye := endParameter_pos hC
  have hcont : Continuous (fun r => (denominator C r)⁻¹) :=
    (continuous_denominator C).inv₀ (fun r => ne_of_gt (denominator_pos hC.1 r))
  have hle : ∫ r in (0 : ℝ)..endParameter C, (denominator C r)⁻¹ ≤
      ∫ _r in (0 : ℝ)..endParameter C, (2 : ℝ) := by
    apply intervalIntegral.integral_mono_on hye.le (hcont.intervalIntegrable _ _)
      intervalIntegrable_const
    intro r hr
    have hDr := denominator_pos hC.1 r
    rw [inv_le_comm₀ hDr (by norm_num)]
    unfold denominator
    nlinarith [hr.1, hr.2, sq_nonneg r, hC.1]
  have hval : ∫ _r in (0 : ℝ)..endParameter C, (2 : ℝ) = 2 * endParameter C := by
    simp [mul_comm]
  unfold scalarI primitive
  linarith

theorem endParameter_tendsto_right : Tendsto endParameter (𝓝[<] (1 / 2)) (𝓝 0) := by
  have h : Tendsto endParameter (𝓝 (1 / 2)) (𝓝 (endParameter (1 / 2))) := by
    apply ContinuousAt.tendsto
    unfold endParameter
    exact ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt).div
      (continuous_id.mul (continuous_const.sub continuous_id)).continuousAt (by norm_num)
  have h0 : endParameter (1 / 2) = 0 := by norm_num [endParameter]
  rw [h0] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

/-- (8), right end: `I(C) → 0`. -/
theorem scalarI_tendsto_right : Tendsto scalarI (𝓝[<] (1 / 2)) (𝓝 0) := by
  have hup : Tendsto (fun C => 2 * endParameter C) (𝓝[<] (1 / 2)) (𝓝 0) := by
    simpa using endParameter_tendsto_right.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [Ioo_mem_nhdsLT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with C hC
    exact (scalarI_pos hC).le
  · filter_upwards [Ioo_mem_nhdsLT (show (9 / 20 : ℝ) < 1 / 2 by norm_num)] with C hC
    have hC' : C ∈ Ioo (1 / 4 : ℝ) (1 / 2) := ⟨by linarith [hC.1], hC.2⟩
    exact scalarI_le_two_endParameter hC' (endParameter_le_of_near_half hC' hC.1.le)

/-- (8), right end: `S(C) → 1`. -/
theorem optimalValue_tendsto_right : Tendsto optimalValue (𝓝[<] (1 / 2)) (𝓝 1) := by
  have h : Tendsto (fun C => C * (2 + scalarI C)) (𝓝[<] (1 / 2)) (𝓝 ((1 / 2) * (2 + 0))) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul (tendsto_const_nhds.add scalarI_tendsto_right)
  norm_num at h
  exact h

/-- (8), right end: `τ(C) → ∞`. -/
theorem initialState_tendsto_right : Tendsto initialState (𝓝[<] (1 / 2)) atTop := by
  have hu : Tendsto (fun C : ℝ => (1 - 2 * C)⁻¹) (𝓝[<] (1 / 2)) atTop := by
    have h1 : Tendsto (fun C : ℝ => 1 - 2 * C) (𝓝[<] (1 / 2)) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have : Tendsto (fun C : ℝ => 1 - 2 * C) (𝓝 (1 / 2)) (𝓝 (1 - 2 * (1 / 2))) :=
          (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.tendsto
        norm_num at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      · filter_upwards [self_mem_nhdsWithin] with C hC
        show 0 < 1 - 2 * C
        have : C < 1 / 2 := hC
        linarith
    exact tendsto_inv_nhdsGT_zero.comp h1
  have hlow : Tendsto (fun C : ℝ => (1 - 2 * C)⁻¹ * (1 / 16)) (𝓝[<] (1 / 2)) atTop :=
    hu.atTop_mul_const (by norm_num)
  apply tendsto_atTop_mono' _ _ hlow
  filter_upwards [Ioo_mem_nhdsLT (show (9 / 20 : ℝ) < 1 / 2 by norm_num)] with C hC
  have hC' : C ∈ Ioo (1 / 4 : ℝ) (1 / 2) := ⟨by linarith [hC.1], hC.2⟩
  have hy := endParameter_le_of_near_half hC' hC.1.le
  have hI := scalarI_le_two_endParameter hC' hy
  have hI0 := scalarI_pos hC'
  have h2 : 0 < 1 - 2 * C := by linarith [hC.2]
  have he : 1 / 2 ≤ Real.exp (-scalarI C / 2) := by
    have := Real.add_one_le_exp (-scalarI C / 2)
    have hy' : scalarI C ≤ 1 := by linarith
    linarith
  have hinv : 0 < (1 - 2 * C)⁻¹ := inv_pos.mpr h2
  have key : initialState C = (1 - 2 * C)⁻¹ * (C ^ 2 * Real.exp (-scalarI C / 2)) := by
    unfold initialState scalarI
    ring
  rw [key]
  apply mul_le_mul_of_nonneg_left _ hinv.le
  have hC2 : 81 / 400 ≤ C ^ 2 := by nlinarith [hC.1]
  nlinarith

/-- `κ(C) → 0` as `C ↓ 1/4`. -/
theorem kappaOf_tendsto_left : Tendsto kappaOf (𝓝[>] (1 / 4)) (𝓝 0) := by
  -- `τ S → 0` because `τ ≤ c e^{-I/2}` and `S ≤ 2 + I`
  have hxe : Tendsto (fun C => (2 + scalarI C) * Real.exp (-scalarI C / 2)) (𝓝[>] (1 / 4)) (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => (2 + x) * Real.exp (-x / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => x * Real.exp (-x / 2)) atTop (𝓝 0) := by
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          (tendsto_id.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
        have h2 := this.const_mul 2
        simp only [mul_zero] at h2
        apply h2.congr
        intro x
        simp only [Function.comp_apply, pow_one, id_eq]
        ring_nf
      have h3 : Tendsto (fun x : ℝ => 2 * Real.exp (-x / 2)) atTop (𝓝 0) := by
        have : Tendsto (fun x : ℝ => -x / 2) atTop atBot := by
          refine (tendsto_neg_atTop_atBot.comp
            (tendsto_id.atTop_div_const (show (0 : ℝ) < 2 by norm_num))).congr ?_
          intro x
          simp [Function.comp, neg_div]
        simpa using (Real.tendsto_exp_atBot.comp this).const_mul 2
      have := h3.add h1
      simp only [add_zero] at this
      apply this.congr
      intro x
      ring
    exact hbase.comp scalarI_tendsto_left
  have hpre : ∀ᶠ C in 𝓝[>] (1 / 4 : ℝ), 0 ≤ kappaOf C ∧
      kappaOf C ≤ 4 * ((2 + scalarI C) * Real.exp (-scalarI C / 2)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 3 / 10 by norm_num)] with C hC
    have hC' : C ∈ Ioo (1 / 4 : ℝ) (1 / 2) := ⟨hC.1, by linarith [hC.2]⟩
    have hk := kappaOf_pos hC'
    refine ⟨hk.le, ?_⟩
    have hI := scalarI_pos hC'
    have h2 : 2 / 5 < 1 - 2 * C := by linarith [hC.2]
    have he := Real.exp_pos (-scalarI C / 2)
    unfold kappaOf initialState optimalValue
    change C ^ 2 / (1 - 2 * C) * Real.exp (-scalarI C / 2) *
      (C * (2 + scalarI C) + (1 - 2 * C)) / (1 - 2 * C) ≤
        4 * ((2 + scalarI C) * Real.exp (-scalarI C / 2))
    have hu : 0 < 1 - 2 * C := by linarith
    rw [div_le_iff₀ hu, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hu]
    have hC2 : C ^ 2 ≤ 9 / 100 := by nlinarith [hC.1, hC.2]
    have hA : C * (2 + scalarI C) + (1 - 2 * C) ≤ (2 + scalarI C) := by nlinarith [hC.1, hC.2]
    have hA0 : 0 ≤ C * (2 + scalarI C) + (1 - 2 * C) := by nlinarith [hC.1]
    have key : C ^ 2 * Real.exp (-scalarI C / 2) * (C * (2 + scalarI C) + (1 - 2 * C)) ≤
        9 / 100 * Real.exp (-scalarI C / 2) * (2 + scalarI C) := by
      have := mul_le_mul (mul_le_mul_of_nonneg_right hC2 he.le) hA hA0 (by positivity)
      linarith
    have hsq : 4 / 25 ≤ (1 - 2 * C) * (1 - 2 * C) := by nlinarith
    have hpos : 0 < (2 + scalarI C) * Real.exp (-scalarI C / 2) :=
      mul_pos (by linarith) he
    have := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hpos.le)
    nlinarith
  have hup : Tendsto (fun C => 4 * ((2 + scalarI C) * Real.exp (-scalarI C / 2))) (𝓝[>] (1 / 4)) (𝓝 0) := by
    simpa using hxe.const_mul 4
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (hpre.mono fun _ h => h.1) (hpre.mono fun _ h => h.2)

/-- `κ(C) → ∞` as `C ↑ 1/2`. -/
theorem kappaOf_tendsto_right : Tendsto kappaOf (𝓝[<] (1 / 2)) atTop := by
  apply tendsto_atTop_mono' _ _ initialState_tendsto_right
  filter_upwards [Ioo_mem_nhdsLT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with C hC
  have hτ := initialState_pos hC
  have hS : 0 < optimalValue C := by linarith [one_lt_optimalValue hC]
  have h2 : 0 < 1 - 2 * C := by linarith [hC.2]
  unfold kappaOf
  rw [le_div_iff₀ h2]
  nlinarith

end Ends

section Bijections

/-- Every ratio `β ∈ (0, 1)` is `1/S(C)` for exactly one `C ∈ (1/4, 1/2)`. -/
theorem existsUnique_optimalValue_eq {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃! C : ℝ, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ optimalValue C = β⁻¹ := by
  have hb : 1 < β⁻¹ := (one_lt_inv₀ hβ.1).mpr hβ.2
  obtain ⟨a, hSa, ha⟩ := ((optimalValue_tendsto_left.eventually_gt_atTop β⁻¹).and
    (Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 1 / 2 by norm_num))).exists
  obtain ⟨b, hSb, hb'⟩ := ((optimalValue_tendsto_right.eventually (gt_mem_nhds hb)).and
    (Ioo_mem_nhdsLT (show (1 / 4 : ℝ) < 1 / 2 by norm_num))).exists
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    have := optimalValue_strictAntiOn hb' ha h
    linarith
  have hsub : Icc a b ⊆ Ioo (1 / 4 : ℝ) (1 / 2) := fun x hx =>
    ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb'.2⟩
  obtain ⟨C, hC, hSC⟩ := intermediate_value_Icc' hab (optimalValue_continuousOn.mono hsub)
    ⟨hSb.le, hSa.le⟩
  refine ⟨C, ⟨hsub hC, hSC⟩, ?_⟩
  rintro C' ⟨hC', hSC'⟩
  exact optimalValue_strictAntiOn.injOn hC' (hsub hC) (hSC'.trans hSC.symm)

/-- `κ` maps `(1/4, 1/2)` onto `(0, ∞)`. -/
theorem existsUnique_kappaOf_eq {κ : ℝ} (hκ : 0 < κ) :
    ∃! C : ℝ, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ kappaOf C = κ := by
  obtain ⟨a, hka, ha⟩ := ((kappaOf_tendsto_left.eventually (gt_mem_nhds hκ)).and
    (Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 1 / 2 by norm_num))).exists
  obtain ⟨b, hkb, hb⟩ := ((kappaOf_tendsto_right.eventually_gt_atTop κ).and
    (Ioo_mem_nhdsLT (show (1 / 4 : ℝ) < 1 / 2 by norm_num))).exists
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    have := kappaOf_strictMonoOn hb ha h
    linarith
  have hsub : Icc a b ⊆ Ioo (1 / 4 : ℝ) (1 / 2) := fun x hx =>
    ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  obtain ⟨C, hC, hkC⟩ := intermediate_value_Icc hab (kappaOf_continuousOn.mono hsub)
    ⟨hka.le, hkb.le⟩
  refine ⟨C, ⟨hsub hC, hkC⟩, ?_⟩
  rintro C' ⟨hC', hkC'⟩
  exact kappaOf_strictMonoOn.injOn hC' (hsub hC) (hkC'.trans hkC.symm)

end Bijections

end FixedPrice
