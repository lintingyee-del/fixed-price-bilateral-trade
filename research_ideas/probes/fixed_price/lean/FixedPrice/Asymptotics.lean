import FixedPrice.FrontierConvex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Corollary B' (endpoint asymptotics (55)):
`δ(β) ~ (e/8) β e^{-2/β}` as `β ↓ 0`, `δ(β) ~ 1/(4(1 - β))` as `β ↑ 1`,
`ρ(κ) ~ 2/log(1/κ)` as `κ ↓ 0`, and `1 - ρ(κ) ~ 1/√κ` as `κ → ∞`.
The analytic inputs are `(C - 1/4) I(C) → 0` as `C ↓ 1/4`, from the bound
`I(C) ≤ 4 + 2π/√(C - 1/4)`, and `I(C)/y_e(C) → 1` as `C ↑ 1/2`. -/

noncomputable section

open Set MeasureTheory Filter Function Asymptotics
open scoped Interval Topology

namespace FixedPrice

section Analytic

/-- `I(C) ≤ 4 + 2π/√(C - 1/4)` near `C = 1/4`. -/
theorem scalarI_le_left {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (29 / 100)) :
    scalarI C ≤ 4 + 2 * Real.pi / Real.sqrt (C - 1 / 4) := by
  set ε := C - 1 / 4 with hε
  have hε0 : 0 < ε := by linarith [hC.1]
  set q := Real.sqrt ε with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hε0
  have hqq : q ^ 2 = ε := Real.sq_sqrt hε0.le
  have hC' : C ∈ Ioo (1 / 4 : ℝ) (1 / 2) := ⟨hC.1, by linarith [hC.2]⟩
  have hC0 : 0 < C := by linarith [hC.1]
  have hC1 : 0 < 1 - C := by linarith [hC.2]
  have hye1 : (1 : ℝ) ≤ endParameter C := by
    unfold endParameter
    rw [le_div_iff₀ (mul_pos hC0 hC1)]
    nlinarith [hC.2]
  have hcont : Continuous (fun r => (denominator C r)⁻¹) :=
    (continuous_denominator C).inv₀ (fun r => ne_of_gt (denominator_pos hC'.1 r))
  have hi := fun a b => hcont.intervalIntegrable (μ := volume) a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 (endParameter C))
  have hfirst : (∫ r in (0 : ℝ)..1, (denominator C r)⁻¹) ≤ 4 := by
    have hle : (∫ r in (0 : ℝ)..1, (denominator C r)⁻¹) ≤ ∫ _r in (0 : ℝ)..1, (4 : ℝ) := by
      apply intervalIntegral.integral_mono_on zero_le_one (hi _ _) intervalIntegrable_const
      intro r hr
      have hD := denominator_pos hC'.1 r
      rw [inv_le_comm₀ hD (by norm_num), denominator_eq_square]
      have h1 : 1 / 4 ≤ (1 - r / 2) ^ 2 := by nlinarith [hr.1, hr.2]
      have h2 : 0 ≤ (C - 1 / 4) * r ^ 2 := mul_nonneg hε0.le (sq_nonneg r)
      linarith
    simpa using hle
  -- the arctan primitive of `1/((1 - r/2)² + ε)`
  set F : ℝ → ℝ := fun r => -(2 / q) * Real.arctan ((1 - r / 2) / q) with hF
  have hFder : ∀ r, HasDerivAt F (((1 - r / 2) ^ 2 + ε)⁻¹) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => (1 - r / 2) / q) (-(1 / 2) / q) r := by
      have := (((hasDerivAt_id r).div_const 2).const_sub 1).div_const q
      simpa using this
    have h2 := (Real.hasDerivAt_arctan ((1 - r / 2) / q)).comp r h1
    have h3 := h2.const_mul (-(2 / q))
    convert h3 using 1
    field_simp
    rw [hqq]
    ring
  have hsecond : (∫ r in (1 : ℝ)..endParameter C, (denominator C r)⁻¹) ≤ 2 * Real.pi / q := by
    have hle : (∫ r in (1 : ℝ)..endParameter C, (denominator C r)⁻¹) ≤
        ∫ r in (1 : ℝ)..endParameter C, ((1 - r / 2) ^ 2 + ε)⁻¹ := by
      apply intervalIntegral.integral_mono_on hye1 (hi _ _)
      · exact (Continuous.intervalIntegrable (by
          exact ((continuous_const.sub (continuous_id.div_const 2)).pow 2 |>.add continuous_const).inv₀
            (fun r => (add_pos_of_nonneg_of_pos (sq_nonneg _) hε0).ne')) _ _)
      intro r hr
      apply inv_anti₀ (add_pos_of_nonneg_of_pos (sq_nonneg _) hε0)
      rw [denominator_eq_square]
      have : ε ≤ (C - 1 / 4) * r ^ 2 := by
        have : (1 : ℝ) ≤ r ^ 2 := by nlinarith [hr.1]
        nlinarith
      linarith
    have hval : (∫ r in (1 : ℝ)..endParameter C, ((1 - r / 2) ^ 2 + ε)⁻¹) =
        F (endParameter C) - F 1 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hFder r)
        (Continuous.intervalIntegrable (by
          exact ((continuous_const.sub (continuous_id.div_const 2)).pow 2 |>.add continuous_const).inv₀
            (fun r => (add_pos_of_nonneg_of_pos (sq_nonneg _) hε0).ne')) _ _)
    have hbound : F (endParameter C) - F 1 ≤ 2 * Real.pi / q := by
      simp only [hF]
      have a1 := Real.arctan_lt_pi_div_two ((1 - 1 / 2) / q)
      have a2 := Real.neg_pi_div_two_lt_arctan ((1 - endParameter C / 2) / q)
      have hq2 : 0 < 2 / q := by positivity
      have : -(2 / q) * Real.arctan ((1 - endParameter C / 2) / q) -
          -(2 / q) * Real.arctan ((1 - 1 / 2) / q) =
          2 / q * (Real.arctan ((1 - 1 / 2) / q) - Real.arctan ((1 - endParameter C / 2) / q)) := by
        ring
      rw [this]
      have : Real.arctan ((1 - 1 / 2) / q) - Real.arctan ((1 - endParameter C / 2) / q) ≤ Real.pi := by
        linarith
      calc 2 / q * (Real.arctan ((1 - 1 / 2) / q) - Real.arctan ((1 - endParameter C / 2) / q))
          ≤ 2 / q * Real.pi := mul_le_mul_of_nonneg_left this hq2.le
        _ = 2 * Real.pi / q := by ring
    linarith
  unfold scalarI primitive
  linarith

/-- `(C - 1/4) I(C) → 0` as `C ↓ 1/4`. -/
theorem tendsto_eps_mul_scalarI :
    Tendsto (fun C => (C - 1 / 4) * scalarI C) (𝓝[>] (1 / 4)) (𝓝 0) := by
  have hε : Tendsto (fun C : ℝ => C - 1 / 4) (𝓝[>] (1 / 4)) (𝓝 0) := by
    have : Tendsto (fun C : ℝ => C - 1 / 4) (𝓝 (1 / 4)) (𝓝 (1 / 4 - 1 / 4)) :=
      tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hsq : Tendsto (fun C : ℝ => Real.sqrt (C - 1 / 4)) (𝓝[>] (1 / 4)) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hε
    simpa using this
  have hup : Tendsto (fun C : ℝ => 4 * (C - 1 / 4) + 2 * Real.pi * Real.sqrt (C - 1 / 4))
      (𝓝[>] (1 / 4)) (𝓝 0) := by
    simpa using (hε.const_mul 4).add (hsq.const_mul (2 * Real.pi))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with C hC
    exact mul_nonneg (by linarith [hC.1]) (scalarI_pos hC).le
  · filter_upwards [Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 29 / 100 by norm_num)] with C hC
    have h := scalarI_le_left hC
    have hε0 : 0 < C - 1 / 4 := by linarith [hC.1]
    have hsq0 : 0 < Real.sqrt (C - 1 / 4) := Real.sqrt_pos.mpr hε0
    have hsqq : Real.sqrt (C - 1 / 4) ^ 2 = C - 1 / 4 := Real.sq_sqrt hε0.le
    calc (C - 1 / 4) * scalarI C ≤ (C - 1 / 4) * (4 + 2 * Real.pi / Real.sqrt (C - 1 / 4)) :=
          mul_le_mul_of_nonneg_left h hε0.le
      _ = 4 * (C - 1 / 4) + 2 * Real.pi * ((C - 1 / 4) / Real.sqrt (C - 1 / 4)) := by ring
      _ = 4 * (C - 1 / 4) + 2 * Real.pi * Real.sqrt (C - 1 / 4) := by rw [Real.div_sqrt]

/-- `I(C)/y_e(C) → 1` as `C ↑ 1/2`. -/
theorem tendsto_scalarI_div_endParameter :
    Tendsto (fun C => scalarI C / endParameter C) (𝓝[<] (1 / 2)) (𝓝 1) := by
  have hy := endParameter_tendsto_right
  have hlow : Tendsto (fun C => 1 / (1 + endParameter C ^ 2)) (𝓝[<] (1 / 2)) (𝓝 1) := by
    have h1 : Tendsto (fun C => 1 + endParameter C ^ 2) (𝓝[<] (1 / 2)) (𝓝 (1 + 0 ^ 2)) :=
      tendsto_const_nhds.add (hy.pow 2)
    have := h1.inv₀ (by norm_num)
    simpa [one_div] using this
  have hup : Tendsto (fun C => 1 / (1 - endParameter C)) (𝓝[<] (1 / 2)) (𝓝 1) := by
    have h1 : Tendsto (fun C => 1 - endParameter C) (𝓝[<] (1 / 2)) (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hy
    have := h1.inv₀ (by norm_num)
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
  · filter_upwards [Ioo_mem_nhdsLT (show (9 / 20 : ℝ) < 1 / 2 by norm_num)] with C hC
    have hC' : C ∈ Ioo (1 / 4 : ℝ) (1 / 2) := ⟨by linarith [hC.1], hC.2⟩
    have hye := endParameter_pos hC'
    have hyh := endParameter_le_of_near_half hC' hC.1.le
    have hcont : Continuous (fun r => (denominator C r)⁻¹) :=
      (continuous_denominator C).inv₀ (fun r => ne_of_gt (denominator_pos hC'.1 r))
    have hle : ∫ _r in (0 : ℝ)..endParameter C, (1 + endParameter C ^ 2)⁻¹ ≤
        ∫ r in (0 : ℝ)..endParameter C, (denominator C r)⁻¹ := by
      apply intervalIntegral.integral_mono_on hye.le intervalIntegrable_const
        (hcont.intervalIntegrable _ _)
      intro r hr
      apply inv_anti₀ (denominator_pos hC'.1 r)
      unfold denominator
      have : C * r ^ 2 ≤ endParameter C ^ 2 := by
        have h1 : r ^ 2 ≤ endParameter C ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
        nlinarith [hC.2, sq_nonneg r]
      linarith [hr.1]
    rw [le_div_iff₀ hye]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
    unfold scalarI primitive
    calc 1 / (1 + endParameter C ^ 2) * endParameter C =
          endParameter C * (1 + endParameter C ^ 2)⁻¹ := by ring
      _ ≤ _ := hle
  · filter_upwards [Ioo_mem_nhdsLT (show (9 / 20 : ℝ) < 1 / 2 by norm_num)] with C hC
    have hC' : C ∈ Ioo (1 / 4 : ℝ) (1 / 2) := ⟨by linarith [hC.1], hC.2⟩
    have hye := endParameter_pos hC'
    have hyh := endParameter_le_of_near_half hC' hC.1.le
    have hcont : Continuous (fun r => (denominator C r)⁻¹) :=
      (continuous_denominator C).inv₀ (fun r => ne_of_gt (denominator_pos hC'.1 r))
    have hle : ∫ r in (0 : ℝ)..endParameter C, (denominator C r)⁻¹ ≤
        ∫ _r in (0 : ℝ)..endParameter C, (1 - endParameter C)⁻¹ := by
      apply intervalIntegral.integral_mono_on hye.le (hcont.intervalIntegrable _ _)
        intervalIntegrable_const
      intro r hr
      apply inv_anti₀ (by linarith)
      unfold denominator
      nlinarith [hr.2, hC.1, sq_nonneg r]
    rw [div_le_iff₀ hye]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
    unfold scalarI primitive
    calc _ ≤ endParameter C * (1 - endParameter C)⁻¹ := hle
      _ = 1 / (1 - endParameter C) * endParameter C := by ring

end Analytic

section Inverses

/-- `C(β) ↓ 1/4` as `β ↓ 0`. -/
theorem tendsto_curvatureOf_zero : Tendsto curvatureOf (𝓝[>] 0) (𝓝[>] (1 / 4)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with β hβ
      exact lt_trans ha (curvatureOf_spec hβ).1.1
    · intro a ha
      set C₁ := min a (3 / 8) with hC₁
      have hC₁m : C₁ ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
        ⟨lt_min ha (by norm_num), by linarith [min_le_right a (3 / 8 : ℝ)]⟩
      have hβ₁ := inv_optimalValue_mem hC₁m
      filter_upwards [Ioo_mem_nhdsGT hβ₁.1] with β hβ
      have hβ' : β ∈ Ioo (0 : ℝ) 1 := ⟨hβ.1, hβ.2.trans hβ₁.2⟩
      have := curvatureOf_strictMonoOn hβ' hβ₁ hβ.2
      rw [curvatureOf_inv_optimalValue hC₁m] at this
      exact lt_of_lt_of_le this (min_le_left _ _)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with β hβ
    exact (curvatureOf_spec hβ).1.1

/-- `C(β) ↑ 1/2` as `β ↑ 1`. -/
theorem tendsto_curvatureOf_one : Tendsto curvatureOf (𝓝[<] 1) (𝓝[<] (1 / 2)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [tendsto_order]
    constructor
    · intro a ha
      set C₁ := max a (3 / 8) with hC₁
      have hC₁m : C₁ ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
        ⟨by linarith [le_max_right a (3 / 8 : ℝ)], max_lt ha (by norm_num)⟩
      have hβ₁ := inv_optimalValue_mem hC₁m
      filter_upwards [Ioo_mem_nhdsLT hβ₁.2] with β hβ
      have hβ' : β ∈ Ioo (0 : ℝ) 1 := ⟨hβ₁.1.trans hβ.1, hβ.2⟩
      have := curvatureOf_strictMonoOn hβ₁ hβ' hβ.1
      rw [curvatureOf_inv_optimalValue hC₁m] at this
      exact lt_of_le_of_lt (le_max_left _ _) this
    · intro a ha
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with β hβ
      exact lt_trans (curvatureOf_spec hβ).1.2 ha
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with β hβ
    exact (curvatureOf_spec hβ).1.2

/-- The curvature `C(κ)` with `κ(C(κ)) = κ`. -/
def curvatureOfKappa (κ : ℝ) : ℝ :=
  if h : 0 < κ then (existsUnique_kappaOf_eq h).exists.choose else 1 / 3

theorem curvatureOfKappa_spec {κ : ℝ} (hκ : 0 < κ) :
    curvatureOfKappa κ ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ kappaOf (curvatureOfKappa κ) = κ := by
  unfold curvatureOfKappa
  rw [dif_pos hκ]
  exact (existsUnique_kappaOf_eq hκ).exists.choose_spec

theorem curvatureOfKappa_kappaOf {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    curvatureOfKappa (kappaOf C) = C :=
  (existsUnique_kappaOf_eq (kappaOf_pos hC)).unique
    (curvatureOfKappa_spec (kappaOf_pos hC)) ⟨hC, rfl⟩

theorem curvatureOfKappa_lt {κ₁ κ₂ : ℝ} (h₁ : 0 < κ₁) (h12 : κ₁ < κ₂) :
    curvatureOfKappa κ₁ < curvatureOfKappa κ₂ := by
  have hA := curvatureOfKappa_spec h₁
  have hB := curvatureOfKappa_spec (h₁.trans h12)
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with h | h
  · have := hA.2
    rw [← h, hB.2] at this
    linarith
  · have := kappaOf_strictMonoOn hB.1 hA.1 h
    rw [hA.2, hB.2] at this
    linarith

/-- `C(κ) ↓ 1/4` as `κ ↓ 0`. -/
theorem tendsto_curvatureOfKappa_zero : Tendsto curvatureOfKappa (𝓝[>] 0) (𝓝[>] (1 / 4)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with κ hκ
      exact lt_trans ha (curvatureOfKappa_spec hκ).1.1
    · intro a ha
      set C₁ := min a (3 / 8) with hC₁
      have hC₁m : C₁ ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
        ⟨lt_min ha (by norm_num), by linarith [min_le_right a (3 / 8 : ℝ)]⟩
      have hk := kappaOf_pos hC₁m
      filter_upwards [Ioo_mem_nhdsGT hk] with κ hκ
      have := curvatureOfKappa_lt hκ.1 hκ.2
      rw [curvatureOfKappa_kappaOf hC₁m] at this
      exact lt_of_lt_of_le this (min_le_left _ _)
  · filter_upwards [self_mem_nhdsWithin] with κ hκ
    exact (curvatureOfKappa_spec hκ).1.1

/-- `C(κ) ↑ 1/2` as `κ → ∞`. -/
theorem tendsto_curvatureOfKappa_top : Tendsto curvatureOfKappa atTop (𝓝[<] (1 / 2)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [tendsto_order]
    constructor
    · intro a ha
      set C₁ := max a (3 / 8) with hC₁
      have hC₁m : C₁ ∈ Ioo (1 / 4 : ℝ) (1 / 2) :=
        ⟨by linarith [le_max_right a (3 / 8 : ℝ)], max_lt ha (by norm_num)⟩
      have hk := kappaOf_pos hC₁m
      filter_upwards [eventually_gt_atTop (kappaOf C₁)] with κ hκ
      have := curvatureOfKappa_lt hk hκ
      rw [curvatureOfKappa_kappaOf hC₁m] at this
      exact lt_of_le_of_lt (le_max_left _ _) this
    · intro a ha
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
      exact lt_trans (curvatureOfKappa_spec hκ).1.2 ha
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
    exact (curvatureOfKappa_spec hκ).1.2

theorem condRatio_eq' {κ : ℝ} (hκ : 0 < κ) :
    condRatio κ = (1 + curvatureOfKappa κ * scalarI (curvatureOfKappa κ))⁻¹ := by
  have h := curvatureOfKappa_spec hκ
  have := condRatio_eq h.1
  rwa [h.2] at this

end Inverses

section Limits

theorem tendsto_left_self : Tendsto (fun C : ℝ => C) (𝓝[>] (1 / 4)) (𝓝 (1 / 4)) :=
  tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

theorem tendsto_right_self : Tendsto (fun C : ℝ => C) (𝓝[<] (1 / 2)) (𝓝 (1 / 2)) :=
  tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

/-- The small-`β` ratio, as a function of the curvature, tends to one. -/
theorem tendsto_smallGains_ratio :
    Tendsto (fun C => 8 * C ^ 2 / (1 - 2 * C) * Real.exp ((4 * C - 1) * (1 + scalarI C / 2)))
      (𝓝[>] (1 / 4)) (𝓝 1) := by
  have hC := tendsto_left_self
  have harg : Tendsto (fun C => (4 * C - 1) * (1 + scalarI C / 2)) (𝓝[>] (1 / 4)) (𝓝 0) := by
    have h1 : Tendsto (fun C : ℝ => 4 * (C - 1 / 4)) (𝓝[>] (1 / 4)) (𝓝 (4 * (1 / 4 - 1 / 4))) :=
      (hC.sub tendsto_const_nhds).const_mul 4
    have h2 := (tendsto_eps_mul_scalarI.const_mul 2)
    simp only [sub_self, mul_zero] at h1 h2
    have := h1.add h2
    simp only [add_zero] at this
    apply this.congr
    intro C
    ring
  have hpre : Tendsto (fun C : ℝ => 8 * C ^ 2 / (1 - 2 * C)) (𝓝[>] (1 / 4))
      (𝓝 (8 * (1 / 4) ^ 2 / (1 - 2 * (1 / 4)))) :=
    ((hC.pow 2).const_mul 8).div (tendsto_const_nhds.sub (hC.const_mul 2)) (by norm_num)
  have := hpre.mul (Real.continuous_exp.continuousAt.tendsto.comp harg)
  norm_num at this
  exact this

/-- The large-`β` ratio `4 τ (S - 1)/S²`, in a form with `I/y_e`, tends to one. -/
theorem tendsto_largeGains_ratio :
    Tendsto (fun C => 4 * C ^ 2 * Real.exp (-scalarI C / 2) *
      ((scalarI C / endParameter C) / (1 - C) - 1) / optimalValue C ^ 2) (𝓝[<] (1 / 2)) (𝓝 1) := by
  have hC := tendsto_right_self
  have hI := scalarI_tendsto_right
  have hr := tendsto_scalarI_div_endParameter
  have hS := optimalValue_tendsto_right
  have he : Tendsto (fun C => Real.exp (-scalarI C / 2)) (𝓝[<] (1 / 2)) (𝓝 (Real.exp (-0 / 2))) :=
    Real.continuous_exp.continuousAt.tendsto.comp ((hI.neg).div_const 2)
  have h1C : Tendsto (fun C : ℝ => 1 - C) (𝓝[<] (1 / 2)) (𝓝 (1 - 1 / 2)) :=
    tendsto_const_nhds.sub hC
  have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] (1 / 2)) (𝓝 1) := tendsto_const_nhds
  have := ((((hC.pow 2).const_mul 4).mul he).mul
    ((hr.div h1C (by norm_num)).sub h1)).div (hS.pow 2) (by norm_num)
  norm_num at this
  exact this

theorem tendsto_largeGains_ratio' :
    Tendsto (fun C => 4 * initialState C * (optimalValue C - 1) / optimalValue C ^ 2)
      (𝓝[<] (1 / 2)) (𝓝 1) := by
  apply tendsto_largeGains_ratio.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with C hC
  have hy := endParameter_pos hC
  have hC0 : C ≠ 0 := ne_of_gt (by linarith [hC.1])
  have hC1 : 1 - C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have h2 : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2])
  have h2' : 1 - C * 2 ≠ 0 := by rwa [mul_comm]
  unfold initialState optimalValue scalarI endParameter
  field_simp
  ring

/-- The small-`κ` ratio `log(1/κ)/(2(1 + C I))` tends to one. -/
theorem tendsto_smallKappa_ratio :
    Tendsto (fun C => (scalarI C / 2 - 2 * Real.log C + 2 * Real.log (1 - 2 * C) -
      Real.log (1 + C * scalarI C)) / (2 * (1 + C * scalarI C))) (𝓝[>] (1 / 4)) (𝓝 1) := by
  have hC := tendsto_left_self
  have hI := scalarI_tendsto_left
  have hCI : Tendsto (fun C => 1 + C * scalarI C) (𝓝[>] (1 / 4)) atTop := by
    apply tendsto_atTop_add_const_left
    apply tendsto_atTop_mono' _ _ (hI.atTop_div_const (show (0 : ℝ) < 4 by norm_num))
    filter_upwards [Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with C hC'
    have := scalarI_pos hC'
    nlinarith [hC'.1]
  have hinvI : Tendsto (fun C => (scalarI C)⁻¹) (𝓝[>] (1 / 4)) (𝓝 0) := hI.inv_tendsto_atTop
  have h1 : Tendsto (fun C => (4 * ((scalarI C)⁻¹ + C))⁻¹) (𝓝[>] (1 / 4))
      (𝓝 (4 * (0 + 1 / 4))⁻¹) :=
    ((hinvI.add hC).const_mul 4).inv₀ (by norm_num)
  norm_num at h1
  have hlogs : Tendsto (fun C => -2 * Real.log C + 2 * Real.log (1 - 2 * C)) (𝓝[>] (1 / 4))
      (𝓝 (-2 * Real.log (1 / 4) + 2 * Real.log (1 - 2 * (1 / 4)))) :=
    (((Real.continuousAt_log (by norm_num)).tendsto.comp hC).const_mul (-2)).add
      (((Real.continuousAt_log (by norm_num)).tendsto.comp
        (tendsto_const_nhds.sub (hC.const_mul 2))).const_mul 2)
  have h2 := hlogs.div_atTop (hCI.atTop_mul_const (show (0 : ℝ) < 2 by norm_num))
  have h3 : Tendsto (fun C => Real.log (1 + C * scalarI C) / (2 * (1 + C * scalarI C)))
      (𝓝[>] (1 / 4)) (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 (by norm_num)).comp hCI
    simpa [Function.comp] using this
  have := (h1.add h2).sub h3
  simp only [add_zero, sub_zero] at this
  apply this.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (1 / 4 : ℝ) < 1 / 2 by norm_num)] with C hC'
  have hI0 := (scalarI_pos hC').ne'
  have hC0 : C ≠ 0 := ne_of_gt (by linarith [hC'.1])
  have hpos : 1 + C * scalarI C ≠ 0 := by
    have := mul_pos (show (0 : ℝ) < C by linarith [hC'.1]) (scalarI_pos hC')
    linarith
  have h4 : (scalarI C)⁻¹ + C ≠ 0 := by
    have := inv_pos.mpr (scalarI_pos hC')
    linarith [hC'.1]
  field_simp
  ring

/-- The large-`κ` quantity `(1 - ρ)² κ`, in a form with `I/y_e`, tends to one. -/
theorem tendsto_largeKappa_ratio :
    Tendsto (fun C => (scalarI C / endParameter C) ^ 2 / (1 - C) ^ 2 *
      (C ^ 2 * Real.exp (-scalarI C / 2)) * (optimalValue C + (1 - 2 * C)) /
        (1 + C * scalarI C) ^ 2) (𝓝[<] (1 / 2)) (𝓝 1) := by
  have hC := tendsto_right_self
  have hI := scalarI_tendsto_right
  have hr := tendsto_scalarI_div_endParameter
  have hS := optimalValue_tendsto_right
  have he : Tendsto (fun C => Real.exp (-scalarI C / 2)) (𝓝[<] (1 / 2)) (𝓝 (Real.exp (-0 / 2))) :=
    Real.continuous_exp.continuousAt.tendsto.comp ((hI.neg).div_const 2)
  have h1C : Tendsto (fun C : ℝ => 1 - C) (𝓝[<] (1 / 2)) (𝓝 (1 - 1 / 2)) :=
    tendsto_const_nhds.sub hC
  have hu : Tendsto (fun C : ℝ => 1 - 2 * C) (𝓝[<] (1 / 2)) (𝓝 (1 - 2 * (1 / 2))) :=
    tendsto_const_nhds.sub (hC.const_mul 2)
  have hCI : Tendsto (fun C : ℝ => 1 + C * scalarI C) (𝓝[<] (1 / 2)) (𝓝 (1 + 1 / 2 * 0)) :=
    tendsto_const_nhds.add (hC.mul hI)
  have := ((((hr.pow 2).div (h1C.pow 2) (by norm_num)).mul
    ((hC.pow 2).mul he)).mul (hS.add hu)).div (hCI.pow 2) (by norm_num)
  norm_num at this
  exact this

end Limits

section Corollary

/-- **Corollary B', (55).** `δ(β) ~ (e/8) β e^{-2/β}` as `β ↓ 0`. -/
theorem frontierDelta_isEquivalent_zero :
    frontierDelta ~[𝓝[>] 0] fun β => Real.exp 1 / 8 * β * Real.exp (-2 / β) := by
  apply isEquivalent_of_tendsto_one
  apply (tendsto_smallGains_ratio.comp tendsto_curvatureOf_zero).congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with β hβ
  obtain ⟨hC, hS⟩ := curvatureOf_spec hβ
  simp only [Function.comp_apply, Pi.div_apply]
  rw [frontierDelta_eq' hβ]
  generalize curvatureOf β = C at hC hS ⊢
  have hβ0 : β ≠ 0 := hβ.1.ne'
  have hβS : β = (optimalValue C)⁻¹ := by rw [hS, inv_inv]
  have hSpos : 0 < optimalValue C := by linarith [one_lt_optimalValue hC]
  have h2 : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2])
  subst hβS
  have hexp : Real.exp ((4 * C - 1) * (1 + scalarI C / 2)) =
      Real.exp (-scalarI C / 2) * Real.exp (2 * optimalValue C) / Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    unfold optimalValue scalarI
    ring
  have h2S : -2 / (optimalValue C)⁻¹ = -(2 * optimalValue C) := by field_simp
  rw [hexp, h2S, Real.exp_neg]
  unfold initialState
  have hE := Real.exp_pos (2 * optimalValue C)
  have hE1 := Real.exp_pos 1
  have hE2 := Real.exp_pos (-primitive C (endParameter C) / 2)
  unfold scalarI
  field_simp

/-- **Corollary B', (55).** `δ(β) ~ 1/(4(1 - β))` as `β ↑ 1`. -/
theorem frontierDelta_isEquivalent_one :
    frontierDelta ~[𝓝[<] 1] fun β => 1 / (4 * (1 - β)) := by
  apply isEquivalent_of_tendsto_one
  apply (tendsto_largeGains_ratio'.comp tendsto_curvatureOf_one).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with β hβ
  obtain ⟨hC, hS⟩ := curvatureOf_spec hβ
  simp only [Function.comp_apply, Pi.div_apply]
  rw [frontierDelta_eq' hβ]
  generalize curvatureOf β = C at hC hS ⊢
  have hβ0 : β ≠ 0 := hβ.1.ne'
  have hβ1 : 1 - β ≠ 0 := ne_of_gt (by linarith [hβ.2])
  rw [hS]
  field_simp

/-- **Corollary B', (55).** `ρ(κ) ~ 2/log(1/κ)` as `κ ↓ 0`. -/
theorem condRatio_isEquivalent_zero :
    condRatio ~[𝓝[>] 0] fun κ => 2 / Real.log (1 / κ) := by
  apply isEquivalent_of_tendsto_one
  apply (tendsto_smallKappa_ratio.comp tendsto_curvatureOfKappa_zero).congr'
  filter_upwards [self_mem_nhdsWithin] with κ hκ
  have hκ0 : 0 < κ := hκ
  obtain ⟨hC, hk⟩ := curvatureOfKappa_spec hκ0
  simp only [Function.comp_apply, Pi.div_apply]
  rw [condRatio_eq' hκ0]
  generalize curvatureOfKappa κ = C at hC hk ⊢
  subst hk
  have hτ := initialState_pos hC
  have hSu := optimalValue_add_u_pos hC
  have hu : 0 < 1 - 2 * C := by linarith [hC.2]
  have hC0 : 0 < C := by linarith [hC.1]
  have hCI : 0 < 1 + C * scalarI C := by
    have := mul_pos hC0 (scalarI_pos hC)
    linarith
  have hlogk : Real.log (1 / kappaOf C) =
      scalarI C / 2 - 2 * Real.log C + 2 * Real.log (1 - 2 * C) -
        Real.log (1 + C * scalarI C) := by
    unfold kappaOf
    rw [optimalValue_add_u, one_div, Real.log_inv, Real.log_div (by positivity) hu.ne',
      Real.log_mul hτ.ne' hCI.ne']
    unfold initialState
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_div (by positivity) hu.ne', Real.log_pow]
    unfold scalarI
    push_cast
    ring
  rw [hlogk]
  field_simp

/-- **Corollary B', (55).** `1 - ρ(κ) ~ 1/√κ` as `κ → ∞`. -/
theorem condRatio_isEquivalent_top :
    (fun κ => 1 - condRatio κ) ~[atTop] fun κ => 1 / Real.sqrt κ := by
  apply isEquivalent_of_tendsto_one
  have hsq := (Real.continuous_sqrt.tendsto 1).comp
    (tendsto_largeKappa_ratio.comp tendsto_curvatureOfKappa_top)
  rw [Real.sqrt_one] at hsq
  apply hsq.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with κ hκ
  obtain ⟨hC, hk⟩ := curvatureOfKappa_spec hκ
  simp only [Function.comp_apply, Pi.div_apply]
  rw [condRatio_eq' hκ]
  generalize curvatureOfKappa κ = C at hC hk ⊢
  subst hk
  have hC0 : 0 < C := by linarith [hC.1]
  have hC1 : 0 < 1 - C := by linarith [hC.2]
  have hu : 0 < 1 - 2 * C := by linarith [hC.2]
  have hI := scalarI_pos hC
  have hy := endParameter_pos hC
  have hpos : 0 < 1 + C * scalarI C := by nlinarith
  have hk0 := kappaOf_pos hC
  have h1ρ : 1 - (1 + C * scalarI C)⁻¹ = C * scalarI C / (1 + C * scalarI C) := by
    field_simp
    ring
  rw [h1ρ, one_div, div_inv_eq_mul]
  have hnn : 0 ≤ C * scalarI C / (1 + C * scalarI C) := by positivity
  rw [← Real.sqrt_sq hnn, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  have hτ : initialState C = C ^ 2 / (1 - 2 * C) * Real.exp (-scalarI C / 2) := rfl
  have hy' : endParameter C = (1 - 2 * C) / (C * (1 - C)) := rfl
  rw [kappaOf, hτ, hy', optimalValue_add_u]
  have hI' := hI
  generalize scalarI C = I at hI' hpos hnn ⊢
  field_simp

end Corollary

end FixedPrice
