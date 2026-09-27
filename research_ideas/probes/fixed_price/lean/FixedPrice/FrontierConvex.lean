import FixedPrice.FrontierConditional
import Mathlib.Analysis.Convex.Deriv

/-! Theorem B, the shape of the frontier: `δ` is strictly increasing and strictly convex on
`(0, 1)`, its derivative at `β = 1/S(C)` is `κ(C)`, which ranges over `(0, ∞)`, and
`κ ρ(κ) = δ*(κ) = sup_{0<β<1} (κ β - δ(β))`, equation (53), with the supremum attained. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- The curvature `C(β)` with `S(C(β)) = 1/β`. -/
def curvatureOf (β : ℝ) : ℝ :=
  if h : β ∈ Ioo (0 : ℝ) 1 then (existsUnique_optimalValue_eq h).exists.choose else 1 / 3

section Curvature

variable {β : ℝ}

theorem curvatureOf_spec (hβ : β ∈ Ioo (0 : ℝ) 1) :
    curvatureOf β ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ optimalValue (curvatureOf β) = β⁻¹ := by
  unfold curvatureOf
  rw [dif_pos hβ]
  exact (existsUnique_optimalValue_eq hβ).exists.choose_spec

theorem curvatureOf_eq {C : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hS : optimalValue C = β⁻¹) : curvatureOf β = C :=
  (existsUnique_optimalValue_eq hβ).unique (curvatureOf_spec hβ) ⟨hC, hS⟩

theorem inv_optimalValue_mem {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    (optimalValue C)⁻¹ ∈ Ioo (0 : ℝ) 1 :=
  ⟨inv_pos.mpr (by linarith [one_lt_optimalValue hC]), inv_lt_one_of_one_lt₀ (one_lt_optimalValue hC)⟩

theorem curvatureOf_inv_optimalValue {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    curvatureOf (optimalValue C)⁻¹ = C :=
  curvatureOf_eq (inv_optimalValue_mem hC) hC (inv_inv _).symm

theorem curvatureOf_strictMonoOn : StrictMonoOn curvatureOf (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hA := curvatureOf_spec ha
  have hB := curvatureOf_spec hb
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with h | h
  · have : a⁻¹ = b⁻¹ := by rw [← hA.2, ← hB.2, h]
    have := inv_injective this
    linarith
  · have := optimalValue_strictAntiOn hB.1 hA.1 h
    rw [hA.2, hB.2] at this
    have := (inv_lt_inv₀ ha.1 hb.1).mp this
    linarith

theorem curvatureOf_image : curvatureOf '' Ioo (0 : ℝ) 1 = Ioo (1 / 4 : ℝ) (1 / 2) := by
  ext C
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact (curvatureOf_spec hβ).1
  · intro hC
    exact ⟨_, inv_optimalValue_mem hC, curvatureOf_inv_optimalValue hC⟩

theorem curvatureOf_continuousAt (hβ : β ∈ Ioo (0 : ℝ) 1) : ContinuousAt curvatureOf β := by
  apply continuousAt_of_monotoneOn_of_image_mem_nhds curvatureOf_strictMonoOn.monotoneOn
    (Ioo_mem_nhds hβ.1 hβ.2)
  rw [curvatureOf_image]
  exact Ioo_mem_nhds (curvatureOf_spec hβ).1.1 (curvatureOf_spec hβ).1.2

theorem hasDerivAt_curvatureOf (hβ : β ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt curvatureOf
      (-(optimalValue (curvatureOf β)) ^ 2 /
        (((2 * curvatureOf β - 1) * scalarI (curvatureOf β) + 8 * curvatureOf β - 6) /
          (4 * curvatureOf β - 1))) β := by
  set C := curvatureOf β
  have hC := (curvatureOf_spec hβ).1
  have hS : optimalValue C ≠ 0 := by linarith [one_lt_optimalValue hC]
  have hσ := optimalValue_deriv_neg hC
  have hf : HasDerivAt (fun x => (optimalValue x)⁻¹)
      (-(((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1)) / optimalValue C ^ 2) C :=
    (hasDerivAt_optimalValue' hC).inv hS
  have hne : -(((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1)) / optimalValue C ^ 2 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hσ.ne) (pow_ne_zero 2 hS)
  have hloc : ∀ᶠ y in 𝓝 β, (fun x => (optimalValue x)⁻¹) (curvatureOf y) = y := by
    filter_upwards [Ioo_mem_nhds hβ.1 hβ.2] with y hy
    rw [(curvatureOf_spec hy).2, inv_inv]
  have h := HasDerivAt.of_local_left_inverse (curvatureOf_continuousAt hβ) hf hne hloc
  convert h using 1
  field_simp

end Curvature

section Frontier

theorem frontierDelta_eq' {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    frontierDelta β = β * initialState (curvatureOf β) := by
  have hC := curvatureOf_spec hβ
  have h := frontierDelta_eq hC.1
  rw [hC.2, inv_inv] at h
  rw [h, div_inv_eq_mul, mul_comm]

/-- `δ'(β) = κ(C(β))`, equation (49). -/
theorem hasDerivAt_frontierDelta {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt frontierDelta (kappaOf (curvatureOf β)) β := by
  obtain ⟨hC, hSβ⟩ := curvatureOf_spec hβ
  have hτ := (hasDerivAt_initialState' hC).comp β (hasDerivAt_curvatureOf hβ)
  have hprod := (hasDerivAt_id β).mul hτ
  have heq : frontierDelta =ᶠ[𝓝 β] fun b => b * initialState (curvatureOf b) := by
    filter_upwards [Ioo_mem_nhds hβ.1 hβ.2] with b hb
    exact frontierDelta_eq' hb
  apply (hprod.congr_of_eventuallyEq heq).congr_deriv
  have hβS1 : β * optimalValue (curvatureOf β) = 1 := by
    rw [hSβ]; exact mul_inv_cancel₀ hβ.1.ne'
  simp only [Function.comp_apply, id_eq, one_mul]
  generalize curvatureOf β = C at hC hSβ hβS1 ⊢
  have hS : optimalValue C ≠ 0 := by linarith [one_lt_optimalValue hC]
  have hσ := (optimalValue_deriv_neg hC).ne
  have h2 : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2])
  generalize ((2 * C - 1) * scalarI C + 8 * C - 6) / (4 * C - 1) = σ at hσ ⊢
  have e : β * (-initialState C * σ / (1 - 2 * C) * (-optimalValue C ^ 2 / σ)) =
      initialState C * optimalValue C * (β * optimalValue C) / (1 - 2 * C) := by
    field_simp
  rw [e, hβS1]
  unfold kappaOf
  field_simp
  ring

theorem frontierDelta_continuousOn : ContinuousOn frontierDelta (Ioo (0 : ℝ) 1) :=
  fun _ hβ => (hasDerivAt_frontierDelta hβ).continuousAt.continuousWithinAt

/-- **Theorem B.** `δ` is strictly increasing on `(0, 1)`. -/
theorem frontierDelta_strictMonoOn : StrictMonoOn frontierDelta (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1) frontierDelta_continuousOn
  intro β hβ
  rw [interior_Ioo] at hβ
  rw [(hasDerivAt_frontierDelta hβ).deriv]
  exact kappaOf_pos (curvatureOf_spec hβ).1

/-- **Theorem B.** `δ` is strictly convex on `(0, 1)`. -/
theorem frontierDelta_strictConvexOn : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) frontierDelta := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioo 0 1) frontierDelta_continuousOn
  rw [interior_Ioo]
  intro a ha b hb hab
  rw [(hasDerivAt_frontierDelta ha).deriv, (hasDerivAt_frontierDelta hb).deriv]
  exact kappaOf_strictMonoOn (curvatureOf_spec ha).1 (curvatureOf_spec hb).1
    (curvatureOf_strictMonoOn ha hb hab)

/-- **Theorem B.** The derivative of `δ` ranges over `(0, ∞)`. -/
theorem frontierDelta_deriv_image :
    (fun β => deriv frontierDelta β) '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext κ
  constructor
  · rintro ⟨β, hβ, rfl⟩
    show deriv frontierDelta β ∈ Ioi 0
    rw [(hasDerivAt_frontierDelta hβ).deriv]
    exact kappaOf_pos (curvatureOf_spec hβ).1
  · intro hκ
    obtain ⟨C, ⟨hC, hkC⟩, -⟩ := existsUnique_kappaOf_eq (mem_Ioi.mp hκ)
    refine ⟨(optimalValue C)⁻¹, inv_optimalValue_mem hC, ?_⟩
    simp only
    rw [(hasDerivAt_frontierDelta (inv_optimalValue_mem hC)).deriv,
      curvatureOf_inv_optimalValue hC, hkC]

/-- **Theorem B, (53).** `κ ρ(κ) = sup_{0<β<1} (κ β - δ(β))`, attained at `β = 1/S(C)`. -/
theorem theoremB_conjugate {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    IsGreatest {x | ∃ β ∈ Ioo (0 : ℝ) 1, x = kappaOf C * β - frontierDelta β}
      (kappaOf C * condRatio (kappaOf C)) := by
  have hκ := kappaOf_pos hC
  have hρ := condRatio_eq hC
  have hglb := theoremB_conditional hC
  have hρ' : condRatio (kappaOf C) = (optimalValue C + (1 - 2 * C))⁻¹ := by
    rw [hρ, optimalValue_add_u]
  constructor
  · refine ⟨(optimalValue C)⁻¹, inv_optimalValue_mem hC, ?_⟩
    rw [frontierDelta_eq hC, hρ']
    have hS : optimalValue C ≠ 0 := by linarith [one_lt_optimalValue hC]
    have hSu : optimalValue C + (1 - 2 * C) ≠ 0 := (optimalValue_add_u_pos hC).ne'
    have h2 : 1 - 2 * C ≠ 0 := ne_of_gt (by linarith [hC.2])
    unfold kappaOf
    field_simp
    ring
  · rintro x ⟨β, hβ, rfl⟩
    -- every admissible pair with `G = κ M` gives `Γ_max/G ≥ β - δ(β)/κ`
    have hC' := curvatureOf_spec hβ
    have hlow : β - frontierDelta β / kappaOf C ≤ condRatio (kappaOf C) := by
      rw [hρ']
      apply hglb.2
      rintro r ⟨μs, μb, A, hM, hGM, rfl⟩
      have hG : 0 < gainsFromTrade μs μb := by rw [hGM]; exact mul_pos hκ hM
      have hg := affine_guarantee hC'.1 A
      rw [hC'.2, inv_inv] at hg
      rw [frontierDelta_eq' hβ, le_div_iff₀ hG]
      rw [hGM] at hg ⊢
      have e : (β - β * initialState (curvatureOf β) / kappaOf C) * (kappaOf C * sellerMean μs) =
          β * (kappaOf C * sellerMean μs) - β * initialState (curvatureOf β) * sellerMean μs := by
        field_simp
      linarith
    have := mul_le_mul_of_nonneg_left hlow hκ.le
    have e : kappaOf C * (β - frontierDelta β / kappaOf C) = kappaOf C * β - frontierDelta β := by
      field_simp
    linarith

end Frontier

end FixedPrice
