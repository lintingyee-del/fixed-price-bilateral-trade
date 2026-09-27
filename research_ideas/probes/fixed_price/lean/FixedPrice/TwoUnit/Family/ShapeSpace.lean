import FixedPrice.TwoUnit.Family.BasicFTC

/-!
# Work package B, part 1: the relaxed problem in a Hilbert space

Proof of `lem:2fam-shape`, "Existence in the obstacle class". With `z = log P` and the scaled
derivative `w = √ξ z'`, the energy is `E = ‖w‖² + d ∫ e^{-2z}`, where `‖·‖` is the `L²` norm on
`(c_f, ξ₀]` and `z(ξ) = -∫_ξ^{ξ₀} w/√s = -⟪w, g_ξ⟫` with `g_ξ = 1_{(ξ, ξ₀]}/√s`. So `z(ξ)` is a
continuous linear functional of `w` for every `ξ > 0`. The obstacle class
`log p_f ≤ z ≤ log U_f` is closed and convex; the energy is uniformly convex
(`E((u+v)/2) ≤ (E u + E v)/2 - ‖u - v‖²/4`), so a minimizing sequence is Cauchy, the limit is
admissible, and it is the unique minimizer.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

variable (θ : Params)

/-- The curve interval, open on the left. -/
def I : Set ℝ := Ioc θ.c θ.ξ₀

/-- Lebesgue measure on the curve interval. -/
def μ : Measure ℝ := volume.restrict (I θ)

instance : IsFiniteMeasure (μ θ) := by
  unfold μ I; exact isFiniteMeasure_restrict.mpr (by simp)

/-- The space of scaled derivatives. -/
abbrev H := Lp ℝ 2 (μ θ)

theorem inner_eq_integral (f g : H θ) : ⟪f, g⟫ = ∫ s, f s * g s ∂(μ θ) := by
  rw [MeasureTheory.L2.inner_def]
  congr 1
  ext s
  simp [mul_comm]

/-- `s ↦ 1_{(ξ, ξ₀]}(s)/√s` -/
def gfun (ξ : ℝ) (s : ℝ) : ℝ := (Ioc ξ θ.ξ₀).indicator (fun s => 1 / Real.sqrt s) s

theorem memLp_gfun {ξ : ℝ} (hξ : 0 < ξ) : MemLp (gfun θ ξ) 2 (μ θ) := by
  refine MemLp.of_bound (C := 1 / Real.sqrt ξ) ?_ ?_
  · exact (((Real.continuous_sqrt.measurable).const_div 1).indicator measurableSet_Ioc).aestronglyMeasurable
  · refine Eventually.of_forall fun s => ?_
    unfold gfun
    by_cases hs : s ∈ Ioc ξ θ.ξ₀
    · rw [indicator_of_mem hs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hξ) (Real.sqrt_le_sqrt hs.1.le)
    · rw [indicator_of_notMem hs, norm_zero]; positivity

/-- `g_ξ` as an element of `L²` (zero for `ξ ≤ 0`). -/
def gLp (ξ : ℝ) : H θ :=
  if hξ : 0 < ξ then (memLp_gfun θ hξ).toLp _ else 0

/-- The log-curve of a scaled derivative: `z(ξ) = -⟪w, g_ξ⟫ = -∫_ξ^{ξ₀} w/√s`. -/
def zfun (w : H θ) (ξ : ℝ) : ℝ := -⟪w, gLp θ ξ⟫

theorem zfun_add (u v : H θ) (ξ : ℝ) : zfun θ (u + v) ξ = zfun θ u ξ + zfun θ v ξ := by
  unfold zfun; rw [inner_add_left]; ring

theorem zfun_smul (a : ℝ) (u : H θ) (ξ : ℝ) : zfun θ (a • u) ξ = a * zfun θ u ξ := by
  unfold zfun; rw [real_inner_smul_left]; ring

theorem zfun_sub (u v : H θ) (ξ : ℝ) : zfun θ (u - v) ξ = zfun θ u ξ - zfun θ v ξ := by
  unfold zfun; rw [inner_sub_left]; ring

theorem abs_zfun_le (u : H θ) (ξ : ℝ) : |zfun θ u ξ| ≤ ‖u‖ * ‖gLp θ ξ‖ := by
  unfold zfun; rw [abs_neg]; exact abs_real_inner_le_norm _ _

theorem continuous_zfun (ξ : ℝ) : Continuous fun u : H θ => zfun θ u ξ := by
  unfold zfun; exact (continuous_id.inner continuous_const).neg

/-- The integral form of `z`. -/
theorem zfun_eq_integral (w : H θ) {ξ : ℝ} (hξ : 0 < ξ) (hcξ : θ.c ≤ ξ) (hle : ξ ≤ θ.ξ₀) :
    zfun θ w ξ = -∫ s in ξ..θ.ξ₀, w s / Real.sqrt s := by
  unfold zfun gLp
  rw [dif_pos hξ, inner_eq_integral]
  congr 1
  · rw [intervalIntegral.integral_of_le hle]
    have hsub : Ioc ξ θ.ξ₀ ⊆ I θ := Ioc_subset_Ioc_left hcξ
    calc ∫ s, w s * (memLp_gfun θ hξ).toLp _ s ∂(μ θ)
        = ∫ s, w s * gfun θ ξ s ∂(μ θ) := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_gfun θ hξ).coeFn_toLp] with s hs
          rw [hs]
      _ = ∫ s in I θ, (Ioc ξ θ.ξ₀).indicator (fun s => w s / Real.sqrt s) s := by
          unfold μ
          refine integral_congr_ae (Eventually.of_forall fun s => ?_)
          unfold gfun
          by_cases hs : s ∈ Ioc ξ θ.ξ₀
          · simp only [indicator_of_mem hs]; ring
          · simp only [indicator_of_notMem hs, mul_zero]
      _ = ∫ s in Ioc ξ θ.ξ₀, w s / Real.sqrt s := by
          rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
            inter_eq_left.mpr hsub]

variable (d : ℝ)

/-- The relaxed energy `‖w‖² + d ∫_{(c, ξ₀]} e^{-2z}`. -/
def J (w : H θ) : ℝ := ‖w‖ ^ 2 + d * ∫ s, Real.exp (-2 * zfun θ w s) ∂(μ θ)

/-- The obstacle class for the scaled derivative. -/
def W : Set (H θ) :=
  {w | ∀ ξ ∈ Icc θ.c θ.ξ₀, 0 < ξ → Real.log θ.p ≤ zfun θ w ξ ∧ zfun θ w ξ ≤ Real.log (θ.U ξ)}

theorem convex_W : Convex ℝ (W θ) := by
  intro u hu v hv a b ha hb hab ξ hξ hξ0
  obtain ⟨hu1, hu2⟩ := hu ξ hξ hξ0
  obtain ⟨hv1, hv2⟩ := hv ξ hξ hξ0
  rw [zfun_add, zfun_smul, zfun_smul]
  have e1 : a * Real.log θ.p + b * Real.log θ.p = Real.log θ.p := by rw [← add_mul, hab, one_mul]
  have e2 : a * Real.log (θ.U ξ) + b * Real.log (θ.U ξ) = Real.log (θ.U ξ) := by
    rw [← add_mul, hab, one_mul]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hu1 ha, mul_le_mul_of_nonneg_left hv1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hu2 ha, mul_le_mul_of_nonneg_left hv2 hb]

theorem isClosed_W : IsClosed (W θ) := by
  have : W θ = ⋂ ξ ∈ {ξ | ξ ∈ Icc θ.c θ.ξ₀ ∧ 0 < ξ},
      ((fun u : H θ => zfun θ u ξ) ⁻¹' Icc (Real.log θ.p) (Real.log (θ.U ξ))) := by
    ext u
    simp only [W, mem_setOf_eq, mem_iInter, mem_preimage, mem_Icc]
    exact ⟨fun h ξ hξ => h ξ hξ.1 hξ.2, fun h ξ hξ hξ0 => h ξ ⟨hξ, hξ0⟩⟩
  rw [this]
  exact isClosed_biInter fun ξ _ => isClosed_Icc.preimage (continuous_zfun θ ξ)

end Relaxed

end FixedPrice.TwoUnit.Family
