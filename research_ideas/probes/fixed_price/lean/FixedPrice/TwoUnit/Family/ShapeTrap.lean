import FixedPrice.TwoUnit.Family.ShapeVar

/-!
# Work package B, part 5: trapezoid variations

The trapezoid `φ` (zero up to `x`, rising to `1` on `[x, x+r]`, one on `[x+r, y]`, falling to `0`
on `[y, y+r]`) is Lipschitz with derivative `(1_{(x,x+r)} - 1_{(y,y+r)})/r` off four points. Its
vector `v = √s φ'` has `z_v = φ` and `⟪w, v⟫ = avg_{[x,x+r]} ω - avg_{[y,y+r]} ω` with `ω = √s w`
(`= ξ z'`). Pushing the minimizer down by `εφ` (allowed where the lower obstacle is slack) or up
(allowed where the upper obstacle is slack) and letting `r → 0` at Lebesgue points gives
`ω(x) - ω(y) ≤ d ∫_x^y e^{-2z}`, respectively `≥`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal RealInnerProductSpace

namespace FixedPrice.TwoUnit.Family

namespace Relaxed

/-- The trapezoid. -/
def trap (x y r : ℝ) (ξ : ℝ) : ℝ := max 0 (min 1 (min ((ξ - x) / r) ((y + r - ξ) / r)))

/-- The derivative of the trapezoid off its four breakpoints. -/
def dtrap (x y r : ℝ) (s : ℝ) : ℝ :=
  (Ioo x (x + r)).indicator (fun _ => 1 / r) s - (Ioo y (y + r)).indicator (fun _ => 1 / r) s

section Trap

variable {x y r : ℝ} (hr : 0 < r) (hxy : x + r ≤ y)
include hr hxy

theorem trap_nonneg (ξ : ℝ) : 0 ≤ trap x y r ξ := le_max_left _ _

theorem trap_le_one (ξ : ℝ) : trap x y r ξ ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem trap_of_le {ξ : ℝ} (h : ξ ≤ x) : trap x y r ξ = 0 := by
  unfold trap
  have : (ξ - x) / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  exact max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans this))

theorem trap_of_ge {ξ : ℝ} (h : y + r ≤ ξ) : trap x y r ξ = 0 := by
  unfold trap
  have : (y + r - ξ) / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans this))

theorem trap_of_mid {ξ : ℝ} (h1 : x + r ≤ ξ) (h2 : ξ ≤ y) : trap x y r ξ = 1 := by
  unfold trap
  have ha : 1 ≤ (ξ - x) / r := by rw [le_div_iff₀ hr]; linarith
  have hb : 1 ≤ (y + r - ξ) / r := by rw [le_div_iff₀ hr]; linarith
  rw [min_eq_left (le_min ha hb), max_eq_right zero_le_one]

theorem trap_of_rise {ξ : ℝ} (h1 : x ≤ ξ) (h2 : ξ ≤ x + r) : trap x y r ξ = (ξ - x) / r := by
  unfold trap
  have ha : (ξ - x) / r ≤ 1 := by rw [div_le_one hr]; linarith
  have hb : (ξ - x) / r ≤ (y + r - ξ) / r := div_le_div_of_nonneg_right (by linarith) hr.le
  have h0 : 0 ≤ (ξ - x) / r := div_nonneg (by linarith) hr.le
  rw [min_eq_left hb, min_eq_right ha, max_eq_right h0]

theorem trap_of_fall {ξ : ℝ} (h1 : y ≤ ξ) (h2 : ξ ≤ y + r) :
    trap x y r ξ = (y + r - ξ) / r := by
  unfold trap
  have ha : (y + r - ξ) / r ≤ 1 := by rw [div_le_one hr]; linarith
  have hb : (y + r - ξ) / r ≤ (ξ - x) / r := div_le_div_of_nonneg_right (by linarith) hr.le
  have h0 : 0 ≤ (y + r - ξ) / r := div_nonneg (by linarith) hr.le
  rw [min_eq_right hb, min_eq_right ha, max_eq_right h0]

theorem hasDerivAt_trap {s : ℝ} (h1 : s ≠ x) (h2 : s ≠ x + r) (h3 : s ≠ y) (h4 : s ≠ y + r) :
    HasDerivAt (trap x y r) (dtrap x y r s) s := by
  rcases lt_or_gt_of_ne h1 with hs1 | hs1
  · -- left of the support
    have heq : trap x y r =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hs1] with t ht
      exact trap_of_le hr hxy (le_of_lt ht)
    have hd : dtrap x y r s = 0 := by
      unfold dtrap
      rw [indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hs1.le)),
        indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr (by linarith))), sub_zero]
    rw [hd]
    exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
  rcases lt_or_gt_of_ne h2 with hs2 | hs2
  · -- the rise
    have heq : trap x y r =ᶠ[𝓝 s] fun t => (t - x) / r := by
      filter_upwards [Ioo_mem_nhds hs1 hs2] with t ht
      exact trap_of_rise hr hxy ht.1.le ht.2.le
    have hd : dtrap x y r s = 1 / r := by
      unfold dtrap
      rw [indicator_of_mem (show s ∈ Ioo x (x + r) from ⟨hs1, hs2⟩),
        indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr (by linarith))), sub_zero]
    rw [hd]
    have : HasDerivAt (fun t => (t - x) / r) (1 / r) s := by
      simpa using ((hasDerivAt_id s).sub_const x).div_const r
    exact this.congr_of_eventuallyEq heq
  rcases lt_or_gt_of_ne h3 with hs3 | hs3
  · -- the plateau
    have heq : trap x y r =ᶠ[𝓝 s] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhds hs2 hs3] with t ht
      exact trap_of_mid hr hxy ht.1.le ht.2.le
    have hd : dtrap x y r s = 0 := by
      unfold dtrap
      rw [indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hs2.le)),
        indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hs3.le)), sub_zero]
    rw [hd]
    exact (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq heq
  rcases lt_or_gt_of_ne h4 with hs4 | hs4
  · -- the fall
    have heq : trap x y r =ᶠ[𝓝 s] fun t => (y + r - t) / r := by
      filter_upwards [Ioo_mem_nhds hs3 hs4] with t ht
      exact trap_of_fall hr hxy ht.1.le ht.2.le
    have hd : dtrap x y r s = -(1 / r) := by
      unfold dtrap
      rw [indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr (by linarith))),
        indicator_of_mem (show s ∈ Ioo y (y + r) from ⟨hs3, hs4⟩), zero_sub]
    rw [hd]
    have : HasDerivAt (fun t => (y + r - t) / r) (-(1 / r)) s := by
      simpa [neg_div] using ((hasDerivAt_id s).const_sub (y + r)).div_const r
    exact this.congr_of_eventuallyEq heq
  · -- right of the support
    have heq : trap x y r =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hs4] with t ht
      exact trap_of_ge hr hxy (le_of_lt ht)
    have hd : dtrap x y r s = 0 := by
      unfold dtrap
      rw [indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr (by linarith))),
        indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hs4.le)), sub_zero]
    rw [hd]
    exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq

theorem lipschitz_trap : LipschitzWith (Real.toNNReal (1 / r)) (trap x y r) := by
  unfold trap
  have h1 : LipschitzWith (Real.toNNReal (1 / r)) (fun ξ => (ξ - x) / r) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq, ← sub_div,
      abs_div, abs_of_pos hr, show a - x - (b - x) = a - b by ring]
    rw [div_eq_mul_inv, one_div, mul_comm]
  have h2 : LipschitzWith (Real.toNNReal (1 / r)) (fun ξ => (y + r - ξ) / r) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq, ← sub_div,
      abs_div, abs_of_pos hr, show y + r - a - (y + r - b) = -(a - b) by ring, abs_neg]
    rw [div_eq_mul_inv, one_div, mul_comm]
  have hmin := (LipschitzWith.const (1 : ℝ)).min (h1.min h2)
  have hmax := (LipschitzWith.const (0 : ℝ)).max hmin
  simpa using hmax

/-- `∫_ξ^{ξ₀} φ' = -φ(ξ)` for a trapezoid ending before `ξ₀`. -/
theorem integral_dtrap {ξ b : ℝ} (hξb : ξ ≤ b) (hb : y + r ≤ b) :
    ∫ s in ξ..b, dtrap x y r s = -trap x y r ξ := by
  have hAC : AbsolutelyContinuousOnInterval (trap x y r) ξ b :=
    ((lipschitz_trap hr hxy).lipschitzOnWith).absolutelyContinuousOnInterval
  rw [← show trap x y r b - trap x y r ξ = -trap x y r ξ by rw [trap_of_ge hr hxy hb]; ring,
    ← hAC.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  have hfin : ({x, x + r, y, y + r} : Set ℝ).Countable := by simp [Set.Countable.insert]
  filter_upwards [hfin.ae_notMem volume] with s hs _
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hs
  exact ((hasDerivAt_trap hr hxy hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).deriv).symm

end Trap

end Relaxed

end FixedPrice.TwoUnit.Family
