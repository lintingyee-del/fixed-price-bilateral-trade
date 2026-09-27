import FixedPrice.TwoUnit.Family.SeqCompactExt

/-!
# Work package A, compactness: derivatives of converging concave functions

If concave functions `f_n` converge pointwise to `f`, and `f` and every `f_n` are differentiable
at `x`, then `f_n'(x) → f'(x)`: the one-sided difference quotients of `f_n` bracket `f_n'(x)`,
they converge to those of `f`, and those tend to `f'(x)`. This is the step "Derivatives of concave
curves converge almost everywhere under uniform convergence" of `lem:2fam-compact`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

theorem tendsto_deriv_of_concave {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hconc : ∀ n, ConcaveOn ℝ univ (f n)) (hlim : ∀ y, Tendsto (fun n => f n y) atTop (𝓝 (g y)))
    {x : ℝ} (hg : DifferentiableAt ℝ g x) (hf : ∀ n, DifferentiableAt ℝ (f n) x) :
    Tendsto (fun n => deriv (f n) x) atTop (𝓝 (deriv g x)) := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp hg.hasDerivAt
  rw [tendsto_order]
  constructor
  · -- lower bounds from the right difference quotients
    intro a ha
    have hev : ∀ᶠ y in 𝓝[>] x, a < slope g x y :=
      (hslope.mono_left (nhdsWithin_mono _ (fun y hy => ne_of_gt hy))).eventually
        (lt_mem_nhds ha)
    obtain ⟨y, hya, hyx⟩ := (hev.and self_mem_nhdsWithin).exists
    have hy : x < y := hyx
    have hconv : Tendsto (fun n => slope (f n) x y) atTop (𝓝 (slope g x y)) := by
      simp only [slope_def_field]
      exact ((hlim y).sub (hlim x)).div_const _
    filter_upwards [hconv.eventually (lt_mem_nhds hya)] with n hn
    exact hn.trans_le ((hconc n).slope_le_deriv (mem_univ _) (mem_univ _) hy (hf n))
  · -- upper bounds from the left difference quotients
    intro b hb
    have hev : ∀ᶠ y in 𝓝[<] x, slope g x y < b :=
      (hslope.mono_left (nhdsWithin_mono _ (fun y hy => ne_of_lt hy))).eventually
        (gt_mem_nhds hb)
    obtain ⟨y, hyb, hyx⟩ := (hev.and self_mem_nhdsWithin).exists
    have hy : y < x := hyx
    have hconv : Tendsto (fun n => slope (f n) y x) atTop (𝓝 (slope g y x)) := by
      simp only [slope_def_field]
      exact ((hlim x).sub (hlim y)).div_const _
    rw [slope_comm] at hyb
    filter_upwards [hconv.eventually (gt_mem_nhds hyb)] with n hn
    exact ((hconc n).deriv_le_slope (mem_univ _) (mem_univ _) hy (hf n)).trans_lt hn

end FixedPrice.TwoUnit.Family
