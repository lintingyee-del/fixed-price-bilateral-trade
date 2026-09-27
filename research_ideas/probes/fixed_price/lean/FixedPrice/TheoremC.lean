import FixedPrice.Attainment
import FixedPrice.UpperBound
import FixedPrice.Uniqueness

/-! Theorem C of the paper: the upper bound, its attainment by the explicit control (31),
and the almost-everywhere uniqueness of the maximizer. -/

noncomputable section

open Set MeasureTheory

namespace FixedPrice

/-- **Theorem C, equation (30).** For `d > 0` and the curvature `C ∈ (1/4, 1/2)` with
`τ(C) = d`, every measurable control with values in `[0, 1]` has objective at most
`S(C) = C (2 + I_C(y_e(C)))`, and the explicit control (31) attains this value. -/
theorem theoremC_bound {d C : ℝ} (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) :
    (∀ h : ℝ → ℝ, AEStronglyMeasurable h (volume.restrict (Icc 0 1)) →
      (∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) → objective d h ≤ optimalValue C) ∧
    objective d (maximizingControl d C) = optimalValue C :=
  ⟨fun _ hmeas hbox => objective_le_optimalValue hd hC hinit hmeas hbox,
    maximizingControl_attains hd hC hinit⟩

/-- Theorem C with its equality characterization. The maximizer
is the explicit formula (31), including its zero and one arcs, and it is unique up to
equality almost everywhere on `[0, 1]`. -/
theorem theoremC {d C : ℝ} (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) :
    AEStronglyMeasurable (maximizingControl d C) (volume.restrict (Icc 0 1)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, maximizingControl d C t ∈ Icc (0 : ℝ) 1) ∧
    objective d (maximizingControl d C) = optimalValue C ∧
    StrictMonoOn (maximizingControl d C) (Ioo C (C * (1 + endParameter C))) ∧
    ∀ h : ℝ → ℝ,
      AEStronglyMeasurable h (volume.restrict (Icc 0 1)) →
      (∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) →
      objective d h ≤ optimalValue C ∧
        (objective d h = optimalValue C ↔
          h =ᵐ[volume.restrict (Icc 0 1)] maximizingControl d C) := by
  obtain ⟨hmeas, hbox, hmono⟩ := maximizingControl_feasible hd hC hinit
  refine ⟨hmeas, hbox, ?_, hmono, ?_⟩
  · exact maximizingControl_attains hd hC hinit
  · intro h hmeas_h hbox_h
    exact ⟨objective_le_optimalValue hd hC hinit hmeas_h hbox_h,
      objective_eq_optimalValue_iff hd hC hinit hmeas_h hbox_h⟩

end FixedPrice
