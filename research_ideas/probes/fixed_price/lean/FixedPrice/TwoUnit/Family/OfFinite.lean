import FixedPrice.TwoUnit.Family.OfFiniteBasic

/-!
# Work package E, part 2: the finite model as a special case (export theorem)

Owned by work package E. The theorem proves `OfFiniteStatement` (the finite model of
`FixedPrice/TwoUnit/Model.lean` is the special case `ofFinite` of the general model of
`GeneralModel.lean`) with the frozen signature below; helpers in `OfFiniteBasic` (finitely
supported laws as finite sums of Dirac masses). `GeneralModel.lean` holds definitions only and
stays with the coordinator.
-/

open MeasureTheory
open FixedPrice.TwoUnit (ofFinite unitGain mean2 opt2 gain2)

namespace FixedPrice.TwoUnit.Family

theorem measurable_unitGain {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) (z : ℝ) : Measurable fun x => unitGain (f x) (g x) z := by
  unfold unitGain
  exact Measurable.ite ((measurableSet_le hg measurable_const).inter
    (measurableSet_le measurable_const hf)) (hf.sub hg) measurable_const

/-- `OfFiniteStatement`. -/
theorem ofFinite_spec_proof : OfFiniteStatement := by
  intro B S hV
  have hB : ∀ b ∈ B, 0 ≤ b.2 := fun b hb => (hV.buyers b hb).1.le
  have hS : ∀ s ∈ S, 0 ≤ s.2 := fun s hs => (hV.sellers s hs).1.le
  have hbuy : (ofFinite B S).buyer = lawMeasure B := rfl
  have hsel : (ofFinite B S).seller = lawMeasure S := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun z => ?_⟩
  · rw [hbuy]; exact ⟨by rw [lawMeasure_univ hB, hV.sumB, ENNReal.ofReal_one]⟩
  · rw [hsel]; exact ⟨by rw [lawMeasure_univ hS, hV.sumS, ENNReal.ofReal_one]⟩
  · rw [hbuy]
    exact ae_lawMeasure (p := fun x => 0 < x.2 ∧ x.2 ≤ x.1) fun b hb =>
      ⟨(hV.buyers b hb).2.1, (hV.buyers b hb).2.2⟩
  · rw [hsel]
    exact ae_lawMeasure (p := fun x => 0 < x.1 ∧ x.1 ≤ x.2) fun s hs =>
      ⟨(hV.sellers s hs).2.1, (hV.sellers s hs).2.2⟩
  · rw [hbuy]; exact integrable_lawMeasure B _
  · rw [hsel]; exact integrable_lawMeasure S _
  · show ∫ s, (s.1 + s.2) ∂(lawMeasure S) = mean2 S
    rw [integral_lawMeasure hS]
    rfl
  · show ∫ x, (max x.1.1 x.2.1 + max x.1.2 x.2.2) ∂((lawMeasure B).prod (lawMeasure S)) = opt2 B S
    rw [integral_prod_lawMeasure hB hS
      (by fun_prop : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) =>
        max x.1.1 x.2.1 + max x.1.2 x.2.2).measurable]
    rfl
  · show ∫ x, (unitGain x.1.1 x.2.1 z + unitGain x.1.2 x.2.2 z) ∂((lawMeasure B).prod
      (lawMeasure S)) = gain2 B S z
    rw [integral_prod_lawMeasure hB hS
      ((measurable_unitGain measurable_fst.fst measurable_snd.fst z).add
        (measurable_unitGain measurable_fst.snd measurable_snd.snd z))]
    rfl

end FixedPrice.TwoUnit.Family
