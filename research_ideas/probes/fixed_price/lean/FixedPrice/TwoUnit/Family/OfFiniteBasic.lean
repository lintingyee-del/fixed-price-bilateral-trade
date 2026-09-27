import FixedPrice.TwoUnit.Family.Statements

/-!
# Work package E, helpers: finitely supported laws as measures

A finitely supported law `L` (a list of weighted points) is the measure `Σ w • δ_x`. Every
function is integrable against it and its integral is the weighted sum; almost-everywhere
properties are pointwise properties of the support; against a product of two such laws a
measurable function integrates to the double weighted sum.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ENNReal
open FixedPrice.TwoUnit (GenInstance ofFinite RLaw)

namespace FixedPrice.TwoUnit.Family

/-- The measure of a finitely supported law. -/
def lawMeasure (L : RLaw) : Measure (ℝ × ℝ) :=
  (L.map fun b => ENNReal.ofReal b.2 • Measure.dirac b.1).sum

theorem lawMeasure_nil : lawMeasure [] = 0 := by simp [lawMeasure]

theorem lawMeasure_cons (b : (ℝ × ℝ) × ℝ) (L : RLaw) :
    lawMeasure (b :: L) = ENNReal.ofReal b.2 • Measure.dirac b.1 + lawMeasure L := by
  simp [lawMeasure]

theorem isFiniteMeasure_smul_dirac (w : ℝ) (x : ℝ × ℝ) :
    IsFiniteMeasure (ENNReal.ofReal w • Measure.dirac x) :=
  ⟨by simp⟩

instance isFiniteMeasure_lawMeasure (L : RLaw) : IsFiniteMeasure (lawMeasure L) := by
  induction L with
  | nil => rw [lawMeasure_nil]; infer_instance
  | cons b L ih =>
    rw [lawMeasure_cons]
    haveI := isFiniteMeasure_smul_dirac b.2 b.1
    infer_instance

theorem integrable_lawMeasure (L : RLaw) (f : ℝ × ℝ → ℝ) : Integrable f (lawMeasure L) := by
  induction L with
  | nil => rw [lawMeasure_nil]; exact integrable_zero_measure
  | cons b L ih =>
    rw [lawMeasure_cons]
    exact ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure ih

theorem integral_lawMeasure {L : RLaw} (hL : ∀ b ∈ L, 0 ≤ b.2) (f : ℝ × ℝ → ℝ) :
    ∫ x, f x ∂(lawMeasure L) = (L.map fun b => b.2 * f b.1).sum := by
  induction L with
  | nil => simp [lawMeasure_nil]
  | cons b L ih =>
    rw [lawMeasure_cons, integral_add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
      (integrable_lawMeasure L f), integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (hL b List.mem_cons_self),
      ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')), List.map_cons, List.sum_cons,
      smul_eq_mul]

theorem lawMeasure_univ {L : RLaw} (hL : ∀ b ∈ L, 0 ≤ b.2) :
    lawMeasure L univ = ENNReal.ofReal (L.map Prod.snd).sum := by
  induction L with
  | nil => simp [lawMeasure_nil]
  | cons b L ih =>
    rw [lawMeasure_cons, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one, ih (fun b' hb' => hL b' (List.mem_cons_of_mem _ hb')), List.map_cons,
      List.sum_cons, ENNReal.ofReal_add (hL b List.mem_cons_self)
        (List.sum_nonneg fun x hx => by
          obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hx
          exact hL b' (List.mem_cons_of_mem _ hb'))]

theorem ae_lawMeasure {L : RLaw} {p : ℝ × ℝ → Prop} (h : ∀ b ∈ L, p b.1) :
    ∀ᵐ x ∂(lawMeasure L), p x := by
  induction L with
  | nil => rw [lawMeasure_nil]; simp
  | cons b L ih =>
    rw [lawMeasure_cons, ae_add_measure_iff]
    refine ⟨Measure.ae_smul_measure ?_ _, ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')⟩
    rw [Filter.Eventually, ae_dirac_eq]
    exact h b List.mem_cons_self

theorem integrable_prod_lawMeasure (B S : RLaw) {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ}
    (hf : Measurable f) : Integrable f ((lawMeasure B).prod (lawMeasure S)) := by
  induction B with
  | nil => rw [lawMeasure_nil, Measure.zero_prod]; exact integrable_zero_measure
  | cons b B ih =>
    haveI := isFiniteMeasure_smul_dirac b.2 b.1
    rw [lawMeasure_cons, Measure.add_prod, Measure.prod_smul_left, Measure.dirac_prod]
    refine (Integrable.smul_measure ?_ ENNReal.ofReal_ne_top).add_measure ih
    exact (integrable_map_measure hf.aestronglyMeasurable measurable_prodMk_left.aemeasurable).mpr
      (integrable_lawMeasure S _)

theorem integral_prod_lawMeasure {B S : RLaw} (hB : ∀ b ∈ B, 0 ≤ b.2) (hS : ∀ s ∈ S, 0 ≤ s.2)
    {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂((lawMeasure B).prod (lawMeasure S)) =
      (B.map fun b => (S.map fun s => b.2 * s.2 * f (b.1, s.1)).sum).sum := by
  induction B with
  | nil => simp [lawMeasure_nil, Measure.zero_prod]
  | cons b B ih =>
    haveI := isFiniteMeasure_smul_dirac b.2 b.1
    have hint : Integrable f ((ENNReal.ofReal b.2 • Measure.dirac b.1).prod (lawMeasure S)) := by
      rw [Measure.prod_smul_left, Measure.dirac_prod]
      exact ((integrable_map_measure hf.aestronglyMeasurable
        measurable_prodMk_left.aemeasurable).mpr (integrable_lawMeasure S _)).smul_measure
        ENNReal.ofReal_ne_top
    rw [lawMeasure_cons, Measure.add_prod, integral_add_measure hint
      (integrable_prod_lawMeasure B S hf), Measure.prod_smul_left, integral_smul_measure,
      Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
        hf.aestronglyMeasurable, integral_lawMeasure hS,
      ih (fun b' hb' => hB b' (List.mem_cons_of_mem _ hb')), List.map_cons, List.sum_cons,
      ENNReal.toReal_ofReal (hB b List.mem_cons_self), smul_eq_mul, ← List.sum_map_mul_left]
    congr 2
    exact List.map_congr_left fun s _ => by ring

end FixedPrice.TwoUnit.Family
