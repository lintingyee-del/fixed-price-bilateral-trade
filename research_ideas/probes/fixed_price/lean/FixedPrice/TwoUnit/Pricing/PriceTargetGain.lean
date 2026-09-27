import FixedPrice.TwoUnit.Pricing.Attainment
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Theorem E, package B, part 1: survival functions of prices and the gain representation

* For a finite price measure `π`, the survival `t ↦ π((t, ∞))` is nonincreasing and
  right-continuous (continuity of the measure along the increasing sets `(t + 1/(n+1), ∞)`).
* The cumulative mass `tail + π₀((s, b̄])` of a normalized price is a cumulative mass.
* The gain of a price is the gain of its cumulative mass: by Fubini on `π ⊗ μ` applied to
  `1{s < z ≤ x} (x - s)`, both sides equal `π((s,∞)) + ∫_{(s,b̄]} (x - s) π((s,x]) dμ(x)`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section Survival

variable {ν : Measure ℝ} [IsFiniteMeasure ν]

theorem survival_antitone : Antitone fun t => ν.real (Ioi t) := fun _ _ hab =>
  measureReal_mono (Ioi_subset_Ioi hab)

theorem survival_measurable : Measurable fun t => ν.real (Ioi t) :=
  survival_antitone.measurable

omit [IsFiniteMeasure ν] in
theorem survival_nonneg (t : ℝ) : 0 ≤ ν.real (Ioi t) := measureReal_nonneg

theorem survival_rightContinuous (s : ℝ) :
    ContinuousWithinAt (fun t => ν.real (Ioi t)) (Ici s) s := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hmono : Monotone fun n : ℕ => Ioi (s + 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply Ioi_subset_Ioi
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have hU : (⋃ n : ℕ, Ioi (s + 1 / ((n : ℝ) + 1))) = Ioi s := by
    ext x
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
  have ht := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hU] at ht
  have ht' : Tendsto (fun n : ℕ => ν.real (Ioi (s + 1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (ν.real (Ioi s))) :=
    (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp ht
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht' ε hε
  have hNε := hN N le_rfl
  rw [Real.dist_eq, abs_lt] at hNε
  refine ⟨1 / ((N : ℝ) + 1), by positivity, fun {u} hu hdu => ?_⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu)] at hdu
  have h1 : ν.real (Ioi (s + 1 / ((N : ℝ) + 1))) ≤ ν.real (Ioi u) :=
    survival_antitone (by linarith)
  have h2 : ν.real (Ioi u) ≤ ν.real (Ioi s) := survival_antitone hu
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hNε.1]

theorem measureReal_Ioc_eq_sub {a b : ℝ} (hab : a ≤ b) :
    ν.real (Ioc a b) = ν.real (Ioi a) - ν.real (Ioi b) := by
  have hdisj : Disjoint (Ioc a b) (Ioi b) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.mpr hx')
  have h := measureReal_union hdisj measurableSet_Ioi (μ := ν)
  rw [Ioc_union_Ioi_eq_Ioi hab] at h
  linarith

end Survival

section Cumulative

variable {bbar : ℝ}

theorem isCumulativeMass_of_price' (π₀ : Measure ℝ) [IsFiniteMeasure π₀] {tail : ℝ}
    (htail : 0 ≤ tail) : IsCumulativeMass bbar (fun s => tail + π₀.real (Ioc s bbar)) := by
  refine ⟨fun s _ => by positivity, fun a _ b hb hab => ?_, fun s hs => ?_⟩
  · have := measureReal_mono (μ := π₀) (Ioc_subset_Ioc_left hab)
    linarith
  · have hc := (survival_rightContinuous (ν := π₀) s).mono (Icc_subset_Ici_self : Icc s bbar ⊆ Ici s)
    have hc' := hc.const_add (tail - π₀.real (Ioi bbar))
    refine hc'.congr (fun y hy => ?_) ?_
    · rw [measureReal_Ioc_eq_sub hy.2]; ring
    · rw [measureReal_Ioc_eq_sub hs.2]; ring

end Cumulative

/-! ### The gain of a price -/

section Gain

variable {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem integral_gainKernel' (hsupp : μ (Icc 0 bbar)ᶜ = 0) (π : Measure ℝ) [IsFiniteMeasure π]
    (s : ℝ) :
    ∫ z, gainKernel μ s z ∂π = gainFromMass bbar μ (fun t => π.real (Ioi t)) s := by
  have hb := bbar_nonneg_of_supp hsupp
  -- the integrand `F(z, x) = 1{s < z ≤ x} (x - s)` on `π ⊗ μ`
  set F : ℝ × ℝ → ℝ := fun p => if s < p.1 ∧ p.1 ≤ p.2 then p.2 - s else 0 with hF
  have hFmeas : Measurable F :=
    Measurable.ite ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)) (measurable_snd.sub measurable_const)
      measurable_const
  have hFint : Integrable F (π.prod μ) := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable (bbar + |s|) ?_
    have hae : ∀ᵐ p ∂(π.prod μ), p.2 ∈ Icc 0 bbar :=
      Measure.quasiMeasurePreserving_snd.ae (ae_mem_Icc_of_supp hsupp)
    filter_upwards [hae] with p hp
    simp only [hF]
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1, h.2])]
      linarith [hp.2, neg_abs_le s]
    · simp only [norm_zero]; positivity
  have hinner_z : ∀ z, ∫ x, F (z, x) ∂μ =
      if s < z then ∫ x in Ici z, (x - s) ∂μ else 0 := fun z => by
    split_ifs with hz
    · rw [← integral_indicator measurableSet_Ici]
      congr 1; ext x
      simp only [hF, indicator, mem_Ici]
      by_cases hzx : z ≤ x
      · rw [if_pos ⟨hz, hzx⟩, if_pos hzx]
      · rw [if_neg (fun h => hzx h.2), if_neg hzx]
    · have : ∀ x, F (z, x) = 0 := fun x => by
        simp only [hF]; rw [if_neg (fun h => hz h.1)]
      simp [this]
  have hinner_x : ∀ x, ∫ z, F (z, x) ∂π = (x - s) * π.real (Ioc s x) := fun x => by
    have : (fun z => F (z, x)) = (Ioc s x).indicator (fun _ => x - s) := by
      ext z
      simp only [hF, indicator, mem_Ioc]
    rw [this, integral_indicator_const _ measurableSet_Ioc, smul_eq_mul, mul_comm]
  -- the left side splits into the tail part and the kernel part
  have hsplit : ∀ z, gainKernel μ s z =
      (Ioi s).indicator (fun _ => (1 : ℝ)) z + ∫ x, F (z, x) ∂μ := fun z => by
    rw [hinner_z]
    unfold gainKernel
    simp only [indicator, mem_Ioi]
    split_ifs <;> ring
  have hint1 : Integrable ((Ioi s).indicator fun _ => (1 : ℝ)) π :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have hint2 : Integrable (fun z => ∫ x, F (z, x) ∂μ) π := hFint.integral_prod_left
  have hLHS : ∫ z, gainKernel μ s z ∂π =
      π.real (Ioi s) + ∫ x, (x - s) * π.real (Ioc s x) ∂μ := by
    simp_rw [hsplit]
    rw [integral_add hint1 hint2, integral_indicator_const _ measurableSet_Ioi, smul_eq_mul,
      mul_one]
    congr 1
    rw [integral_integral_swap (f := fun z x => F (z, x)) hFint]
    simp_rw [hinner_x]
  -- the right side
  have hmeasIoc : Measurable fun x => π.real (Ioc s x) :=
    (show Monotone fun x => π.real (Ioc s x) from fun _ _ hxy =>
      measureReal_mono (Ioc_subset_Ioc_right hxy)).measurable
  have hbdd1 : ∀ x ∈ Icc 0 bbar, |π.real (Ioc s x)| ≤ π.real univ := fun x _ => by
    rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_mono (subset_univ _)
  have hbdd2 : ∀ x ∈ Icc 0 bbar, |π.real (Ioi x)| ≤ π.real univ := fun x _ => by
    rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_mono (subset_univ _)
  have hi1 := integrable_sub_mul hsupp hmeasIoc.aestronglyMeasurable hbdd1 s
  have hi2 := integrable_sub_mul hsupp survival_measurable.aestronglyMeasurable hbdd2 s
  have hi3 := integrable_sub_mul hsupp (f := fun _ => π.real (Ioi s)) aestronglyMeasurable_const
    (B := |π.real (Ioi s)|) (fun _ _ => le_rfl) s
  have hRHS : ∫ x, (x - s) * π.real (Ioc s x) ∂μ =
      (Lbar μ s - 1) * π.real (Ioi s) - kernelIntegral bbar μ (fun t => π.real (Ioi t)) s := by
    have e1 : ∫ x, (x - s) * π.real (Ioc s x) ∂μ =
        ∫ x in Ioc s bbar, (x - s) * π.real (Ioc s x) ∂μ := by
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_mem_Icc_of_supp hsupp] with x hx
      by_cases hsx : s < x
      · rw [indicator_of_mem (show x ∈ Ioc s bbar from ⟨hsx, hx.2⟩)]
      · rw [indicator_of_notMem (fun h => hsx h.1), Ioc_eq_empty hsx]
        simp
    have e2 : ∫ x in Ioc s bbar, (x - s) * π.real (Ioc s x) ∂μ =
        ∫ x in Ioc s bbar, ((x - s) * π.real (Ioi s) - (x - s) * π.real (Ioi x)) ∂μ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      simp only
      rw [measureReal_Ioc_eq_sub hx.1.le]
      ring
    rw [e1, e2, integral_sub hi3.integrableOn hi2.integrableOn, integral_mul_const,
      ← Lbar_sub_one hsupp s]
    rfl
  rw [hLHS, hRHS]
  unfold gainFromMass
  ring

end Gain

end FixedPrice.TwoUnit.Pricing
