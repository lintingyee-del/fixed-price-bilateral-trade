import FixedPrice.TwoUnit.Pricing.OperatorKernel

/-!
# Theorem E, package A, part 2: the operator and its least fixed point

The operator `𝒯ϖ(s) = sup_{s ≤ t ≤ b̄} max {0, A₁ϖ(t), A₂ϖ(t)}` is a supremum over the future
interval `[s, b̄]`, so its output is nonincreasing on `[0, b̄]` whatever the input. Its obstacles
differ by `(K_{ϖ₁} - K_{ϖ₂})/L̄`, which the kernel bound and the certified scalar fact
`kernel_contraction` control by `b̄/(1+b̄)` times the input difference; `max_nonexpansive` passes
this through the maxima. The iteration from `0` increases, its successive differences decay
geometrically, and its limit (the supremum `leastMass`) is the unique bounded fixed point.
Right-continuity comes from the fact that the future supremum of a right-continuous function is
right-continuous.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-! ### Suprema over future intervals -/

section FutureSup

theorem csSup_image_le_csSup_image {S : Set ℝ} {f g : ℝ → ℝ} (hS : S.Nonempty)
    (hg : BddAbove (g '' S)) (h : ∀ x ∈ S, f x ≤ g x) : sSup (f '' S) ≤ sSup (g '' S) :=
  csSup_le (hS.image f) (by
    rintro _ ⟨x, hx, rfl⟩
    exact (h x hx).trans (le_csSup hg ⟨x, hx, rfl⟩))

theorem abs_csSup_image_sub_le {S : Set ℝ} {f g : ℝ → ℝ} (hS : S.Nonempty)
    (hf : BddAbove (f '' S)) (hg : BddAbove (g '' S)) {c : ℝ}
    (h : ∀ x ∈ S, |f x - g x| ≤ c) : |sSup (f '' S) - sSup (g '' S)| ≤ c := by
  have h1 : sSup (f '' S) ≤ sSup (g '' S) + c := by
    apply csSup_le (hS.image f)
    rintro _ ⟨x, hx, rfl⟩
    have := (abs_le.mp (h x hx)).2
    have := le_csSup hg ⟨x, hx, rfl⟩
    linarith
  have h2 : sSup (g '' S) ≤ sSup (f '' S) + c := by
    apply csSup_le (hS.image g)
    rintro _ ⟨x, hx, rfl⟩
    have := (abs_le.mp (h x hx)).1
    have := le_csSup hf ⟨x, hx, rfl⟩
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The future supremum of a function that is right-continuous on `[0, b̄]` is right-continuous
there: a strict drop of the future supremum just after `s` would need an isolated peak at `s`,
which right-continuity excludes. -/
theorem futureSup_rightContinuous {bbar : ℝ} {F : ℝ → ℝ} (hF : BddAbove (F '' Icc 0 bbar))
    (hcont : ∀ s ∈ Icc 0 bbar, ContinuousWithinAt F (Icc s bbar) s) {s : ℝ}
    (hs : s ∈ Icc 0 bbar) :
    ContinuousWithinAt (fun u => sSup (F '' Icc u bbar)) (Icc s bbar) s := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hbdd : ∀ u ∈ Icc 0 bbar, BddAbove (F '' Icc u bbar) := fun u hu =>
    hF.mono (image_mono (Icc_subset_Icc hu.1 le_rfl))
  have hne : ∀ u ∈ Icc 0 bbar, (Icc u bbar).Nonempty := fun u hu => ⟨u, le_rfl, hu.2⟩
  have hmem : ∀ u ∈ Icc s bbar, u ∈ Icc 0 bbar := fun u hu => ⟨hs.1.trans hu.1, hu.2⟩
  have hle : ∀ u ∈ Icc s bbar, sSup (F '' Icc u bbar) ≤ sSup (F '' Icc s bbar) := fun u hu =>
    csSup_le_csSup (hbdd s hs) ((hne u (hmem u hu)).image F)
      (image_mono (Icc_subset_Icc hu.1 le_rfl))
  obtain ⟨_, ⟨t, ht, rfl⟩, hFt⟩ := exists_lt_of_lt_csSup ((hne s hs).image F)
    (show sSup (F '' Icc s bbar) - ε < sSup (F '' Icc s bbar) by linarith)
  rcases eq_or_lt_of_le ht.1 with hts | hts
  · obtain rfl := hts
    obtain ⟨δ, hδ, hδF⟩ := Metric.continuousWithinAt_iff.mp (hcont s hs)
      (F s - (sSup (F '' Icc s bbar) - ε)) (by linarith)
    refine ⟨δ, hδ, fun {u} hu hdu => ?_⟩
    have hFu := hδF hu hdu
    have hGu : F u ≤ sSup (F '' Icc u bbar) :=
      le_csSup (hbdd u (hmem u hu)) ⟨u, ⟨le_rfl, hu.2⟩, rfl⟩
    have := hle u hu
    rw [Real.dist_eq, abs_lt] at hFu ⊢
    constructor <;> linarith [hFu.1]
  · refine ⟨t - s, by linarith, fun {u} hu hdu => ?_⟩
    rw [Real.dist_eq, abs_lt] at hdu
    have hut : u ≤ t := by linarith [hdu.2]
    have hGu : F t ≤ sSup (F '' Icc u bbar) :=
      le_csSup (hbdd u (hmem u hu)) ⟨t, ⟨hut, ht.2⟩, rfl⟩
    have := hle u hu
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

end FutureSup

/-! ### Bounds on the kernel and the obstacles -/

theorem abs_div_le_abs_of_one_le {x L : ℝ} (hL : 1 ≤ L) : |x / L| ≤ |x| := by
  rw [abs_div, abs_of_pos (show (0 : ℝ) < L by linarith)]
  exact div_le_self (abs_nonneg x) hL

theorem abs_compSign (i : Fin 2) : |compSign i| = 1 := by
  unfold compSign
  split_ifs <;> simp

theorem abs_kernelIntegral_le {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ} {B : ℝ} (hB : ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B)
    (s : ℝ) : |kernelIntegral bbar μ ϖ s| ≤ B * (Lbar μ s - 1) := by
  rw [kernelIntegral_eq_integral_max hsupp]
  have hLb : Lbar μ s - 1 = ∫ t, max (t - s) 0 ∂μ := by unfold Lbar; ring
  rw [hLb, ← integral_const_mul]
  have := norm_integral_le_of_norm_le ((integrable_max_sub hsupp s).const_mul B) (μ := μ)
    (f := fun t => max (t - s) 0 * ϖ t) (by
      filter_upwards [ae_mem_Icc_of_supp hsupp] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_max_right _ _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hB t ht) (le_max_right _ _))
  simpa [Real.norm_eq_abs] using this

/-- The kernel mass bound `|K|/L̄ ≤ (b̄/(1+b̄)) B` from the certified scalar fact. -/
theorem abs_kernel_div_le (cert : PricingScalarCertificates) {bbar : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0) {k B : ℝ} (hB0 : 0 ≤ B) {t : ℝ}
    (ht : 0 ≤ t) (hk : |k| ≤ B * (Lbar μ t - 1)) :
    |k / Lbar μ t| ≤ bbar / (1 + bbar) * B := by
  have hb := bbar_nonneg_of_supp hsupp
  have hL1 : 1 ≤ Lbar μ t := one_le_Lbar' μ t
  have hLb : Lbar μ t ≤ 1 + bbar := Lbar_le_one_add' hsupp ht
  have hL0 : 0 < Lbar μ t := by linarith
  have hc := cert.kernel_contraction bbar (Lbar μ t) B k hb hL1 (by linarith) hB0 hk
  rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0,
    show bbar / (1 + bbar) * B * Lbar μ t = bbar * B * Lbar μ t / (1 + bbar) by ring,
    le_div_iff₀ (by linarith)]
  linarith

section Operator

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d : ℝ} {ϑ : ℝ → ℝ}

/-- The integrand `max {0, A₁ϖ(t), A₂ϖ(t)}` of the operator. -/
def obsMax (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d : ℝ) (ϑ : ℝ → ℝ) (ϖ : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  max 0 (max (obstacle bbar law d ϑ 0 ϖ t) (obstacle bbar law d ϑ 1 ϖ t))

theorem pricingOperator_eq_sSup (ϖ : ℝ → ℝ) (s : ℝ) :
    pricingOperator bbar law d ϑ ϖ s = sSup (obsMax bbar law d ϑ ϖ '' Icc s bbar) := rfl

/-- Two-law good masses. -/
def GoodMass2 (bbar : ℝ) (law : Fin 2 → Measure ℝ) (ϖ : ℝ → ℝ) : Prop :=
  ∀ i, GoodMass bbar (law i) ϖ

theorem goodMass2_of_antitoneOn (hB : IsBuyerBodies bbar law) {ϖ : ℝ → ℝ}
    (hϖ : AntitoneOn ϖ (Icc 0 bbar)) : GoodMass2 bbar law ϖ := fun i => by
  haveI := hB.isProbability i
  exact goodMass_of_antitoneOn (hB.supported i) hϖ

theorem goodMass2_of_measurable {ϖ : ℝ → ℝ} (hϖ : Measurable ϖ)
    (hb : ∃ B, ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) : GoodMass2 bbar law ϖ := fun _ =>
  goodMass_of_measurable hϖ hb

/-- An obstacle bound that does not depend on the input's measurability. -/
theorem abs_obstacle_le (hB : IsBuyerBodies bbar law) (hd : 0 < d) {Cϑ : ℝ}
    (hϑ : ∀ x ∈ Icc 0 bbar, |ϑ x| ≤ Cϑ) {ϖ : ℝ → ℝ} {B : ℝ}
    (hϖ : ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) (i : Fin 2) {t : ℝ} (ht : t ∈ Icc 0 bbar) :
    |obstacle bbar law d ϑ i ϖ t| ≤ 1 + d * bbar + Cϑ + B * bbar := by
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  have hb := bbar_nonneg_of_supp hsupp
  have hL1 : 1 ≤ Lbar (law i) t := one_le_Lbar' _ _
  have hLb : Lbar (law i) t ≤ 1 + bbar := Lbar_le_one_add' hsupp ht.1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hϖ 0 ⟨le_rfl, hb⟩)
  have e1 : |d * t / Lbar (law i) t| ≤ d * bbar := by
    refine (abs_div_le_abs_of_one_le hL1).trans ?_
    rw [abs_of_nonneg (mul_nonneg hd.le ht.1)]
    exact mul_le_mul_of_nonneg_left ht.2 hd.le
  have e2 : |compSign i * ϑ t / Lbar (law i) t| ≤ Cϑ := by
    refine (abs_div_le_abs_of_one_le hL1).trans ?_
    rw [abs_mul, abs_compSign, one_mul]
    exact hϑ t ht
  have e3 : |kernelIntegral bbar (law i) ϖ t / Lbar (law i) t| ≤ B * bbar := by
    refine (abs_div_le_abs_of_one_le hL1).trans ?_
    refine (abs_kernelIntegral_le hsupp hϖ t).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hB0
  unfold obstacle
  have a1 := abs_le.mp e1
  have a2 := abs_le.mp e2
  have a3 := abs_le.mp e3
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

/-- The upper obstacle bound used for the iteration: for `|ϖ| ≤ B` on `[0, b̄]`,
`A_i ϖ(t) ≤ 1 + C_ϑ + (b̄/(1+b̄)) B`. -/
theorem obstacle_le_of_bound (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) {Cϑ : ℝ} (hϑ : ∀ x ∈ Icc 0 bbar, |ϑ x| ≤ Cϑ) {ϖ : ℝ → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hϖ : ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) (i : Fin 2) {t : ℝ}
    (ht : t ∈ Icc 0 bbar) :
    obstacle bbar law d ϑ i ϖ t ≤ 1 + Cϑ + bbar / (1 + bbar) * B := by
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  have hL1 : 1 ≤ Lbar (law i) t := one_le_Lbar' _ _
  have hL0 : 0 < Lbar (law i) t := by linarith
  have e1 : 0 ≤ d * t / Lbar (law i) t := div_nonneg (mul_nonneg hd.le ht.1) hL0.le
  have e2 : |compSign i * ϑ t / Lbar (law i) t| ≤ Cϑ := by
    refine (abs_div_le_abs_of_one_le hL1).trans ?_
    rw [abs_mul, abs_compSign, one_mul]
    exact hϑ t ht
  have e3 := abs_kernel_div_le cert hsupp hB0 ht.1 (abs_kernelIntegral_le hsupp hϖ t)
  unfold obstacle
  linarith [(abs_le.mp e2).2, (abs_le.mp e3).2]

theorem obsMax_nonneg (ϖ : ℝ → ℝ) (t : ℝ) : 0 ≤ obsMax bbar law d ϑ ϖ t := le_max_left _ _

theorem obsMax_le (hB : IsBuyerBodies bbar law) (hd : 0 < d) {Cϑ : ℝ}
    (hϑ : ∀ x ∈ Icc 0 bbar, |ϑ x| ≤ Cϑ) {ϖ : ℝ → ℝ} {B : ℝ}
    (hϖ : ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) {t : ℝ} (ht : t ∈ Icc 0 bbar) :
    obsMax bbar law d ϑ ϖ t ≤ 1 + d * bbar + Cϑ + B * bbar := by
  haveI := hB.isProbability 0
  have h0 := abs_obstacle_le hB hd hϑ hϖ 0 ht
  have h1 := abs_obstacle_le hB hd hϑ hϖ 1 ht
  have hb := bbar_nonneg_of_supp (μ := law 0) (hB.supported 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hϖ 0 ⟨le_rfl, hb⟩)
  have hC0 : 0 ≤ Cϑ := (abs_nonneg _).trans (hϑ 0 ⟨le_rfl, hb⟩)
  unfold obsMax
  refine max_le (by positivity) (max_le ?_ ?_)
  · exact (le_abs_self _).trans h0
  · exact (le_abs_self _).trans h1

theorem bddAbove_obsMax (hB : IsBuyerBodies bbar law) (hd : 0 < d)
    (hϑ : ∃ C, ∀ x ∈ Icc 0 bbar, |ϑ x| ≤ C) {ϖ : ℝ → ℝ}
    (hϖ : ∃ B, ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) {s : ℝ} (hs : 0 ≤ s) :
    BddAbove (obsMax bbar law d ϑ ϖ '' Icc s bbar) := by
  obtain ⟨C, hC⟩ := hϑ
  obtain ⟨B, hB'⟩ := hϖ
  refine ⟨1 + d * bbar + C + B * bbar, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact obsMax_le hB hd hC hB' ⟨hs.trans ht.1, ht.2⟩

variable (hB : IsBuyerBodies bbar law) (hd : 0 < d) (hϑ : ∃ C, ∀ x ∈ Icc 0 bbar, |ϑ x| ≤ C)
include hB hd hϑ

theorem le_pricingOperator {ϖ : ℝ → ℝ} (hϖ : ∃ B, ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) {s t : ℝ}
    (hs : 0 ≤ s) (ht : t ∈ Icc s bbar) :
    obsMax bbar law d ϑ ϖ t ≤ pricingOperator bbar law d ϑ ϖ s :=
  le_csSup (bddAbove_obsMax hB hd hϑ hϖ hs) ⟨t, ht, rfl⟩

theorem pricingOperator_nonneg {ϖ : ℝ → ℝ} (hϖ : ∃ B, ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) {s : ℝ}
    (hs : s ∈ Icc 0 bbar) : 0 ≤ pricingOperator bbar law d ϑ ϖ s :=
  (obsMax_nonneg ϖ s).trans (le_pricingOperator hB hd hϑ hϖ hs.1 ⟨le_rfl, hs.2⟩)

theorem pricingOperator_antitoneOn {ϖ : ℝ → ℝ} (hϖ : ∃ B, ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) :
    AntitoneOn (pricingOperator bbar law d ϑ ϖ) (Icc 0 bbar) := by
  intro a ha b hb hab
  exact csSup_le_csSup (bddAbove_obsMax hB hd hϑ hϖ ha.1)
    ((show (Icc b bbar).Nonempty from ⟨b, le_rfl, hb.2⟩).image _)
    (image_mono (Icc_subset_Icc hab le_rfl))

/-- Contraction of the operator on good masses. -/
theorem abs_pricingOperator_sub_le (cert : PricingScalarCertificates) {ϖ₁ ϖ₂ : ℝ → ℝ}
    (h₁ : GoodMass2 bbar law ϖ₁) (h₂ : GoodMass2 bbar law ϖ₂) {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ t ∈ Icc 0 bbar, |ϖ₁ t - ϖ₂ t| ≤ E) {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    |pricingOperator bbar law d ϑ ϖ₁ s - pricingOperator bbar law d ϑ ϖ₂ s| ≤
      bbar / (1 + bbar) * E := by
  haveI := hB.isProbability 0
  have hb := bbar_nonneg_of_supp (μ := law 0) (hB.supported 0)
  have hq0 : 0 ≤ bbar / (1 + bbar) * E := by positivity
  have hobs : ∀ i : Fin 2, ∀ t ∈ Icc 0 bbar,
      |obstacle bbar law d ϑ i ϖ₁ t - obstacle bbar law d ϑ i ϖ₂ t| ≤
        bbar / (1 + bbar) * E := by
    intro i t ht
    haveI := hB.isProbability i
    have hsupp := hB.supported i
    have e : obstacle bbar law d ϑ i ϖ₁ t - obstacle bbar law d ϑ i ϖ₂ t =
        (kernelIntegral bbar (law i) ϖ₁ t - kernelIntegral bbar (law i) ϖ₂ t) /
          Lbar (law i) t := by
      unfold obstacle; ring
    rw [e]
    exact abs_kernel_div_le cert hsupp hE0 ht.1
      (abs_kernelIntegral_sub_le hsupp (h₁ i) (h₂ i) hE t)
  refine abs_csSup_image_sub_le (show (Icc s bbar).Nonempty from ⟨s, le_rfl, hs.2⟩)
    (bddAbove_obsMax hB hd hϑ (h₁ 0).bound hs.1) (bddAbove_obsMax hB hd hϑ (h₂ 0).bound hs.1)
    fun t ht => ?_
  have ht' : t ∈ Icc 0 bbar := ⟨hs.1.trans ht.1, ht.2⟩
  exact cert.max_nonexpansive _ _ _ _ _ hq0 (hobs 0 t ht') (hobs 1 t ht')

/-- The operator is order-preserving on good masses. -/
theorem pricingOperator_mono {ϖ₁ ϖ₂ : ℝ → ℝ} (h₁ : GoodMass2 bbar law ϖ₁)
    (h₂ : GoodMass2 bbar law ϖ₂) (hle : ∀ t ∈ Icc 0 bbar, ϖ₁ t ≤ ϖ₂ t) {s : ℝ}
    (hs : s ∈ Icc 0 bbar) :
    pricingOperator bbar law d ϑ ϖ₁ s ≤ pricingOperator bbar law d ϑ ϖ₂ s := by
  have hobs : ∀ i : Fin 2, ∀ t ∈ Icc 0 bbar,
      obstacle bbar law d ϑ i ϖ₁ t ≤ obstacle bbar law d ϑ i ϖ₂ t := by
    intro i t ht
    haveI := hB.isProbability i
    have hsupp := hB.supported i
    have hL0 : 0 < Lbar (law i) t := by linarith [one_le_Lbar' (law i) t]
    have hK := kernelIntegral_mono_of_le hsupp (h₁ i) (h₂ i) (s := t)
      (fun u hu => hle u ⟨ht.1.trans hu.1.le, hu.2⟩)
    unfold obstacle
    have := div_le_div_of_nonneg_right hK hL0.le
    linarith
  refine csSup_image_le_csSup_image (show (Icc s bbar).Nonempty from ⟨s, le_rfl, hs.2⟩)
    (bddAbove_obsMax hB hd hϑ (h₂ 0).bound hs.1) fun t ht => ?_
  have ht' : t ∈ Icc 0 bbar := ⟨hs.1.trans ht.1, ht.2⟩
  exact max_le_max le_rfl (max_le_max (hobs 0 t ht') (hobs 1 t ht'))

end Operator

end FixedPrice.TwoUnit.Pricing
