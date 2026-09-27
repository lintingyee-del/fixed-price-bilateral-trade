import FixedPrice.TwoUnit.Pricing.Statements

/-!
# Theorem E, package A, part 1: the kernel

Internal lemmas of package A about `L̄` and the positive kernel
`K_ϖ(s) = ∫_{(s,b̄]} (t - s) ϖ(t) (-dH)(t)` for a buyer law supported on `[0, b̄]`.

The one identity everything rests on: on the support of the law,
`∫_{(s,b̄]} (t - s) ϖ(t) dμ = ∫ max (t - s) 0 · ϖ(t) dμ` for every `s`, because a body value
`t ∈ [0, b̄]` lies in `(s, b̄]` exactly when `t > s`. In the second form the dependence on `s` is
Lipschitz, which gives the continuity of the kernel without any limit argument.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section Support

variable {bbar : ℝ} {μ : Measure ℝ}

theorem ae_mem_Icc_of_supp (hsupp : μ (Icc 0 bbar)ᶜ = 0) : ∀ᵐ x ∂μ, x ∈ Icc 0 bbar :=
  mem_ae_iff.mpr hsupp

theorem restrict_Icc_of_supp (hsupp : μ (Icc 0 bbar)ᶜ = 0) : μ.restrict (Icc 0 bbar) = μ :=
  Measure.restrict_eq_self_of_ae_mem (ae_mem_Icc_of_supp hsupp)

theorem bbar_nonneg_of_supp [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0) :
    0 ≤ bbar := by
  by_contra h
  push Not at h
  have : Icc (0 : ℝ) bbar = ∅ := Icc_eq_empty (by linarith)
  rw [this, compl_empty, measure_univ] at hsupp
  exact one_ne_zero hsupp

/-- A function that is a.e.-strongly measurable and bounded on `[0, b̄]` is integrable. -/
theorem integrable_of_bdd_on_supp [IsFiniteMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ x ∈ Icc 0 bbar, |f x| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf C ((ae_mem_Icc_of_supp hsupp).mono fun x hx => by
    rw [Real.norm_eq_abs]; exact hC x hx)

theorem aestronglyMeasurable_of_antitoneOn (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (hϖ : AntitoneOn ϖ (Icc 0 bbar)) : AEStronglyMeasurable ϖ μ := by
  rw [← restrict_Icc_of_supp hsupp]
  exact (aemeasurable_restrict_of_antitoneOn measurableSet_Icc hϖ).aestronglyMeasurable

end Support

theorem abs_le_of_antitoneOn {bbar : ℝ} (hb : 0 ≤ bbar) {ϖ : ℝ → ℝ}
    (hϖ : AntitoneOn ϖ (Icc 0 bbar)) : ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ max |ϖ 0| |ϖ bbar| := by
  intro x hx
  have h0 : (0 : ℝ) ∈ Icc 0 bbar := ⟨le_rfl, hb⟩
  have hb' : bbar ∈ Icc 0 bbar := ⟨hb, le_rfl⟩
  have h1 : ϖ x ≤ ϖ 0 := hϖ h0 hx hx.1
  have h2 : ϖ bbar ≤ ϖ x := hϖ hx hb' hx.2
  have h3 := neg_abs_le (ϖ bbar)
  have h4 := le_abs_self (ϖ 0)
  have h5 := le_max_left |ϖ 0| |ϖ bbar|
  have h6 := le_max_right |ϖ 0| |ϖ bbar|
  rw [abs_le]
  constructor <;> linarith

section Kernel

variable {bbar : ℝ} {μ : Measure ℝ}

/-- On the support, the positive kernel is an integral against `max (t - s) 0`. -/
theorem kernelIntegral_eq_integral_max (hsupp : μ (Icc 0 bbar)ᶜ = 0) (ϖ : ℝ → ℝ) (s : ℝ) :
    kernelIntegral bbar μ ϖ s = ∫ t, max (t - s) 0 * ϖ t ∂μ := by
  unfold kernelIntegral
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_mem_Icc_of_supp hsupp] with t ht
  by_cases hts : s < t
  · rw [indicator_of_mem (show t ∈ Ioc s bbar from ⟨hts, ht.2⟩), max_eq_left (by linarith)]
  · rw [indicator_of_notMem (fun h => hts h.1), max_eq_right (by linarith), zero_mul]

theorem abs_max_sub_le (t s : ℝ) (hb : 0 ≤ bbar) (ht : t ∈ Icc 0 bbar) :
    |max (t - s) 0| ≤ bbar + |s| := by
  rw [abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ (by positivity)
  have := neg_abs_le s
  linarith [ht.2]

theorem abs_sub_le_of_mem (t s : ℝ) (ht : t ∈ Icc 0 bbar) : |t - s| ≤ bbar + |s| := by
  have h1 := abs_sub t s
  rw [abs_of_nonneg ht.1] at h1
  linarith [ht.2]

variable [IsProbabilityMeasure μ]

/-- `(t - s) f(t)` is integrable for `f` a.e.-strongly measurable and bounded on `[0, b̄]`. -/
theorem integrable_sub_mul (hsupp : μ (Icc 0 bbar)ᶜ = 0) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x ∈ Icc 0 bbar, |f x| ≤ B) (s : ℝ) :
    Integrable (fun t => (t - s) * f t) μ := by
  have hb := bbar_nonneg_of_supp hsupp
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, hb⟩)
  refine integrable_of_bdd_on_supp hsupp
    (((continuous_id.sub continuous_const).aestronglyMeasurable).mul hf) (C := (bbar + |s|) * B)
    fun t ht => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_sub_le_of_mem t s ht) (hB t ht) (abs_nonneg _) (by positivity)

/-- `max (t - s) 0 · f(t)` is integrable for `f` a.e.-strongly measurable and bounded on
`[0, b̄]`. -/
theorem integrable_max_sub_mul (hsupp : μ (Icc 0 bbar)ᶜ = 0) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x ∈ Icc 0 bbar, |f x| ≤ B) (s : ℝ) :
    Integrable (fun t => max (t - s) 0 * f t) μ := by
  have hb := bbar_nonneg_of_supp hsupp
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, hb⟩)
  refine integrable_of_bdd_on_supp hsupp
    ((((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable).mul hf)
    (C := (bbar + |s|) * B) fun t ht => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_max_sub_le t s hb ht) (hB t ht) (abs_nonneg _) (by positivity)

theorem integrable_max_sub (hsupp : μ (Icc 0 bbar)ᶜ = 0) (s : ℝ) :
    Integrable (fun x => max (x - s) 0) μ := by
  have := integrable_max_sub_mul hsupp (f := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (B := 1) (fun _ _ => by simp) s
  simpa using this

theorem one_le_Lbar' (μ : Measure ℝ) (s : ℝ) : 1 ≤ Lbar μ s := by
  unfold Lbar
  have : 0 ≤ ∫ x, max (x - s) 0 ∂μ := integral_nonneg fun x => le_max_right _ _
  linarith

omit [IsProbabilityMeasure μ] in
/-- `L̄(s) - 1 = ∫_{(s,b̄]} (t - s) dμ`. -/
theorem Lbar_sub_one (hsupp : μ (Icc 0 bbar)ᶜ = 0) (s : ℝ) :
    Lbar μ s - 1 = ∫ t in Ioc s bbar, (t - s) ∂μ := by
  have h := kernelIntegral_eq_integral_max hsupp (fun _ => (1 : ℝ)) s
  simp only [kernelIntegral, mul_one] at h
  rw [h]
  unfold Lbar
  ring

omit [IsProbabilityMeasure μ] in
theorem kernelIntegral_const' (hsupp : μ (Icc 0 bbar)ᶜ = 0) (c s : ℝ) :
    kernelIntegral bbar μ (fun _ => c) s = c * (Lbar μ s - 1) := by
  unfold kernelIntegral
  rw [integral_mul_const, ← Lbar_sub_one hsupp s, mul_comm]

theorem Lbar_le_one_add' (hsupp : μ (Icc 0 bbar)ᶜ = 0) {s : ℝ} (hs : 0 ≤ s) :
    Lbar μ s ≤ 1 + bbar := by
  have hb := bbar_nonneg_of_supp hsupp
  unfold Lbar
  have : ∫ x, max (x - s) 0 ∂μ ≤ ∫ _x, bbar ∂μ := by
    refine integral_mono_of_nonneg (ae_of_all _ fun x => le_max_right _ _) (integrable_const _) ?_
    filter_upwards [ae_mem_Icc_of_supp hsupp] with x hx
    exact max_le (by linarith [hx.2]) hb
  simp only [integral_const, probReal_univ, one_smul] at this
  linarith

omit [IsProbabilityMeasure μ] in
theorem Lbar_eq_one_of_le' (hsupp : μ (Icc 0 bbar)ᶜ = 0) {s : ℝ} (hs : bbar ≤ s) :
    Lbar μ s = 1 := by
  unfold Lbar
  have : ∫ x, max (x - s) 0 ∂μ = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_mem_Icc_of_supp hsupp] with x hx
    simp only [Pi.zero_apply]
    exact max_eq_right (by linarith [hx.2])
  rw [this, add_zero]

theorem Lbar_lipschitz' (hsupp : μ (Icc 0 bbar)ᶜ = 0) : LipschitzWith 1 (Lbar μ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  unfold Lbar
  have hsub : (1 + ∫ t, max (t - x) 0 ∂μ) - (1 + ∫ t, max (t - y) 0 ∂μ) =
      ∫ t, (max (t - x) 0 - max (t - y) 0) ∂μ := by
    rw [integral_sub (integrable_max_sub hsupp x) (integrable_max_sub hsupp y)]
    ring
  rw [hsub]
  have := norm_integral_le_of_norm_le (integrable_const |x - y|) (μ := μ)
    (f := fun t => max (t - x) 0 - max (t - y) 0) (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs]
      have := abs_max_sub_max_le_abs (t - x) (t - y) 0
      rw [show t - x - (t - y) = y - x by ring, abs_sub_comm y x] at this
      exact this)
  simpa [Real.norm_eq_abs] using this

theorem self_add_Lbar' (hsupp : μ (Icc 0 bbar)ᶜ = 0) (s : ℝ) :
    s + Lbar μ s = 1 + ∫ x, max x s ∂μ := by
  have h : ∀ x : ℝ, max x s = s + max (x - s) 0 := fun x => by
    rcases le_total x s with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  simp_rw [h]
  rw [integral_add (integrable_const s) (integrable_max_sub hsupp s)]
  simp only [integral_const, probReal_univ, one_smul]
  unfold Lbar
  ring

/-- Masses that are a.e.-strongly measurable and bounded on `[0, b̄]` (for instance antitone on
`[0, b̄]`, or measurable and bounded there). -/
structure GoodMass (bbar : ℝ) (μ : Measure ℝ) (ϖ : ℝ → ℝ) : Prop where
  aesm : AEStronglyMeasurable ϖ μ
  bound : ∃ B, ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B

theorem goodMass_of_antitoneOn (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (hϖ : AntitoneOn ϖ (Icc 0 bbar)) : GoodMass bbar μ ϖ :=
  ⟨aestronglyMeasurable_of_antitoneOn hsupp hϖ,
    ⟨_, abs_le_of_antitoneOn (bbar_nonneg_of_supp hsupp) hϖ⟩⟩

omit [IsProbabilityMeasure μ] in
theorem goodMass_of_measurable {ϖ : ℝ → ℝ} (hϖ : Measurable ϖ)
    (hB : ∃ B, ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) : GoodMass bbar μ ϖ :=
  ⟨hϖ.aestronglyMeasurable, hB⟩

theorem GoodMass.integrable_sub_mul (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (h : GoodMass bbar μ ϖ) (s : ℝ) : Integrable (fun t => (t - s) * ϖ t) μ := by
  obtain ⟨B, hB⟩ := h.bound
  exact Pricing.integrable_sub_mul hsupp h.aesm hB s

theorem GoodMass.integrable_max_sub_mul (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (h : GoodMass bbar μ ϖ) (s : ℝ) : Integrable (fun t => max (t - s) 0 * ϖ t) μ := by
  obtain ⟨B, hB⟩ := h.bound
  exact Pricing.integrable_max_sub_mul hsupp h.aesm hB s

/-- The kernel is linear in the mass. -/
theorem kernelIntegral_linear (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ₁ ϖ₂ : ℝ → ℝ}
    (h₁ : GoodMass bbar μ ϖ₁) (h₂ : GoodMass bbar μ ϖ₂) (a b s : ℝ) :
    kernelIntegral bbar μ (fun t => a * ϖ₁ t + b * ϖ₂ t) s =
      a * kernelIntegral bbar μ ϖ₁ s + b * kernelIntegral bbar μ ϖ₂ s := by
  simp only [kernelIntegral_eq_integral_max hsupp]
  have e : ∀ t, max (t - s) 0 * (a * ϖ₁ t + b * ϖ₂ t) =
      a * (max (t - s) 0 * ϖ₁ t) + b * (max (t - s) 0 * ϖ₂ t) := fun t => by ring
  simp_rw [e]
  rw [integral_add ((h₁.integrable_max_sub_mul hsupp s).const_mul a)
    ((h₂.integrable_max_sub_mul hsupp s).const_mul b), integral_const_mul, integral_const_mul]

/-- The kernel difference is controlled by `E (L̄ - 1)` when `|ϖ₁ - ϖ₂| ≤ E` on `[0, b̄]`. -/
theorem abs_kernelIntegral_sub_le (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ₁ ϖ₂ : ℝ → ℝ}
    (h₁ : GoodMass bbar μ ϖ₁) (h₂ : GoodMass bbar μ ϖ₂) {E : ℝ}
    (hE : ∀ t ∈ Icc 0 bbar, |ϖ₁ t - ϖ₂ t| ≤ E) (s : ℝ) :
    |kernelIntegral bbar μ ϖ₁ s - kernelIntegral bbar μ ϖ₂ s| ≤ E * (Lbar μ s - 1) := by
  simp only [kernelIntegral_eq_integral_max hsupp]
  rw [← integral_sub (h₁.integrable_max_sub_mul hsupp s) (h₂.integrable_max_sub_mul hsupp s)]
  have hLb : Lbar μ s - 1 = ∫ t, max (t - s) 0 ∂μ := by unfold Lbar; ring
  rw [hLb, ← integral_const_mul]
  have := norm_integral_le_of_norm_le ((integrable_max_sub hsupp s).const_mul E) (μ := μ)
    (f := fun t => max (t - s) 0 * ϖ₁ t - max (t - s) 0 * ϖ₂ t) (by
      filter_upwards [ae_mem_Icc_of_supp hsupp] with t ht
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (le_max_right _ _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hE t ht) (le_max_right _ _))
  simpa [Real.norm_eq_abs] using this

/-- The kernel is order-preserving (on masses that are good for the law). -/
theorem kernelIntegral_mono_of_le (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ ϖ' : ℝ → ℝ}
    (h : GoodMass bbar μ ϖ) (h' : GoodMass bbar μ ϖ') {s : ℝ}
    (hle : ∀ t ∈ Ioc s bbar, ϖ t ≤ ϖ' t) :
    kernelIntegral bbar μ ϖ s ≤ kernelIntegral bbar μ ϖ' s := by
  unfold kernelIntegral
  exact setIntegral_mono_on (h.integrable_sub_mul hsupp s).integrableOn
    (h'.integrable_sub_mul hsupp s).integrableOn measurableSet_Ioc fun t ht =>
      mul_le_mul_of_nonneg_left (hle t ht) (by linarith [ht.1])

/-- The kernel is Lipschitz in `s`, with constant a bound of `|ϖ|` on `[0, b̄]`. -/
theorem abs_kernelIntegral_sub_le_of_bound (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (h : GoodMass bbar μ ϖ) {B : ℝ} (hB : ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B) (s s' : ℝ) :
    |kernelIntegral bbar μ ϖ s - kernelIntegral bbar μ ϖ s'| ≤ B * |s - s'| := by
  simp only [kernelIntegral_eq_integral_max hsupp]
  rw [← integral_sub (h.integrable_max_sub_mul hsupp s) (h.integrable_max_sub_mul hsupp s')]
  have := norm_integral_le_of_norm_le (integrable_const (B * |s - s'|)) (μ := μ)
    (f := fun t => max (t - s) 0 * ϖ t - max (t - s') 0 * ϖ t) (by
      filter_upwards [ae_mem_Icc_of_supp hsupp] with t ht
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul, mul_comm]
      have h1 := abs_max_sub_max_le_abs (t - s) (t - s') 0
      rw [show t - s - (t - s') = s' - s by ring, abs_sub_comm s' s] at h1
      exact mul_le_mul (hB t ht) h1 (abs_nonneg _)
        ((abs_nonneg _).trans (hB 0 ⟨le_rfl, bbar_nonneg_of_supp hsupp⟩)))
  simpa [Real.norm_eq_abs] using this

theorem continuous_kernelIntegral (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (h : GoodMass bbar μ ϖ) : Continuous (kernelIntegral bbar μ ϖ) := by
  obtain ⟨B, hB⟩ := h.bound
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, bbar_nonneg_of_supp hsupp⟩)
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal B) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hB0]
  exact abs_kernelIntegral_sub_le_of_bound hsupp h hB x y

/-- The gain in the form `ϖ(s) + E[(Z - s)_+ (ϖ(s) - ϖ(Z))]`. -/
theorem gainFromMass_eq' (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (h : GoodMass bbar μ ϖ) (s : ℝ) :
    gainFromMass bbar μ ϖ s = ϖ s + ∫ t in Ioc s bbar, (t - s) * (ϖ s - ϖ t) ∂μ := by
  have e : ∀ t, (t - s) * (ϖ s - ϖ t) = (t - s) * ϖ s - (t - s) * ϖ t := fun t => by ring
  simp_rw [e]
  have hi1 : Integrable (fun t => (t - s) * ϖ s) μ :=
    integrable_sub_mul hsupp (f := fun _ => ϖ s) aestronglyMeasurable_const
      (B := |ϖ s|) (fun _ _ => le_rfl) s
  rw [integral_sub hi1.integrableOn (h.integrable_sub_mul hsupp s).integrableOn,
    integral_mul_const, ← Lbar_sub_one hsupp s]
  unfold gainFromMass kernelIntegral
  ring

theorem sellerPotential_convexComb' (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ₁ ϖ₂ : ℝ → ℝ}
    (h₁ : GoodMass bbar μ ϖ₁) (h₂ : GoodMass bbar μ ϖ₂) (a d₁ d₂ s : ℝ) :
    sellerPotential bbar μ (a * d₁ + (1 - a) * d₂) (fun t => a * ϖ₁ t + (1 - a) * ϖ₂ t) s =
      a * sellerPotential bbar μ d₁ ϖ₁ s + (1 - a) * sellerPotential bbar μ d₂ ϖ₂ s := by
  unfold sellerPotential gainFromMass
  rw [kernelIntegral_linear hsupp h₁ h₂]
  ring

theorem sellerPotential_add_const' (hsupp : μ (Icc 0 bbar)ᶜ = 0) {ϖ : ℝ → ℝ}
    (h : GoodMass bbar μ ϖ) (d c s : ℝ) :
    sellerPotential bbar μ d (fun t => ϖ t + c) s = sellerPotential bbar μ d ϖ s + c := by
  have hc : GoodMass bbar μ (fun _ => c) :=
    ⟨aestronglyMeasurable_const, ⟨|c|, fun _ _ => le_rfl⟩⟩
  have hlin := kernelIntegral_linear hsupp h hc 1 1 s
  simp only [one_mul] at hlin
  unfold sellerPotential gainFromMass
  rw [hlin, kernelIntegral_const' hsupp]
  ring

end Kernel

end FixedPrice.TwoUnit.Pricing
