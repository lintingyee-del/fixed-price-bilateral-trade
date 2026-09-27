import FixedPrice.TwoUnit.Family.RealizationPhi

/-!
# Work package E, realization helpers: the approximating instances

For `n : ℕ` put `x_n = b_f + 3 + n` and `η_n = 1/x_n ∈ (0, 1/3]`. The `n`-th instance has

* buyer law `(1 - η_n) · law(Z₁ + η_n, a_f + η_n) + η_n · δ_{(x_n, x_n)}` (both buyer bodies
  shifted up by `η_n`, weight `1 - η_n`, and a common escaping atom of mass `η_n` at `x_n`, whose
  first moment per unit is `η_n x_n = 1`);
* seller law `law(Y₁ + 2η_n, Y₂ + 2η_n)` (both sellers shifted up by `2η_n`, strictly more than the
  buyers, which separates coincident buyer and seller atoms).

Body values stay below `b_f + 1 < x_n`. This file proves validity, the escaping atom, the weak
convergence of the laws to the body laws, and the decomposition of integrals against the
independent joint law.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal
open FixedPrice.TwoUnit (GenInstance HasCommonEscapingAtom LawsConvergeTo unitGain)

namespace FixedPrice.TwoUnit.Family

namespace Realize

variable {θ : Params} {P : ℝ → ℝ}

/-! ### The approximation parameters -/

/-- The location `x_n = b_f + 3 + n` of the escaping buyer atom. -/
def xAt (θ : Params) (P : ℝ → ℝ) (n : ℕ) : ℝ := bF θ P + 3 + n

/-- The mass `η_n = 1/x_n` of the escaping buyer atom (also the buyer shift). -/
def ηAt (θ : Params) (P : ℝ → ℝ) (n : ℕ) : ℝ := (xAt θ P n)⁻¹

theorem three_le_xAt (hP : InClass θ P) (n : ℕ) : 3 ≤ xAt θ P n := by
  unfold xAt
  have := bF_nonneg hP
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem ηAt_pos (hP : InClass θ P) (n : ℕ) : 0 < ηAt θ P n := by
  unfold ηAt; have := three_le_xAt hP n; positivity

theorem ηAt_le (hP : InClass θ P) (n : ℕ) : ηAt θ P n ≤ 1 / 3 := by
  unfold ηAt
  rw [one_div]
  exact inv_anti₀ (by norm_num) (three_le_xAt hP n)

theorem ηAt_mul_xAt (hP : InClass θ P) (n : ℕ) : ηAt θ P n * xAt θ P n = 1 := by
  unfold ηAt
  have := three_le_xAt hP n
  field_simp

theorem tendsto_xAt (θ : Params) (P : ℝ → ℝ) : Tendsto (xAt θ P) atTop atTop := by
  unfold xAt
  exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop

theorem tendsto_ηAt (θ : Params) (P : ℝ → ℝ) : Tendsto (ηAt θ P) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_xAt θ P)

/-! ### The instances -/

/-- The shifted buyer body map `u ↦ (Z₁ + η, a_f + η)`. -/
def fB (θ : Params) (P : ℝ → ℝ) (η : ℝ) (u : ℝ) : ℝ × ℝ := (Zf θ P u + η, θ.a + η)

/-- The shifted seller map `v ↦ (Y₁ + 2η, Y₂ + 2η)`. -/
def fS (θ : Params) (P : ℝ → ℝ) (η : ℝ) (v : ℝ) : ℝ × ℝ := (Y₁f θ P v + 2 * η, Y₂f θ P v + 2 * η)

theorem measurable_fB (hP : InClass θ P) (η : ℝ) : Measurable (fB θ P η) :=
  ((measurable_Zf hP).add_const η).prodMk measurable_const

theorem measurable_fS (hI : FamilyIdentities) (hP : InClass θ P) (η : ℝ) :
    Measurable (fS θ P η) :=
  ((measurable_Y₁f hI hP).add_const _).prodMk ((measurable_Y₂f hP).add_const _)

/-- The buyer law: shifted body with weight `1 - η`, plus the atom `η δ_{(x, x)}`. -/
def buyerLaw (θ : Params) (P : ℝ → ℝ) (η x : ℝ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (1 - η) • unifLaw.map (fB θ P η) + ENNReal.ofReal η • Measure.dirac (x, x)

/-- The seller law: the seller body shifted by `2η`. -/
def sellerLaw (θ : Params) (P : ℝ → ℝ) (η : ℝ) : Measure (ℝ × ℝ) := unifLaw.map (fS θ P η)

/-- The `n`-th approximating instance. -/
def inst (θ : Params) (P : ℝ → ℝ) (n : ℕ) : GenInstance :=
  ⟨buyerLaw θ P (ηAt θ P n) (xAt θ P n), sellerLaw θ P (ηAt θ P n)⟩

/-! ### General integration facts -/

/-- A bounded measurable function of a measurable image of the uniform law is integrable. -/
theorem integrable_map_unif {f : ℝ → ℝ × ℝ} (hf : Measurable f) {g : ℝ × ℝ → ℝ}
    (hg : Measurable g) {K : ℝ} (hK : ∀ u, |g (f u)| ≤ K) : Integrable g (unifLaw.map f) := by
  rw [integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable]
  exact integrable_unif_of_bound (hg.comp hf) hK

/-- Integrals against a mixture of a uniform image and a Dirac mass. -/
theorem integral_mix {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {x : ℝ × ℝ} {f : ℝ → ℝ × ℝ}
    (hf : Measurable f) {g : ℝ × ℝ → ℝ} (hg : Measurable g) {K : ℝ} (hK : ∀ u, |g (f u)| ≤ K) :
    ∫ b, g b ∂(ENNReal.ofReal (1 - η) • unifLaw.map f + ENNReal.ofReal η • Measure.dirac x) =
      (1 - η) * ∫ u, g (f u) ∂unifLaw + η * g x := by
  have hi1 : Integrable g (unifLaw.map f) := integrable_map_unif hf hg hK
  have hi2 : Integrable g (Measure.dirac x) := integrable_dirac (by simp)
  rw [integral_add_measure (hi1.smul_measure ENNReal.ofReal_ne_top)
      (hi2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_map hf.aemeasurable hg.aestronglyMeasurable, integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hη0, smul_eq_mul, smul_eq_mul]

/-- Integrals against the independent joint law of a mixture buyer and a uniform-image seller. -/
theorem integral_joint {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {x : ℝ × ℝ} {f g : ℝ → ℝ × ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hF : Measurable F)
    {K : ℝ} (hK : ∀ u v, |F (f u, g v)| ≤ K) (hKx : ∀ v, |F (x, g v)| ≤ K) :
    ∫ q, F q ∂((ENNReal.ofReal (1 - η) • unifLaw.map f + ENNReal.ofReal η • Measure.dirac x).prod
        (unifLaw.map g)) =
      (1 - η) * ∫ q, F (f q.1, g q.2) ∂(unifLaw.prod unifLaw) +
        η * ∫ v, F (x, g v) ∂unifLaw := by
  have hprod1 : (unifLaw.map f).prod (unifLaw.map g) =
      (unifLaw.prod unifLaw).map (Prod.map f g) := Measure.map_prod_map _ _ hf hg
  have hprod2 : (Measure.dirac x).prod (unifLaw.map g) = (unifLaw.map g).map (Prod.mk x) :=
    Measure.dirac_prod x
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left, hprod1, hprod2]
  have hi1 : Integrable F ((unifLaw.prod unifLaw).map (Prod.map f g)) := by
    rw [integrable_map_measure hF.aestronglyMeasurable (hf.prodMap hg).aemeasurable]
    exact integrable_prod_of_bound (hF.comp (hf.prodMap hg)) (fun q => hK q.1 q.2)
  have hi2 : Integrable F ((unifLaw.map g).map (Prod.mk x)) := by
    rw [integrable_map_measure hF.aestronglyMeasurable measurable_prodMk_left.aemeasurable,
      integrable_map_measure (hF.comp measurable_prodMk_left).aestronglyMeasurable
        hg.aemeasurable]
    exact integrable_unif_of_bound ((hF.comp measurable_prodMk_left).comp hg) hKx
  rw [integral_add_measure (hi1.smul_measure ENNReal.ofReal_ne_top)
      (hi2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_map (hf.prodMap hg).aemeasurable hF.aestronglyMeasurable,
    integral_map measurable_prodMk_left.aemeasurable hF.aestronglyMeasurable,
    integral_map hg.aemeasurable
      (show Measurable (fun y => F (x, y)) from hF.comp measurable_prodMk_left).aestronglyMeasurable,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hη0, smul_eq_mul, smul_eq_mul]
  rfl

/-- Dominated convergence along a vanishing parameter. -/
theorem tendsto_integral_param {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {G : ℝ → α → ℝ} (hG : ∀ t, Measurable (G t))
    (hcont : ∀ a, ContinuousAt (fun t => G t a) 0) {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    {B : ℝ} (hB : ∀ n a, |G (η n) a| ≤ B) :
    Tendsto (fun n => ∫ a, G (η n) a ∂μ) atTop (𝓝 (∫ a, G 0 a ∂μ)) :=
  tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (hG (η n)).aestronglyMeasurable) (integrable_const B)
    (fun n => ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact hB n a)
    (ae_of_all _ fun a => (hcont a).tendsto.comp hη)

/-! ### Bounds on the instance values -/

theorem fB_fst_le (hP : InClass θ P) (n : ℕ) (u : ℝ) :
    Zf θ P u + ηAt θ P n < xAt θ P n := by
  have h1 := Zf_le_bF hP u
  have h2 := ηAt_le hP n
  unfold xAt
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem a_shift_lt (hP : InClass θ P) (n : ℕ) : θ.a + ηAt θ P n < xAt θ P n := by
  have h1 := a_le_bF hP
  have h2 := ηAt_le hP n
  unfold xAt
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem Y₁_shift_lt (hP : InClass θ P) (n : ℕ) (v : ℝ) :
    Y₁f θ P v + 2 * ηAt θ P n < xAt θ P n := by
  have h1 := Y₁f_le_bF hP v
  have h2 := ηAt_le hP n
  unfold xAt
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem Y₂_shift_lt (hP : InClass θ P) (n : ℕ) (v : ℝ) :
    Y₂f θ P v + 2 * ηAt θ P n < xAt θ P n := by
  have h1 := Y₂f_le_bF hP v
  have h2 := ηAt_le hP n
  unfold xAt
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-! ### Validity -/

theorem isProbabilityMeasure_buyerLaw (hP : InClass θ P) (n : ℕ) :
    IsProbabilityMeasure (buyerLaw θ P (ηAt θ P n) (xAt θ P n)) := by
  haveI : IsProbabilityMeasure (unifLaw.map (fB θ P (ηAt θ P n))) :=
    Measure.isProbabilityMeasure_map (measurable_fB hP _).aemeasurable
  have hη := ηAt_pos hP n
  have hη1 := ηAt_le hP n
  constructor
  unfold buyerLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) hη.le]
  simp

theorem isProbabilityMeasure_sellerLaw (hI : FamilyIdentities) (hP : InClass θ P) (η : ℝ) :
    IsProbabilityMeasure (sellerLaw θ P η) :=
  Measure.isProbabilityMeasure_map (measurable_fS hI hP η).aemeasurable

theorem inst_valid (hI : FamilyIdentities) (hP : InClass θ P) (n : ℕ) : (inst θ P n).Valid := by
  have hη := ηAt_pos hP n
  have hη1 := ηAt_le hP n
  have hx := three_le_xAt hP n
  have ha := hP.admissible.a_nonneg
  have hmeasB : MeasurableSet {b : ℝ × ℝ | 0 < b.2 ∧ b.2 ≤ b.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hmeasS : MeasurableSet {s : ℝ × ℝ | 0 < s.1 ∧ s.1 ≤ s.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  refine ⟨isProbabilityMeasure_buyerLaw hP n, isProbabilityMeasure_sellerLaw hI hP _, ?_, ?_, ?_,
    ?_⟩
  · show ∀ᵐ b ∂(buyerLaw θ P (ηAt θ P n) (xAt θ P n)), 0 < b.2 ∧ b.2 ≤ b.1
    unfold buyerLaw
    rw [ae_add_measure_iff]
    constructor
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_map_iff (measurable_fB hP _).aemeasurable hmeasB]
      refine ae_of_all _ fun u => ?_
      show 0 < θ.a + ηAt θ P n ∧ θ.a + ηAt θ P n ≤ Zf θ P u + ηAt θ P n
      exact ⟨by linarith, by linarith [a_le_Zf hP u]⟩
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_iff hmeasB]
      exact ⟨by linarith, le_rfl⟩
  · show ∀ᵐ s ∂(sellerLaw θ P (ηAt θ P n)), 0 < s.1 ∧ s.1 ≤ s.2
    unfold sellerLaw
    rw [ae_map_iff (measurable_fS hI hP _).aemeasurable hmeasS]
    refine ae_of_all _ fun v => ?_
    show 0 < Y₁f θ P v + 2 * ηAt θ P n ∧ Y₁f θ P v + 2 * ηAt θ P n ≤ Y₂f θ P v + 2 * ηAt θ P n
    exact ⟨by linarith [Y₁f_nonneg hP v], by linarith [Y₁f_le_Y₂f hP v]⟩
  · show Integrable (fun b : ℝ × ℝ => b.1) (buyerLaw θ P (ηAt θ P n) (xAt θ P n))
    unfold buyerLaw
    refine Integrable.add_measure ?_ ?_
    · refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
      refine integrable_map_unif (measurable_fB hP _) measurable_fst (K := bF θ P + 1)
        (fun u => ?_)
      show |Zf θ P u + ηAt θ P n| ≤ bF θ P + 1
      rw [abs_of_nonneg (by linarith [Zf_nonneg hP u])]
      linarith [Zf_le_bF hP u]
    · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · show Integrable (fun s : ℝ × ℝ => s.2) (sellerLaw θ P (ηAt θ P n))
    refine integrable_map_unif (measurable_fS hI hP _) measurable_snd (K := bF θ P + 1)
      (fun v => ?_)
    show |Y₂f θ P v + 2 * ηAt θ P n| ≤ bF θ P + 1
    rw [abs_of_nonneg (by linarith [Y₂f_nonneg hP v])]
    linarith [Y₂f_le_bF hP v]

/-! ### The common escaping buyer atom -/

theorem inst_escaping (hP : InClass θ P) : HasCommonEscapingAtom (inst θ P) := by
  refine ⟨xAt θ P, ηAt θ P, fun n => ⟨ηAt_pos hP n, ?_⟩, tendsto_ηAt θ P, tendsto_xAt θ P, ?_⟩
  · show buyerLaw θ P (ηAt θ P n) (xAt θ P n) {(xAt θ P n, xAt θ P n)} =
      ENNReal.ofReal (ηAt θ P n)
    unfold buyerLaw
    have hpre : fB θ P (ηAt θ P n) ⁻¹' {(xAt θ P n, xAt θ P n)} = ∅ := by
      ext u
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro h
      have h1 : Zf θ P u + ηAt θ P n = xAt θ P n := congrArg Prod.fst h
      linarith [fB_fst_le hP n u]
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply (measurable_fB hP _) (measurableSet_singleton _), hpre, measure_empty,
      Measure.dirac_apply_of_mem (mem_singleton _), smul_eq_mul, smul_eq_mul, mul_zero,
      mul_one, zero_add]
  · have : (fun n => ηAt θ P n * xAt θ P n) = fun _ => (1 : ℝ) := by
      ext n; exact ηAt_mul_xAt hP n
    rw [this]
    exact tendsto_const_nhds

/-! ### Weak convergence of the laws -/

theorem inst_laws (hI : FamilyIdentities) (hP : InClass θ P) :
    LawsConvergeTo (inst θ P) (buyerBodyLaw θ P) (sellerBodyLaw θ P) := by
  refine ⟨fun n => isProbabilityMeasure_buyerLaw hP n,
    fun n => isProbabilityMeasure_sellerLaw hI hP _, isProbabilityMeasure_buyerBodyLaw hP,
    isProbabilityMeasure_sellerBodyLaw hI hP, ?_, ?_⟩
  · rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simp only [ProbabilityMeasure.coe_mk]
    have hfm : Measurable (f : ℝ × ℝ → ℝ) := f.continuous.measurable
    have hK : ∀ η u, |f (fB θ P η u)| ≤ ‖f‖ := fun η u => by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
    have e : ∀ n, ∫ b, f b ∂((inst θ P n).buyer) =
        (1 - ηAt θ P n) * ∫ u, f (fB θ P (ηAt θ P n) u) ∂unifLaw +
          ηAt θ P n * f (xAt θ P n, xAt θ P n) := fun n =>
      integral_mix (ηAt_pos hP n).le (by linarith [ηAt_le hP n]) (measurable_fB hP _) hfm
        (hK _)
    simp_rw [e]
    rw [buyerBodyLaw_eq, integral_map ((measurable_Zf hP).prodMk measurable_const).aemeasurable
      hfm.aestronglyMeasurable]
    have hlim1 : Tendsto (fun n => ∫ u, f (fB θ P (ηAt θ P n) u) ∂unifLaw) atTop
        (𝓝 (∫ u, f (fB θ P 0 u) ∂unifLaw)) := by
      refine tendsto_integral_param (G := fun t u => f (fB θ P t u))
        (fun t => hfm.comp (measurable_fB hP t)) (fun u => ?_) (tendsto_ηAt θ P)
        (fun n u => hK _ u)
      unfold fB
      exact (f.continuous.comp ((continuous_const.add continuous_id).prodMk
        (continuous_const.add continuous_id))).continuousAt
    have hlim2 : Tendsto (fun n => ηAt θ P n * f (xAt θ P n, xAt θ P n)) atTop (𝓝 0) := by
      have hb : ∀ n, |ηAt θ P n * f (xAt θ P n, xAt θ P n)| ≤ ηAt θ P n * ‖f‖ := by
        intro n
        rw [abs_mul, abs_of_pos (ηAt_pos hP n), ← Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (ηAt_pos hP n).le
      have h0 : Tendsto (fun n => ηAt θ P n * ‖f‖) atTop (𝓝 0) := by
        simpa using (tendsto_ηAt θ P).mul_const ‖f‖
      exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) h0
    have hlim : Tendsto (fun n => (1 - ηAt θ P n) * ∫ u, f (fB θ P (ηAt θ P n) u) ∂unifLaw +
        ηAt θ P n * f (xAt θ P n, xAt θ P n)) atTop
        (𝓝 ((1 - 0) * ∫ u, f (fB θ P 0 u) ∂unifLaw + 0)) :=
      ((tendsto_const_nhds.sub (tendsto_ηAt θ P)).mul hlim1).add hlim2
    have e2 : (1 - 0) * ∫ u, f (fB θ P 0 u) ∂unifLaw + 0 = ∫ u, f (Zf θ P u, θ.a) ∂unifLaw := by
      simp [fB]
    rwa [e2] at hlim
  · rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simp only [ProbabilityMeasure.coe_mk]
    have hfm : Measurable (f : ℝ × ℝ → ℝ) := f.continuous.measurable
    have e : ∀ n, ∫ s, f s ∂((inst θ P n).seller) =
        ∫ v, f (fS θ P (ηAt θ P n) v) ∂unifLaw := fun n =>
      integral_map (measurable_fS hI hP _).aemeasurable hfm.aestronglyMeasurable
    simp_rw [e]
    rw [sellerBodyLaw_eq, integral_map ((measurable_Y₁f hI hP).prodMk
      (measurable_Y₂f hP)).aemeasurable hfm.aestronglyMeasurable]
    have hlim : Tendsto (fun n => ∫ v, f (fS θ P (ηAt θ P n) v) ∂unifLaw) atTop
        (𝓝 (∫ v, f (fS θ P 0 v) ∂unifLaw)) := by
      refine tendsto_integral_param (G := fun t v => f (fS θ P t v))
        (fun t => hfm.comp (measurable_fS hI hP t)) (fun v => ?_) (tendsto_ηAt θ P)
        (fun n v => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _)
      unfold fS
      exact (f.continuous.comp ((continuous_const.add (continuous_const.mul continuous_id)).prodMk
        (continuous_const.add (continuous_const.mul continuous_id)))).continuousAt
    have e2 : ∫ v, f (fS θ P 0 v) ∂unifLaw = ∫ v, f (Y₁f θ P v, Y₂f θ P v) ∂unifLaw := by
      simp [fS]
    rwa [e2] at hlim

end Realize

end FixedPrice.TwoUnit.Family
