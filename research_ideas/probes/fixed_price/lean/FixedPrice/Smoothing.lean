import FixedPrice.JointWelfare

/-! Lemma 11.1 (smoothing). A bounded independent pair of value laws on `[0, Λ]` can be
replaced by an absolutely continuous independent pair supported in `(0, Λ)` whose first-best
welfare is `η`-close to `M + G` and under which no posted price earns more than
`M + sup_{z ≥ 0} Γ(z) + η`.

The smoothed law of a value `V` is the law of `(1 - 2e) V + eΛ + eΛ U` with `U` uniform on
`[-1/2, 1/2]` and independent of `V`. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-! ### Window gains -/

/-- The gain `(b - s)_+` counted when some price in `[t - ρ, t + ρ]` could separate the values:
`s ≤ t + ρ` and `t - ρ ≤ b`. -/
def windowIntegrand (t ρ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 ≤ t + ρ ∧ t - ρ ≤ p.2 then max (p.2 - p.1) 0 else 0

/-- Expected window gain under a joint prior `P` on `ℝ × ℝ`. -/
def windowGain (P : Measure (ℝ × ℝ)) (t ρ : ℝ) : ℝ := ∫ p, windowIntegrand t ρ p ∂P

theorem measurable_windowIntegrand (t ρ : ℝ) : Measurable (windowIntegrand t ρ) := by
  unfold windowIntegrand
  apply Measurable.ite _ ((measurable_snd.sub measurable_fst).max measurable_const)
    measurable_const
  rw [setOf_and]
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_const measurable_snd)

theorem windowIntegrand_nonneg (t ρ : ℝ) (p : ℝ × ℝ) : 0 ≤ windowIntegrand t ρ p := by
  unfold windowIntegrand
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem windowIntegrand_le {Λ t ρ : ℝ} {p : ℝ × ℝ} (hp : p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ) :
    windowIntegrand t ρ p ≤ Λ := by
  obtain ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ := hp
  unfold windowIntegrand
  split_ifs
  · exact max_le (by linarith) (by linarith)
  · linarith

theorem windowIntegrand_mono {t ρ t' ρ' : ℝ} (h1 : t + ρ ≤ t' + ρ') (h2 : t' - ρ' ≤ t - ρ)
    (p : ℝ × ℝ) : windowIntegrand t ρ p ≤ windowIntegrand t' ρ' p := by
  unfold windowIntegrand
  split_ifs with h h'
  · exact le_rfl
  · exact absurd ⟨h.1.trans h1, h2.trans h.2⟩ h'
  · exact le_max_right _ _
  · exact le_rfl

/-- A measurable real function that is a.e. bounded in absolute value is integrable
against a finite measure. -/
theorem integrable_of_ae_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ᵐ x ∂μ, |f x| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (by simpa only [Real.norm_eq_abs] using h)

/-- Almost-everywhere statements about the two coordinates combine on a product measure. -/
theorem ae_prod_both {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} {p : α → Prop} {q : β → Prop} (hp : ∀ᵐ x ∂μ, p x) (hq : ∀ᵐ y ∂ν, q y) :
    ∀ᵐ z ∂μ.prod ν, p z.1 ∧ q z.2 :=
  (Measure.quasiMeasurePreserving_fst.ae hp).and (Measure.quasiMeasurePreserving_snd.ae hq)

section Window

variable {Λ : ℝ} {P : Measure (ℝ × ℝ)} [IsProbabilityMeasure P]

theorem integrable_windowIntegrand (hbox : ∀ᵐ p ∂P, p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ)
    (t ρ : ℝ) : Integrable (windowIntegrand t ρ) P :=
  integrable_of_ae_abs_le (measurable_windowIntegrand t ρ) Λ (by
    filter_upwards [hbox] with p hp
    rw [abs_of_nonneg (windowIntegrand_nonneg t ρ p)]
    exact windowIntegrand_le hp)

omit [IsProbabilityMeasure P] in
theorem windowGain_nonneg (t ρ : ℝ) : 0 ≤ windowGain P t ρ :=
  integral_nonneg (windowIntegrand_nonneg t ρ)

theorem windowGain_le (hbox : ∀ᵐ p ∂P, p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ) (t ρ : ℝ) :
    windowGain P t ρ ≤ Λ := by
  calc windowGain P t ρ ≤ ∫ _p, Λ ∂P :=
        integral_mono_ae (integrable_windowIntegrand hbox t ρ) (integrable_const Λ)
          (by filter_upwards [hbox] with p hp using windowIntegrand_le hp)
    _ = Λ := by simp

/-- The window gain is monotone in the window. -/
theorem windowGain_mono (hbox : ∀ᵐ p ∂P, p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ) {t ρ t' ρ' : ℝ}
    (h1 : t + ρ ≤ t' + ρ') (h2 : t' - ρ' ≤ t - ρ) : windowGain P t ρ ≤ windowGain P t' ρ' :=
  integral_mono (integrable_windowIntegrand hbox t ρ) (integrable_windowIntegrand hbox t' ρ')
    (windowIntegrand_mono h1 h2)

omit [IsProbabilityMeasure P] in
theorem windowGain_eq_zero_of_add_neg (hbox : ∀ᵐ p ∂P, p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ)
    {t ρ : ℝ} (h : t + ρ < 0) : windowGain P t ρ = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hbox] with p hp
  unfold windowIntegrand
  rw [if_neg (fun h' => by linarith [h'.1, hp.1.1])]
  rfl

omit [IsProbabilityMeasure P] in
theorem windowGain_eq_zero_of_lt_sub (hbox : ∀ᵐ p ∂P, p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ)
    {t ρ : ℝ} (h : Λ < t - ρ) : windowGain P t ρ = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hbox] with p hp
  unfold windowIntegrand
  rw [if_neg (fun h' => by linarith [h'.2, hp.2.2])]
  rfl

/-- Shrinking the window to a point: `windowGain P t (1/(m+1)) → windowGain P t 0`
(dominated convergence with the constant bound `Λ`). -/
theorem tendsto_windowGain (hbox : ∀ᵐ p ∂P, p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ) (t : ℝ) :
    Tendsto (fun m : ℕ => windowGain P t (1 / ((m : ℝ) + 1))) atTop
      (𝓝 (windowGain P t 0)) := by
  have hρ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine tendsto_integral_of_dominated_convergence (fun _ => Λ)
    (fun m => (measurable_windowIntegrand _ _).aestronglyMeasurable) (integrable_const Λ)
    (fun m => ?_) ?_
  · filter_upwards [hbox] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (windowIntegrand_nonneg _ _ p)]
    exact windowIntegrand_le hp
  · filter_upwards with p
    by_cases h : p.1 ≤ t ∧ t ≤ p.2
    · apply tendsto_const_nhds.congr'
      filter_upwards with m
      have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      unfold windowIntegrand
      rw [if_pos ⟨by linarith [h.1], by linarith [h.2]⟩,
        if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
    · have h0 : windowIntegrand t 0 p = 0 := by
        unfold windowIntegrand
        rw [if_neg (by simpa only [add_zero, sub_zero] using h)]
      rw [h0]
      apply tendsto_const_nhds.congr'
      rcases not_and_or.mp h with h1 | h2
      · rw [not_le] at h1
        filter_upwards [hρ.eventually (eventually_lt_nhds (sub_pos.mpr h1))] with m hm
        unfold windowIntegrand
        rw [if_neg (fun h' => by linarith [h'.1])]
      · rw [not_le] at h2
        filter_upwards [hρ.eventually (eventually_lt_nhds (sub_pos.mpr h2))] with m hm
        unfold windowIntegrand
        rw [if_neg (fun h' => by linarith [h'.2])]

/-- **Uniform window lemma.** If every point window has gain at most `G`, then for every
`η > 0` one radius `ρ₀ > 0` keeps every window gain below `G + η`. -/
theorem uniform_window (hbox : ∀ᵐ p ∂P, p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ) {G : ℝ}
    (hG : ∀ t, windowGain P t 0 ≤ G) {η : ℝ} (hη : 0 < η) :
    ∃ ρ₀ > 0, ∀ t, windowGain P t ρ₀ ≤ G + η := by
  by_contra hcon
  push Not at hcon
  have hG0 : 0 ≤ G := (windowGain_nonneg 0 0).trans (hG 0)
  choose t ht using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have htmem : ∀ n, t n ∈ Icc (-1) (Λ + 1) := by
    intro n
    have hρpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hρle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    constructor
    · by_contra hlt
      rw [not_le] at hlt
      have := windowGain_eq_zero_of_add_neg hbox (t := t n) (ρ := 1 / ((n : ℝ) + 1))
        (by linarith)
      linarith [ht n]
    · by_contra hlt
      rw [not_le] at hlt
      have := windowGain_eq_zero_of_lt_sub hbox (t := t n) (ρ := 1 / ((n : ℝ) + 1))
        (by linarith)
      linarith [ht n]
  obtain ⟨T, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq htmem
  have hρφ : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  have hup : Tendsto (fun k => t (φ k) + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 T) := by
    simpa using hlim.add hρφ
  have hdn : Tendsto (fun k => t (φ k) - 1 / ((φ k : ℝ) + 1)) atTop (𝓝 T) := by
    simpa using hlim.sub hρφ
  have hbig : ∀ m : ℕ, G + η < windowGain P T (1 / ((m : ℝ) + 1)) := by
    intro m
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨k, hk1, hk2⟩ :=
      ((hup.eventually (eventually_lt_nhds (lt_add_of_pos_right T hm))).and
        (hdn.eventually (eventually_gt_nhds (sub_lt_self T hm)))).exists
    exact (ht (φ k)).trans_le (windowGain_mono hbox hk1.le hk2.le)
  have hlow : G + η ≤ windowGain P T 0 :=
    ge_of_tendsto' (tendsto_windowGain hbox T) (fun m => (hbig m).le)
  linarith [hG T]

end Window

/-! ### Identities under the product prior -/

section Product

variable {Λ : ℝ} {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

theorem sellerMean_eq_integral_prod : sellerMean μs = ∫ p, p.1 ∂(μs.prod μb) := by
  have h := integral_fun_fst (μ := μs) (ν := μb) (E := ℝ) (fun s : ℝ => s)
  simp only [probReal_univ, one_smul] at h
  rw [h]
  rfl

theorem gain_eq_windowGain (hbox : ∀ᵐ p ∂(μs.prod μb), p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ)
    (z : ℝ) : gain μs μb z = windowGain (μs.prod μb) z 0 := by
  rw [windowGain, integral_prod _ (integrable_windowIntegrand hbox z 0)]
  unfold gain
  congr 1
  ext s
  congr 1
  ext b
  unfold windowIntegrand
  simp only [add_zero, sub_zero]
  split_ifs with h
  · rw [max_eq_left (by linarith [h.1, h.2])]
  · rfl

theorem firstBest_prod_eq (hbox : ∀ᵐ p ∂(μs.prod μb), p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ) :
    firstBest (μs.prod μb) = sellerMean μs + gainsFromTrade μs μb := by
  have hfst : Integrable (fun p : ℝ × ℝ => p.1) (μs.prod μb) :=
    integrable_of_ae_abs_le measurable_fst Λ (by
      filter_upwards [hbox] with p hp
      rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2])
  have hgft : Integrable (fun p : ℝ × ℝ => max (p.2 - p.1) 0) (μs.prod μb) :=
    integrable_of_ae_abs_le ((measurable_snd.sub measurable_fst).max measurable_const) Λ (by
      filter_upwards [hbox] with p hp
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hp.1.1, hp.2.2]) (by linarith [hp.1.1, hp.1.2]))
  have hpt : (fun p : ℝ × ℝ => max p.1 p.2) = fun p => p.1 + max (p.2 - p.1) 0 := by
    ext p
    rcases le_total p.1 p.2 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  rw [firstBest, hpt, integral_add hfst hgft, ← sellerMean_eq_integral_prod,
    integral_prod _ hgft]
  rfl

end Product

/-! ### The smoothed laws -/

/-- Uniform noise on `[-1/2, 1/2]`. -/
def noise : Measure ℝ := volume.restrict (Icc (-1 / 2 : ℝ) (1 / 2))

instance : IsProbabilityMeasure noise :=
  ⟨by simp [noise, Real.volume_Icc]; norm_num⟩

theorem ae_noise : ∀ᵐ u ∂noise, u ∈ Icc (-1 / 2 : ℝ) (1 / 2) :=
  ae_restrict_mem measurableSet_Icc

/-- The smoothing map `(v, u) ↦ (1 - 2e) v + eΛ + eΛ u`. -/
def smoothMap (Λ e : ℝ) (q : ℝ × ℝ) : ℝ := (1 - 2 * e) * q.1 + e * Λ + e * Λ * q.2

theorem measurable_smoothMap (Λ e : ℝ) : Measurable (smoothMap Λ e) := by
  unfold smoothMap
  fun_prop

/-- The smoothed law of `ν`: the law of `(1 - 2e) V + eΛ + eΛ U`, `V ~ ν`, `U ~ noise`
independent. This simplified version omits the paper's extra uniform mixture on `(0, Λ)`,
since full support is not needed for the statement proved here. -/
def smoothLaw (Λ e : ℝ) (ν : Measure ℝ) : Measure ℝ := (ν.prod noise).map (smoothMap Λ e)

instance (Λ e : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (smoothLaw Λ e ν) :=
  Measure.isProbabilityMeasure_map (measurable_smoothMap Λ e).aemeasurable

theorem smoothMap_mem_Ioo {Λ e x u : ℝ} (hΛ : 0 < Λ) (he : 0 < e) (he2 : e < 1 / 2)
    (hx : x ∈ Icc 0 Λ) (hu : u ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    smoothMap Λ e (x, u) ∈ Ioo 0 Λ := by
  obtain ⟨hx0, hxΛ⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have heΛ : 0 < e * Λ := mul_pos he hΛ
  have ha : 0 < 1 - 2 * e := by linarith
  have h1 : 0 ≤ (1 - 2 * e) * x := mul_nonneg ha.le hx0
  have h2 : (1 - 2 * e) * x ≤ (1 - 2 * e) * Λ := mul_le_mul_of_nonneg_left hxΛ ha.le
  have h3 : e * Λ * (-1 / 2) ≤ e * Λ * u := mul_le_mul_of_nonneg_left hu0 heΛ.le
  have h4 : e * Λ * u ≤ e * Λ * (1 / 2) := mul_le_mul_of_nonneg_left hu1 heΛ.le
  simp only [smoothMap]
  constructor <;> linarith

theorem abs_smoothMap_sub_le {Λ e x u : ℝ} (hΛ : 0 < Λ) (he : 0 < e)
    (hx : x ∈ Icc 0 Λ) (hu : u ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    |smoothMap Λ e (x, u) - x| ≤ 2 * (e * Λ) := by
  obtain ⟨hx0, hxΛ⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have heΛ : 0 < e * Λ := mul_pos he hΛ
  have h1 : 0 ≤ e * x := mul_nonneg he.le hx0
  have h2 : e * x ≤ e * Λ := mul_le_mul_of_nonneg_left hxΛ he.le
  have h3 : e * Λ * (-1 / 2) ≤ e * Λ * u := mul_le_mul_of_nonneg_left hu0 heΛ.le
  have h4 : e * Λ * u ≤ e * Λ * (1 / 2) := mul_le_mul_of_nonneg_left hu1 heΛ.le
  simp only [smoothMap]
  rw [abs_le]
  constructor <;> linarith

/-- The smoothed law is absolutely continuous: each section `u ↦ c + eΛ u` is an affine
bijection of `ℝ`, so it pulls Lebesgue-null sets back to null sets. -/
theorem smoothLaw_absolutelyContinuous {Λ e : ℝ} (heΛ : e * Λ ≠ 0) (ν : Measure ℝ) :
    smoothLaw Λ e ν ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_
  rw [smoothLaw, Measure.map_apply (measurable_smoothMap Λ e) hN,
    Measure.prod_apply (measurable_smoothMap Λ e hN)]
  have key : ∀ x : ℝ, noise (Prod.mk x ⁻¹' (smoothMap Λ e ⁻¹' N)) = 0 := by
    intro x
    have hset : Prod.mk x ⁻¹' (smoothMap Λ e ⁻¹' N) =
        (fun u => e * Λ * u) ⁻¹' ((fun y => ((1 - 2 * e) * x + e * Λ) + y) ⁻¹' N) := rfl
    rw [hset]
    refine le_antisymm ?_ zero_le
    calc noise ((fun u => e * Λ * u) ⁻¹' ((fun y => ((1 - 2 * e) * x + e * Λ) + y) ⁻¹' N))
        ≤ volume ((fun u => e * Λ * u) ⁻¹'
            ((fun y => ((1 - 2 * e) * x + e * Λ) + y) ⁻¹' N)) := by
          unfold noise
          exact Measure.restrict_apply_le _ _
      _ = 0 := by
          rw [Real.volume_preimage_mul_left heΛ, measure_preimage_add, hN0, mul_zero]
  simp only [key, lintegral_zero]

theorem ae_smoothLaw_mem_Ioo {Λ e : ℝ} (hΛ : 0 < Λ) (he : 0 < e) (he2 : e < 1 / 2)
    {ν : Measure ℝ} (hν : ∀ᵐ x ∂ν, x ∈ Icc 0 Λ) : ∀ᵐ y ∂smoothLaw Λ e ν, y ∈ Ioo 0 Λ := by
  rw [smoothLaw, ae_map_iff (p := fun y => y ∈ Ioo 0 Λ) (measurable_smoothMap Λ e).aemeasurable
    measurableSet_Ioo]
  filter_upwards [ae_prod_both hν ae_noise] with q hq
  exact smoothMap_mem_Ioo hΛ he he2 hq.1 hq.2

/-! ### Integrals against the smoothed pair -/

section Smoothed

variable {Λ e : ℝ} {μs μb : Measure ℝ} [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]

theorem integral_smoothLaw_prod {F : ℝ × ℝ → ℝ} (hF : Measurable F) :
    ∫ p, F p ∂((smoothLaw Λ e μs).prod (smoothLaw Λ e μb)) =
      ∫ q, F (smoothMap Λ e q.1, smoothMap Λ e q.2) ∂((μs.prod noise).prod (μb.prod noise)) := by
  rw [smoothLaw, smoothLaw,
    Measure.map_prod_map _ _ (measurable_smoothMap Λ e) (measurable_smoothMap Λ e),
    integral_map ((measurable_smoothMap Λ e).prodMap (measurable_smoothMap Λ e)).aemeasurable
      hF.aestronglyMeasurable]
  rfl

theorem integral_fst_fst {H : ℝ × ℝ → ℝ} (hH : Measurable H) :
    ∫ q, H (q.1.1, q.2.1) ∂((μs.prod noise).prod (μb.prod noise)) = ∫ p, H p ∂(μs.prod μb) := by
  have hmap : ((μs.prod noise).prod (μb.prod noise)).map (Prod.map Prod.fst Prod.fst) =
      μs.prod μb := by
    rw [← Measure.map_prod_map _ _ measurable_fst measurable_fst, Measure.map_fst_prod,
      Measure.map_fst_prod]
    simp
  rw [← hmap, integral_map (measurable_fst.prodMap measurable_fst).aemeasurable
    hH.aestronglyMeasurable]
  rfl

omit [IsProbabilityMeasure μs] [IsProbabilityMeasure μb] in
theorem ae_bigBox (hs : ∀ᵐ s ∂μs, s ∈ Icc 0 Λ) (hb : ∀ᵐ b ∂μb, b ∈ Icc 0 Λ) :
    ∀ᵐ q ∂((μs.prod noise).prod (μb.prod noise)),
      (q.1.1 ∈ Icc 0 Λ ∧ q.1.2 ∈ Icc (-1 / 2 : ℝ) (1 / 2)) ∧
        (q.2.1 ∈ Icc 0 Λ ∧ q.2.2 ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :=
  ae_prod_both (ae_prod_both hs ae_noise) (ae_prod_both hb ae_noise)

/-- Pointwise comparison of the posted-price gain at the smoothed values with the window
integrand at the original values. -/
theorem priceGainAt_smooth_le {z t ρ₀ S B u v : ℝ} (hΛ : 0 < Λ) (he : 0 < e)
    (he2 : e < 1 / 2) (hS : S ∈ Icc 0 Λ) (hB : B ∈ Icc 0 Λ)
    (hu : u ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (hv : v ∈ Icc (-1 / 2 : ℝ) (1 / 2))
    (ht : (1 - 2 * e) * t = z - e * Λ) (hρ : e * Λ / 2 ≤ (1 - 2 * e) * ρ₀) :
    priceGainAt z (smoothMap Λ e (S, u), smoothMap Λ e (B, v)) ≤
      windowIntegrand t ρ₀ (S, B) + e * Λ := by
  obtain ⟨hS0, hSΛ⟩ := hS
  obtain ⟨hB0, hBΛ⟩ := hB
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  have heΛ : 0 < e * Λ := mul_pos he hΛ
  have ha : 0 < 1 - 2 * e := by linarith
  have hu0' : e * Λ * (-1 / 2) ≤ e * Λ * u := mul_le_mul_of_nonneg_left hu0 heΛ.le
  have hu1' : e * Λ * u ≤ e * Λ * (1 / 2) := mul_le_mul_of_nonneg_left hu1 heΛ.le
  have hv0' : e * Λ * (-1 / 2) ≤ e * Λ * v := mul_le_mul_of_nonneg_left hv0 heΛ.le
  have hv1' : e * Λ * v ≤ e * Λ * (1 / 2) := mul_le_mul_of_nonneg_left hv1 heΛ.le
  unfold priceGainAt windowIntegrand smoothMap
  dsimp only
  split_ifs with h1 h2
  · have hmax : (1 - 2 * e) * (B - S) ≤ max (B - S) 0 := by
      rcases le_total 0 (B - S) with hBS | hBS
      · rw [max_eq_left hBS]
        nlinarith
      · rw [max_eq_right hBS]
        nlinarith
    nlinarith
  · exfalso
    apply h2
    constructor
    · have : (1 - 2 * e) * S ≤ (1 - 2 * e) * (t + ρ₀) := by
        rw [mul_add, ht]
        linarith [h1.1]
      exact le_of_mul_le_mul_left this ha
    · have : (1 - 2 * e) * (t - ρ₀) ≤ (1 - 2 * e) * B := by
        rw [mul_sub, ht]
        linarith [h1.2]
      exact le_of_mul_le_mul_left this ha
  · linarith [le_max_right (B - S) 0]
  · linarith

theorem jointPriceWelfare_smooth_le (hΛ : 0 < Λ) (he : 0 < e) (he2 : e < 1 / 2)
    (hs : ∀ᵐ s ∂μs, s ∈ Icc 0 Λ) (hb : ∀ᵐ b ∂μb, b ∈ Icc 0 Λ) {z t ρ₀ : ℝ}
    (ht : (1 - 2 * e) * t = z - e * Λ) (hρ : e * Λ / 2 ≤ (1 - 2 * e) * ρ₀) :
    jointPriceWelfare ((smoothLaw Λ e μs).prod (smoothLaw Λ e μb)) z ≤
      sellerMean μs + windowGain (μs.prod μb) t ρ₀ + 3 * (e * Λ) := by
  have hQ := ae_bigBox hs hb
  have hbox : ∀ᵐ p ∂(μs.prod μb), p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ := ae_prod_both hs hb
  have heΛ : 0 < e * Λ := mul_pos he hΛ
  have hF : Measurable (fun p : ℝ × ℝ => p.1 + priceGainAt z p) :=
    measurable_fst.add (measurable_priceGainAt z)
  have hW : Measurable (windowIntegrand t ρ₀) := measurable_windowIntegrand t ρ₀
  have hH : Measurable (fun p : ℝ × ℝ => p.1 + windowIntegrand t ρ₀ p + 3 * (e * Λ)) :=
    (measurable_fst.add hW).add measurable_const
  have hint1 : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      smoothMap Λ e q.1 + priceGainAt z (smoothMap Λ e q.1, smoothMap Λ e q.2))
      ((μs.prod noise).prod (μb.prod noise)) := by
    refine integrable_of_ae_abs_le
      (hF.comp ((measurable_smoothMap Λ e).comp measurable_fst |>.prodMk
        ((measurable_smoothMap Λ e).comp measurable_snd))) (2 * Λ) ?_
    filter_upwards [hQ] with q hq
    have hS : smoothMap Λ e q.1 ∈ Ioo 0 Λ := smoothMap_mem_Ioo hΛ he he2 hq.1.1 hq.1.2
    have hB : smoothMap Λ e q.2 ∈ Ioo 0 Λ := smoothMap_mem_Ioo hΛ he he2 hq.2.1 hq.2.2
    have hg0 := priceGainAt_nonneg z (smoothMap Λ e q.1, smoothMap Λ e q.2)
    have hg1 : priceGainAt z (smoothMap Λ e q.1, smoothMap Λ e q.2) ≤ Λ := by
      unfold priceGainAt
      split_ifs
      · dsimp only; linarith [hS.1, hB.2]
      · exact hΛ.le
    rw [abs_le]
    constructor <;> linarith [hS.1, hS.2]
  have hint2 : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      q.1.1 + windowIntegrand t ρ₀ (q.1.1, q.2.1) + 3 * (e * Λ))
      ((μs.prod noise).prod (μb.prod noise)) := by
    refine integrable_of_ae_abs_le
      (hH.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))) (2 * Λ + 3 * (e * Λ)) ?_
    filter_upwards [hQ] with q hq
    have hw0 := windowIntegrand_nonneg t ρ₀ (q.1.1, q.2.1)
    have hw1 : windowIntegrand t ρ₀ (q.1.1, q.2.1) ≤ Λ := windowIntegrand_le ⟨hq.1.1, hq.2.1⟩
    rw [abs_le]
    constructor <;> linarith [hq.1.1.1, hq.1.1.2]
  have hfst : Integrable (fun p : ℝ × ℝ => p.1) (μs.prod μb) :=
    integrable_of_ae_abs_le measurable_fst Λ (by
      filter_upwards [hbox] with p hp
      rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2])
  have hWi := integrable_windowIntegrand hbox t ρ₀
  rw [jointPriceWelfare, integral_smoothLaw_prod hF]
  calc ∫ q, (smoothMap Λ e q.1 + priceGainAt z (smoothMap Λ e q.1, smoothMap Λ e q.2))
        ∂((μs.prod noise).prod (μb.prod noise))
      ≤ ∫ q, (q.1.1 + windowIntegrand t ρ₀ (q.1.1, q.2.1) + 3 * (e * Λ))
          ∂((μs.prod noise).prod (μb.prod noise)) := by
        refine integral_mono_ae hint1 hint2 ?_
        filter_upwards [hQ] with q hq
        have h1 : |smoothMap Λ e q.1 - q.1.1| ≤ 2 * (e * Λ) :=
          abs_smoothMap_sub_le hΛ he hq.1.1 hq.1.2
        have h2 : priceGainAt z (smoothMap Λ e q.1, smoothMap Λ e q.2) ≤
            windowIntegrand t ρ₀ (q.1.1, q.2.1) + e * Λ :=
          priceGainAt_smooth_le hΛ he he2 hq.1.1 hq.2.1 hq.1.2 hq.2.2 ht hρ
        rw [abs_le] at h1
        linarith [h1.2]
    _ = ∫ p, (p.1 + windowIntegrand t ρ₀ p + 3 * (e * Λ)) ∂(μs.prod μb) := integral_fst_fst hH
    _ = sellerMean μs + windowGain (μs.prod μb) t ρ₀ + 3 * (e * Λ) := by
        rw [integral_add (f := fun p : ℝ × ℝ => p.1 + windowIntegrand t ρ₀ p) (hfst.add hWi)
            (integrable_const _), integral_add hfst hWi,
          ← sellerMean_eq_integral_prod]
        simp [windowGain]

theorem abs_firstBest_smooth_sub (hΛ : 0 < Λ) (he : 0 < e) (he2 : e < 1 / 2)
    (hs : ∀ᵐ s ∂μs, s ∈ Icc 0 Λ) (hb : ∀ᵐ b ∂μb, b ∈ Icc 0 Λ) :
    |firstBest ((smoothLaw Λ e μs).prod (smoothLaw Λ e μb)) - firstBest (μs.prod μb)| ≤
      2 * (e * Λ) := by
  have hQ := ae_bigBox hs hb
  have hM : Measurable (fun p : ℝ × ℝ => max p.1 p.2) := measurable_fst.max measurable_snd
  have hint1 : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      max (smoothMap Λ e q.1) (smoothMap Λ e q.2)) ((μs.prod noise).prod (μb.prod noise)) := by
    refine integrable_of_ae_abs_le
      (hM.comp ((measurable_smoothMap Λ e).comp measurable_fst |>.prodMk
        ((measurable_smoothMap Λ e).comp measurable_snd))) Λ ?_
    filter_upwards [hQ] with q hq
    have hS : smoothMap Λ e q.1 ∈ Ioo 0 Λ := smoothMap_mem_Ioo hΛ he he2 hq.1.1 hq.1.2
    have hB : smoothMap Λ e q.2 ∈ Ioo 0 Λ := smoothMap_mem_Ioo hΛ he he2 hq.2.1 hq.2.2
    rw [abs_le]
    constructor
    · linarith [le_max_left (smoothMap Λ e q.1) (smoothMap Λ e q.2), hS.1]
    · exact max_le hS.2.le hB.2.le
  have hint2 : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => max q.1.1 q.2.1)
      ((μs.prod noise).prod (μb.prod noise)) := by
    refine integrable_of_ae_abs_le
      (hM.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))) Λ ?_
    filter_upwards [hQ] with q hq
    rw [abs_le]
    constructor
    · linarith [le_max_left q.1.1 q.2.1, hq.1.1.1]
    · exact max_le hq.1.1.2 hq.2.1.2
  rw [firstBest, firstBest, integral_smoothLaw_prod hM, ← integral_fst_fst hM,
    ← integral_sub hint1 hint2]
  have hbd := norm_integral_le_of_norm_le_const (μ := (μs.prod noise).prod (μb.prod noise))
    (f := fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      max (smoothMap Λ e q.1) (smoothMap Λ e q.2) - max q.1.1 q.2.1) (C := 2 * (e * Λ)) (by
    filter_upwards [hQ] with q hq
    have h1 : |smoothMap Λ e q.1 - q.1.1| ≤ 2 * (e * Λ) :=
      abs_smoothMap_sub_le hΛ he hq.1.1 hq.1.2
    have h2 : |smoothMap Λ e q.2 - q.2.1| ≤ 2 * (e * Λ) :=
      abs_smoothMap_sub_le hΛ he hq.2.1 hq.2.2
    rw [Real.norm_eq_abs]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le h1 h2))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hbd

end Smoothed

/-! ### Lemma 11.1 -/

/-- **Lemma 11.1 (smoothing).** -/
theorem lemma_smoothing {Λ : ℝ} (hΛ : 0 < Λ) {μs μb : Measure ℝ}
    [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]
    (hs : ∀ᵐ s ∂μs, s ∈ Icc 0 Λ) (hb : ∀ᵐ b ∂μb, b ∈ Icc 0 Λ) {η : ℝ} (hη : 0 < η) :
    ∃ μs' μb' : Measure ℝ, IsProbabilityMeasure μs' ∧ IsProbabilityMeasure μb' ∧
      μs' ≪ volume ∧ μb' ≪ volume ∧
      (∀ᵐ s ∂μs', s ∈ Ioo 0 Λ) ∧ (∀ᵐ b ∂μb', b ∈ Ioo 0 Λ) ∧
      |firstBest (μs'.prod μb') - (sellerMean μs + gainsFromTrade μs μb)| ≤ η ∧
      ∀ z : ℝ, jointPriceWelfare (μs'.prod μb') z ≤
        sellerMean μs + (⨆ z : Ici (0 : ℝ), gain μs μb z) + η := by
  have hbox : ∀ᵐ p ∂(μs.prod μb), p.1 ∈ Icc 0 Λ ∧ p.2 ∈ Icc 0 Λ := ae_prod_both hs hb
  set Gmax := ⨆ z : Ici (0 : ℝ), gain μs μb z with hGmax
  have hbdd : BddAbove (range fun z : Ici (0 : ℝ) => gain μs μb z) := by
    refine ⟨Λ, ?_⟩
    rintro _ ⟨z, rfl⟩
    dsimp only
    rw [gain_eq_windowGain hbox]
    exact windowGain_le hbox _ _
  have hG : ∀ t, windowGain (μs.prod μb) t 0 ≤ Gmax := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [← gain_eq_windowGain hbox]
      exact le_ciSup hbdd (⟨t, ht⟩ : Ici (0 : ℝ))
    · rw [windowGain_eq_zero_of_add_neg hbox (by linarith)]
      exact (gain_nonneg μs μb 0).trans (le_ciSup hbdd (⟨0, self_mem_Ici⟩ : Ici (0 : ℝ)))
  obtain ⟨ρ₀, hρ₀, hstar⟩ := uniform_window hbox hG (half_pos hη)
  set e := min (1 / 4 : ℝ) (min (η / (6 * Λ)) (ρ₀ / Λ)) with he_def
  have he : 0 < e := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have he4 : e ≤ 1 / 4 := min_le_left _ _
  have heη : e ≤ η / (6 * Λ) := (min_le_right _ _).trans (min_le_left _ _)
  have heρ : e ≤ ρ₀ / Λ := (min_le_right _ _).trans (min_le_right _ _)
  have heΛη : 6 * (e * Λ) ≤ η := by
    rw [le_div_iff₀ (by positivity)] at heη
    linarith
  have heΛρ : e * Λ ≤ ρ₀ := by
    rw [le_div_iff₀ hΛ] at heρ
    linarith
  have he2 : e < 1 / 2 := by linarith
  have heΛ : e * Λ ≠ 0 := (mul_pos he hΛ).ne'
  refine ⟨smoothLaw Λ e μs, smoothLaw Λ e μb, inferInstance, inferInstance,
    smoothLaw_absolutelyContinuous heΛ μs, smoothLaw_absolutelyContinuous heΛ μb,
    ae_smoothLaw_mem_Ioo hΛ he he2 hs, ae_smoothLaw_mem_Ioo hΛ he he2 hb, ?_, ?_⟩
  · rw [← firstBest_prod_eq hbox]
    exact (abs_firstBest_smooth_sub hΛ he he2 hs hb).trans (by linarith)
  · intro z
    have ha : 0 < 1 - 2 * e := by linarith
    have ht : (1 - 2 * e) * ((z - e * Λ) / (1 - 2 * e)) = z - e * Λ :=
      mul_div_cancel₀ _ ha.ne'
    have hρ : e * Λ / 2 ≤ (1 - 2 * e) * ρ₀ := by
      have : (1 / 2) * ρ₀ ≤ (1 - 2 * e) * ρ₀ :=
        mul_le_mul_of_nonneg_right (by linarith) hρ₀.le
      linarith
    calc jointPriceWelfare ((smoothLaw Λ e μs).prod (smoothLaw Λ e μb)) z
        ≤ sellerMean μs + windowGain (μs.prod μb) ((z - e * Λ) / (1 - 2 * e)) ρ₀
            + 3 * (e * Λ) := jointPriceWelfare_smooth_le hΛ he he2 hs hb ht hρ
      _ ≤ sellerMean μs + (Gmax + η / 2) + 3 * (e * Λ) := by
          gcongr
          exact hstar _
      _ ≤ sellerMean μs + Gmax + η := by linarith

end FixedPrice
