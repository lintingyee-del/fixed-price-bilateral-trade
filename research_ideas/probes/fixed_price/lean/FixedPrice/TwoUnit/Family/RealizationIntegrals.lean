import FixedPrice.TwoUnit.Family.RealizationQuantile

/-!
# Work package E, realization helpers: integrals of the body laws

The body variables are functions of uniform quantiles; their expectations reduce, by
`(s_f(η₁) - s_f(η₂))₊ = ∫ 1{η₂ ≤ r < η₁} P(r)⁻² dr` and Tonelli's theorem, to integrals over the
curve interval against the quantile probabilities `1 - buyerCurveCDF` and `sellerCurveCDF`, which
the fundamental theorem of calculus (for `1/P` and `ξ/P`) evaluates:

* `E Z₁ = a_f + 1/p_f - 1`,
* `E(Y₁ + Y₂) = M_f`,
* `E(Z₁ - Y₁)₊ + E(Z₂ - Y₂)₊ = G_f - 2` (with the certified `gain_density`),
* at `w = s_f(ξ)`: `E(Z₁ - w)₊ = 1/P(ξ) - 1`, `E(w - Y₁)₊ = N_f ξ/P(ξ)` (with the certified
  `area_derivative_in_price`), `P(Z₁ > w) = 1 - buyerCurveCDF ξ`, `P(Y₁ ≤ w) = sellerCurveCDF ξ`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

namespace Realize

variable {θ : Params} {P : ℝ → ℝ}

/-! ### A continuous weight equal to `P⁻²` on the curve interval -/

/-- The projection onto the curve interval. -/
def projC (θ : Params) (r : ℝ) : ℝ := max θ.c (min r θ.ξ₀)

theorem projC_mem (hP : InClass θ P) (r : ℝ) : projC θ r ∈ Icc θ.c θ.ξ₀ :=
  ⟨le_max_left _ _, max_le hP.c_le_ξ₀ (min_le_right _ _)⟩

theorem projC_of_mem {r : ℝ} (hr : r ∈ Icc θ.c θ.ξ₀) : projC θ r = r := by
  unfold projC; rw [min_eq_left hr.2, max_eq_right hr.1]

theorem continuous_projC : Continuous (projC θ) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The weight `P⁻²`, extended continuously from the curve interval. -/
def gc (θ : Params) (P : ℝ → ℝ) (r : ℝ) : ℝ := (P (projC θ r) ^ 2)⁻¹

theorem gc_of_mem {r : ℝ} (hr : r ∈ Icc θ.c θ.ξ₀) : gc θ P r = (P r ^ 2)⁻¹ := by
  unfold gc; rw [projC_of_mem hr]

theorem continuous_gc (hP : InClass θ P) : Continuous (gc θ P) := by
  have h1 : Continuous (fun r => P (projC θ r)) :=
    hP.continuousOn.comp_continuous continuous_projC (projC_mem hP)
  exact (h1.pow 2).inv₀ (fun r => pow_ne_zero 2 (hP.pos' (projC_mem hP r)).ne')

theorem measurable_gc (hP : InClass θ P) : Measurable (gc θ P) := (continuous_gc hP).measurable

theorem gc_pos (hP : InClass θ P) (r : ℝ) : 0 < gc θ P r := by
  unfold gc; have := hP.pos' (projC_mem hP r); positivity

theorem gc_le (hP : InClass θ P) (r : ℝ) : gc θ P r ≤ (θ.p ^ 2)⁻¹ := by
  unfold gc
  have h1 := hP.p_le (projC_mem hP r)
  have hp := hP.admissible.p_pos
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le h1 2)

theorem abs_gc_le (hP : InClass θ P) (r : ℝ) : |gc θ P r| ≤ (θ.p ^ 2)⁻¹ := by
  rw [abs_of_pos (gc_pos hP r)]; exact gc_le hP r

/-! ### Positive parts of physical-time differences -/

/-- `(s_f(y) - s_f(x))₊ = ∫_{[c_f, ξ₀]} 1{x ≤ r < y} P(r)⁻² dr` for `x, y` in the curve
interval. -/
theorem posPart_sF_sub (hP : InClass θ P) {x y : ℝ} (hx : x ∈ Icc θ.c θ.ξ₀)
    (hy : y ∈ Icc θ.c θ.ξ₀) :
    max (sF θ P y - sF θ P x) 0 = ∫ r in Icc θ.c θ.ξ₀, (Ico x y).indicator (gc θ P) r := by
  rw [setIntegral_indicator measurableSet_Ico]
  rcases le_or_gt x y with h | h
  · have hsub : Icc θ.c θ.ξ₀ ∩ Ico x y = Ico x y :=
      inter_eq_right.mpr (fun r hr => ⟨hx.1.trans hr.1, hr.2.le.trans hy.2⟩)
    rw [hsub, max_eq_left (sub_nonneg.mpr (sF_monotoneOn hP hx hy h)), sF_sub hP hx hy,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h]
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [uIcc_of_le h] at hr
    exact (gc_of_mem ⟨hx.1.trans hr.1, hr.2.trans hy.2⟩).symm
  · rw [Ico_eq_empty (not_lt.mpr h.le), inter_empty, Measure.restrict_empty,
      integral_zero_measure, max_eq_right (sub_nonpos.mpr (sF_monotoneOn hP hy hx h.le))]

/-! ### Tonelli for sections -/

/-- `∫_u ∫_r 1_S(u, r) g(r) = ∫_r g(r) μ{u : (u, r) ∈ S}` for a bounded measurable weight. -/
theorem integral_integral_indicator {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {ν : Measure ℝ} [IsFiniteMeasure ν] {S : Set (α × ℝ)}
    (hS : MeasurableSet S) {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ r, |g r| ≤ B) :
    ∫ u, (∫ r, S.indicator (fun q => g q.2) (u, r) ∂ν) ∂μ =
      ∫ r, g r * μ.real {u | (u, r) ∈ S} ∂ν := by
  rw [integral_integral_swap]
  · refine integral_congr_ae (ae_of_all _ fun r => ?_)
    have e : (fun u => S.indicator (fun q => g q.2) (u, r)) =
        {u | (u, r) ∈ S}.indicator (fun _ => g r) := by
      ext u
      by_cases hu : (u, r) ∈ S
      · rw [indicator_of_mem hu, indicator_of_mem (show u ∈ {u | (u, r) ∈ S} from hu)]
      · rw [indicator_of_notMem hu, indicator_of_notMem (show u ∉ {u | (u, r) ∈ S} from hu)]
    show ∫ u, S.indicator (fun q => g q.2) (u, r) ∂μ = g r * μ.real {u | (u, r) ∈ S}
    rw [e, integral_indicator_const _
      (show MeasurableSet {u | (u, r) ∈ S} from measurable_prodMk_right hS), smul_eq_mul, mul_comm]
  · refine Integrable.of_bound ?_ B (ae_of_all _ fun q => ?_)
    · exact ((hg.comp measurable_snd).indicator hS).aestronglyMeasurable
    · show ‖S.indicator (fun q => g q.2) (q.1, q.2)‖ ≤ B
      by_cases hq : (q.1, q.2) ∈ S
      · rw [indicator_of_mem hq, Real.norm_eq_abs]; exact hB _
      · rw [indicator_of_notMem hq, norm_zero]; exact (abs_nonneg _).trans (hB 0)

/-! ### Conversions between set and interval integrals -/

theorem setIntegral_Icc_eq {f : ℝ → ℝ} {α β : ℝ} (h : α ≤ β) :
    ∫ r in Icc α β, f r = ∫ r in α..β, f r := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le h]

theorem setIntegral_Ico_eq {f : ℝ → ℝ} {α β : ℝ} (h : α ≤ β) :
    ∫ r in Ico α β, f r = ∫ r in α..β, f r := by
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le h]

theorem setIntegral_indicator_Icc {f : ℝ → ℝ} {ξ : ℝ}
    (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    ∫ r in Icc θ.c θ.ξ₀, (Icc ξ θ.ξ₀).indicator f r = ∫ r in ξ..θ.ξ₀, f r := by
  rw [setIntegral_indicator measurableSet_Icc,
    inter_eq_right.mpr (Icc_subset_Icc_left hξ.1), setIntegral_Icc_eq hξ.2]

theorem setIntegral_indicator_Ico {f : ℝ → ℝ} {ξ : ℝ}
    (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    ∫ r in Icc θ.c θ.ξ₀, (Ico θ.c ξ).indicator f r = ∫ r in θ.c..ξ, f r := by
  rw [setIntegral_indicator measurableSet_Ico,
    inter_eq_right.mpr (Ico_subset_Icc_self.trans (Icc_subset_Icc_right hξ.2)),
    setIntegral_Ico_eq hξ.1]

/-! ### Fundamental theorem of calculus on subintervals -/

theorem ae_good_of_sub (hP : InClass θ P) {α β : ℝ} (hα : θ.c ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ θ.ξ₀) :
    ∀ᵐ r ∂volume, r ∈ Ι α β → r ∈ Ioo θ.c θ.ξ₀ ∧ DifferentiableAt ℝ P r := by
  filter_upwards [hP.absCont.ae_differentiableAt, Measure.ae_ne volume θ.ξ₀] with r hr hne hrI
  rw [uIoc_of_le hαβ] at hrI
  have hr1 : r ∈ Ioo θ.c θ.ξ₀ :=
    ⟨hα.trans_lt hrI.1, lt_of_le_of_ne (hrI.2.trans hβ) hne⟩
  exact ⟨hr1, hr (by rw [uIcc_of_le hP.c_le_ξ₀]; exact Ioo_subset_Icc_self hr1)⟩

theorem uIcc_sub (hP : InClass θ P) {α β : ℝ} (hα : θ.c ≤ α) (hαβ : α ≤ β) (hβ : β ≤ θ.ξ₀) :
    [[α, β]] ⊆ [[θ.c, θ.ξ₀]] := by
  rw [uIcc_of_le hαβ, uIcc_of_le hP.c_le_ξ₀]; exact Icc_subset_Icc hα hβ

/-- `∫_α^β P'/P² = 1/P(α) - 1/P(β)`. -/
theorem integral_deriv_div_sq_sub (hP : InClass θ P) {α β : ℝ} (hα : θ.c ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ θ.ξ₀) : ∫ r in α..β, deriv P r / P r ^ 2 = (P α)⁻¹ - (P β)⁻¹ := by
  have h := (hP.absCont_inv.mono (uIcc_sub hP hα hαβ hβ)).integral_deriv_eq_sub
  have h' : ∫ r in α..β, deriv P r / P r ^ 2 =
      -∫ r in α..β, deriv (fun x => (P x)⁻¹) r := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_good_of_sub hP hα hαβ hβ] with r hr hrI
    obtain ⟨hr1, hr2⟩ := hr hrI
    have hd : deriv (fun x => (P x)⁻¹) r = -(deriv P r) / P r ^ 2 :=
      (hr2.hasDerivAt.inv (hP.pos' (Ioo_subset_Icc_self hr1)).ne').deriv
    rw [hd]
    ring
  rw [h', h]; ring

/-- `∫_α^β (P - rP')/P² = β/P(β) - α/P(α)`: the integrand is `d(r/P)/dr`, which is the certified
`area_derivative_in_price` (with `N = 1`). -/
theorem integral_sub_mul_deriv_div_sq (hI : FamilyIdentities) (hP : InClass θ P) {α β : ℝ}
    (hα : θ.c ≤ α) (hαβ : α ≤ β) (hβ : β ≤ θ.ξ₀) :
    ∫ r in α..β, (P r - r * deriv P r) / P r ^ 2 = β * (P β)⁻¹ - α * (P α)⁻¹ := by
  have h := (hP.absCont_div.mono (uIcc_sub hP hα hαβ hβ)).integral_deriv_eq_sub
  rw [← h]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_good_of_sub hP hα hαβ hβ] with r hr hrI
  obtain ⟨hr1, hr2⟩ := hr hrI
  have hPr : P r ≠ 0 := (hP.pos' (Ioo_subset_Icc_self hr1)).ne'
  have hd : deriv (fun x => x * (P x)⁻¹) r = 1 * (P r)⁻¹ + r * (-(deriv P r) / P r ^ 2) :=
    ((hasDerivAt_id' r).mul (hr2.hasDerivAt.inv hPr)).deriv
  rw [hd]
  have hA := hI.area_derivative_in_price r (P r) (deriv P r) 1 hPr
  have hP2 : P r ^ 2 ≠ 0 := pow_ne_zero 2 hPr
  have e : (P r - r * deriv P r) / P r ^ 2 = 1 / P r - 1 * r * deriv P r / P r ^ 2 := by
    rw [div_eq_iff hP2, hA]; ring
  rw [e]
  show 1 / P r - 1 * r * deriv P r / P r ^ 2 = 1 * (P r)⁻¹ + r * (-deriv P r / P r ^ 2)
  ring

/-! ### The weights on the curve interval, almost everywhere -/

/-- At a good point, the curve distribution functions are given by the derivative. -/
theorem weights_at_good {r : ℝ} (hr : r ∈ Ioo θ.c θ.ξ₀) (hd : DifferentiableAt ℝ P r) :
    gc θ P r = (P r ^ 2)⁻¹ ∧ buyerCurveCDF θ P r = 1 - deriv P r ∧
      sellerCurveCDF θ P r = θ.N * (P r - r * deriv P r) := by
  refine ⟨gc_of_mem (Ioo_subset_Icc_self hr), ?_, ?_⟩
  · rw [buyerCDF_of_mem hr.1.le hr.2, rd_eq_deriv hd]
  · rw [sellerCDF_of_mem hr.1.le hr.2]; unfold bodySellerCDF
    rw [show derivWithin P (Ici r) r = bodySurvival P r from rfl, rd_eq_deriv hd]

/-- `∫_ξ^{ξ₀} P⁻² (1 - buyerCurveCDF) = 1/P(ξ) - 1`. -/
theorem integral_gc_buyer (hP : InClass θ P) {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    ∫ r in ξ..θ.ξ₀, gc θ P r * (1 - buyerCurveCDF θ P r) = (P ξ)⁻¹ - 1 := by
  have h := integral_deriv_div_sq_sub hP hξ.1 hξ.2 le_rfl
  rw [hP.right_end, inv_one] at h
  rw [← h]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_good_of_sub hP hξ.1 hξ.2 le_rfl] with r hr hrI
  obtain ⟨hr1, hr2⟩ := hr hrI
  obtain ⟨e1, e2, -⟩ := weights_at_good hr1 hr2
  rw [e1, e2]; ring

/-- `∫_{c_f}^ξ P⁻² sellerCurveCDF = N_f (ξ/P(ξ) - c_f/p_f)`. -/
theorem integral_gc_seller (hI : FamilyIdentities) (hP : InClass θ P) {ξ : ℝ}
    (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    ∫ r in θ.c..ξ, gc θ P r * sellerCurveCDF θ P r = θ.N * (ξ * (P ξ)⁻¹ - θ.c * θ.p⁻¹) := by
  have h := integral_sub_mul_deriv_div_sq hI hP le_rfl hξ.1 hξ.2
  rw [hP.left_end] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_good_of_sub hP le_rfl hξ.1 hξ.2] with r hr hrI
  obtain ⟨hr1, hr2⟩ := hr hrI
  obtain ⟨e1, -, e3⟩ := weights_at_good hr1 hr2
  rw [e1, e3]; ring

/-- `∫_{c_f}^ξ P⁻² = s_f(ξ) - a_f`. -/
theorem integral_gc (hP : InClass θ P) {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    ∫ r in θ.c..ξ, gc θ P r = sF θ P ξ - θ.a := by
  have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
  rw [← sF_c (θ := θ) (P := P), sF_sub hP hc hξ]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [uIcc_of_le hξ.1] at hr
  exact gc_of_mem ⟨hr.1, hr.2.trans hξ.2⟩

theorem integral_gc_full (hP : InClass θ P) : ∫ r in θ.c..θ.ξ₀, gc θ P r = Tf θ P := by
  unfold Tf
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [uIcc_of_le hP.c_le_ξ₀] at hr
  exact gc_of_mem hr

/-- `∫_{c_f}^{ξ₀} P⁻² (1 - buyerCurveCDF) sellerCurveCDF = G_f - 2 - 2 m_f a_f` (certified
`gain_density`: `N(P - ξH)H/P² = NH/P - NξH²/P²`). -/
theorem integral_gc_buyer_seller (hI : FamilyIdentities) (hP : InClass θ P) :
    ∫ r in θ.c..θ.ξ₀, gc θ P r * ((1 - buyerCurveCDF θ P r) * sellerCurveCDF θ P r) =
      Gf θ P - 2 - 2 * θ.m * θ.a := by
  have hG := hP.Gf_sub_two
  have e : ∫ r in θ.c..θ.ξ₀, gc θ P r * ((1 - buyerCurveCDF θ P r) * sellerCurveCDF θ P r) =
      θ.N * ∫ ξ in θ.c..θ.ξ₀, (deriv P ξ / P ξ - ξ * (deriv P ξ / P ξ) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_good_of_sub hP le_rfl hP.c_le_ξ₀ le_rfl] with r hr hrI
    obtain ⟨hr1, hr2⟩ := hr hrI
    obtain ⟨e1, e2, e3⟩ := weights_at_good hr1 hr2
    have hPr : P r ≠ 0 := (hP.pos' (Ioo_subset_Icc_self hr1)).ne'
    have hgd := hI.gain_density r (P r) (deriv P r) θ.N hPr
    rw [e1, e2, e3]
    calc (P r ^ 2)⁻¹ * ((1 - (1 - deriv P r)) * (θ.N * (P r - r * deriv P r)))
        = θ.N * (P r - r * deriv P r) * deriv P r / P r ^ 2 := by ring
      _ = θ.N * deriv P r / P r - θ.N * r * deriv P r ^ 2 / P r ^ 2 := hgd
      _ = θ.N * (deriv P r / P r - r * (deriv P r / P r) ^ 2) := by
          field_simp
  rw [e]; linarith

/-! ### Measurability and bounds of the curve distribution functions -/

theorem measurable_buyerCDF (hP : InClass θ P) : Measurable (buyerCurveCDF θ P) :=
  (buyerCDF_mono hP).measurable

theorem measurable_sellerCDF (hI : FamilyIdentities) (hP : InClass θ P) :
    Measurable (sellerCurveCDF θ P) :=
  (sellerCDF_mono hI hP).measurable

theorem unif_real_of_eq {s : Set ℝ} {x : ℝ} (h : unifLaw s = ENNReal.ofReal x) (hx : 0 ≤ x) :
    unifLaw.real s = x := by
  rw [measureReal_def, h, ENNReal.toReal_ofReal hx]

theorem integrable_unif_of_bound {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable f unifLaw :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB x)

theorem integrable_prod_of_bound {f : ℝ × ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) : Integrable f (unifLaw.prod unifLaw) :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB x)

theorem intervalIntegrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ r, |f r| ≤ B) (a b : ℝ) : IntervalIntegrable f volume a b := by
  have hb : ∀ᵐ r ∂volume, ‖f r‖ ≤ B := ae_of_all _ fun r => by rw [Real.norm_eq_abs]; exact hB r
  exact ⟨Integrable.of_bound hf.aestronglyMeasurable B (ae_restrict_of_ae hb),
    Integrable.of_bound hf.aestronglyMeasurable B (ae_restrict_of_ae hb)⟩

theorem intervalIntegrable_gc_sellerCDF (hI : FamilyIdentities) (hP : InClass θ P) (a b : ℝ) :
    IntervalIntegrable (fun r => gc θ P r * sellerCurveCDF θ P r) volume a b := by
  refine intervalIntegrable_of_bound ((measurable_gc hP).mul (measurable_sellerCDF hI hP))
    (B := (θ.p ^ 2)⁻¹) (fun r => ?_) a b
  rw [abs_mul, abs_of_pos (gc_pos hP r),
    abs_of_nonneg ((hP.admissible.m_pos.le).trans (m_le_sellerCDF hI hP r))]
  have h1 := gc_le hP r
  have h2 := sellerCDF_le_one hP r
  have h3 := gc_pos hP r
  nlinarith

/-! ### Expectations of the body variables -/

theorem abs_Zf_le (hP : InClass θ P) (u : ℝ) : |Zf θ P u| ≤ bF θ P := by
  rw [abs_of_nonneg (Zf_nonneg hP u)]; exact Zf_le_bF hP u

theorem abs_Y₁f_le (hP : InClass θ P) (u : ℝ) : |Y₁f θ P u| ≤ bF θ P := by
  rw [abs_of_nonneg (Y₁f_nonneg hP u)]; exact Y₁f_le_bF hP u

theorem abs_Y₂f_le (hP : InClass θ P) (u : ℝ) : |Y₂f θ P u| ≤ bF θ P := by
  rw [abs_of_nonneg (Y₂f_nonneg hP u)]; exact Y₂f_le_bF hP u

/-- `E Z₁ = a_f + 1/p_f - 1`. -/
theorem integral_Zf (hP : InClass θ P) : ∫ u, Zf θ P u ∂unifLaw = θ.a + (θ.p⁻¹ - 1) := by
  set S : Set (ℝ × ℝ) := {q | θ.c ≤ q.2 ∧ q.2 < qB θ P q.1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd ((measurable_qB hP).comp measurable_fst))
  have hpt : ∀ u, Zf θ P u = θ.a + ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (u, r) := by
    intro u
    have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
    have h := posPart_sF_sub hP hc (qB_mem hP u)
    rw [sF_c, max_eq_left (sub_nonneg.mpr (a_le_sF hP (qB_mem hP u)))] at h
    have e : ∀ r, S.indicator (fun q => gc θ P q.2) (u, r) = (Ico θ.c (qB θ P u)).indicator (gc θ P) r := by
      intro r
      by_cases hr : r ∈ Ico θ.c (qB θ P u)
      · rw [indicator_of_mem hr, indicator_of_mem (show (u, r) ∈ S from hr)]
      · rw [indicator_of_notMem hr, indicator_of_notMem (show (u, r) ∉ S from hr)]
    simp_rw [e]
    unfold Zf
    linarith
  have hint : ∫ u, Zf θ P u ∂unifLaw =
      θ.a + ∫ u, (∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (u, r)) ∂unifLaw := by
    have e2 : (fun u => ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (u, r)) =
        fun u => Zf θ P u - θ.a := by
      ext u; rw [hpt u]; ring
    rw [e2, integral_sub (integrable_unif_of_bound (measurable_Zf hP) (abs_Zf_le hP))
      (integrable_const _), integral_const, probReal_univ, one_smul]
    ring
  rw [hint, integral_integral_indicator hSm (measurable_gc hP) (abs_gc_le hP)]
  have e3 : ∫ r in Icc θ.c θ.ξ₀, gc θ P r * unifLaw.real {u | (u, r) ∈ S} =
      ∫ r in Icc θ.c θ.ξ₀, gc θ P r * (1 - buyerCurveCDF θ P r) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    have hsec : {u | (u, r) ∈ S} = {u | r < qB θ P u} := by
      ext u; simp only [hS, mem_setOf_eq, hr.1, true_and]
    rw [hsec, unif_real_of_eq (unif_qB_gt hP r) (by linarith [buyerCDF_le_one hP r])]
  have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
  rw [e3, setIntegral_Icc_eq hP.c_le_ξ₀, integral_gc_buyer hP hc, hP.left_end]

/-- `E Y₁ = (1 - m_f) a_f + T_f - N_f (ξ₀ - c_f/p_f)`. -/
theorem integral_Y₁f (hI : FamilyIdentities) (hP : InClass θ P) :
    ∫ v, Y₁f θ P v ∂unifLaw =
      (1 - θ.m) * θ.a + (Tf θ P - θ.N * (θ.ξ₀ - θ.c * θ.p⁻¹)) := by
  set S : Set (ℝ × ℝ) := {q | θ.m < q.1 ∧ θ.c ≤ q.2 ∧ q.2 < qS θ P q.1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd ((measurable_qS hI hP).comp measurable_fst)))
  have hmset : MeasurableSet {v : ℝ | θ.m < v} := measurableSet_Ioi
  have hpt : ∀ v, Y₁f θ P v = {v : ℝ | θ.m < v}.indicator (fun _ => θ.a) v +
      ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (v, r) := by
    intro v
    by_cases hv : θ.m < v
    · have hc : θ.c ∈ Icc θ.c θ.ξ₀ := left_mem_Icc.mpr hP.c_le_ξ₀
      have h := posPart_sF_sub hP hc (qS_mem hP v)
      rw [sF_c, max_eq_left (sub_nonneg.mpr (a_le_sF hP (qS_mem hP v)))] at h
      have e : ∀ r, S.indicator (fun q => gc θ P q.2) (v, r) =
          (Ico θ.c (qS θ P v)).indicator (gc θ P) r := by
        intro r
        by_cases hr : r ∈ Ico θ.c (qS θ P v)
        · rw [indicator_of_mem hr, indicator_of_mem (show (v, r) ∈ S from ⟨hv, hr⟩)]
        · rw [indicator_of_notMem hr,
            indicator_of_notMem (show (v, r) ∉ S from fun h' => hr h'.2)]
      simp_rw [e]
      rw [Y₁f_of_gt hv, indicator_of_mem (show v ∈ {v : ℝ | θ.m < v} from hv)]
      linarith
    · have e : ∀ r, S.indicator (fun q => gc θ P q.2) (v, r) = 0 := fun r =>
        indicator_of_notMem (show (v, r) ∉ S from fun h' => hv h'.1) _
      simp_rw [e]
      rw [Y₁f_of_le (not_lt.mp hv), indicator_of_notMem (show v ∉ {v : ℝ | θ.m < v} from hv)]
      simp
  have hind : Integrable (fun v => {v : ℝ | θ.m < v}.indicator (fun _ => θ.a) v) unifLaw :=
    (integrable_const θ.a).indicator hmset
  have hint : ∫ v, Y₁f θ P v ∂unifLaw = (1 - θ.m) * θ.a +
      ∫ v, (∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (v, r)) ∂unifLaw := by
    have e2 : (fun v => ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (v, r)) =
        fun v => Y₁f θ P v - {v : ℝ | θ.m < v}.indicator (fun _ => θ.a) v := by
      ext v; rw [hpt v]; ring
    rw [e2, integral_sub (integrable_unif_of_bound (measurable_Y₁f hI hP) (abs_Y₁f_le hP)) hind,
      integral_indicator_const _ hmset,
      unif_real_of_eq (unif_gt_m hP) (by linarith [hP.admissible.m_lt_one]), smul_eq_mul]
    ring
  rw [hint, integral_integral_indicator hSm (measurable_gc hP) (abs_gc_le hP)]
  have e3 : ∫ r in Icc θ.c θ.ξ₀, gc θ P r * unifLaw.real {u | (u, r) ∈ S} =
      ∫ r in Icc θ.c θ.ξ₀, (gc θ P r - gc θ P r * sellerCurveCDF θ P r) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    have hsec : {u | (u, r) ∈ S} = {v | θ.m < v ∧ r < qS θ P v} := by
      ext u; simp only [hS, mem_setOf_eq, hr.1, true_and]
    rw [hsec, unif_real_of_eq (unif_qS_gt hI hP r) (by linarith [sellerCDF_le_one hP r])]
    ring
  have hr1 : θ.ξ₀ ∈ Icc θ.c θ.ξ₀ := right_mem_Icc.mpr hP.c_le_ξ₀
  rw [e3, setIntegral_Icc_eq hP.c_le_ξ₀, intervalIntegral.integral_sub
      ((continuous_gc hP).intervalIntegrable _ _) (intervalIntegrable_gc_sellerCDF hI hP _ _),
    integral_gc_full hP, integral_gc_seller hI hP hr1, hP.right_end, inv_one, mul_one]

/-- `E Y₂ = (1 - m_f) b_f`. -/
theorem integral_Y₂f (hP : InClass θ P) :
    ∫ v, Y₂f θ P v ∂unifLaw = (1 - θ.m) * bF θ P := by
  have e : (fun v => Y₂f θ P v) = fun v => {v : ℝ | θ.m < v}.indicator (fun _ => bF θ P) v := by
    ext v
    by_cases hv : θ.m < v
    · rw [Y₂f_of_gt hv, indicator_of_mem (show v ∈ {v : ℝ | θ.m < v} from hv)]
    · rw [Y₂f_of_le (not_lt.mp hv), indicator_of_notMem (show v ∉ {v : ℝ | θ.m < v} from hv)]
  rw [e, integral_indicator_const _ (show MeasurableSet {v : ℝ | θ.m < v} from measurableSet_Ioi),
    unif_real_of_eq (unif_gt_m hP) (by linarith [hP.admissible.m_lt_one]), smul_eq_mul]

/-- `N_f + m_f = 2`. -/
theorem N_add_m (hP : InClass θ P) : θ.N + θ.m = 2 := by
  have ht := hP.admissible.t_pos
  unfold Params.N Params.m NF mF
  field_simp

/-- `E(Y₁ + Y₂) = M_f`. -/
theorem integral_Y_sum (hI : FamilyIdentities) (hP : InClass θ P) :
    ∫ v, (Y₁f θ P v + Y₂f θ P v) ∂unifLaw = Mf θ P := by
  rw [integral_add (integrable_unif_of_bound (measurable_Y₁f hI hP) (abs_Y₁f_le hP))
    (integrable_unif_of_bound (measurable_Y₂f hP) (abs_Y₂f_le hP)), integral_Y₁f hI hP,
    integral_Y₂f hP]
  have hma := hP.admissible.m_mul_a
  have hNm := N_add_m hP
  have hb : bF θ P = θ.a + Tf θ P := rfl
  have hp := hP.admissible.p_pos
  unfold Mf
  rw [hb]
  have e : θ.N * θ.c * θ.p⁻¹ = θ.m * θ.a := by rw [hma]; field_simp
  have hNm' : θ.N = 2 - θ.m := by linarith
  rw [hNm'] at e ⊢
  linear_combination e

end Realize

end FixedPrice.TwoUnit.Family
