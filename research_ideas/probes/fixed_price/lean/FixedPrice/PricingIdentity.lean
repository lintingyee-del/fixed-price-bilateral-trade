import FixedPrice.PriceDensity

/-! The per-seller identity behind Lemma 9.1: for a seller value `s ∈ [0, s₀]`,
`∫_s^{s₀} q(z) (L(z) + (z - s) H(z)) dz = β (L(s) - d s)`. Both sides are absolutely
continuous in `s`, have the same derivative almost everywhere, and vanish at `s₀`. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

section Identity

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {d s₀ β : ℝ}

/-- `s ↦ ∫_s^{s₀} f` is absolutely continuous on `[0, s₀]` for integrable `f`. -/
theorem absolutelyContinuous_integral_to (hs₀ : 0 ≤ s₀) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 s₀) :
    AbsolutelyContinuousOnInterval (fun s => ∫ z in s..s₀, f z) 0 s₀ := by
  have h := hf.absolutelyContinuousOnInterval_intervalIntegral (c := s₀)
    (by rw [uIcc_of_le hs₀]; exact ⟨hs₀, le_rfl⟩)
  have heq : (fun s => ∫ z in s..s₀, f z) = fun s => -(∫ z in s₀..s, f z) := by
    funext s
    rw [intervalIntegral.integral_symm]
  rw [heq]
  exact h.neg

theorem ae_hasDerivAt_integral_to (hs₀ : 0 ≤ s₀) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 s₀) :
    ∀ᵐ s, s ∈ uIcc (0 : ℝ) s₀ → HasDerivAt (fun s => ∫ z in s..s₀, f z) (-f s) s := by
  filter_upwards [hf.ae_hasDerivAt_integral] with s hs hmem
  have h := (hs hmem s₀ (by rw [uIcc_of_le hs₀]; exact ⟨hs₀, le_rfl⟩)).neg
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with x
  show ∫ z in x..s₀, f z = -∫ t in s₀..x, f t
  exact intervalIntegral.integral_symm s₀ x

theorem absolutelyContinuous_const (a b c : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

theorem IsCutoff.tailIntegral_eq_integral (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    {s : ℝ} (hs : s ≤ s₀) : tailIntegral μ s = d * s₀ + ∫ z in s..s₀, survival μ z := by
  have h := tailIntegral_sub μ hint hs
  rw [hc.eq] at h
  linarith

theorem IsCutoff.ae_hasDerivAt_tailIntegral (hc : IsCutoff μ d s₀)
    (hint : Integrable (fun v => v) μ) :
    ∀ᵐ s, s ∈ Ioo (0 : ℝ) s₀ → HasDerivAt (tailIntegral μ) (-survival μ s) s := by
  filter_upwards [ae_hasDerivAt_integral_to hc.pos.le (survival_antitone μ).intervalIntegrable]
    with s hs hmem
  have hmem' : s ∈ uIcc (0 : ℝ) s₀ := by rw [uIcc_of_le hc.pos.le]; exact Ioo_subset_Icc_self hmem
  have h := (hs hmem').const_add (d * s₀)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hmem.2] with x hx
  exact hc.tailIntegral_eq_integral hint (le_of_lt hx)

theorem ae_hasDerivAt_secondTail (hs₀ : 0 ≤ s₀) :
    ∀ᵐ s, s ∈ uIcc (0 : ℝ) s₀ → HasDerivAt (secondTail μ s₀) (-(survival μ s) ^ 2) s :=
  ae_hasDerivAt_integral_to hs₀ (survival_sq_intervalIntegrable 0 s₀)

theorem IsCutoff.tailIntegral_absolutelyContinuous (hc : IsCutoff μ d s₀)
    (hint : Integrable (fun v => v) μ) :
    AbsolutelyContinuousOnInterval (tailIntegral μ) 0 s₀ :=
  (tailIntegral_lipschitz μ hint).lipschitzOnWith.absolutelyContinuousOnInterval

theorem secondTail_absolutelyContinuous (hs₀ : 0 ≤ s₀) :
    AbsolutelyContinuousOnInterval (secondTail μ s₀) 0 s₀ :=
  absolutelyContinuous_integral_to hs₀ (survival_sq_intervalIntegrable 0 s₀)

theorem IsCutoff.inv_tailIntegral_absolutelyContinuous (hc : IsCutoff μ d s₀)
    (hint : Integrable (fun v => v) μ) :
    AbsolutelyContinuousOnInterval (fun s => (tailIntegral μ s)⁻¹) 0 s₀ := by
  have hds : 0 < d * s₀ := mul_pos hc.hd hc.pos
  have hlip := (inv_lipschitzOn_Ici hds).comp (tailIntegral_lipschitz μ hint).lipschitzOnWith
    (s := uIcc 0 s₀) (fun s hs => by
      rw [uIcc_of_le hc.pos.le] at hs
      exact hc.tailIntegral_ge hint hs.2)
  exact hlip.absolutelyContinuousOnInterval

theorem measurable_priceDensity (hint : Integrable (fun v => v) μ) :
    Measurable (priceDensity β μ d s₀) :=
  measurable_const.mul (measurable_priceBracket hint)

theorem IsCutoff.priceDensity_intervalIntegrable (hc : IsCutoff μ d s₀)
    (hint : Integrable (fun v => v) μ) :
    IntervalIntegrable (priceDensity β μ d s₀) volume 0 s₀ :=
  (hc.priceBracket_intervalIntegrable hint).const_mul β

/-- The price density times a bounded measurable function is integrable on `[0, s₀]`. -/
theorem IsCutoff.priceDensity_mul_intervalIntegrable (hc : IsCutoff μ d s₀)
    (hint : Integrable (fun v => v) μ) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ z ∈ Ioc (0 : ℝ) s₀, |g z| ≤ C) :
    IntervalIntegrable (fun z => priceDensity β μ d s₀ z * g z) volume 0 s₀ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgC s₀ ⟨hc.pos, le_rfl⟩)
  apply ((hc.priceDensity_intervalIntegrable (β := β) hint).const_mul C).mono_fun
  · exact ((measurable_priceDensity hint).mul hg).aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with z hz
    have hz' : z ∈ Ioc 0 s₀ := by rwa [uIoc_of_le hc.pos.le] at hz
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC0]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hgC z hz') (abs_nonneg _)

theorem survival_abs_le (z : ℝ) : |survival μ z| ≤ 1 := by
  rw [abs_of_nonneg (survival_nonneg μ z)]
  exact survival_le_one μ z

/-- The first identity: `∫_s^{s₀} q H = β (d - (d² s₀ - K(s))/L(s))`. -/
theorem IsCutoff.integral_priceDensity_survival (hc : IsCutoff μ d s₀)
    (hint : Integrable (fun v => v) μ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) s₀) :
    (∫ z in s..s₀, priceDensity β μ d s₀ z * survival μ z) =
      β * (d - (d ^ 2 * s₀ - secondTail μ s₀ s) / tailIntegral μ s) := by
  have hs₀ := hc.pos
  have hqH : IntervalIntegrable (fun z => priceDensity β μ d s₀ z * survival μ z) volume 0 s₀ :=
    hc.priceDensity_mul_intervalIntegrable hint (survival_measurable μ)
      (fun z _ => survival_abs_le (μ := μ) z)
  set G₁ : ℝ → ℝ := fun s => ∫ z in s..s₀, priceDensity β μ d s₀ z * survival μ z with hG₁
  set G₂ : ℝ → ℝ := fun s =>
    β * (d - (d ^ 2 * s₀ - secondTail μ s₀ s) * (tailIntegral μ s)⁻¹) with hG₂
  have hG₁ac : AbsolutelyContinuousOnInterval G₁ 0 s₀ := absolutelyContinuous_integral_to hs₀.le hqH
  have hG₂ac : AbsolutelyContinuousOnInterval G₂ 0 s₀ := by
    have h1 := ((absolutelyContinuous_const 0 s₀ (d ^ 2 * s₀)).sub
      (secondTail_absolutelyContinuous (μ := μ) hs₀.le)).mul
      (hc.inv_tailIntegral_absolutelyContinuous hint)
    exact ((absolutelyContinuous_const 0 s₀ d).sub h1).const_mul β
  have hF : AbsolutelyContinuousOnInterval (fun s => G₁ s - G₂ s) 0 s₀ := hG₁ac.sub hG₂ac
  have hderiv : ∀ᵐ s, s ∈ uIcc (0 : ℝ) s₀ → HasDerivAt (fun s => G₁ s - G₂ s) 0 s := by
    filter_upwards [ae_hasDerivAt_integral_to hs₀.le hqH, hc.ae_hasDerivAt_tailIntegral hint,
      ae_hasDerivAt_secondTail (μ := μ) hs₀.le, volume.ae_ne (0 : ℝ), volume.ae_ne s₀]
      with s h1 h2 h3 hne0 hnes hmem
    have hmem' : s ∈ Icc (0 : ℝ) s₀ := by rwa [uIcc_of_le hs₀.le] at hmem
    have hIoo : s ∈ Ioo (0 : ℝ) s₀ :=
      ⟨lt_of_le_of_ne hmem'.1 (Ne.symm hne0), lt_of_le_of_ne hmem'.2 hnes⟩
    have hL := hc.tailIntegral_pos hint hmem'.2
    have hd1 := h1 hmem
    have hd2 := h2 hIoo
    have hd3 := h3 hmem
    have hX : HasDerivAt (fun s => (d ^ 2 * s₀ - secondTail μ s₀ s) * (tailIntegral μ s)⁻¹)
        ((-(-(survival μ s) ^ 2)) * (tailIntegral μ s)⁻¹ +
          (d ^ 2 * s₀ - secondTail μ s₀ s) * (-(-survival μ s) / (tailIntegral μ s) ^ 2)) s :=
      (hd3.const_sub (d ^ 2 * s₀)).mul (hd2.inv (ne_of_gt hL))
    have hG₂' : HasDerivAt G₂ (β * (-((-(-(survival μ s) ^ 2)) * (tailIntegral μ s)⁻¹ +
        (d ^ 2 * s₀ - secondTail μ s₀ s) * (-(-survival μ s) / (tailIntegral μ s) ^ 2)))) s :=
      (hX.const_sub d).const_mul β
    refine (hd1.sub hG₂').congr_deriv ?_
    unfold priceDensity priceBracket
    field_simp
    ring
  obtain ⟨c, hconst⟩ := hF.const_of_ae_hasDerivAt_zero hderiv
  have hs₀mem : s₀ ∈ uIcc (0 : ℝ) s₀ := by rw [uIcc_of_le hs₀.le]; exact ⟨hs₀.le, le_rfl⟩
  have hsmem : s ∈ uIcc (0 : ℝ) s₀ := by rw [uIcc_of_le hs₀.le]; exact hs
  have hend : G₁ s₀ - G₂ s₀ = 0 := by
    simp only [hG₁, hG₂, intervalIntegral.integral_same]
    have hK : secondTail μ s₀ s₀ = 0 := by simp [secondTail]
    rw [hK, hc.eq]
    have hds : d * s₀ ≠ 0 := ne_of_gt (mul_pos hc.hd hc.pos)
    field_simp
    try ring
  have h1 := hconst s hsmem
  have h2 := hconst s₀ hs₀mem
  have hval : G₁ s = G₂ s := by linarith
  simp only [hG₁, hG₂] at hval
  rw [hval]
  ring

/-- The per-seller identity of Lemma 9.1. -/
theorem IsCutoff.seller_identity (hc : IsCutoff μ d s₀) (hint : Integrable (fun v => v) μ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) s₀) :
    (∫ z in s..s₀, priceDensity β μ d s₀ z * (tailIntegral μ z + (z - s) * survival μ z)) =
      β * (tailIntegral μ s - d * s) := by
  have hs₀ := hc.pos
  have hL0 : tailIntegral μ 0 ≤ tailIntegral μ 0 := le_rfl
  -- integrability of the two pieces
  have hqH : IntervalIntegrable (fun z => priceDensity β μ d s₀ z * survival μ z) volume 0 s₀ :=
    hc.priceDensity_mul_intervalIntegrable hint (survival_measurable μ)
      (fun z _ => survival_abs_le (μ := μ) z)
  have hqL : IntervalIntegrable
      (fun z => priceDensity β μ d s₀ z * (tailIntegral μ z + z * survival μ z)) volume 0 s₀ := by
    apply hc.priceDensity_mul_intervalIntegrable hint
      (g := fun z => tailIntegral μ z + z * survival μ z)
      ((tailIntegral_continuous μ hint).measurable.add (measurable_id.mul (survival_measurable μ)))
      (C := tailIntegral μ 0 + s₀)
    intro z hz
    have hLz := tailIntegral_antitone μ hint hz.1.le
    have hLnn := tailIntegral_nonneg μ z
    have hH0 := survival_nonneg μ z
    have hH1 := survival_le_one μ z
    have hzH : z * survival μ z ≤ z := mul_le_of_le_one_right hz.1.le hH1
    have hzH0 : 0 ≤ z * survival μ z := mul_nonneg hz.1.le hH0
    rw [abs_of_nonneg (by linarith)]
    linarith [hz.2]
  set G₁ : ℝ → ℝ := fun s => ∫ z in s..s₀, priceDensity β μ d s₀ z * survival μ z with hG₁
  set F : ℝ → ℝ := fun s =>
    (∫ z in s..s₀, priceDensity β μ d s₀ z * (tailIntegral μ z + z * survival μ z)) -
      s * G₁ s - β * (tailIntegral μ s - d * s) with hF
  have hFac : AbsolutelyContinuousOnInterval F 0 s₀ := by
    have hA := absolutelyContinuous_integral_to hs₀.le hqL
    have hB := ((LipschitzWith.id).lipschitzOnWith (s := uIcc 0 s₀)).absolutelyContinuousOnInterval.mul
      (absolutelyContinuous_integral_to hs₀.le hqH)
    have hC := (hc.tailIntegral_absolutelyContinuous hint).sub
      (((LipschitzWith.id).lipschitzOnWith (s := uIcc 0 s₀)).absolutelyContinuousOnInterval.const_mul d)
    exact (hA.sub hB).sub (hC.const_mul β)
  have hderiv : ∀ᵐ s, s ∈ uIcc (0 : ℝ) s₀ → HasDerivAt F 0 s := by
    filter_upwards [ae_hasDerivAt_integral_to hs₀.le hqL, ae_hasDerivAt_integral_to hs₀.le hqH,
      hc.ae_hasDerivAt_tailIntegral hint, volume.ae_ne (0 : ℝ), volume.ae_ne s₀]
      with s h1 h2 h3 hne0 hnes hmem
    have hmem' : s ∈ Icc (0 : ℝ) s₀ := by rwa [uIcc_of_le hs₀.le] at hmem
    have hIoo : s ∈ Ioo (0 : ℝ) s₀ :=
      ⟨lt_of_le_of_ne hmem'.1 (Ne.symm hne0), lt_of_le_of_ne hmem'.2 hnes⟩
    have hL := hc.tailIntegral_pos hint hmem'.2
    have hd1 := h1 hmem
    have hd2 := h2 hmem
    have hd3 := h3 hIoo
    have hG₁val : G₁ s = β * (d - (d ^ 2 * s₀ - secondTail μ s₀ s) / tailIntegral μ s) :=
      hc.integral_priceDensity_survival (β := β) hint hmem'
    have hsG : HasDerivAt (fun s => s * G₁ s)
        (1 * G₁ s + s * (-(priceDensity β μ d s₀ s * survival μ s))) s :=
      (hasDerivAt_id s).mul hd2
    have hlin : HasDerivAt (fun s => β * (tailIntegral μ s - d * s))
        (β * (-survival μ s - d * 1)) s :=
      (hd3.sub ((hasDerivAt_id s).const_mul d)).const_mul β
    refine ((hd1.sub hsG).sub hlin).congr_deriv ?_
    rw [hG₁val]
    unfold priceDensity priceBracket
    field_simp
    ring
  obtain ⟨c, hconst⟩ := hFac.const_of_ae_hasDerivAt_zero hderiv
  have hs₀mem : s₀ ∈ uIcc (0 : ℝ) s₀ := by rw [uIcc_of_le hs₀.le]; exact ⟨hs₀.le, le_rfl⟩
  have hsmem : s ∈ uIcc (0 : ℝ) s₀ := by rw [uIcc_of_le hs₀.le]; exact hs
  have hend : F s₀ = 0 := by
    simp only [hF, hG₁, intervalIntegral.integral_same, mul_zero, sub_zero]
    rw [hc.eq]
    ring
  have hFs : F s = 0 := by
    have h1 := hconst s hsmem
    have h2 := hconst s₀ hs₀mem
    linarith
  -- expand the integrand
  have hsplit : (∫ z in s..s₀, priceDensity β μ d s₀ z * (tailIntegral μ z + (z - s) * survival μ z)) =
      (∫ z in s..s₀, priceDensity β μ d s₀ z * (tailIntegral μ z + z * survival μ z)) -
        s * G₁ s := by
    have hsub : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) s₀ → b ∈ Icc (0 : ℝ) s₀ →
        IntervalIntegrable (fun z => priceDensity β μ d s₀ z * survival μ z) volume a b :=
      fun a b ha hb => hqH.mono_set (by rw [uIcc_of_le hs₀.le]; exact uIcc_subset_Icc ha hb)
    have hsubL : IntervalIntegrable
        (fun z => priceDensity β μ d s₀ z * (tailIntegral μ z + z * survival μ z)) volume s s₀ :=
      hqL.mono_set (by rw [uIcc_of_le hs₀.le]; exact uIcc_subset_Icc hs ⟨hs₀.le, le_rfl⟩)
    simp only [hG₁]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hsubL
      ((hsub s s₀ hs ⟨hs₀.le, le_rfl⟩).const_mul s)]
    apply intervalIntegral.integral_congr
    intro z _
    ring
  rw [hsplit]
  simp only [hF] at hFs
  linarith

end Identity

end FixedPrice
