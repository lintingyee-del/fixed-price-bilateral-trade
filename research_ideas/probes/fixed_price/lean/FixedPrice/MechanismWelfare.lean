import FixedPrice.Mechanism
import FixedPrice.JointWelfare

/-! Proposition 11.2, the welfare bound. Under any joint prior on `(0, Λ)²` that is absolutely
continuous with respect to Lebesgue measure, a mechanism of `DSICOn Λ` has expected welfare at
most the supremum of the posted-price welfares. By the representation,
`(b - s) φ(s, b) = (b - s) (G(b) - G(s)) 1{s < b}` almost surely, and
`G(b) - G(s) = ∫_0^1 1{G(s) < u ≤ G(b)} du`; at each level `u` the event
`{G(s) < u ≤ G(b)}` forces `s ≤ z(u) ≤ b` for the posted price `z(u) = inf {x : u ≤ G(x)}`.
Measurability of `φ` is not needed: the welfare integrand agrees almost surely with a
measurable function. -/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice

/-- The monotone extension of the price distribution function: `0` below, `1` above. -/
def extendCDF (Λ : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Ioo 0 Λ then F x else if x ≤ 0 then 0 else 1

theorem extendCDF_monotone {Λ : ℝ} {F : ℝ → ℝ} (hF : MonotoneOn F (Ioo 0 Λ))
    (hF01 : ∀ x ∈ Ioo 0 Λ, F x ∈ Icc (0 : ℝ) 1) : Monotone (extendCDF Λ F) := by
  intro x y hxy
  unfold extendCDF
  by_cases hx : x ∈ Ioo 0 Λ <;> by_cases hy : y ∈ Ioo 0 Λ
  · rw [if_pos hx, if_pos hy]; exact hF hx hy hxy
  · rw [if_pos hx, if_neg hy, if_neg (by intro h; exact absurd (hx.1.trans_le hxy) (not_lt.mpr h))]
    exact (hF01 x hx).2
  · rw [if_neg hx, if_pos hy]
    by_cases hx0 : x ≤ 0
    · rw [if_pos hx0]; exact (hF01 y hy).1
    · exfalso
      push Not at hx0
      exact hx ⟨hx0, hxy.trans_lt hy.2⟩
  · rw [if_neg hx, if_neg hy]
    by_cases hx0 : x ≤ 0
    · rw [if_pos hx0]; split_ifs <;> norm_num
    · push Not at hx0
      rw [if_neg (not_le.mpr hx0), if_neg (not_le.mpr (hx0.trans_le hxy))]

theorem extendCDF_mem {Λ : ℝ} {F : ℝ → ℝ} (hF01 : ∀ x ∈ Ioo 0 Λ, F x ∈ Icc (0 : ℝ) 1)
    (x : ℝ) : extendCDF Λ F x ∈ Icc (0 : ℝ) 1 := by
  unfold extendCDF
  split_ifs with h1 h2
  · exact hF01 x h1
  · norm_num
  · norm_num

theorem extendCDF_of_nonpos {Λ : ℝ} {F : ℝ → ℝ} {x : ℝ} (hx : x ≤ 0) : extendCDF Λ F x = 0 := by
  unfold extendCDF
  rw [if_neg (fun h => absurd h.1 (not_lt.mpr hx)), if_pos hx]

/-- The posted price of level `u`: `z(u) = inf {x : u ≤ G(x)}`. -/
def levelPrice (G : ℝ → ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ G x}

theorem le_levelPrice_le {G : ℝ → ℝ} (hG : Monotone G) {u s b : ℝ}
    (hbdd : BddBelow {x | u ≤ G x}) (hs : G s < u) (hb : u ≤ G b) :
    s ≤ levelPrice G u ∧ levelPrice G u ≤ b := by
  unfold levelPrice
  constructor
  · by_contra h
    push Not at h
    obtain ⟨x, hx, hxs⟩ := exists_lt_of_csInf_lt ⟨b, hb⟩ h
    have := hG hxs.le
    simp only [mem_setOf_eq] at hx
    linarith
  · exact csInf_le hbdd hb

theorem volume_diagonal_prod : (volume : Measure (ℝ × ℝ)) {p | p.1 = p.2} = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  have : ∀ x : ℝ, (volume : Measure ℝ) (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y
      simp [eq_comm]
    rw [this, Real.volume_singleton]
  simp

theorem volume_fst_mem_countable {E : Set ℝ} (hE : E.Countable) :
    (volume : Measure (ℝ × ℝ)) {p | p.1 ∈ E} = 0 := by
  have : {p : ℝ × ℝ | p.1 ∈ E} = E ×ˢ univ := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, hE.measure_zero, zero_mul]

section Welfare

variable {Λ : ℝ} {φ pay : ℝ → ℝ → ℝ}

/-- **Proposition 11.2, welfare bound.** Under an absolutely continuous joint prior on the
report square `(0, Λ)²`, the expected welfare of a `DSICOn Λ` mechanism is at most the
supremum of posted-price welfares. -/
theorem DSICOn.mechWelfare_le (M : DSICOn Λ φ pay)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    (hsupp : ∀ᵐ p ∂μ, p ∈ Ioo 0 Λ ×ˢ Ioo 0 Λ) :
    mechWelfare μ φ ≤ ⨆ z : ℝ, jointPriceWelfare μ z := by
  obtain ⟨F, hFm, hF01, E, hE, hrep, hzero⟩ := M.representation
  set G := extendCDF Λ F with hGdef
  have hG : Monotone G := extendCDF_monotone hFm hF01
  have hGm : Measurable G := hG.measurable
  have hG01 : ∀ x, G x ∈ Icc (0 : ℝ) 1 := extendCDF_mem hF01
  have hGF : ∀ x ∈ Ioo 0 Λ, G x = F x := fun x hx => by simp [hGdef, extendCDF, hx]
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  -- the layer function
  set f : (ℝ × ℝ) × ℝ → ℝ := fun q =>
    if 0 < q.1.1 ∧ q.1.1 < q.1.2 ∧ q.1.2 < Λ ∧ G q.1.1 < q.2 ∧ q.2 ≤ G q.1.2
    then q.1.2 - q.1.1 else 0 with hf
  have m1 : Measurable (fun q : (ℝ × ℝ) × ℝ => q.1.1) := measurable_fst.comp measurable_fst
  have m2 : Measurable (fun q : (ℝ × ℝ) × ℝ => q.1.2) := measurable_snd.comp measurable_fst
  have m3 : Measurable (fun q : (ℝ × ℝ) × ℝ => q.2) := measurable_snd
  have hfmeas : Measurable f := by
    apply Measurable.ite _ (m2.sub m1) measurable_const
    exact (measurableSet_lt measurable_const m1).inter ((measurableSet_lt m1 m2).inter
      ((measurableSet_lt m2 measurable_const).inter ((measurableSet_lt (hGm.comp m1) m3).inter
        (measurableSet_le m3 (hGm.comp m2)))))
  have hfnn : ∀ q, 0 ≤ f q := by
    intro q
    simp only [hf]
    split_ifs with h
    · linarith [h.2.1]
    · exact le_rfl
  have hfbd : ∀ q, ‖f q‖ ≤ |Λ| := by
    intro q
    rw [Real.norm_of_nonneg (hfnn q)]
    simp only [hf]
    split_ifs with h
    · have := le_abs_self Λ
      linarith [h.1, h.2.1, h.2.2.1]
    · exact abs_nonneg Λ
  have hfint : Integrable f (μ.prod ν) :=
    Integrable.of_bound hfmeas.aestronglyMeasurable |Λ| (ae_of_all _ hfbd)
  have h1int : Integrable (fun p : ℝ × ℝ => p.1) μ := by
    refine Integrable.of_bound measurable_fst.aestronglyMeasurable |Λ| ?_
    filter_upwards [hsupp] with p hp
    rw [mem_prod] at hp
    rw [Real.norm_eq_abs, abs_of_pos hp.1.1]
    exact hp.1.2.le.trans (le_abs_self Λ)
  -- the representation holds almost surely
  have hE' : ∀ᵐ p ∂μ, p.1 ∉ E :=
    hac.ae_le (measure_eq_zero_iff_ae_notMem.mp (volume_fst_mem_countable hE))
  have hD' : ∀ᵐ p ∂μ, p.1 ≠ p.2 :=
    hac.ae_le (measure_eq_zero_iff_ae_notMem.mp volume_diagonal_prod)
  have hae : ∀ᵐ p ∂μ, p.1 + (p.2 - p.1) * φ p.1 p.2 = p.1 + ∫ u, f (p, u) ∂ν := by
    filter_upwards [hsupp, hE', hD'] with p hp hpE hpD
    rw [mem_prod] at hp
    obtain ⟨hs, hb⟩ := hp
    rcases lt_or_gt_of_ne hpD with hlt | hgt
    · obtain ⟨hφ, -⟩ := hrep p.1 hs hpE p.2 hb hlt
      have hfu : (fun u => f (p, u)) =
          (Ioc (G p.1) (G p.2)).indicator (fun _ => p.2 - p.1) := by
        ext u
        simp only [hf, indicator, mem_Ioc]
        by_cases hu : G p.1 < u ∧ u ≤ G p.2
        · rw [if_pos ⟨hs.1, hlt, hb.2, hu⟩, if_pos hu]
        · rw [if_neg (fun h => hu ⟨h.2.2.2.1, h.2.2.2.2⟩), if_neg hu]
      rw [hfu, hν, setIntegral_indicator measurableSet_Ioc,
        inter_eq_right.mpr (Ioc_subset_Ioc (hG01 _).1 (hG01 _).2), setIntegral_const,
        Real.volume_real_Ioc_of_le (hG hlt.le), hφ, ← hGF _ hs, ← hGF _ hb, smul_eq_mul]
      ring
    · obtain ⟨hφ, -⟩ := hzero p.1 hs p.2 hb hgt
      have hfu : (fun u => f (p, u)) = fun _ => 0 := by
        ext u
        simp only [hf]
        rw [if_neg (fun h => absurd h.2.1 (not_lt.mpr hgt.le))]
      rw [hfu, hφ, integral_zero]
      ring
  -- posted prices
  have hpg_int : ∀ z, Integrable (priceGainAt z) μ := by
    intro z
    refine Integrable.of_bound (measurable_priceGainAt z).aestronglyMeasurable |Λ| ?_
    filter_upwards [hsupp] with p hp
    rw [mem_prod] at hp
    rw [Real.norm_of_nonneg (priceGainAt_nonneg z p)]
    unfold priceGainAt
    split_ifs
    · have := le_abs_self Λ
      linarith [hp.1.1, hp.2.2]
    · exact abs_nonneg Λ
  have hjoint : ∀ z, jointPriceWelfare μ z = ∫ p, p.1 ∂μ + ∫ p, priceGainAt z p ∂μ :=
    fun z => integral_add h1int (hpg_int z)
  have hbdd : BddAbove (range (jointPriceWelfare μ)) := by
    refine ⟨∫ p, p.1 ∂μ + |Λ|, ?_⟩
    rintro _ ⟨z, rfl⟩
    rw [hjoint]
    have : ∫ p, priceGainAt z p ∂μ ≤ ∫ _p, |Λ| ∂μ := by
      apply integral_mono_ae (hpg_int z) (integrable_const _)
      filter_upwards [hsupp] with p hp
      rw [mem_prod] at hp
      unfold priceGainAt
      split_ifs
      · have := le_abs_self Λ
        linarith [hp.1.1, hp.2.2]
      · exact abs_nonneg Λ
    rw [integral_const, probReal_univ, one_smul] at this
    linarith
  set S := ⨆ z, jointPriceWelfare μ z with hS
  -- the bound at each level
  have hlevel : ∀ u ∈ Ioc (0 : ℝ) 1, ∫ p, f (p, u) ∂μ ≤ S - ∫ p, p.1 ∂μ := by
    intro u hu
    set z := levelPrice G u
    have hbddB : BddBelow {x | u ≤ G x} := by
      refine ⟨0, fun x hx => ?_⟩
      by_contra hneg
      push Not at hneg
      have : G x = 0 := extendCDF_of_nonpos hneg.le
      simp only [mem_setOf_eq] at hx
      linarith [hu.1]
    have hpt : ∀ p, f (p, u) ≤ priceGainAt z p := by
      intro p
      simp only [hf]
      split_ifs with h
      · obtain ⟨h1, h2⟩ := le_levelPrice_le hG hbddB h.2.2.2.1 h.2.2.2.2
        unfold priceGainAt
        rw [if_pos ⟨h1, h2⟩]
      · exact priceGainAt_nonneg z p
    have hfu_int : Integrable (fun p => f (p, u)) μ :=
      Integrable.of_bound (hfmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        |Λ| (ae_of_all _ fun p => hfbd _)
    have h1 : ∫ p, f (p, u) ∂μ ≤ ∫ p, priceGainAt z p ∂μ :=
      integral_mono hfu_int (hpg_int z) hpt
    have h2 : jointPriceWelfare μ z ≤ S := le_ciSup hbdd z
    rw [hjoint] at h2
    linarith
  have hswap : ∫ p, ∫ u, f (p, u) ∂ν ∂μ = ∫ u, ∫ p, f (p, u) ∂μ ∂ν :=
    integral_integral_swap (f := fun p u => f (p, u)) hfint
  have hint_u : Integrable (fun u => ∫ p, f (p, u) ∂μ) ν := hfint.integral_prod_right
  calc mechWelfare μ φ = ∫ p, (p.1 + ∫ u, f (p, u) ∂ν) ∂μ := integral_congr_ae hae
    _ = ∫ p, p.1 ∂μ + ∫ p, ∫ u, f (p, u) ∂ν ∂μ := integral_add h1int hfint.integral_prod_left
    _ = ∫ p, p.1 ∂μ + ∫ u, ∫ p, f (p, u) ∂μ ∂ν := by rw [hswap]
    _ ≤ ∫ p, p.1 ∂μ + ∫ _u, (S - ∫ p, p.1 ∂μ) ∂ν := by
        have := integral_mono_ae hint_u (integrable_const (S - ∫ p, p.1 ∂μ))
          (ae_restrict_of_forall_mem measurableSet_Ioc hlevel)
        linarith
    _ = S := by
        rw [integral_const, hν, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          Real.volume_Ioc]
        norm_num

end Welfare

end FixedPrice

