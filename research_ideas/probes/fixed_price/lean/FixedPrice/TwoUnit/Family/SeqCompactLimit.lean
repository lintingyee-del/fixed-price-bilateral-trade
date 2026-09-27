import FixedPrice.TwoUnit.Family.SeqCompactDeriv

/-!
# Work package A, compactness: the compact extension (`SeqCompactStatement`)

On the region `1/32 ≤ m_f ≤ 3/4`, `ξ₀ ≤ 600` the parameters lie in the box
`t ∈ [1/63, 3/5]`, `p ∈ [1/63, 1]`, `ξ₀ ∈ [1/5, 600]` (`ξ₀ ≥ v_f` since `h_f ≤ 1`). The extended
curves are `1`-Lipschitz and concave on `ℝ`. One extraction (Tychonoff on the box times the
values at the rationals) makes the parameters and the values at every rational converge; the
Lipschitz bound turns this into convergence at every point. The limit is concave, `1`-Lipschitz,
passes through `(c', p')` and `(ξ₀', 1)`, stays below the limit obstacles and above `t' > 0`, so it
is a class member. `T_f` converges by moving-endpoint dominated convergence (the integrands are
bounded by `63²`); `Q_f` converges the same way, the derivatives converging almost everywhere by
`tendsto_deriv_of_concave`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

theorem region_param_bounds {θ : Params} {P : ℝ → ℝ} (hP : InClass θ P)
    (hm : 1 / 32 ≤ θ.m ∧ θ.m ≤ 3 / 4 ∧ θ.ξ₀ ≤ 600) :
    θ.t ∈ Icc (1 / 63 : ℝ) (3 / 5) ∧ θ.p ∈ Icc (1 / 63 : ℝ) 1 ∧ θ.ξ₀ ∈ Icc (1 / 5 : ℝ) 600 := by
  have hadm := hP.admissible
  have ht := hadm.t_pos
  have h1t : 0 < 1 + θ.t := by linarith
  have hm1 : 1 / 32 ≤ 2 * θ.t / (1 + θ.t) := hm.1
  have hm2 : 2 * θ.t / (1 + θ.t) ≤ 3 / 4 := hm.2.1
  rw [le_div_iff₀ h1t] at hm1
  rw [div_le_iff₀ h1t] at hm2
  have ht1 : 1 / 63 ≤ θ.t := by linarith
  have ht2 : θ.t ≤ 3 / 5 := by linarith
  have hh := hP.h_le_one
  have hv : θ.v ≤ θ.ξ₀ := by
    unfold Params.h at hh; rwa [div_le_one hadm.ξ₀_pos] at hh
  have hv' : 1 / 5 ≤ θ.v := by unfold Params.v vF eF; linarith
  exact ⟨⟨ht1, ht2⟩, ⟨ht1.trans hadm.t_le_p, hadm.p_le_one⟩, ⟨hv'.trans hv, hm.2.2⟩⟩

theorem seq_compact' : SeqCompactStatement := by
  intro θ P hP hreg
  have hb := fun n => region_param_bounds (hP n) (hreg n)
  set E : ℕ → ℝ → ℝ := fun n => extCurve (θ n) (P n) with hE
  have hElip : ∀ n, LipschitzWith 1 (E n) := fun n => (hP n).ext_lipschitz
  have hEconc : ∀ n, ConcaveOn ℝ univ (E n) := fun n => (hP n).ext_concave
  have hE0 : ∀ n, E n 0 ∈ Icc (0 : ℝ) 1 := fun n => by
    refine ⟨((hP n).admissible.t_pos.le).trans ((hP n).t_le_ext le_rfl), ?_⟩
    have := ((hP n).ext_le_U 0).trans (min_le_left _ _)
    unfold Params.line₁ Params.δ δF at this
    have := (hP n).admissible.p_le_one
    have := (hP n).admissible.t_lt_one
    linarith
  have hEbd : ∀ n (q : ℚ), E n q ∈ Icc (-(1 + |(q : ℝ)|)) (1 + |(q : ℝ)|) := fun n q => by
    have h := (hElip n).dist_le_mul (q : ℝ) 0
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, sub_zero] at h
    have h0 := hE0 n
    rw [abs_le] at h
    constructor <;> linarith [h0.1, h0.2]
  -- one extraction for the parameters and the values at the rationals
  set x : ℕ → (ℝ × ℝ × ℝ) × (ℚ → ℝ) :=
    fun n => (((θ n).t, (θ n).p, (θ n).ξ₀), fun q => E n q) with hx
  set K : Set ((ℝ × ℝ × ℝ) × (ℚ → ℝ)) :=
    (Icc (1 / 63 : ℝ) (3 / 5) ×ˢ Icc (1 / 63 : ℝ) 1 ×ˢ Icc (1 / 5 : ℝ) 600) ×ˢ
      Set.pi univ fun q : ℚ => Icc (-(1 + |(q : ℝ)|)) (1 + |(q : ℝ)|) with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have hxK : ∀ n, x n ∈ K := fun n =>
    ⟨⟨(hb n).1, (hb n).2.1, (hb n).2.2⟩, fun q _ => hEbd n q⟩
  obtain ⟨xl, hxlK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hxK
  have ht : Tendsto (fun n => (θ (φ n)).t) atTop (𝓝 xl.1.1) :=
    ((continuous_fst.comp continuous_fst).tendsto xl).comp hlim
  have hp : Tendsto (fun n => (θ (φ n)).p) atTop (𝓝 xl.1.2.1) :=
    ((continuous_fst.comp (continuous_snd.comp continuous_fst)).tendsto xl).comp hlim
  have hξ : Tendsto (fun n => (θ (φ n)).ξ₀) atTop (𝓝 xl.1.2.2) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_fst)).tendsto xl).comp hlim
  have hq : ∀ q : ℚ, Tendsto (fun n => E (φ n) q) atTop (𝓝 (xl.2 q)) := fun q =>
    tendsto_pi_nhds.mp ((continuous_snd.tendsto xl).comp hlim) q
  obtain ⟨⟨hxt, hxp, hxξ⟩, -⟩ := hxlK
  set θ' : Params := ⟨xl.1.1, xl.1.2.1, xl.1.2.2⟩ with hθ'
  -- convergence at every point
  have hcauchy : ∀ y : ℝ, CauchySeq fun n => E (φ n) y := by
    intro y
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y - ε / 3 < y + ε / 3 by linarith)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hq q).cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    have l1 : dist (E (φ m) y) (E (φ m) q) ≤ dist y q := by
      simpa using (hElip (φ m)).dist_le_mul y q
    have l2 : dist (E (φ n) q) (E (φ n) y) ≤ dist y q := by
      rw [dist_comm]; simpa using (hElip (φ n)).dist_le_mul y q
    have hyq : dist y (q : ℝ) < ε / 3 := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    calc dist (E (φ m) y) (E (φ n) y)
        ≤ dist (E (φ m) y) (E (φ m) q) + dist (E (φ m) q) (E (φ n) q) +
            dist (E (φ n) q) (E (φ n) y) := dist_triangle4 _ _ _ _
      _ < ε := by linarith
  have hconv : ∀ y, ∃ a, Tendsto (fun n => E (φ n) y) atTop (𝓝 a) := fun y =>
    cauchySeq_tendsto_of_complete (hcauchy y)
  choose g hg using hconv
  -- the limit parameters
  have ht'0 : 0 < θ'.t := lt_of_lt_of_le (by norm_num) hxt.1
  have ht'1 : θ'.t < 1 := lt_of_le_of_lt hxt.2 (by norm_num)
  have hξ'0 : 0 < θ'.ξ₀ := lt_of_lt_of_le (by norm_num) hxξ.1
  have htp' : θ'.t ≤ θ'.p :=
    le_of_tendsto_of_tendsto' ht hp fun n => (hP (φ n)).admissible.t_le_p
  have hc : Tendsto (fun n => (θ (φ n)).c) atTop (𝓝 θ'.c) := by
    simp only [Params.c, cF]; exact (hp.sub ht).div_const 2
  have hδ : Tendsto (fun n => (θ (φ n)).δ) atTop (𝓝 θ'.δ) := by
    simp only [Params.δ, δF]; exact (hp.add ht).div_const 2
  have he : Tendsto (fun n => (θ (φ n)).e) atTop (𝓝 θ'.e) := by
    simp only [Params.e, eF]; exact (tendsto_const_nhds.add ht).div_const 2
  have hh : Tendsto (fun n => (θ (φ n)).h) atTop (𝓝 θ'.h) := by
    simp only [Params.h, Params.v, vF]
    exact (tendsto_const_nhds.sub he).div hξ hξ'0.ne'
  have hcξ' : θ'.c ≤ θ'.ξ₀ :=
    le_of_tendsto_of_tendsto' hc hξ fun n => (hP (φ n)).c_le_ξ₀
  have hc'0 : 0 ≤ θ'.c := by
    show 0 ≤ cF θ'.t θ'.p; unfold cF; linarith
  have hadm' : θ'.Admissible := ⟨ht'0, ht'1, htp', hxp.2, hξ'0, hcξ'⟩
  -- the limit curve
  have hglip : LipschitzWith 1 g := LipschitzWith.of_dist_le_mul fun y z =>
    le_of_tendsto_of_tendsto' ((hg y).dist (hg z)) tendsto_const_nhds fun n =>
      (hElip (φ n)).dist_le_mul y z
  have hgconc : ConcaveOn ℝ univ g := ⟨convex_univ, fun y _ z _ a b ha hb hab =>
    le_of_tendsto_of_tendsto' (((hg y).const_smul a).add ((hg z).const_smul b))
      (hg (a • y + b • z)) fun n => (hEconc (φ n)).2 (mem_univ y) (mem_univ z) ha hb hab⟩
  have hgt : ∀ y, 0 ≤ y → θ'.t ≤ g y := fun y hy =>
    le_of_tendsto_of_tendsto' ht (hg y) fun n => (hP (φ n)).t_le_ext hy
  have hgU : ∀ y, g y ≤ θ'.U y := fun y => by
    refine le_of_tendsto_of_tendsto' (hg y) ?_ fun n => (hP (φ n)).ext_le_U y
    simp only [Params.U, Params.line₁, Params.line₂]
    exact (tendsto_const_nhds.add hδ).min ((hh.mul_const y).add he)
  have hend : ∀ {a : ℕ → ℝ} {a' v' : ℝ} {vv : ℕ → ℝ}, Tendsto a atTop (𝓝 a') →
      Tendsto vv atTop (𝓝 v') → (∀ n, E (φ n) (a n) = vv n) → g a' = v' := by
    intro a a' v' vv ha hv hEa
    have hlo : Tendsto (fun n => vv n - |a' - a n|) atTop (𝓝 v') := by
      simpa using hv.sub (((tendsto_const_nhds (x := a')).sub ha).abs)
    have hhi : Tendsto (fun n => vv n + |a' - a n|) atTop (𝓝 v') := by
      simpa using hv.add (((tendsto_const_nhds (x := a')).sub ha).abs)
    have hsq : Tendsto (fun n => E (φ n) a') atTop (𝓝 v') := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => ?_) (fun n => ?_)
      · have := (hElip (φ n)).dist_le_mul a' (a n)
        rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, hEa n] at this
        linarith [le_abs_self (E (φ n) a' - vv n), neg_abs_le (E (φ n) a' - vv n)]
      · have := (hElip (φ n)).dist_le_mul a' (a n)
        rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, hEa n] at this
        linarith [le_abs_self (E (φ n) a' - vv n)]
    exact tendsto_nhds_unique (hg a') hsq
  have hgc : g θ'.c = θ'.p := hend hc hp fun n => by
    simp only [E]
    rw [(hP (φ n)).extCurve_of_le le_rfl, Params.line₁_c]
  have hgξ : g θ'.ξ₀ = 1 := hend hξ tendsto_const_nhds fun n => by
    simp only [E]
    rw [(hP (φ n)).extCurve_of_ge le_rfl, (hP (φ n)).admissible.line₂_ξ₀]
  have hP' : InClass θ' g := {
    admissible := hadm'
    pos := fun y hy => ht'0.trans_le (hgt y (hc'0.trans hy.1))
    concave := hgconc.subset (subset_univ _) (convex_Icc _ _)
    lipschitz := ⟨1, hglip.lipschitzOnWith⟩
    left_end := hgc
    right_end := hgξ
    obstacle := fun y _ => hgU y }
  -- the integrals: moving endpoints in `[0, 600]`
  have hab : ∀ n, (0 : ℝ) ≤ (θ (φ n)).c ∧ (θ (φ n)).c ≤ (θ (φ n)).ξ₀ ∧ (θ (φ n)).ξ₀ ≤ 600 :=
    fun n => ⟨(hP (φ n)).admissible.c_nonneg, (hP (φ n)).c_le_ξ₀, (hreg (φ n)).2.2⟩
  have hElow : ∀ n, ∀ y ∈ Icc (0 : ℝ) 600, 1 / 63 ≤ E (φ n) y := fun n y hy =>
    (hb (φ n)).1.1.trans ((hP (φ n)).t_le_ext hy.1)
  have hglow : ∀ y ∈ Icc (0 : ℝ) 600, 1 / 63 ≤ g y := fun y hy =>
    hxt.1.trans (hgt y hy.1)
  have hT : Tendsto (fun n => Tf (θ (φ n)) (P (φ n))) atTop (𝓝 (Tf θ' g)) := by
    have hTn : ∀ n, Tf (θ (φ n)) (P (φ n)) =
        ∫ y in (θ (φ n)).c..(θ (φ n)).ξ₀, (E (φ n) y ^ 2)⁻¹ := fun n => by
      unfold Tf
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le (hP (φ n)).c_le_ξ₀] at hy
      simp only [E]
      rw [InClass.extCurve_of_mem hy]
    simp_rw [hTn]
    refine movingEndpoint' (fun n y => (E (φ n) y ^ 2)⁻¹) (fun y => (g y ^ 2)⁻¹)
      (fun n => (θ (φ n)).c) (fun n => (θ (φ n)).ξ₀) θ'.c θ'.ξ₀ 0 600 (63 ^ 2) hab hc hξ
      (fun n => ((hElip (φ n)).continuous.measurable.pow_const 2).inv.aestronglyMeasurable)
      (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      have h1 := hElow n y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      calc (63 ^ 2 : ℝ)⁻¹ = (1 / 63) ^ 2 := by norm_num
        _ ≤ E (φ n) y ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      have hne : g y ^ 2 ≠ 0 := pow_ne_zero 2 (lt_of_lt_of_le (by norm_num) (hglow y hy)).ne'
      exact ((hg y).pow 2).inv₀ hne
  have hQ : Tendsto (fun n => Qf (θ (φ n)) (P (φ n))) atTop (𝓝 (Qf θ' g)) := by
    have hQn : ∀ n, Qf (θ (φ n)) (P (φ n)) =
        ∫ y in (θ (φ n)).c..(θ (φ n)).ξ₀, y * (deriv (E (φ n)) y / E (φ n) y) ^ 2 := fun n => by
      unfold Qf
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume (θ (φ n)).ξ₀] with y hyne hy
      rw [uIoc_of_le (hP (φ n)).c_le_ξ₀] at hy
      have hyo : y ∈ Ioo (θ (φ n)).c (θ (φ n)).ξ₀ := ⟨hy.1, lt_of_le_of_ne hy.2 hyne⟩
      have heq := InClass.ext_eventuallyEq (P := P (φ n)) hyo
      simp only [E]
      rw [heq.deriv_eq, InClass.extCurve_of_mem (Ioo_subset_Icc_self hyo)]
    simp_rw [hQn]
    have hgd : ∀ᵐ y, DifferentiableAt ℝ g y := hglip.ae_differentiableAt_real
    have hEd : ∀ᵐ y, ∀ n, DifferentiableAt ℝ (E (φ n)) y :=
      ae_all_iff.mpr fun n => (hElip (φ n)).ae_differentiableAt_real
    refine movingEndpoint' (fun n y => y * (deriv (E (φ n)) y / E (φ n) y) ^ 2)
      (fun y => y * (deriv g y / g y) ^ 2)
      (fun n => (θ (φ n)).c) (fun n => (θ (φ n)).ξ₀) θ'.c θ'.ξ₀ 0 600 (600 * 63 ^ 2) hab hc hξ
      (fun n => (measurable_id.mul (((measurable_deriv _).div
        (hElip (φ n)).continuous.measurable).pow_const 2)).aestronglyMeasurable)
      (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      have h1 := hElow n y hy
      have hd : |deriv (E (φ n)) y| ≤ 1 := by
        have := norm_deriv_le_of_lipschitz (x₀ := y) (hElip (φ n))
        rwa [Real.norm_eq_abs, NNReal.coe_one] at this
      have hq : |deriv (E (φ n)) y / E (φ n) y| ≤ 63 := by
        rw [abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num) h1), div_le_iff₀ (by linarith)]
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hy.1, abs_pow]
      have := pow_le_pow_left₀ (abs_nonneg _) hq 2
      exact mul_le_mul hy.2 this (by positivity) (by norm_num)
    · filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hgd,
        ae_restrict_of_ae hEd] with y hy hgy hEy
      have hne : g y ≠ 0 := (lt_of_lt_of_le (by norm_num) (hglow y hy)).ne'
      have hder := tendsto_deriv_of_concave (fun n => hEconc (φ n)) hg hgy hEy
      exact tendsto_const_nhds.mul ((hder.div (hg y) hne).pow 2)
  exact ⟨φ, hφ, θ', g, hP', ht, hp, hξ, hT, hQ⟩

end FixedPrice.TwoUnit.Family
