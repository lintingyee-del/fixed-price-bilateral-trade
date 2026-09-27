import FixedPrice.TwoUnit.Family.RealizationIntegrals

/-!
# Work package E, realization helpers: efficient gains and the price-gain bound

* `E(Z₁ - Y₁)₊ + E(Z₂ - Y₂)₊ = G_f - 2` for the independent body vectors.
* The unshifted "right-limit" gain at a price `w` plus the atom's share,
  `Φ(w) = E(Z₁ - w)₊ P(Y₁ ≤ w) + E(w - Y₁)₊ P(Z₁ > w) + (a_f - w)₊ P(Y₂ ≤ w)
    + E(w - Y₂)₊ 1{w < a_f} + P(Y₁ ≤ w) + P(Y₂ ≤ w)`,
  is at most `2` at every `w`: it vanishes below `0`, equals
  `m_f(2 + z̄_f + a_f) = 2` on `[0, a_f)` (certified `low_price_balance`), equals
  `N_f + m_f = 2` on `[a_f, b_f)` (certified `first_unit_equalizer`, with the exact body
  distributions in the curve coordinate), and is at most `P(Y₁ ≤ w) + P(Y₂ ≤ w) ≤ 2` from `b_f`
  on.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

namespace Realize

variable {θ : Params} {P : ℝ → ℝ}

theorem measurableSet_Iic_m : MeasurableSet {v : ℝ | v ≤ θ.m} := measurableSet_Iic

theorem measurableSet_Ioi_m : MeasurableSet {v : ℝ | θ.m < v} := measurableSet_Ioi

theorem unif_real_le_m (hP : InClass θ P) : unifLaw.real {v | v ≤ θ.m} = θ.m :=
  unif_real_of_eq (unif_le_m hP) hP.admissible.m_pos.le

theorem unif_real_gt_m (hP : InClass θ P) : unifLaw.real {v | θ.m < v} = 1 - θ.m :=
  unif_real_of_eq (unif_gt_m hP) (by linarith [hP.admissible.m_lt_one])

/-! ### Efficient gains of the body -/

/-- `E(Z₁ - Y₁)₊ = m_f E Z₁ + ∫ P⁻² (1 - buyerCurveCDF)(sellerCurveCDF - m_f)`. -/
theorem integral_posPart_Z_Y₁ (hI : FamilyIdentities) (hP : InClass θ P) :
    ∫ q, max (Zf θ P q.1 - Y₁f θ P q.2) 0 ∂(unifLaw.prod unifLaw) =
      θ.m * ∫ u, Zf θ P u ∂unifLaw +
        ∫ r in Icc θ.c θ.ξ₀,
          gc θ P r * ((1 - buyerCurveCDF θ P r) * (sellerCurveCDF θ P r - θ.m)) := by
  set S : Set ((ℝ × ℝ) × ℝ) :=
    {p | θ.m < p.1.2 ∧ qS θ P p.1.2 ≤ p.2 ∧ p.2 < qB θ P p.1.1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const (measurable_snd.comp measurable_fst)).inter
      ((measurableSet_le ((measurable_qS hI hP).comp (measurable_snd.comp measurable_fst))
        measurable_snd).inter
        (measurableSet_lt measurable_snd ((measurable_qB hP).comp
          (measurable_fst.comp measurable_fst))))
  have hpt : ∀ q : ℝ × ℝ, max (Zf θ P q.1 - Y₁f θ P q.2) 0 =
      Zf θ P q.1 * {v : ℝ | v ≤ θ.m}.indicator 1 q.2 +
        ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun p => gc θ P p.2) (q, r) := by
    rintro ⟨u, v⟩
    by_cases hv : v ≤ θ.m
    · have e : ∀ r, S.indicator (fun p => gc θ P p.2) ((u, v), r) = 0 := fun r =>
        indicator_of_notMem (show ((u, v), r) ∉ S from fun h' => absurd h'.1 (not_lt.mpr hv)) _
      simp only
      simp_rw [e]
      rw [Y₁f_of_le hv, indicator_of_mem (show v ∈ {v : ℝ | v ≤ θ.m} from hv),
        Pi.one_apply, sub_zero, max_eq_left (Zf_nonneg hP u)]
      simp
    · have hv' : θ.m < v := not_le.mp hv
      have h := posPart_sF_sub hP (qS_mem hP v) (qB_mem hP u)
      have e : ∀ r, S.indicator (fun p => gc θ P p.2) ((u, v), r) =
          (Ico (qS θ P v) (qB θ P u)).indicator (gc θ P) r := by
        intro r
        by_cases hr : r ∈ Ico (qS θ P v) (qB θ P u)
        · rw [indicator_of_mem hr, indicator_of_mem (show ((u, v), r) ∈ S from ⟨hv', hr⟩)]
        · rw [indicator_of_notMem hr,
            indicator_of_notMem (show ((u, v), r) ∉ S from fun h' => hr h'.2)]
      simp only
      simp_rw [e]
      rw [Y₁f_of_gt hv', indicator_of_notMem (show v ∉ {v : ℝ | v ≤ θ.m} from hv), mul_zero,
        zero_add]
      exact h
  have hbd : ∀ q : ℝ × ℝ, |Zf θ P q.1 * {v : ℝ | v ≤ θ.m}.indicator 1 q.2| ≤ bF θ P := by
    intro q
    rw [abs_mul]
    have h1 := abs_Zf_le hP q.1
    have h2 : |{v : ℝ | v ≤ θ.m}.indicator (1 : ℝ → ℝ) q.2| ≤ 1 := by
      by_cases hq : q.2 ∈ {v : ℝ | v ≤ θ.m}
      · rw [indicator_of_mem hq]; simp
      · rw [indicator_of_notMem hq]; simp
    nlinarith [abs_nonneg (Zf θ P q.1), abs_nonneg ({v : ℝ | v ≤ θ.m}.indicator (1 : ℝ → ℝ) q.2)]
  have hmeas1 : Measurable (fun q : ℝ × ℝ => Zf θ P q.1 * {v : ℝ | v ≤ θ.m}.indicator 1 q.2) :=
    ((measurable_Zf hP).comp measurable_fst).mul
      ((measurable_const.indicator measurableSet_Iic_m).comp measurable_snd)
  have hint1 := integrable_prod_of_bound hmeas1 hbd
  have e1 : (fun q : ℝ × ℝ => ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun p => gc θ P p.2) (q, r)) =
      fun q => max (Zf θ P q.1 - Y₁f θ P q.2) 0 -
        Zf θ P q.1 * {v : ℝ | v ≤ θ.m}.indicator 1 q.2 := by
    ext q; rw [hpt q]; ring
  have hmeas2 : Measurable (fun q : ℝ × ℝ => max (Zf θ P q.1 - Y₁f θ P q.2) 0) :=
    (((measurable_Zf hP).comp measurable_fst).sub
      ((measurable_Y₁f hI hP).comp measurable_snd)).max measurable_const
  have hbd2 : ∀ q : ℝ × ℝ, |max (Zf θ P q.1 - Y₁f θ P q.2) 0| ≤ bF θ P := by
    intro q
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [Zf_le_bF hP q.1, Y₁f_nonneg hP q.2]) (bF_nonneg hP)
  have hint2 := integrable_prod_of_bound hmeas2 hbd2
  have hsplit : ∫ q, max (Zf θ P q.1 - Y₁f θ P q.2) 0 ∂(unifLaw.prod unifLaw) =
      ∫ q, Zf θ P q.1 * {v : ℝ | v ≤ θ.m}.indicator 1 q.2 ∂(unifLaw.prod unifLaw) +
        ∫ q, (∫ r in Icc θ.c θ.ξ₀, S.indicator (fun p => gc θ P p.2) (q, r))
          ∂(unifLaw.prod unifLaw) := by
    rw [e1, integral_sub hint2 hint1]; ring
  rw [hsplit, integral_prod_mul (fun u => Zf θ P u)
      (fun v => {v : ℝ | v ≤ θ.m}.indicator (1 : ℝ → ℝ) v),
    integral_indicator_one measurableSet_Iic_m, unif_real_le_m hP,
    integral_integral_indicator hSm (measurable_gc hP) (abs_gc_le hP)]
  have e3 : ∫ r in Icc θ.c θ.ξ₀, gc θ P r * (unifLaw.prod unifLaw).real {x | (x, r) ∈ S} =
      ∫ r in Icc θ.c θ.ξ₀,
        gc θ P r * ((1 - buyerCurveCDF θ P r) * (sellerCurveCDF θ P r - θ.m)) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun r _ => ?_)
    have hsec : {x : ℝ × ℝ | (x, r) ∈ S} =
        {u | r < qB θ P u} ×ˢ {v | θ.m < v ∧ qS θ P v ≤ r} := by
      ext ⟨u, v⟩
      simp only [hS, mem_setOf_eq, mem_prod]
      exact ⟨fun ⟨a, b, c⟩ => ⟨c, a, b⟩, fun ⟨c, a, b⟩ => ⟨a, b, c⟩⟩
    rw [hsec, measureReal_def, Measure.prod_prod, unif_qB_gt hP r, unif_qS_le hI hP r,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [buyerCDF_le_one hP r]),
      ENNReal.toReal_ofReal (by linarith [m_le_sellerCDF hI hP r])]
  rw [e3]; ring

/-- `E(a_f - Y₂)₊ = m_f a_f`. -/
theorem integral_posPart_a_Y₂ (hP : InClass θ P) :
    ∫ v, max (θ.a - Y₂f θ P v) 0 ∂unifLaw = θ.m * θ.a := by
  have e : (fun v => max (θ.a - Y₂f θ P v) 0) = fun v => {v : ℝ | v ≤ θ.m}.indicator
      (fun _ => θ.a) v := by
    ext v
    by_cases hv : v ≤ θ.m
    · rw [Y₂f_of_le hv, indicator_of_mem (show v ∈ {v : ℝ | v ≤ θ.m} from hv), sub_zero,
        max_eq_left hP.admissible.a_nonneg]
    · rw [Y₂f_of_gt (not_le.mp hv), indicator_of_notMem (show v ∉ {v : ℝ | v ≤ θ.m} from hv),
        max_eq_right (by linarith [a_le_bF hP])]
  rw [e, integral_indicator_const _ measurableSet_Iic_m, unif_real_le_m hP, smul_eq_mul]

/-- The body efficient gains: `E(Z₁ - Y₁)₊ + E(Z₂ - Y₂)₊ = G_f - 2`. -/
theorem integral_posPart_body (hI : FamilyIdentities) (hP : InClass θ P) :
    ∫ q, (max (Zf θ P q.1 - Y₁f θ P q.2) 0 + max (θ.a - Y₂f θ P q.2) 0)
      ∂(unifLaw.prod unifLaw) = Gf θ P - 2 := by
  have hm1 : Measurable (fun q : ℝ × ℝ => max (Zf θ P q.1 - Y₁f θ P q.2) 0) :=
    (((measurable_Zf hP).comp measurable_fst).sub
      ((measurable_Y₁f hI hP).comp measurable_snd)).max measurable_const
  have hb1 : ∀ q : ℝ × ℝ, |max (Zf θ P q.1 - Y₁f θ P q.2) 0| ≤ bF θ P := by
    intro q
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [Zf_le_bF hP q.1, Y₁f_nonneg hP q.2]) (bF_nonneg hP)
  have hm2 : Measurable (fun q : ℝ × ℝ => max (θ.a - Y₂f θ P q.2) 0) :=
    (measurable_const.sub ((measurable_Y₂f hP).comp measurable_snd)).max measurable_const
  have hb2 : ∀ q : ℝ × ℝ, |max (θ.a - Y₂f θ P q.2) 0| ≤ bF θ P := by
    intro q
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [a_le_bF hP, Y₂f_nonneg hP q.2]) (bF_nonneg hP)
  rw [integral_add (integrable_prod_of_bound hm1 hb1) (integrable_prod_of_bound hm2 hb2),
    integral_posPart_Z_Y₁ hI hP, integral_Zf hP,
    integral_fun_snd (fun v => max (θ.a - Y₂f θ P v) 0), probReal_univ, one_smul,
    integral_posPart_a_Y₂ hP]
  -- split the curve integral
  have hB1 : ∀ r, |gc θ P r * ((1 - buyerCurveCDF θ P r) * sellerCurveCDF θ P r)| ≤
      (θ.p ^ 2)⁻¹ := by
    intro r
    have h0 := gc_pos hP r; have h1 := gc_le hP r
    have g0 := buyerCDF_nonneg hP r; have g1 := buyerCDF_le_one hP r
    have s0 := (hP.admissible.m_pos.le).trans (m_le_sellerCDF hI hP r)
    have s1 := sellerCDF_le_one hP r
    rw [abs_of_nonneg (by positivity)]
    have : (1 - buyerCurveCDF θ P r) * sellerCurveCDF θ P r ≤ 1 := by nlinarith
    calc gc θ P r * ((1 - buyerCurveCDF θ P r) * sellerCurveCDF θ P r) ≤ gc θ P r * 1 :=
          mul_le_mul_of_nonneg_left this h0.le
      _ ≤ (θ.p ^ 2)⁻¹ := by rw [mul_one]; exact h1
  have hB2 : ∀ r, |θ.m * (gc θ P r * (1 - buyerCurveCDF θ P r))| ≤ (θ.p ^ 2)⁻¹ := by
    intro r
    have h0 := gc_pos hP r; have h1 := gc_le hP r
    have g0 := buyerCDF_nonneg hP r; have g1 := buyerCDF_le_one hP r
    have m0 := hP.admissible.m_pos; have m1 := hP.admissible.m_lt_one
    rw [abs_of_nonneg (mul_nonneg m0.le (mul_nonneg h0.le (by linarith)))]
    have : θ.m * (1 - buyerCurveCDF θ P r) ≤ 1 := by nlinarith
    calc θ.m * (gc θ P r * (1 - buyerCurveCDF θ P r))
        = gc θ P r * (θ.m * (1 - buyerCurveCDF θ P r)) := by ring
      _ ≤ gc θ P r * 1 := mul_le_mul_of_nonneg_left this h0.le
      _ ≤ (θ.p ^ 2)⁻¹ := by rw [mul_one]; exact h1
  have hmg := measurable_gc hP
  have hmB := measurable_buyerCDF hP
  have hmS := measurable_sellerCDF hI hP
  have e4 : ∫ r in Icc θ.c θ.ξ₀,
      gc θ P r * ((1 - buyerCurveCDF θ P r) * (sellerCurveCDF θ P r - θ.m)) =
      (Gf θ P - 2 - 2 * θ.m * θ.a) - θ.m * ((P θ.c)⁻¹ - 1) := by
    have e5 : (fun r => gc θ P r * ((1 - buyerCurveCDF θ P r) * (sellerCurveCDF θ P r - θ.m))) =
        fun r => gc θ P r * ((1 - buyerCurveCDF θ P r) * sellerCurveCDF θ P r) -
          θ.m * (gc θ P r * (1 - buyerCurveCDF θ P r)) := by
      ext r; ring
    rw [e5, setIntegral_Icc_eq hP.c_le_ξ₀, intervalIntegral.integral_sub
        (intervalIntegrable_of_bound (hmg.mul ((measurable_const.sub hmB).mul hmS)) hB1 _ _)
        (intervalIntegrable_of_bound (measurable_const.mul (hmg.mul (measurable_const.sub hmB)))
          hB2 _ _),
      intervalIntegral.integral_const_mul, integral_gc_buyer_seller hI hP,
      integral_gc_buyer hP (left_mem_Icc.mpr hP.c_le_ξ₀)]
  rw [e4, hP.left_end]
  ring

/-! ### The price-gain bound `Φ ≤ 2` -/

/-- `E(Z₁ - w)₊`. -/
def L1 (θ : Params) (P : ℝ → ℝ) (w : ℝ) : ℝ := ∫ u, max (Zf θ P u - w) 0 ∂unifLaw
/-- `E(w - Y₁)₊`. -/
def A1 (θ : Params) (P : ℝ → ℝ) (w : ℝ) : ℝ := ∫ v, max (w - Y₁f θ P v) 0 ∂unifLaw
/-- `E(w - Y₂)₊`. -/
def A2 (θ : Params) (P : ℝ → ℝ) (w : ℝ) : ℝ := ∫ v, max (w - Y₂f θ P v) 0 ∂unifLaw
/-- `P(Y₁ ≤ w)`. -/
def F1 (θ : Params) (P : ℝ → ℝ) (w : ℝ) : ℝ := unifLaw.real {v | Y₁f θ P v ≤ w}
/-- `P(Y₂ ≤ w)`. -/
def F2 (θ : Params) (P : ℝ → ℝ) (w : ℝ) : ℝ := unifLaw.real {v | Y₂f θ P v ≤ w}
/-- `P(Z₁ > w)`. -/
def H1 (θ : Params) (P : ℝ → ℝ) (w : ℝ) : ℝ := unifLaw.real {u | w < Zf θ P u}

/-- The body gain part of `Φ(w)`. -/
def Φg (θ : Params) (P : ℝ → ℝ) (w : ℝ) : ℝ :=
  L1 θ P w * F1 θ P w + A1 θ P w * H1 θ P w + max (θ.a - w) 0 * F2 θ P w +
    A2 θ P w * (if w < θ.a then 1 else 0)

theorem Φg_nonneg (w : ℝ) : 0 ≤ Φg θ P w := by
  have hL : 0 ≤ L1 θ P w := integral_nonneg fun _ => le_max_right _ _
  have hA1 : 0 ≤ A1 θ P w := integral_nonneg fun _ => le_max_right _ _
  have hA2 : 0 ≤ A2 θ P w := integral_nonneg fun _ => le_max_right _ _
  have hF1 : 0 ≤ F1 θ P w := measureReal_nonneg
  have hF2 : 0 ≤ F2 θ P w := measureReal_nonneg
  have hH1 : 0 ≤ H1 θ P w := measureReal_nonneg
  have hi : (0 : ℝ) ≤ if w < θ.a then 1 else 0 := by split_ifs <;> norm_num
  unfold Φg
  have := le_max_right (θ.a - w) 0
  positivity

/-! #### Values below `0` -/

theorem F1_of_neg (hP : InClass θ P) {w : ℝ} (hw : w < 0) : F1 θ P w = 0 := by
  unfold F1
  rw [show {v | Y₁f θ P v ≤ w} = ∅ from eq_empty_of_forall_notMem fun v hv =>
    absurd (show Y₁f θ P v ≤ w from hv) (not_le.mpr (hw.trans_le (Y₁f_nonneg hP v))),
    measureReal_empty]

theorem F2_of_neg (hP : InClass θ P) {w : ℝ} (hw : w < 0) : F2 θ P w = 0 := by
  unfold F2
  rw [show {v | Y₂f θ P v ≤ w} = ∅ from eq_empty_of_forall_notMem fun v hv =>
    absurd (show Y₂f θ P v ≤ w from hv) (not_le.mpr (hw.trans_le (Y₂f_nonneg hP v))),
    measureReal_empty]

theorem A1_of_neg (hP : InClass θ P) {w : ℝ} (hw : w < 0) : A1 θ P w = 0 := by
  unfold A1
  have : (fun v => max (w - Y₁f θ P v) 0) = fun _ => 0 := by
    ext v; exact max_eq_right (by linarith [Y₁f_nonneg hP v])
  rw [this, integral_zero]

theorem A2_of_neg (hP : InClass θ P) {w : ℝ} (hw : w < 0) : A2 θ P w = 0 := by
  unfold A2
  have : (fun v => max (w - Y₂f θ P v) 0) = fun _ => 0 := by
    ext v; exact max_eq_right (by linarith [Y₂f_nonneg hP v])
  rw [this, integral_zero]

/-! #### Values on `[0, a_f)` -/

theorem Y₁f_le_iff_of_lt_a (hP : InClass θ P) {w : ℝ} (hw0 : 0 ≤ w) (hwa : w < θ.a) (v : ℝ) :
    Y₁f θ P v ≤ w ↔ v ≤ θ.m := by
  constructor
  · intro h
    by_contra hv
    rw [Y₁f_of_gt (not_le.mp hv)] at h
    linarith [a_le_sF hP (qS_mem hP v)]
  · intro hv; rw [Y₁f_of_le hv]; exact hw0

theorem Y₂f_le_iff_of_lt_b {w : ℝ} (hw0 : 0 ≤ w) (hwb : w < bF θ P)
    (v : ℝ) : Y₂f θ P v ≤ w ↔ v ≤ θ.m := by
  constructor
  · intro h
    by_contra hv
    rw [Y₂f_of_gt (not_le.mp hv)] at h
    linarith
  · intro hv; rw [Y₂f_of_le hv]; exact hw0

theorem F1_of_lt_a (hP : InClass θ P) {w : ℝ} (hw0 : 0 ≤ w) (hwa : w < θ.a) :
    F1 θ P w = θ.m := by
  unfold F1
  rw [show {v | Y₁f θ P v ≤ w} = {v | v ≤ θ.m} from
    Set.ext fun v => Y₁f_le_iff_of_lt_a hP hw0 hwa v, unif_real_le_m hP]

theorem F2_of_lt_b (hP : InClass θ P) {w : ℝ} (hw0 : 0 ≤ w) (hwb : w < bF θ P) :
    F2 θ P w = θ.m := by
  unfold F2
  rw [show {v | Y₂f θ P v ≤ w} = {v | v ≤ θ.m} from
    Set.ext fun v => Y₂f_le_iff_of_lt_b hw0 hwb v, unif_real_le_m hP]

theorem H1_of_lt_a (hP : InClass θ P) {w : ℝ} (hwa : w < θ.a) : H1 θ P w = 1 := by
  unfold H1
  rw [show {u | w < Zf θ P u} = univ from eq_univ_of_forall fun u =>
    show w < Zf θ P u from hwa.trans_le (a_le_Zf hP u), probReal_univ]

theorem L1_of_lt_a (hP : InClass θ P) {w : ℝ} (hwa : w < θ.a) :
    L1 θ P w = θ.a + (θ.p⁻¹ - 1) - w := by
  unfold L1
  have : (fun u => max (Zf θ P u - w) 0) = fun u => Zf θ P u - w := by
    ext u; exact max_eq_left (by linarith [a_le_Zf hP u])
  rw [this, integral_sub (integrable_unif_of_bound (measurable_Zf hP) (abs_Zf_le hP))
    (integrable_const w), integral_const, probReal_univ, one_smul, integral_Zf hP]

theorem A1_of_lt_a (hP : InClass θ P) {w : ℝ} (hw0 : 0 ≤ w) (hwa : w < θ.a) :
    A1 θ P w = θ.m * w := by
  unfold A1
  have : (fun v => max (w - Y₁f θ P v) 0) = fun v => {v : ℝ | v ≤ θ.m}.indicator (fun _ => w) v := by
    ext v
    by_cases hv : v ≤ θ.m
    · rw [Y₁f_of_le hv, indicator_of_mem (show v ∈ {v : ℝ | v ≤ θ.m} from hv), sub_zero,
        max_eq_left hw0]
    · rw [Y₁f_of_gt (not_le.mp hv), indicator_of_notMem (show v ∉ {v : ℝ | v ≤ θ.m} from hv),
        max_eq_right (by linarith [a_le_sF hP (qS_mem hP v)])]
  rw [this, integral_indicator_const _ measurableSet_Iic_m, unif_real_le_m hP, smul_eq_mul]

theorem A2_of_lt_a (hP : InClass θ P) {w : ℝ} (hw0 : 0 ≤ w) (hwa : w < θ.a) :
    A2 θ P w = θ.m * w := by
  unfold A2
  have : (fun v => max (w - Y₂f θ P v) 0) = fun v => {v : ℝ | v ≤ θ.m}.indicator (fun _ => w) v := by
    ext v
    by_cases hv : v ≤ θ.m
    · rw [Y₂f_of_le hv, indicator_of_mem (show v ∈ {v : ℝ | v ≤ θ.m} from hv), sub_zero,
        max_eq_left hw0]
    · rw [Y₂f_of_gt (not_le.mp hv), indicator_of_notMem (show v ∉ {v : ℝ | v ≤ θ.m} from hv),
        max_eq_right (by linarith [a_le_bF hP])]
  rw [this, integral_indicator_const _ measurableSet_Iic_m, unif_real_le_m hP, smul_eq_mul]

/-! #### Values on the body `[a_f, b_f)`, in the curve coordinate -/

theorem H1_at (hP : InClass θ P) {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    H1 θ P (sF θ P ξ) = 1 - buyerCurveCDF θ P ξ := by
  unfold H1
  rw [show {u | sF θ P ξ < Zf θ P u} = {u | ξ < qB θ P u} from Set.ext fun u =>
    (sF_strictMonoOn hP).lt_iff_lt hξ (qB_mem hP u),
    unif_real_of_eq (unif_qB_gt hP ξ) (by linarith [buyerCDF_le_one hP ξ])]

theorem F1_at (hI : FamilyIdentities) (hP : InClass θ P) {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    F1 θ P (sF θ P ξ) = sellerCurveCDF θ P ξ := by
  unfold F1
  have hset : {v | Y₁f θ P v ≤ sF θ P ξ} = {v | v ≤ θ.m} ∪ {v | θ.m < v ∧ qS θ P v ≤ ξ} := by
    ext v
    simp only [mem_setOf_eq, mem_union]
    by_cases hv : v ≤ θ.m
    · rw [Y₁f_of_le hv]
      exact ⟨fun _ => Or.inl hv, fun _ => (a_le_sF hP hξ).trans' hP.admissible.a_nonneg⟩
    · have hv' : θ.m < v := not_le.mp hv
      rw [Y₁f_of_gt hv', (sF_strictMonoOn hP).le_iff_le (qS_mem hP v) hξ]
      exact ⟨fun h => Or.inr ⟨hv', h⟩, fun h => h.elim (fun h' => absurd h' hv) (fun h' => h'.2)⟩
  have hdisj : Disjoint {v : ℝ | v ≤ θ.m} {v | θ.m < v ∧ qS θ P v ≤ ξ} := by
    rw [Set.disjoint_left]
    intro v h1 h2
    exact absurd h2.1 (not_lt.mpr h1)
  rw [hset, measureReal_union hdisj (measurableSet_qS_le hI hP ξ), unif_real_le_m hP,
    unif_real_of_eq (unif_qS_le hI hP ξ) (by linarith [m_le_sellerCDF hI hP ξ])]
  ring

theorem L1_at (hP : InClass θ P) {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    L1 θ P (sF θ P ξ) = (P ξ)⁻¹ - 1 := by
  unfold L1
  set S : Set (ℝ × ℝ) := {q | ξ ≤ q.2 ∧ q.2 < qB θ P q.1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd ((measurable_qB hP).comp measurable_fst))
  have hpt : ∀ u, max (Zf θ P u - sF θ P ξ) 0 =
      ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (u, r) := by
    intro u
    have h := posPart_sF_sub hP hξ (qB_mem hP u)
    have e : ∀ r, S.indicator (fun q => gc θ P q.2) (u, r) =
        (Ico ξ (qB θ P u)).indicator (gc θ P) r := by
      intro r
      by_cases hr : r ∈ Ico ξ (qB θ P u)
      · rw [indicator_of_mem hr, indicator_of_mem (show (u, r) ∈ S from hr)]
      · rw [indicator_of_notMem hr, indicator_of_notMem (show (u, r) ∉ S from hr)]
    simp_rw [e]
    exact h
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_integral_indicator hSm (measurable_gc hP) (abs_gc_le hP)]
  have e3 : ∫ r in Icc θ.c θ.ξ₀, gc θ P r * unifLaw.real {u | (u, r) ∈ S} =
      ∫ r in Icc θ.c θ.ξ₀, (Icc ξ θ.ξ₀).indicator
        (fun r => gc θ P r * (1 - buyerCurveCDF θ P r)) r := by
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    by_cases hξr : ξ ≤ r
    · have hsec : {u | (u, r) ∈ S} = {u | r < qB θ P u} := by
        ext u; simp only [hS, mem_setOf_eq, hξr, true_and]
      rw [hsec, unif_real_of_eq (unif_qB_gt hP r) (by linarith [buyerCDF_le_one hP r]),
        indicator_of_mem (show r ∈ Icc ξ θ.ξ₀ from ⟨hξr, hr.2⟩)]
    · have hsec : {u | (u, r) ∈ S} = ∅ := by
        ext u; simp only [hS, mem_setOf_eq, hξr, false_and, mem_empty_iff_false]
      rw [hsec, measureReal_empty, mul_zero,
        indicator_of_notMem (show r ∉ Icc ξ θ.ξ₀ from fun h => hξr h.1)]
  rw [e3, setIntegral_indicator_Icc hξ, integral_gc_buyer hP hξ]

theorem A1_at (hI : FamilyIdentities) (hP : InClass θ P) {ξ : ℝ} (hξ : ξ ∈ Icc θ.c θ.ξ₀) :
    A1 θ P (sF θ P ξ) = θ.N * ξ * (P ξ)⁻¹ := by
  unfold A1
  set S : Set (ℝ × ℝ) := {q | θ.m < q.1 ∧ qS θ P q.1 ≤ q.2 ∧ q.2 < ξ} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le ((measurable_qS hI hP).comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hsξ0 : 0 ≤ sF θ P ξ := hP.admissible.a_nonneg.trans (a_le_sF hP hξ)
  have hpt : ∀ v, max (sF θ P ξ - Y₁f θ P v) 0 =
      {v : ℝ | v ≤ θ.m}.indicator (fun _ => sF θ P ξ) v +
        ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (v, r) := by
    intro v
    by_cases hv : v ≤ θ.m
    · have e : ∀ r, S.indicator (fun q => gc θ P q.2) (v, r) = 0 := fun r =>
        indicator_of_notMem (show (v, r) ∉ S from fun h' => absurd h'.1 (not_lt.mpr hv)) _
      simp_rw [e]
      rw [Y₁f_of_le hv, indicator_of_mem (show v ∈ {v : ℝ | v ≤ θ.m} from hv), sub_zero,
        max_eq_left hsξ0]
      simp
    · have hv' : θ.m < v := not_le.mp hv
      have h := posPart_sF_sub hP (qS_mem hP v) hξ
      have e : ∀ r, S.indicator (fun q => gc θ P q.2) (v, r) =
          (Ico (qS θ P v) ξ).indicator (gc θ P) r := by
        intro r
        by_cases hr : r ∈ Ico (qS θ P v) ξ
        · rw [indicator_of_mem hr, indicator_of_mem (show (v, r) ∈ S from ⟨hv', hr⟩)]
        · rw [indicator_of_notMem hr,
            indicator_of_notMem (show (v, r) ∉ S from fun h' => hr h'.2)]
      simp_rw [e]
      rw [Y₁f_of_gt hv', indicator_of_notMem (show v ∉ {v : ℝ | v ≤ θ.m} from hv), zero_add]
      exact h
  have hind : Integrable (fun v => {v : ℝ | v ≤ θ.m}.indicator (fun _ => sF θ P ξ) v) unifLaw :=
    (integrable_const _).indicator measurableSet_Iic_m
  have hmax : Integrable (fun v => max (sF θ P ξ - Y₁f θ P v) 0) unifLaw := by
    refine integrable_unif_of_bound ((measurable_const.sub (measurable_Y₁f hI hP)).max
      measurable_const) (B := sF θ P ξ) (fun v => ?_)
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [Y₁f_nonneg hP v]) hsξ0
  have hint : ∫ v, max (sF θ P ξ - Y₁f θ P v) 0 ∂unifLaw = θ.m * sF θ P ξ +
      ∫ v, (∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (v, r)) ∂unifLaw := by
    have e2 : (fun v => ∫ r in Icc θ.c θ.ξ₀, S.indicator (fun q => gc θ P q.2) (v, r)) =
        fun v => max (sF θ P ξ - Y₁f θ P v) 0 -
          {v : ℝ | v ≤ θ.m}.indicator (fun _ => sF θ P ξ) v := by
      ext v; rw [hpt v]; ring
    rw [e2, integral_sub hmax hind, integral_indicator_const _ measurableSet_Iic_m,
      unif_real_le_m hP, smul_eq_mul]
    ring
  rw [hint, integral_integral_indicator hSm (measurable_gc hP) (abs_gc_le hP)]
  have e3 : ∫ r in Icc θ.c θ.ξ₀, gc θ P r * unifLaw.real {u | (u, r) ∈ S} =
      ∫ r in Icc θ.c θ.ξ₀, (Ico θ.c ξ).indicator
        (fun r => gc θ P r * sellerCurveCDF θ P r - θ.m * gc θ P r) r := by
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    by_cases hrξ : r < ξ
    · have hsec : {u | (u, r) ∈ S} = {v | θ.m < v ∧ qS θ P v ≤ r} := by
        ext u; simp only [hS, mem_setOf_eq, hrξ, and_true]
      rw [hsec, unif_real_of_eq (unif_qS_le hI hP r) (by linarith [m_le_sellerCDF hI hP r]),
        indicator_of_mem (show r ∈ Ico θ.c ξ from ⟨hr.1, hrξ⟩)]
      ring
    · have hsec : {u | (u, r) ∈ S} = ∅ := by
        ext u; simp only [hS, mem_setOf_eq, hrξ, and_false, mem_empty_iff_false]
      rw [hsec, measureReal_empty, mul_zero,
        indicator_of_notMem (show r ∉ Ico θ.c ξ from fun h => hrξ h.2)]
  have hB : ∀ r, |θ.m * gc θ P r| ≤ (θ.p ^ 2)⁻¹ := by
    intro r
    rw [abs_mul, abs_of_pos hP.admissible.m_pos]
    have := abs_gc_le hP r
    have := hP.admissible.m_lt_one
    nlinarith [abs_nonneg (gc θ P r)]
  rw [e3, setIntegral_indicator_Ico hξ, intervalIntegral.integral_sub
      (intervalIntegrable_gc_sellerCDF hI hP _ _)
      (intervalIntegrable_of_bound (measurable_const.mul (measurable_gc hP)) hB _ _),
    intervalIntegral.integral_const_mul, integral_gc_seller hI hP hξ, integral_gc hP hξ]
  have hma := hP.admissible.m_mul_a
  have hp := hP.admissible.p_pos
  have e : θ.N * θ.c * θ.p⁻¹ = θ.m * θ.a := by rw [hma]; field_simp
  linear_combination -e

/-! #### The bound -/

/-- `Φ(w) ≤ 2` at every price `w`. -/
theorem Φ_le_two (hI : FamilyIdentities) (hP : InClass θ P) (w : ℝ) :
    Φg θ P w + (F1 θ P w + F2 θ P w) ≤ 2 := by
  have hadm := hP.admissible
  unfold Φg
  rcases lt_or_ge w 0 with hw0 | hw0
  · -- below zero
    rw [F1_of_neg hP hw0, F2_of_neg hP hw0, A1_of_neg hP hw0, A2_of_neg hP hw0]
    norm_num
  rcases lt_or_ge w θ.a with hwa | hwa
  · -- on `[0, a_f)`: `m (2 + z̄ + a) = 2`
    have hwb : w < bF θ P := hwa.trans_le (a_le_bF hP)
    rw [F1_of_lt_a hP hw0 hwa, F2_of_lt_b hP hw0 hwb, H1_of_lt_a hP hwa, L1_of_lt_a hP hwa,
      A1_of_lt_a hP hw0 hwa, A2_of_lt_a hP hw0 hwa, if_pos hwa, max_eq_left (by linarith)]
    have hlow := hI.low_price_balance θ.t θ.p hadm.t_pos hadm.p_pos
    have e : mF θ.t * (1 + 1 / θ.p + 2 * aF θ.t θ.p) = θ.m * (1 + θ.p⁻¹ + 2 * θ.a) := by
      rw [one_div]; rfl
    rw [e] at hlow
    linarith
  rcases lt_or_ge w (bF θ P) with hwb | hwb
  · -- on the body: `w = s_f(ξ)` with `c_f ≤ ξ < ξ₀`, and `N + m = 2`
    have hcont : ContinuousOn (sF θ P) (Icc θ.c θ.ξ₀) := fun x hx =>
      (hP.hasDerivWithinAt_sF hx).continuousWithinAt
    have hmem : w ∈ Icc (sF θ P θ.c) (sF θ P θ.ξ₀) := by
      rw [sF_c]; exact ⟨hwa, hwb.le⟩
    obtain ⟨ξ, hξ, hξw⟩ := intermediate_value_Icc hP.c_le_ξ₀ hcont hmem
    have hξ₀ : ξ < θ.ξ₀ := by
      rcases eq_or_lt_of_le hξ.2 with h | h
      · rw [h] at hξw; exact absurd hξw (ne_of_lt hwb).symm
      · exact h
    subst hξw
    rw [F1_at hI hP hξ, F2_of_lt_b hP hw0 hwb, H1_at hP hξ, L1_at hP hξ, A1_at hI hP hξ,
      if_neg (not_lt.mpr hwa), max_eq_right (by linarith), buyerCDF_of_mem hξ.1 hξ₀,
      sellerCDF_of_mem hξ.1 hξ₀]
    have hPξ : P ξ ≠ 0 := (hP.pos' hξ).ne'
    have heq := hI.first_unit_equalizer ξ (P ξ) (bodySurvival P ξ) θ.N hPξ
    have hNm := N_add_m hP
    unfold bodySellerCDF
    rw [show derivWithin P (Ici ξ) ξ = bodySurvival P ξ from rfl]
    have e : ((P ξ)⁻¹ - 1) * (θ.N * (P ξ - ξ * bodySurvival P ξ)) +
        θ.N * ξ * (P ξ)⁻¹ * (1 - (1 - bodySurvival P ξ)) +
        0 * θ.m + A2 θ P (sF θ P ξ) * 0 +
        (θ.N * (P ξ - ξ * bodySurvival P ξ) + θ.m) =
        (θ.N * (P ξ - ξ * bodySurvival P ξ) / P ξ +
          bodySurvival P ξ * (θ.N * ξ / P ξ)) + θ.m := by
      field_simp
      ring
    rw [e, heq]
    linarith
  · -- above the body: no body gains
    have hL : L1 θ P w = 0 := by
      unfold L1
      have : (fun u => max (Zf θ P u - w) 0) = fun _ => 0 := by
        ext u; exact max_eq_right (by linarith [Zf_le_bF hP u])
      rw [this, integral_zero]
    have hH : H1 θ P w = 0 := by
      unfold H1
      rw [show {u | w < Zf θ P u} = ∅ from eq_empty_of_forall_notMem fun u hu =>
        absurd (show w < Zf θ P u from hu) (not_lt.mpr (hwb.trans' (Zf_le_bF hP u))),
        measureReal_empty]
    rw [hL, hH, if_neg (not_lt.mpr hwa), max_eq_right (by linarith)]
    have h1 : F1 θ P w ≤ 1 := measureReal_le_one
    have h2 : F2 θ P w ≤ 1 := measureReal_le_one
    linarith

end Realize

end FixedPrice.TwoUnit.Family
