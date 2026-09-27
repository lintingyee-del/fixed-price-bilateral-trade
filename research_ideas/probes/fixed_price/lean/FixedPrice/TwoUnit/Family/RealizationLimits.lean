import FixedPrice.TwoUnit.Family.RealizationInstance

/-!
# Work package E, realization helpers: the scalar limits

For the instances of `RealizationInstance.lean`:

* seller welfare `M_f + 4η_n → M_f`;
* optimal welfare `(1 - η_n) W(η_n) + 2 → M_f + G_f`, where `W(η)` is the body's efficient welfare
  under the shifts and `W(0) = M_f + G_f - 2`; hence efficient gains `→ G_f`;
* every price gain is at most `2`: with `w = z - 2η_n`, each body gain is at most the unshifted
  right-limit gain at `w`, the atom's gain is at most `x_n (P(Y₁ ≤ w) + P(Y₂ ≤ w))`, and
  `η_n x_n = 1`, so the total is at most `Φ(w) ≤ 2`; the price `x_n` gains
  `2 - η_n (M_f + 4η_n)`; hence best price gains `→ 2`;
* the best ratios `→ (M_f + 2)/(M_f + G_f) = R_f`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal
open FixedPrice.TwoUnit (GenInstance unitGain)

namespace FixedPrice.TwoUnit.Family

namespace Realize

variable {θ : Params} {P : ℝ → ℝ}

/-! ### Seller welfare -/

theorem integrable_Y_sum (hI : FamilyIdentities) (hP : InClass θ P) :
    Integrable (fun v => Y₁f θ P v + Y₂f θ P v) unifLaw :=
  (integrable_unif_of_bound (measurable_Y₁f hI hP) (abs_Y₁f_le hP)).add
    (integrable_unif_of_bound (measurable_Y₂f hP) (abs_Y₂f_le hP))

theorem inst_sellerWelfare (hI : FamilyIdentities) (hP : InClass θ P) (n : ℕ) :
    (inst θ P n).sellerWelfare = Mf θ P + 4 * ηAt θ P n := by
  show ∫ s, (s.1 + s.2) ∂(sellerLaw θ P (ηAt θ P n)) = _
  unfold sellerLaw
  rw [integral_map (measurable_fS hI hP _).aemeasurable
    (measurable_fst.add measurable_snd).aestronglyMeasurable]
  have e : (fun v => (fS θ P (ηAt θ P n) v).1 + (fS θ P (ηAt θ P n) v).2) =
      fun v => (Y₁f θ P v + Y₂f θ P v) + 4 * ηAt θ P n := by
    ext v; simp only [fS]; ring
  rw [e, integral_add (integrable_Y_sum hI hP) (integrable_const _), integral_const,
    probReal_univ, one_smul, integral_Y_sum hI hP]

theorem tendsto_sellerWelfare (hI : FamilyIdentities) (hP : InClass θ P) :
    Tendsto (fun n => (inst θ P n).sellerWelfare) atTop (𝓝 (Mf θ P)) := by
  simp_rw [inst_sellerWelfare hI hP]
  simpa using tendsto_const_nhds.add ((tendsto_ηAt θ P).const_mul 4)

/-! ### Optimal welfare and efficient gains -/

/-- The shifted body's efficient welfare. -/
def W (θ : Params) (P : ℝ → ℝ) (η : ℝ) : ℝ :=
  ∫ q, (max (Zf θ P q.1 + η) (Y₁f θ P q.2 + 2 * η) + max (θ.a + η) (Y₂f θ P q.2 + 2 * η))
    ∂(unifLaw.prod unifLaw)

theorem measurable_maxSum : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
    max q.1.1 q.2.1 + max q.1.2 q.2.2) :=
  ((measurable_fst.comp measurable_fst).max (measurable_fst.comp measurable_snd)).add
    ((measurable_snd.comp measurable_fst).max (measurable_snd.comp measurable_snd))

theorem inst_optimalWelfare (hI : FamilyIdentities) (hP : InClass θ P) (n : ℕ) :
    (inst θ P n).optimalWelfare = (1 - ηAt θ P n) * W θ P (ηAt θ P n) + 2 := by
  have hη := ηAt_pos hP n
  have hη1 := ηAt_le hP n
  have hx := three_le_xAt hP n
  have hb := bF_nonneg hP
  show ∫ q, (max q.1.1 q.2.1 + max q.1.2 q.2.2)
    ∂((buyerLaw θ P (ηAt θ P n) (xAt θ P n)).prod (sellerLaw θ P (ηAt θ P n))) = _
  unfold buyerLaw sellerLaw
  rw [integral_joint hη.le (by linarith) (measurable_fB hP _) (measurable_fS hI hP _)
    measurable_maxSum (K := 2 * xAt θ P n)]
  · have e : (fun v => max (xAt θ P n, xAt θ P n).1 (fS θ P (ηAt θ P n) v).1 +
        max (xAt θ P n, xAt θ P n).2 (fS θ P (ηAt θ P n) v).2) =
        fun _ => 2 * xAt θ P n := by
      ext v
      simp only [fS]
      rw [max_eq_left (Y₁_shift_lt hP n v).le, max_eq_left (Y₂_shift_lt hP n v).le]
      ring
    rw [e, integral_const, probReal_univ, one_smul]
    have h1 : ηAt θ P n * (2 * xAt θ P n) = 2 := by
      rw [mul_left_comm, ηAt_mul_xAt hP n, mul_one]
    rw [h1]
    rfl
  · intro u v
    simp only [fB, fS]
    have h1 := fB_fst_le hP n u
    have h2 := a_shift_lt hP n
    have h3 := Y₁_shift_lt hP n v
    have h4 := Y₂_shift_lt hP n v
    have h5 := Zf_nonneg hP u
    have h6 := Y₁f_nonneg hP v
    have h7 := Y₂f_nonneg hP v
    have h8 := hP.admissible.a_nonneg
    rw [abs_of_nonneg (by positivity)]
    have := max_le h1.le h3.le
    have := max_le h2.le h4.le
    linarith
  · intro v
    simp only [fS]
    have h3 := Y₁_shift_lt hP n v
    have h4 := Y₂_shift_lt hP n v
    rw [max_eq_left h3.le, max_eq_left h4.le, abs_of_nonneg (by linarith)]
    linarith

theorem max_eq_add_posPart (x y : ℝ) : max x y = y + max (x - y) 0 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

theorem W_zero (hI : FamilyIdentities) (hP : InClass θ P) :
    W θ P 0 = Mf θ P + (Gf θ P - 2) := by
  unfold W
  have e : (fun q : ℝ × ℝ => max (Zf θ P q.1 + 0) (Y₁f θ P q.2 + 2 * 0) +
      max (θ.a + 0) (Y₂f θ P q.2 + 2 * 0)) =
      fun q => (Y₁f θ P q.2 + Y₂f θ P q.2) +
        (max (Zf θ P q.1 - Y₁f θ P q.2) 0 + max (θ.a - Y₂f θ P q.2) 0) := by
    ext q
    simp only [add_zero, mul_zero]
    rw [max_eq_add_posPart (Zf θ P q.1), max_eq_add_posPart θ.a]
    ring
  have hm1 : Measurable (fun q : ℝ × ℝ => max (Zf θ P q.1 - Y₁f θ P q.2) 0 +
      max (θ.a - Y₂f θ P q.2) 0) :=
    ((((measurable_Zf hP).comp measurable_fst).sub
      ((measurable_Y₁f hI hP).comp measurable_snd)).max measurable_const).add
      ((measurable_const.sub ((measurable_Y₂f hP).comp measurable_snd)).max measurable_const)
  have hb1 : ∀ q : ℝ × ℝ, |max (Zf θ P q.1 - Y₁f θ P q.2) 0 + max (θ.a - Y₂f θ P q.2) 0| ≤
      2 * bF θ P := by
    intro q
    have h1 := Zf_le_bF hP q.1
    have h2 := Y₁f_nonneg hP q.2
    have h3 := Y₂f_nonneg hP q.2
    have h4 := a_le_bF hP
    have hb := bF_nonneg hP
    rw [abs_of_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))]
    have := max_le (show Zf θ P q.1 - Y₁f θ P q.2 ≤ bF θ P by linarith) hb
    have := max_le (show θ.a - Y₂f θ P q.2 ≤ bF θ P by linarith) hb
    linarith
  have hm2 : Measurable (fun q : ℝ × ℝ => Y₁f θ P q.2 + Y₂f θ P q.2) :=
    ((measurable_Y₁f hI hP).comp measurable_snd).add ((measurable_Y₂f hP).comp measurable_snd)
  have hb2 : ∀ q : ℝ × ℝ, |Y₁f θ P q.2 + Y₂f θ P q.2| ≤ 2 * bF θ P := by
    intro q
    have h1 := Y₁f_le_bF hP q.2
    have h2 := Y₂f_le_bF hP q.2
    rw [abs_of_nonneg (add_nonneg (Y₁f_nonneg hP q.2) (Y₂f_nonneg hP q.2))]
    linarith
  rw [e, integral_add (integrable_prod_of_bound hm2 hb2) (integrable_prod_of_bound hm1 hb1),
    integral_fun_snd (fun v => Y₁f θ P v + Y₂f θ P v), probReal_univ, one_smul,
    integral_Y_sum hI hP, integral_posPart_body hI hP]

theorem tendsto_W (hI : FamilyIdentities) (hP : InClass θ P) :
    Tendsto (fun n => W θ P (ηAt θ P n)) atTop (𝓝 (W θ P 0)) := by
  let G : ℝ → ℝ × ℝ → ℝ := fun t q =>
    max (Zf θ P q.1 + t) (Y₁f θ P q.2 + 2 * t) + max (θ.a + t) (Y₂f θ P q.2 + 2 * t)
  have hW : ∀ t, W θ P t = ∫ q, G t q ∂(unifLaw.prod unifLaw) := fun t => rfl
  have hGm : ∀ t, Measurable (G t) := by
    intro t
    have h1 : Measurable (fun q : ℝ × ℝ => Zf θ P q.1 + t) :=
      ((measurable_Zf hP).comp measurable_fst).add_const t
    have h2 : Measurable (fun q : ℝ × ℝ => Y₁f θ P q.2 + 2 * t) :=
      ((measurable_Y₁f hI hP).comp measurable_snd).add_const _
    have h3 : Measurable (fun q : ℝ × ℝ => Y₂f θ P q.2 + 2 * t) :=
      ((measurable_Y₂f hP).comp measurable_snd).add_const _
    exact (h1.max h2).add (measurable_const.max h3)
  have hGc : ∀ q : ℝ × ℝ, ContinuousAt (fun t => G t q) 0 := by
    intro q
    have c1 : Continuous (fun t : ℝ => Zf θ P q.1 + t) := continuous_const.add continuous_id
    have c2 : Continuous (fun t : ℝ => Y₁f θ P q.2 + 2 * t) :=
      continuous_const.add (continuous_const.mul continuous_id)
    have c3 : Continuous (fun t : ℝ => θ.a + t) := continuous_const.add continuous_id
    have c4 : Continuous (fun t : ℝ => Y₂f θ P q.2 + 2 * t) :=
      continuous_const.add (continuous_const.mul continuous_id)
    exact ((c1.max c2).add (c3.max c4)).continuousAt
  have hGb : ∀ n (q : ℝ × ℝ), |G (ηAt θ P n) q| ≤ 2 * (bF θ P + 1) := by
    intro n q
    have hη := ηAt_pos hP n
    have hη1 := ηAt_le hP n
    have h1 := Zf_le_bF hP q.1
    have h2 := Y₁f_le_bF hP q.2
    have h3 := Y₂f_le_bF hP q.2
    have h4 := a_le_bF hP
    have h5 := Zf_nonneg hP q.1
    have h6 := hP.admissible.a_nonneg
    show |max (Zf θ P q.1 + ηAt θ P n) (Y₁f θ P q.2 + 2 * ηAt θ P n) +
      max (θ.a + ηAt θ P n) (Y₂f θ P q.2 + 2 * ηAt θ P n)| ≤ 2 * (bF θ P + 1)
    have p1 : (0 : ℝ) ≤ max (Zf θ P q.1 + ηAt θ P n) (Y₁f θ P q.2 + 2 * ηAt θ P n) :=
      (by linarith : (0 : ℝ) ≤ Zf θ P q.1 + ηAt θ P n).trans (le_max_left _ _)
    have p2 : (0 : ℝ) ≤ max (θ.a + ηAt θ P n) (Y₂f θ P q.2 + 2 * ηAt θ P n) :=
      (by linarith : (0 : ℝ) ≤ θ.a + ηAt θ P n).trans (le_max_left _ _)
    rw [abs_of_nonneg (add_nonneg p1 p2)]
    have := max_le (show Zf θ P q.1 + ηAt θ P n ≤ bF θ P + 1 by linarith)
      (show Y₁f θ P q.2 + 2 * ηAt θ P n ≤ bF θ P + 1 by linarith)
    have := max_le (show θ.a + ηAt θ P n ≤ bF θ P + 1 by linarith)
      (show Y₂f θ P q.2 + 2 * ηAt θ P n ≤ bF θ P + 1 by linarith)
    linarith
  simp_rw [hW]
  exact tendsto_integral_param hGm hGc (tendsto_ηAt θ P) hGb

theorem tendsto_optimalWelfare (hI : FamilyIdentities) (hP : InClass θ P) :
    Tendsto (fun n => (inst θ P n).optimalWelfare) atTop (𝓝 (Mf θ P + Gf θ P)) := by
  simp_rw [inst_optimalWelfare hI hP]
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_ηAt θ P)).mul
    (tendsto_W hI hP)).add (tendsto_const_nhds (x := (2 : ℝ)))
  rw [W_zero hI hP] at h
  convert h using 2
  ring

theorem tendsto_efficientGains (hI : FamilyIdentities) (hP : InClass θ P) :
    Tendsto (fun n => (inst θ P n).efficientGains) atTop (𝓝 (Gf θ P)) := by
  have h := (tendsto_optimalWelfare hI hP).sub (tendsto_sellerWelfare hI hP)
  rw [add_sub_cancel_left] at h
  exact h

/-! ### Price gains -/

theorem unitGain_shift_le {Z Y κ σ z : ℝ} (hκσ : κ < σ) :
    unitGain (Z + κ) (Y + σ) z ≤
      max (Z - (z - σ)) 0 * (if Y ≤ z - σ then 1 else 0) +
        (if z - σ < Z then 1 else 0) * max ((z - σ) - Y) 0 := by
  unfold unitGain
  have h0 : (0 : ℝ) ≤ max (Z - (z - σ)) 0 * (if Y ≤ z - σ then 1 else 0) +
      (if z - σ < Z then 1 else 0) * max ((z - σ) - Y) 0 := by
    have i1 : (0 : ℝ) ≤ if Y ≤ z - σ then 1 else 0 := by split_ifs <;> norm_num
    have i2 : (0 : ℝ) ≤ if z - σ < Z then 1 else 0 := by split_ifs <;> norm_num
    exact add_nonneg (mul_nonneg (le_max_right _ _) i1) (mul_nonneg i2 (le_max_right _ _))
  by_cases h : Y + σ ≤ z ∧ z ≤ Z + κ
  · rw [if_pos h]
    have h1 : Y ≤ z - σ := by linarith [h.1]
    have h2 : z - σ < Z := by linarith [h.2]
    rw [if_pos h1, if_pos h2, max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · rw [if_neg h]
    exact h0

theorem unitGain_atom_le {x Y σ z : ℝ} (hY : 0 ≤ Y) (hσ : 0 ≤ σ) (hx : 0 ≤ x) :
    unitGain x (Y + σ) z ≤ x * (if Y ≤ z - σ then 1 else 0) := by
  unfold unitGain
  by_cases h : Y + σ ≤ z ∧ z ≤ x
  · rw [if_pos h, if_pos (by linarith [h.1] : Y ≤ z - σ)]; linarith
  · rw [if_neg h]
    split_ifs <;> linarith

theorem measurable_unitGain_comp {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (z : ℝ) :
    Measurable (fun a => unitGain (f a) (g a) z) := by
  unfold unitGain
  exact Measurable.ite ((measurableSet_le hg measurable_const).inter
    (measurableSet_le measurable_const hf)) (hf.sub hg) measurable_const

theorem abs_unitGain_le (b s z : ℝ) : |unitGain b s z| ≤ |b| + |s| := by
  unfold unitGain
  split_ifs
  · exact (abs_sub _ _)
  · simp only [abs_zero]; positivity

/-- The body bound function whose integral is `Φg`. -/
def Bnd (θ : Params) (P : ℝ → ℝ) (w : ℝ) (q : ℝ × ℝ) : ℝ :=
  max (Zf θ P q.1 - w) 0 * {v | Y₁f θ P v ≤ w}.indicator 1 q.2 +
    {u | w < Zf θ P u}.indicator 1 q.1 * max (w - Y₁f θ P q.2) 0 +
    max (θ.a - w) 0 * {v | Y₂f θ P v ≤ w}.indicator 1 q.2 +
    (if w < θ.a then 1 else 0) * max (w - Y₂f θ P q.2) 0

theorem abs_indicator_one_le {s : Set ℝ} (x : ℝ) : |s.indicator (1 : ℝ → ℝ) x| ≤ 1 := by
  by_cases h : x ∈ s
  · rw [indicator_of_mem h]; simp
  · rw [indicator_of_notMem h]; simp

theorem Bnd_parts_integrable (hI : FamilyIdentities) (hP : InClass θ P) (w : ℝ) :
    Integrable (fun q : ℝ × ℝ => max (Zf θ P q.1 - w) 0 *
      {v | Y₁f θ P v ≤ w}.indicator 1 q.2) (unifLaw.prod unifLaw) ∧
    Integrable (fun q : ℝ × ℝ => {u | w < Zf θ P u}.indicator 1 q.1 *
      max (w - Y₁f θ P q.2) 0) (unifLaw.prod unifLaw) ∧
    Integrable (fun q : ℝ × ℝ => max (θ.a - w) 0 *
      {v | Y₂f θ P v ≤ w}.indicator 1 q.2) (unifLaw.prod unifLaw) ∧
    Integrable (fun q : ℝ × ℝ => (if w < θ.a then (1 : ℝ) else 0) *
      max (w - Y₂f θ P q.2) 0) (unifLaw.prod unifLaw) := by
  have hmF1 : MeasurableSet {v | Y₁f θ P v ≤ w} :=
    measurableSet_le (measurable_Y₁f hI hP) measurable_const
  have hmF2 : MeasurableSet {v | Y₂f θ P v ≤ w} :=
    measurableSet_le (measurable_Y₂f hP) measurable_const
  have hmH : MeasurableSet {u | w < Zf θ P u} :=
    measurableSet_lt measurable_const (measurable_Zf hP)
  -- boundedness of the four pieces
  have bL : ∀ u, |max (Zf θ P u - w) 0| ≤ |bF θ P| + |w| := by
    intro u
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    have := Zf_le_bF hP u
    linarith [le_abs_self (bF θ P), neg_abs_le w]
  have bA1 : ∀ v, |max (w - Y₁f θ P v) 0| ≤ |w| := by
    intro v
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self w, Y₁f_nonneg hP v]) (abs_nonneg _)
  have bA2 : ∀ v, |max (w - Y₂f θ P v) 0| ≤ |w| := by
    intro v
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self w, Y₂f_nonneg hP v]) (abs_nonneg _)
  have mL : Measurable (fun u => max (Zf θ P u - w) 0) :=
    ((measurable_Zf hP).sub_const w).max measurable_const
  have mA1 : Measurable (fun v => max (w - Y₁f θ P v) 0) :=
    (measurable_const.sub (measurable_Y₁f hI hP)).max measurable_const
  have mA2 : Measurable (fun v => max (w - Y₂f θ P v) 0) :=
    (measurable_const.sub (measurable_Y₂f hP)).max measurable_const
  have mI1 : Measurable ({v | Y₁f θ P v ≤ w}.indicator (1 : ℝ → ℝ)) :=
    measurable_const.indicator hmF1
  have mI2 : Measurable ({v | Y₂f θ P v ≤ w}.indicator (1 : ℝ → ℝ)) :=
    measurable_const.indicator hmF2
  have mIH : Measurable ({u | w < Zf θ P u}.indicator (1 : ℝ → ℝ)) :=
    measurable_const.indicator hmH
  have hi1 : Integrable (fun q : ℝ × ℝ => max (Zf θ P q.1 - w) 0 *
      {v | Y₁f θ P v ≤ w}.indicator 1 q.2) (unifLaw.prod unifLaw) := by
    refine integrable_prod_of_bound ((mL.comp measurable_fst).mul (mI1.comp measurable_snd))
      (B := |bF θ P| + |w|) (fun q => ?_)
    rw [abs_mul]
    have := bL q.1
    have := abs_indicator_one_le (s := {v | Y₁f θ P v ≤ w}) q.2
    nlinarith [abs_nonneg (max (Zf θ P q.1 - w) 0),
      abs_nonneg ({v | Y₁f θ P v ≤ w}.indicator (1 : ℝ → ℝ) q.2)]
  have hi2 : Integrable (fun q : ℝ × ℝ => {u | w < Zf θ P u}.indicator 1 q.1 *
      max (w - Y₁f θ P q.2) 0) (unifLaw.prod unifLaw) := by
    refine integrable_prod_of_bound ((mIH.comp measurable_fst).mul (mA1.comp measurable_snd))
      (B := |w|) (fun q => ?_)
    rw [abs_mul]
    have := bA1 q.2
    have := abs_indicator_one_le (s := {u | w < Zf θ P u}) q.1
    nlinarith [abs_nonneg (max (w - Y₁f θ P q.2) 0),
      abs_nonneg ({u | w < Zf θ P u}.indicator (1 : ℝ → ℝ) q.1)]
  have hi3 : Integrable (fun q : ℝ × ℝ => max (θ.a - w) 0 *
      {v | Y₂f θ P v ≤ w}.indicator 1 q.2) (unifLaw.prod unifLaw) := by
    refine integrable_prod_of_bound (measurable_const.mul (mI2.comp measurable_snd))
      (B := |max (θ.a - w) 0|) (fun q => ?_)
    rw [abs_mul]
    have := abs_indicator_one_le (s := {v | Y₂f θ P v ≤ w}) q.2
    nlinarith [abs_nonneg (max (θ.a - w) 0),
      abs_nonneg ({v | Y₂f θ P v ≤ w}.indicator (1 : ℝ → ℝ) q.2)]
  have hi4 : Integrable (fun q : ℝ × ℝ => (if w < θ.a then (1 : ℝ) else 0) *
      max (w - Y₂f θ P q.2) 0) (unifLaw.prod unifLaw) := by
    refine integrable_prod_of_bound (measurable_const.mul (mA2.comp measurable_snd))
      (B := |w|) (fun q => ?_)
    rw [abs_mul]
    have := bA2 q.2
    have hc : |(if w < θ.a then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    nlinarith [abs_nonneg (max (w - Y₂f θ P q.2) 0),
      abs_nonneg (if w < θ.a then (1 : ℝ) else 0)]
  exact ⟨hi1, hi2, hi3, hi4⟩

theorem integrable_Bnd (hI : FamilyIdentities) (hP : InClass θ P) (w : ℝ) :
    Integrable (Bnd θ P w) (unifLaw.prod unifLaw) := by
  obtain ⟨hi1, hi2, hi3, hi4⟩ := Bnd_parts_integrable hI hP w
  exact ((hi1.add hi2).add hi3).add hi4

theorem integral_Bnd (hI : FamilyIdentities) (hP : InClass θ P) (w : ℝ) :
    ∫ q, Bnd θ P w q ∂(unifLaw.prod unifLaw) = Φg θ P w := by
  have hmF1 : MeasurableSet {v | Y₁f θ P v ≤ w} :=
    measurableSet_le (measurable_Y₁f hI hP) measurable_const
  have hmF2 : MeasurableSet {v | Y₂f θ P v ≤ w} :=
    measurableSet_le (measurable_Y₂f hP) measurable_const
  have hmH : MeasurableSet {u | w < Zf θ P u} :=
    measurableSet_lt measurable_const (measurable_Zf hP)
  obtain ⟨hi1, hi2, hi3, hi4⟩ := Bnd_parts_integrable hI hP w
  have hi12 : Integrable (fun q : ℝ × ℝ => max (Zf θ P q.1 - w) 0 *
      {v | Y₁f θ P v ≤ w}.indicator 1 q.2 +
      {u | w < Zf θ P u}.indicator 1 q.1 * max (w - Y₁f θ P q.2) 0) (unifLaw.prod unifLaw) :=
    hi1.add hi2
  have hi123 : Integrable (fun q : ℝ × ℝ => max (Zf θ P q.1 - w) 0 *
      {v | Y₁f θ P v ≤ w}.indicator 1 q.2 +
      {u | w < Zf θ P u}.indicator 1 q.1 * max (w - Y₁f θ P q.2) 0 +
      max (θ.a - w) 0 * {v | Y₂f θ P v ≤ w}.indicator 1 q.2) (unifLaw.prod unifLaw) :=
    hi12.add hi3
  unfold Bnd
  rw [integral_add hi123 hi4, integral_add hi12 hi3, integral_add hi1 hi2,
    integral_prod_mul (fun u => max (Zf θ P u - w) 0) (fun v => {v | Y₁f θ P v ≤ w}.indicator
      (1 : ℝ → ℝ) v),
    integral_prod_mul (fun u => {u | w < Zf θ P u}.indicator (1 : ℝ → ℝ) u)
      (fun v => max (w - Y₁f θ P v) 0),
    integral_const_mul, integral_const_mul,
    integral_fun_snd (fun v => {v | Y₂f θ P v ≤ w}.indicator (1 : ℝ → ℝ) v),
    integral_fun_snd (fun v => max (w - Y₂f θ P v) 0), probReal_univ, one_smul, one_smul,
    integral_indicator_one hmF1, integral_indicator_one hmF2, integral_indicator_one hmH]
  unfold Φg L1 A1 A2 F1 F2 H1
  ring

/-- Every price gain of the `n`-th instance is at most `2`. -/
theorem inst_priceGain_le (hI : FamilyIdentities) (hP : InClass θ P) (n : ℕ) (z : ℝ) :
    (inst θ P n).priceGain z ≤ 2 := by
  set η := ηAt θ P n with hηdef
  set x := xAt θ P n with hxdef
  set w := z - 2 * η with hw
  have hη := ηAt_pos hP n
  have hη1 := ηAt_le hP n
  have hx := three_le_xAt hP n
  have hηx : η * x = 1 := ηAt_mul_xAt hP n
  have hb := bF_nonneg hP
  set F : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun q => unitGain q.1.1 q.2.1 z + unitGain q.1.2 q.2.2 z
    with hF
  have hFm : Measurable F :=
    (measurable_unitGain_comp (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd) z).add
      (measurable_unitGain_comp (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd) z)
  have hFb : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), |F q| ≤ |q.1.1| + |q.2.1| + (|q.1.2| + |q.2.2|) := by
    intro q
    exact (abs_add_le _ _).trans (add_le_add (abs_unitGain_le _ _ _) (abs_unitGain_le _ _ _))
  have hKb : ∀ u v, |F (fB θ P η u, fS θ P η v)| ≤ 4 * (x + 1) := by
    intro u v
    refine (hFb _).trans ?_
    simp only [fB, fS]
    have h1 := fB_fst_le hP n u
    have h2 := a_shift_lt hP n
    have h3 := Y₁_shift_lt hP n v
    have h4 := Y₂_shift_lt hP n v
    rw [abs_of_nonneg (by linarith [Zf_nonneg hP u]),
      abs_of_nonneg (by linarith [Y₁f_nonneg hP v]),
      abs_of_nonneg (by linarith [hP.admissible.a_nonneg]),
      abs_of_nonneg (by linarith [Y₂f_nonneg hP v])]
    linarith
  have hKx : ∀ v, |F ((x, x), fS θ P η v)| ≤ 4 * (x + 1) := by
    intro v
    refine (hFb _).trans ?_
    simp only [fS]
    have h3 := Y₁_shift_lt hP n v
    have h4 := Y₂_shift_lt hP n v
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [Y₁f_nonneg hP v]),
      abs_of_nonneg (by linarith [Y₂f_nonneg hP v])]
    linarith
  have hPG : (inst θ P n).priceGain z =
      (1 - η) * ∫ q, F (fB θ P η q.1, fS θ P η q.2) ∂(unifLaw.prod unifLaw) +
        η * ∫ v, F ((x, x), fS θ P η v) ∂unifLaw := by
    show ∫ q, F q ∂((buyerLaw θ P η x).prod (sellerLaw θ P η)) = _
    unfold buyerLaw sellerLaw
    exact integral_joint hη.le (by linarith) (measurable_fB hP _) (measurable_fS hI hP _) hFm
      hKb hKx
  -- the body part is bounded by `Φg w`
  have hbody : ∫ q, F (fB θ P η q.1, fS θ P η q.2) ∂(unifLaw.prod unifLaw) ≤ Φg θ P w := by
    rw [← integral_Bnd hI hP w]
    refine integral_mono (integrable_prod_of_bound (hFm.comp ((measurable_fB hP η).prodMap
      (measurable_fS hI hP η))) (fun q => hKb q.1 q.2)) (integrable_Bnd hI hP w) (fun q => ?_)
    show F (fB θ P η q.1, fS θ P η q.2) ≤ Bnd θ P w q
    have h1 := unitGain_shift_le (Z := Zf θ P q.1) (Y := Y₁f θ P q.2) (z := z)
      (show η < 2 * η by linarith)
    have h2 := unitGain_shift_le (Z := θ.a) (Y := Y₂f θ P q.2) (z := z)
      (show η < 2 * η by linarith)
    rw [← hw] at h1 h2
    simp only [hF, fB, fS, Bnd, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    linarith
  -- the atom part is bounded by `x (F1 w + F2 w)`
  have hatom : ∫ v, F ((x, x), fS θ P η v) ∂unifLaw ≤ x * (F1 θ P w + F2 θ P w) := by
    have hmF1 : MeasurableSet {v | Y₁f θ P v ≤ w} :=
      measurableSet_le (measurable_Y₁f hI hP) measurable_const
    have hmF2 : MeasurableSet {v | Y₂f θ P v ≤ w} :=
      measurableSet_le (measurable_Y₂f hP) measurable_const
    have hbnd : ∀ v, F ((x, x), fS θ P η v) ≤
        x * {v | Y₁f θ P v ≤ w}.indicator 1 v + x * {v | Y₂f θ P v ≤ w}.indicator 1 v := by
      intro v
      simp only [hF, fS, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      have h1 := unitGain_atom_le (x := x) (z := z) (Y₁f_nonneg hP v)
        (show (0 : ℝ) ≤ 2 * η by linarith) (by linarith)
      have h2 := unitGain_atom_le (x := x) (z := z) (Y₂f_nonneg hP v)
        (show (0 : ℝ) ≤ 2 * η by linarith) (by linarith)
      rw [← hw] at h1 h2
      linarith
    have hi1 : Integrable (fun v => x * {v | Y₁f θ P v ≤ w}.indicator (1 : ℝ → ℝ) v) unifLaw :=
      ((integrable_const (1 : ℝ)).indicator hmF1).const_mul x
    have hi2 : Integrable (fun v => x * {v | Y₂f θ P v ≤ w}.indicator (1 : ℝ → ℝ) v) unifLaw :=
      ((integrable_const (1 : ℝ)).indicator hmF2).const_mul x
    have hint2 : Integrable (fun v => x * {v | Y₁f θ P v ≤ w}.indicator 1 v +
        x * {v | Y₂f θ P v ≤ w}.indicator 1 v) unifLaw := hi1.add hi2
    calc ∫ v, F ((x, x), fS θ P η v) ∂unifLaw
        ≤ ∫ v, (x * {v | Y₁f θ P v ≤ w}.indicator 1 v +
            x * {v | Y₂f θ P v ≤ w}.indicator 1 v) ∂unifLaw :=
          integral_mono (integrable_unif_of_bound (hFm.comp (measurable_prodMk_left.comp
            (measurable_fS hI hP η))) hKx) hint2 hbnd
      _ = x * (F1 θ P w + F2 θ P w) := by
          rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul]
          have e1 : ∫ v, {v | Y₁f θ P v ≤ w}.indicator (1 : ℝ → ℝ) v ∂unifLaw = F1 θ P w :=
            integral_indicator_one hmF1
          have e2 : ∫ v, {v | Y₂f θ P v ≤ w}.indicator (1 : ℝ → ℝ) v ∂unifLaw = F2 θ P w :=
            integral_indicator_one hmF2
          rw [e1, e2]; ring
  have hΦ := Φ_le_two hI hP w
  have hg0 := Φg_nonneg (θ := θ) (P := P) w
  rw [hPG]
  have hA : η * ∫ v, F ((x, x), fS θ P η v) ∂unifLaw ≤ F1 θ P w + F2 θ P w := by
    calc η * ∫ v, F ((x, x), fS θ P η v) ∂unifLaw ≤ η * (x * (F1 θ P w + F2 θ P w)) :=
          mul_le_mul_of_nonneg_left hatom hη.le
      _ = F1 θ P w + F2 θ P w := by rw [← mul_assoc, hηx, one_mul]
  have hB : (1 - η) * ∫ q, F (fB θ P η q.1, fS θ P η q.2) ∂(unifLaw.prod unifLaw) ≤
      Φg θ P w := by
    calc (1 - η) * ∫ q, F (fB θ P η q.1, fS θ P η q.2) ∂(unifLaw.prod unifLaw)
        ≤ (1 - η) * Φg θ P w := mul_le_mul_of_nonneg_left hbody (by linarith)
      _ ≤ Φg θ P w := by nlinarith
  linarith

/-- The price `x_n` gains `2 - η_n (M_f + 4η_n)`. -/
theorem inst_priceGain_x (hI : FamilyIdentities) (hP : InClass θ P) (n : ℕ) :
    (inst θ P n).priceGain (xAt θ P n) = 2 - ηAt θ P n * (Mf θ P + 4 * ηAt θ P n) := by
  set η := ηAt θ P n with hηdef
  set x := xAt θ P n with hxdef
  have hη := ηAt_pos hP n
  have hη1 := ηAt_le hP n
  have hx := three_le_xAt hP n
  have hηx : η * x = 1 := ηAt_mul_xAt hP n
  set F : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun q => unitGain q.1.1 q.2.1 x + unitGain q.1.2 q.2.2 x
    with hF
  have hFm : Measurable F :=
    (measurable_unitGain_comp (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd) x).add
      (measurable_unitGain_comp (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd) x)
  have hbody : ∀ u v, F (fB θ P η u, fS θ P η v) = 0 := by
    intro u v
    simp only [hF, fB, fS, unitGain]
    rw [if_neg (fun h => absurd h.2 (not_le.mpr (fB_fst_le hP n u))),
      if_neg (fun h => absurd h.2 (not_le.mpr (a_shift_lt hP n)))]
    ring
  have hatom : ∀ v, F ((x, x), fS θ P η v) =
      2 * x - (Y₁f θ P v + Y₂f θ P v) - 4 * η := by
    intro v
    simp only [hF, fS, unitGain]
    rw [if_pos ⟨(Y₁_shift_lt hP n v).le, le_rfl⟩, if_pos ⟨(Y₂_shift_lt hP n v).le, le_rfl⟩]
    ring
  have hPG : (inst θ P n).priceGain x =
      (1 - η) * ∫ q, F (fB θ P η q.1, fS θ P η q.2) ∂(unifLaw.prod unifLaw) +
        η * ∫ v, F ((x, x), fS θ P η v) ∂unifLaw := by
    show ∫ q, F q ∂((buyerLaw θ P η x).prod (sellerLaw θ P η)) = _
    unfold buyerLaw sellerLaw
    refine integral_joint hη.le (by linarith) (measurable_fB hP _) (measurable_fS hI hP _) hFm
      (K := 2 * x + 4) (fun u v => ?_) (fun v => ?_)
    · rw [hbody]; simp only [abs_zero]; linarith
    · rw [hatom]
      have h1 := Y₁f_nonneg hP v
      have h2 := Y₂f_nonneg hP v
      have h3 := Y₁_shift_lt hP n v
      have h4 := Y₂_shift_lt hP n v
      rw [abs_le]
      constructor <;> linarith
  rw [hPG]
  have e1 : (fun q : ℝ × ℝ => F (fB θ P η q.1, fS θ P η q.2)) = fun _ => 0 := by
    ext q; exact hbody q.1 q.2
  have e2 : (fun v => F ((x, x), fS θ P η v)) =
      fun v => (2 * x - 4 * η) - (Y₁f θ P v + Y₂f θ P v) := by
    ext v; rw [hatom]; ring
  rw [e1, e2, integral_zero, integral_sub (integrable_const _) (integrable_Y_sum hI hP),
    integral_const, probReal_univ, one_smul, integral_Y_sum hI hP]
  have : η * (2 * x - 4 * η - Mf θ P) = 2 * (η * x) - η * (Mf θ P + 4 * η) := by ring
  rw [mul_zero, zero_add, this, hηx]
  ring

theorem tendsto_bestGain (hI : FamilyIdentities) (hP : InClass θ P) :
    Tendsto (fun n => (inst θ P n).bestGain) atTop (𝓝 2) := by
  have hle : ∀ n, (inst θ P n).bestGain ≤ 2 := by
    intro n
    unfold GenInstance.bestGain
    refine csSup_le ⟨_, xAt θ P n, (show (0 : ℝ) ≤ xAt θ P n by linarith [three_le_xAt hP n]),
      rfl⟩ ?_
    rintro _ ⟨z, -, rfl⟩
    exact inst_priceGain_le hI hP n z
  have hge : ∀ n, 2 - ηAt θ P n * (Mf θ P + 4 * ηAt θ P n) ≤ (inst θ P n).bestGain := by
    intro n
    unfold GenInstance.bestGain
    rw [← inst_priceGain_x hI hP n]
    refine le_csSup ⟨2, ?_⟩ ⟨xAt θ P n,
      (show (0 : ℝ) ≤ xAt θ P n by linarith [three_le_xAt hP n]), rfl⟩
    rintro _ ⟨z, -, rfl⟩
    exact inst_priceGain_le hI hP n z
  have hlow : Tendsto (fun n => 2 - ηAt θ P n * (Mf θ P + 4 * ηAt θ P n)) atTop (𝓝 2) := by
    have h := tendsto_const_nhds (x := (2 : ℝ)) |>.sub
      ((tendsto_ηAt θ P).mul ((tendsto_const_nhds (x := Mf θ P)).add
        ((tendsto_ηAt θ P).const_mul 4)))
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hge hle

theorem tendsto_bestRatio (hI : FamilyIdentities) (hP : InClass θ P) :
    Tendsto (fun n => (inst θ P n).bestRatio) atTop (𝓝 (Rf θ P)) := by
  have hpos := hP.positivity'
  have hne : Mf θ P + Gf θ P ≠ 0 := by linarith [hpos.2.1, hpos.2.2.1]
  unfold GenInstance.bestRatio Rf
  exact ((tendsto_sellerWelfare hI hP).add (tendsto_bestGain hI hP)).div
    (tendsto_optimalWelfare hI hP) hne

end Realize

end FixedPrice.TwoUnit.Family
