import FixedPrice.TwoUnit.Pricing.OperatorFixed

/-!
# Theorem E, package A, part 3: iteration, least fixed point, feasibility

With `q = b̄/(1+b̄)` and `M = (1 + C_ϑ)(1 + b̄)` (`C_ϑ` a bound of `|ϑ|` on `[0, b̄]`):

* the iterates `𝒯^[n] 0` are nonincreasing on `[0, b̄]`, lie in `[0, M]`, and increase in `n`;
* their successive differences are at most `qⁿ 𝒯0(0)`, so `ϖ_{d,ϑ} = sup_n 𝒯^[n] 0` is within
  `qⁿ 𝒯0(0)(1 + b̄)` of the `n`-th iterate, and it is a fixed point;
* every bounded fixed point is nonincreasing, and the contraction makes it equal to `ϖ_{d,ϑ}`;
  the iterates approach `ϖ_{d,ϑ}` at the rate `qⁿ ϖ_{d,ϑ}(0)`;
* the potential constraints are equivalent to `𝒯ϖ ≤ ϖ` (certified identity
  `obstacle_identity`), so `ϖ_{d,ϑ}` is feasible and lies below every feasible mass.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

section Iteration

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d : ℝ} {ϑ : ℝ → ℝ}

/-- The iterates `𝒯^[n] 0`. -/
abbrev iter (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d : ℝ) (ϑ : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (pricingOperator bbar law d ϑ)^[n] 0

theorem iter_succ (n : ℕ) :
    iter bbar law d ϑ (n + 1) = pricingOperator bbar law d ϑ (iter bbar law d ϑ n) :=
  Function.iterate_succ_apply' _ _ _

theorem bbar_nonneg_of_bodies (hB : IsBuyerBodies bbar law) : 0 ≤ bbar := by
  haveI := hB.isProbability 0
  exact bbar_nonneg_of_supp (hB.supported 0)

variable (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law) (hd : 0 < d)
  {C : ℝ} (hC : ∀ x ∈ Icc 0 bbar, |ϑ x| ≤ C)

include cert hB hd hC in
theorem iter_props (n : ℕ) :
    AntitoneOn (iter bbar law d ϑ n) (Icc 0 bbar) ∧
      ∀ s ∈ Icc 0 bbar, 0 ≤ iter bbar law d ϑ n s ∧
        iter bbar law d ϑ n s ≤ (1 + C) * (1 + bbar) := by
  have hb := bbar_nonneg_of_bodies hB
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 ⟨le_rfl, hb⟩)
  have hM0 : 0 ≤ (1 + C) * (1 + bbar) := by positivity
  induction n with
  | zero =>
    exact ⟨fun _ _ _ _ _ => le_rfl, fun _ _ => ⟨le_rfl, hM0⟩⟩
  | succ n ih =>
    obtain ⟨_, hbd⟩ := ih
    have habs : ∀ x ∈ Icc 0 bbar, |iter bbar law d ϑ n x| ≤ (1 + C) * (1 + bbar) :=
      fun x hx => by rw [abs_of_nonneg (hbd x hx).1]; exact (hbd x hx).2
    have hbound : ∃ B, ∀ x ∈ Icc 0 bbar, |iter bbar law d ϑ n x| ≤ B := ⟨_, habs⟩
    have hϑb : ∃ C', ∀ x ∈ Icc 0 bbar, |ϑ x| ≤ C' := ⟨C, hC⟩
    rw [iter_succ]
    refine ⟨pricingOperator_antitoneOn hB hd hϑb hbound,
      fun s hs => ⟨pricingOperator_nonneg hB hd hϑb hbound hs, ?_⟩⟩
    rw [pricingOperator_eq_sSup]
    apply csSup_le ((show (Icc s bbar).Nonempty from ⟨s, le_rfl, hs.2⟩).image _)
    rintro _ ⟨t, ht, rfl⟩
    have ht' : t ∈ Icc 0 bbar := ⟨hs.1.trans ht.1, ht.2⟩
    have e1 : bbar / (1 + bbar) * ((1 + C) * (1 + bbar)) = bbar * (1 + C) := by
      field_simp
    have h0 := obstacle_le_of_bound cert hB hd hC hM0 habs 0 ht'
    have h1 := obstacle_le_of_bound cert hB hd hC hM0 habs 1 ht'
    rw [e1] at h0 h1
    exact max_le hM0 (max_le (by nlinarith) (by nlinarith))

include cert hB hd hC in
theorem iter_le_succ (n : ℕ) :
    ∀ s ∈ Icc 0 bbar, iter bbar law d ϑ n s ≤ iter bbar law d ϑ (n + 1) s := by
  induction n with
  | zero => intro s hs; exact ((iter_props cert hB hd hC 1).2 s hs).1
  | succ n ih =>
    intro s hs
    rw [iter_succ (n + 1)]
    conv_lhs => rw [iter_succ n]
    exact pricingOperator_mono hB hd ⟨C, hC⟩
      (goodMass2_of_antitoneOn hB (iter_props cert hB hd hC n).1)
      (goodMass2_of_antitoneOn hB (iter_props cert hB hd hC (n + 1)).1) ih hs

include cert hB hd hC in
theorem iter_bddAbove {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    BddAbove (range fun n => iter bbar law d ϑ n s) :=
  ⟨(1 + C) * (1 + bbar), by
    rintro _ ⟨n, rfl⟩
    exact ((iter_props cert hB hd hC n).2 s hs).2⟩

include cert hB hd hC in
theorem iter_monotone {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    Monotone fun n => iter bbar law d ϑ n s :=
  monotone_nat_of_le_succ fun n => iter_le_succ cert hB hd hC n s hs

include cert hB hd hC in
theorem iter_le_leastMass {s : ℝ} (hs : s ∈ Icc 0 bbar) (n : ℕ) :
    iter bbar law d ϑ n s ≤ leastMass bbar law d ϑ s :=
  le_ciSup (iter_bddAbove cert hB hd hC hs) n

include cert hB hd hC in
theorem leastMass_le_bound {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    leastMass bbar law d ϑ s ≤ (1 + C) * (1 + bbar) :=
  ciSup_le fun n => ((iter_props cert hB hd hC n).2 s hs).2

include cert hB hd hC in
theorem leastMass_nonneg {s : ℝ} (hs : s ∈ Icc 0 bbar) : 0 ≤ leastMass bbar law d ϑ s :=
  ((iter_props cert hB hd hC 0).2 s hs).1.trans (iter_le_leastMass cert hB hd hC hs 0)

include cert hB hd hC in
theorem tendsto_iter {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    Tendsto (fun n => iter bbar law d ϑ n s) atTop (𝓝 (leastMass bbar law d ϑ s)) :=
  tendsto_atTop_ciSup (iter_monotone cert hB hd hC hs) (iter_bddAbove cert hB hd hC hs)

include cert hB hd hC in
theorem leastMass_antitoneOn : AntitoneOn (leastMass bbar law d ϑ) (Icc 0 bbar) :=
  fun _ ha _ hb hab => ciSup_mono (iter_bddAbove cert hB hd hC ha) fun n =>
    (iter_props cert hB hd hC n).1 ha hb hab

include cert hB hd hC in
theorem leastMass_abs_le {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    |leastMass bbar law d ϑ s| ≤ (1 + C) * (1 + bbar) := by
  rw [abs_of_nonneg (leastMass_nonneg cert hB hd hC hs)]
  exact leastMass_le_bound cert hB hd hC hs

include cert hB hd hC in
/-- Successive differences decay geometrically. -/
theorem iter_succ_sub_le (n : ℕ) :
    ∀ s ∈ Icc 0 bbar, iter bbar law d ϑ (n + 1) s - iter bbar law d ϑ n s ≤
      (bbar / (1 + bbar)) ^ n * iter bbar law d ϑ 1 0 := by
  have hb := bbar_nonneg_of_bodies hB
  have h0mem : (0 : ℝ) ∈ Icc 0 bbar := ⟨le_rfl, hb⟩
  have hM0 : 0 ≤ iter bbar law d ϑ 1 0 := ((iter_props cert hB hd hC 1).2 0 h0mem).1
  induction n with
  | zero =>
    intro s hs
    simp only [pow_zero, one_mul]
    have hz : iter bbar law d ϑ 0 s = 0 := rfl
    rw [hz, sub_zero]
    exact (iter_props cert hB hd hC 1).1 h0mem hs hs.1
  | succ n ih =>
    intro s hs
    have hE0 : 0 ≤ (bbar / (1 + bbar)) ^ n * iter bbar law d ϑ 1 0 := by positivity
    have hE : ∀ t ∈ Icc 0 bbar,
        |iter bbar law d ϑ (n + 1) t - iter bbar law d ϑ n t| ≤
          (bbar / (1 + bbar)) ^ n * iter bbar law d ϑ 1 0 := fun t ht => by
      rw [abs_of_nonneg (sub_nonneg.mpr (iter_le_succ cert hB hd hC n t ht))]
      exact ih t ht
    have hc := abs_pricingOperator_sub_le hB hd ⟨C, hC⟩ cert
      (goodMass2_of_antitoneOn hB (iter_props cert hB hd hC (n + 1)).1)
      (goodMass2_of_antitoneOn hB (iter_props cert hB hd hC n).1) hE0 hE hs
    rw [← iter_succ (n + 1), ← iter_succ n] at hc
    calc iter bbar law d ϑ (n + 1 + 1) s - iter bbar law d ϑ (n + 1) s
        ≤ |iter bbar law d ϑ (n + 1 + 1) s - iter bbar law d ϑ (n + 1) s| := le_abs_self _
      _ ≤ bbar / (1 + bbar) * ((bbar / (1 + bbar)) ^ n * iter bbar law d ϑ 1 0) := hc
      _ = (bbar / (1 + bbar)) ^ (n + 1) * iter bbar law d ϑ 1 0 := by ring

include cert hB hd hC in
/-- The distance from the `n`-th iterate to `ϖ_{d,ϑ}`. -/
theorem leastMass_sub_iter_le (n : ℕ) {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    leastMass bbar law d ϑ s - iter bbar law d ϑ n s ≤
      (bbar / (1 + bbar)) ^ n * iter bbar law d ϑ 1 0 * (1 + bbar) := by
  have hb := bbar_nonneg_of_bodies hB
  have h0mem : (0 : ℝ) ∈ Icc 0 bbar := ⟨le_rfl, hb⟩
  have hM0 : 0 ≤ iter bbar law d ϑ 1 0 := ((iter_props cert hB hd hC 1).2 0 h0mem).1
  set q := bbar / (1 + bbar) with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq : q * (1 + bbar) = bbar := by rw [hq_def]; field_simp
  have key : ∀ j : ℕ, iter bbar law d ϑ (j + n) s - iter bbar law d ϑ n s ≤
      q ^ n * iter bbar law d ϑ 1 0 * (1 + bbar) * (1 - q ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ihj =>
      have h1 := iter_succ_sub_le cert hB hd hC (j + n) s hs
      rw [show j + 1 + n = j + n + 1 by ring]
      have e : q ^ n * iter bbar law d ϑ 1 0 * (1 + bbar) * (1 - q ^ (j + 1)) =
          q ^ n * iter bbar law d ϑ 1 0 * (1 + bbar) * (1 - q ^ j) +
            q ^ (j + n) * iter bbar law d ϑ 1 0 := by
        linear_combination (-(q ^ n * iter bbar law d ϑ 1 0 * q ^ j)) * hq
      rw [e]
      linarith
  have hlim : Tendsto (fun j => iter bbar law d ϑ (j + n) s - iter bbar law d ϑ n s) atTop
      (𝓝 (leastMass bbar law d ϑ s - iter bbar law d ϑ n s)) :=
    ((tendsto_add_atTop_iff_nat n).mpr (tendsto_iter cert hB hd hC hs)).sub_const _
  refine le_of_tendsto' hlim fun j => (key j).trans ?_
  have : 0 ≤ q ^ n * iter bbar law d ϑ 1 0 * (1 + bbar) * q ^ j := by positivity
  linarith

include cert hB hd hC in
/-- `ϖ_{d,ϑ}` is a fixed point of the operator on `[0, b̄]`. -/
theorem leastMass_isFixedPt {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    pricingOperator bbar law d ϑ (leastMass bbar law d ϑ) s = leastMass bbar law d ϑ s := by
  have hb := bbar_nonneg_of_bodies hB
  have h0mem : (0 : ℝ) ∈ Icc 0 bbar := ⟨le_rfl, hb⟩
  have hM0 : 0 ≤ iter bbar law d ϑ 1 0 := ((iter_props cert hB hd hC 1).2 0 h0mem).1
  set q := bbar / (1 + bbar) with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq_def, div_lt_one (by linarith)]; linarith
  have hgm : GoodMass2 bbar law (leastMass bbar law d ϑ) :=
    goodMass2_of_antitoneOn hB (leastMass_antitoneOn cert hB hd hC)
  have hbound : ∀ n : ℕ, ∀ t ∈ Icc 0 bbar,
      |leastMass bbar law d ϑ t - iter bbar law d ϑ n t| ≤
        q ^ n * iter bbar law d ϑ 1 0 * (1 + bbar) := fun n t ht => by
    rw [abs_of_nonneg (sub_nonneg.mpr (iter_le_leastMass cert hB hd hC ht n))]
    exact leastMass_sub_iter_le cert hB hd hC n ht
  have hdist : ∀ n : ℕ,
      |pricingOperator bbar law d ϑ (leastMass bbar law d ϑ) s -
          iter bbar law d ϑ (n + 1) s| ≤
        q * (q ^ n * iter bbar law d ϑ 1 0 * (1 + bbar)) := fun n => by
    rw [iter_succ n]
    exact abs_pricingOperator_sub_le hB hd ⟨C, hC⟩ cert hgm
      (goodMass2_of_antitoneOn hB (iter_props cert hB hd hC n).1) (by positivity) (hbound n) hs
  have hlim0 : Tendsto (fun n : ℕ => q * (q ^ n * iter bbar law d ϑ 1 0 * (1 + bbar))) atTop
      (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (iter bbar law d ϑ 1 0 * (1 + bbar))).const_mul q
    simp only [zero_mul, mul_zero] at h
    refine h.congr fun n => ?_
    ring
  have h1 : Tendsto (fun n => iter bbar law d ϑ (n + 1) s) atTop
      (𝓝 (pricingOperator bbar law d ϑ (leastMass bbar law d ϑ) s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hlim0
    rw [Real.dist_eq, abs_sub_comm]
    exact hdist n
  have h2 : Tendsto (fun n => iter bbar law d ϑ (n + 1) s) atTop
      (𝓝 (leastMass bbar law d ϑ s)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_iter cert hB hd hC hs)
  exact tendsto_nhds_unique h1 h2

include cert hB hd hC in
/-- The rate of Theorem E (i): `|𝒯^[n] 0 - ϖ_{d,ϑ}| ≤ qⁿ ϖ_{d,ϑ}(0)` on `[0, b̄]`. -/
theorem iter_rate (n : ℕ) :
    ∀ s ∈ Icc 0 bbar, |iter bbar law d ϑ n s - leastMass bbar law d ϑ s| ≤
      (bbar / (1 + bbar)) ^ n * leastMass bbar law d ϑ 0 := by
  have hb := bbar_nonneg_of_bodies hB
  have h0mem : (0 : ℝ) ∈ Icc 0 bbar := ⟨le_rfl, hb⟩
  have hL0 : 0 ≤ leastMass bbar law d ϑ 0 := leastMass_nonneg cert hB hd hC h0mem
  have hgm : GoodMass2 bbar law (leastMass bbar law d ϑ) :=
    goodMass2_of_antitoneOn hB (leastMass_antitoneOn cert hB hd hC)
  induction n with
  | zero =>
    intro s hs
    have hz : iter bbar law d ϑ 0 s = 0 := rfl
    rw [hz, zero_sub, abs_neg, abs_of_nonneg (leastMass_nonneg cert hB hd hC hs), pow_zero,
      one_mul]
    exact leastMass_antitoneOn cert hB hd hC h0mem hs hs.1
  | succ n ih =>
    intro s hs
    rw [iter_succ n, ← leastMass_isFixedPt cert hB hd hC hs]
    have hc := abs_pricingOperator_sub_le hB hd ⟨C, hC⟩ cert
      (goodMass2_of_antitoneOn hB (iter_props cert hB hd hC n).1) hgm (by positivity) ih hs
    calc _ ≤ bbar / (1 + bbar) * ((bbar / (1 + bbar)) ^ n * leastMass bbar law d ϑ 0) := hc
      _ = (bbar / (1 + bbar)) ^ (n + 1) * leastMass bbar law d ϑ 0 := by ring

include cert hB hd hC in
/-- Every bounded fixed point on `[0, b̄]` is `ϖ_{d,ϑ}`. -/
theorem fixedPt_eq_leastMass {ϖ : ℝ → ℝ} (hϖb : IsBoundedOn bbar ϖ)
    (hfix : ∀ s ∈ Icc 0 bbar, pricingOperator bbar law d ϑ ϖ s = ϖ s) :
    ∀ s ∈ Icc 0 bbar, ϖ s = leastMass bbar law d ϑ s := by
  have hb := bbar_nonneg_of_bodies hB
  have h0mem : (0 : ℝ) ∈ Icc 0 bbar := ⟨le_rfl, hb⟩
  have hanti : AntitoneOn ϖ (Icc 0 bbar) := fun a ha b hb' hab => by
    rw [← hfix a ha, ← hfix b hb']
    exact pricingOperator_antitoneOn hB hd ⟨C, hC⟩ hϖb ha hb' hab
  obtain ⟨Bϖ, hBϖ⟩ := hϖb
  set q := bbar / (1 + bbar) with hq_def
  have hq1 : q < 1 := by rw [hq_def, div_lt_one (by linarith)]; linarith
  have hbddE : BddAbove ((fun t => |ϖ t - leastMass bbar law d ϑ t|) '' Icc 0 bbar) := by
    refine ⟨Bϖ + (1 + C) * (1 + bbar), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have h1 := abs_sub (ϖ t) (leastMass bbar law d ϑ t)
    have h2 := hBϖ t ht
    have h3 := leastMass_abs_le cert hB hd hC ht
    linarith
  set E := sSup ((fun t => |ϖ t - leastMass bbar law d ϑ t|) '' Icc 0 bbar) with hE_def
  have hle : ∀ t ∈ Icc 0 bbar, |ϖ t - leastMass bbar law d ϑ t| ≤ E := fun t ht =>
    le_csSup hbddE ⟨t, ht, rfl⟩
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hle 0 h0mem)
  have hgm : GoodMass2 bbar law (leastMass bbar law d ϑ) :=
    goodMass2_of_antitoneOn hB (leastMass_antitoneOn cert hB hd hC)
  have hEq : E ≤ q * E := by
    apply csSup_le ((show (Icc (0 : ℝ) bbar).Nonempty from ⟨0, h0mem⟩).image _)
    rintro _ ⟨t, ht, rfl⟩
    have hc := abs_pricingOperator_sub_le hB hd ⟨C, hC⟩ cert (goodMass2_of_antitoneOn hB hanti)
      hgm hE0 hle ht
    rw [hfix t ht, leastMass_isFixedPt cert hB hd hC ht] at hc
    exact hc
  have hE : E ≤ 0 := by nlinarith
  intro s hs
  have h := (hle s hs).trans hE
  have := abs_nonpos_iff.mp h
  linarith

include cert hB hd hC in
theorem leastMass_isBoundedOn : IsBoundedOn bbar (leastMass bbar law d ϑ) :=
  ⟨_, fun _ hs => leastMass_abs_le cert hB hd hC hs⟩

end Iteration

/-! ### Right-continuity and feasibility -/

section Feasibility

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d : ℝ} {ϑ : ℝ → ℝ}

theorem obsMax_rightContinuous (hB : IsBuyerBodies bbar law) (hϑ : ϑ ∈ compensationClass bbar)
    {ϖ : ℝ → ℝ} (hϖ : GoodMass2 bbar law ϖ) {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    ContinuousWithinAt (obsMax bbar law d ϑ ϖ) (Icc s bbar) s := by
  have hϑc : IsCompensation bbar ϑ := hϑ
  have hobs : ∀ i : Fin 2,
      ContinuousWithinAt (obstacle bbar law d ϑ i ϖ) (Icc s bbar) s := by
    intro i
    haveI := hB.isProbability i
    have hsupp := hB.supported i
    have hL : Continuous (Lbar (law i)) := (Lbar_lipschitz' hsupp).continuous
    have hK : Continuous (kernelIntegral bbar (law i) ϖ) :=
      continuous_kernelIntegral hsupp (hϖ i)
    have hLs : Lbar (law i) s ≠ 0 := by
      have := one_le_Lbar' (law i) s
      exact ne_of_gt (by linarith)
    have h1 : ContinuousWithinAt (fun t => d * t / Lbar (law i) t) (Icc s bbar) s :=
      ((continuous_const.mul continuous_id).continuousWithinAt).div hL.continuousWithinAt hLs
    have h2 : ContinuousWithinAt (fun t => compSign i * ϑ t / Lbar (law i) t) (Icc s bbar) s :=
      (continuousWithinAt_const.mul (hϑc.rightContinuous s hs)).div hL.continuousWithinAt hLs
    have h3 : ContinuousWithinAt (fun t => kernelIntegral bbar (law i) ϖ t / Lbar (law i) t)
        (Icc s bbar) s :=
      hK.continuousWithinAt.div hL.continuousWithinAt hLs
    have h : ContinuousWithinAt (fun t => 1 - d * t / Lbar (law i) t +
        compSign i * ϑ t / Lbar (law i) t + kernelIntegral bbar (law i) ϖ t / Lbar (law i) t)
        (Icc s bbar) s := ((continuousWithinAt_const.sub h1).add h2).add h3
    exact h
  have h : ContinuousWithinAt (fun t => max 0 (max (obstacle bbar law d ϑ 0 ϖ t)
      (obstacle bbar law d ϑ 1 ϖ t))) (Icc s bbar) s :=
    continuousWithinAt_const.max ((hobs 0).max (hobs 1))
  exact h

theorem pricingOperator_rightContinuous (hB : IsBuyerBodies bbar law) (hd : 0 < d)
    (hϑ : ϑ ∈ compensationClass bbar) {ϖ : ℝ → ℝ} (hϖ : GoodMass2 bbar law ϖ) {s : ℝ}
    (hs : s ∈ Icc 0 bbar) :
    ContinuousWithinAt (pricingOperator bbar law d ϑ ϖ) (Icc s bbar) s := by
  have hϑc : IsCompensation bbar ϑ := hϑ
  exact futureSup_rightContinuous (F := obsMax bbar law d ϑ ϖ)
    (bddAbove_obsMax hB hd hϑc.bounded (hϖ 0).bound le_rfl)
    (fun u hu => obsMax_rightContinuous hB hϑ hϖ hu) hs

/-- The potential constraint of unit `i` at `t` is the obstacle inequality `A_i ϖ(t) ≤ ϖ(t)`
(certified identity `obstacle_identity`, `L̄ > 0`). -/
theorem potential_iff_obstacle (cert : PricingScalarCertificates) (i : Fin 2) {ϖ : ℝ → ℝ}
    {t : ℝ} :
    compSign i * ϑ t ≤ sellerPotential bbar (law i) d ϖ t ↔
      obstacle bbar law d ϑ i ϖ t ≤ ϖ t := by
  have hL1 := one_le_Lbar' (law i) t
  have hL0 : 0 < Lbar (law i) t := by linarith
  have key := cert.obstacle_identity (Lbar (law i) t) (ϖ t) d t (compSign i) (ϑ t)
    (kernelIntegral bbar (law i) ϖ t) hL0.ne'
  have hpot : sellerPotential bbar (law i) d ϖ t = d * t - Lbar (law i) t +
      Lbar (law i) t * ϖ t - kernelIntegral bbar (law i) ϖ t := by
    unfold sellerPotential gainFromMass; ring
  have hobs : obstacle bbar law d ϑ i ϖ t = 1 - d * t / Lbar (law i) t +
      compSign i * ϑ t / Lbar (law i) t + kernelIntegral bbar (law i) ϖ t / Lbar (law i) t := rfl
  rw [hpot, hobs]
  constructor
  · intro h
    have h' : 0 ≤ Lbar (law i) t * (ϖ t - (1 - d * t / Lbar (law i) t +
        compSign i * ϑ t / Lbar (law i) t + kernelIntegral bbar (law i) ϖ t / Lbar (law i) t)) := by
      rw [key]; linarith
    have := (mul_nonneg_iff_of_pos_left hL0).mp h'
    linarith
  · intro h
    have h' : 0 ≤ Lbar (law i) t * (ϖ t - (1 - d * t / Lbar (law i) t +
        compSign i * ϑ t / Lbar (law i) t + kernelIntegral bbar (law i) ϖ t / Lbar (law i) t)) :=
      mul_nonneg hL0.le (by linarith)
    rw [key] at h'
    linarith

theorem potential_ge_iff_operator_le' (cert : PricingScalarCertificates)
    (hB : IsBuyerBodies bbar law) (hd : 0 < d) (hϑ : ϑ ∈ compensationClass bbar)
    {ϖ : ℝ → ℝ} (hϖ₀ : ∀ s ∈ Icc 0 bbar, 0 ≤ ϖ s) (hϖ : AntitoneOn ϖ (Icc 0 bbar)) :
    (∀ i : Fin 2, ∀ s ∈ Icc 0 bbar, compSign i * ϑ s ≤ sellerPotential bbar (law i) d ϖ s) ↔
      ∀ s ∈ Icc 0 bbar, pricingOperator bbar law d ϑ ϖ s ≤ ϖ s := by
  have hb := bbar_nonneg_of_bodies hB
  have hϖb : ∃ B, ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ B := ⟨_, abs_le_of_antitoneOn hb hϖ⟩
  have hϑc : IsCompensation bbar ϑ := hϑ
  constructor
  · intro h s hs
    rw [pricingOperator_eq_sSup]
    apply csSup_le ((show (Icc s bbar).Nonempty from ⟨s, le_rfl, hs.2⟩).image _)
    rintro _ ⟨t, ht, rfl⟩
    have ht' : t ∈ Icc 0 bbar := ⟨hs.1.trans ht.1, ht.2⟩
    have hts : ϖ t ≤ ϖ s := hϖ hs ht' ht.1
    refine max_le (hϖ₀ s hs) (max_le ?_ ?_)
    · exact ((potential_iff_obstacle cert 0).mp (h 0 t ht')).trans hts
    · exact ((potential_iff_obstacle cert 1).mp (h 1 t ht')).trans hts
  · intro h i s hs
    apply (potential_iff_obstacle cert i).mpr
    have h1 : obstacle bbar law d ϑ i ϖ s ≤ obsMax bbar law d ϑ ϖ s := by
      unfold obsMax
      fin_cases i
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    exact h1.trans ((le_pricingOperator hB hd hϑc.bounded hϖb hs.1 ⟨le_rfl, hs.2⟩).trans
      (h s hs))

theorem leastMass_isFeasible' (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) (hϑ : ϑ ∈ compensationClass bbar) :
    IsFeasibleMass bbar law d ϑ (leastMass bbar law d ϑ) := by
  have hϑc : IsCompensation bbar ϑ := hϑ
  obtain ⟨C, hC⟩ := hϑc.bounded
  have hanti := leastMass_antitoneOn cert hB hd hC
  have hnn : ∀ s ∈ Icc 0 bbar, 0 ≤ leastMass bbar law d ϑ s := fun s hs =>
    leastMass_nonneg cert hB hd hC hs
  refine ⟨⟨hnn, hanti, fun s hs => ?_⟩, ?_⟩
  · have hT := pricingOperator_rightContinuous hB hd hϑ (goodMass2_of_antitoneOn hB hanti) hs
    exact hT.congr (fun y hy => (leastMass_isFixedPt cert hB hd hC ⟨hs.1.trans hy.1, hy.2⟩).symm)
      (leastMass_isFixedPt cert hB hd hC hs).symm
  · exact (potential_ge_iff_operator_le' cert hB hd hϑ hnn hanti).mpr fun s hs =>
      (leastMass_isFixedPt cert hB hd hC hs).le

theorem leastMass_le_of_isFeasible' (cert : PricingScalarCertificates)
    (hB : IsBuyerBodies bbar law) (hd : 0 < d) (hϑ : ϑ ∈ compensationClass bbar)
    {ϖ : ℝ → ℝ} (hϖ : IsFeasibleMass bbar law d ϑ ϖ) :
    ∀ s ∈ Icc 0 bbar, leastMass bbar law d ϑ s ≤ ϖ s := by
  have hϑc : IsCompensation bbar ϑ := hϑ
  obtain ⟨C, hC⟩ := hϑc.bounded
  have hT : ∀ s ∈ Icc 0 bbar, pricingOperator bbar law d ϑ ϖ s ≤ ϖ s :=
    (potential_ge_iff_operator_le' cert hB hd hϑ hϖ.cumulative.nonneg
      hϖ.cumulative.antitoneOn).mp hϖ.potential_ge
  have hgm : GoodMass2 bbar law ϖ := goodMass2_of_antitoneOn hB hϖ.cumulative.antitoneOn
  have hit : ∀ n : ℕ, ∀ s ∈ Icc 0 bbar, iter bbar law d ϑ n s ≤ ϖ s := by
    intro n
    induction n with
    | zero => intro s hs; exact hϖ.cumulative.nonneg s hs
    | succ n ih =>
      intro s hs
      rw [iter_succ n]
      exact (pricingOperator_mono hB hd ⟨C, hC⟩
        (goodMass2_of_antitoneOn hB (iter_props cert hB hd hC n).1) hgm ih hs).trans (hT s hs)
  intro s hs
  exact ciSup_le fun n => hit n s hs

end Feasibility

end FixedPrice.TwoUnit.Pricing
