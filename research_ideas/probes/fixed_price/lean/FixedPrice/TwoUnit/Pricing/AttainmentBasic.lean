import FixedPrice.TwoUnit.Pricing.Operator

/-!
# Theorem E, package C, part 1: canonical compensation and convexity

* the ordered sum of potentials under a compensation;
* the potentials of a cumulative mass are right-continuous and uniformly bounded;
* the canonical compensation `Θ_ϖ(s) = -inf_{[0,s]} ψ₁^ϖ` of a mass with nonnegative ordered
  potential sums is a compensation (bounded, nondecreasing, right-continuous: it is minus a
  running infimum of a right-continuous function) and is feasible with `ϖ`;
* the compensation class is convex, and `ϖ_{d,ϑ}(0)` is jointly convex in `(d, ϑ)`: a convex
  combination of two least masses is feasible for the combined data (the slack of the combined
  constraint is the convex combination of the slacks, certified field `affine_slack`), and
  leastness bounds the combined least mass by it.

Package C uses package A's internal lemmas directly (`OperatorKernel`, `OperatorFixed`,
`OperatorLeast`); package A is complete, so there is no drift to guard against.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

theorem compSign_zero : compSign 0 = -1 := by simp [compSign]

theorem compSign_one : compSign 1 = 1 := by simp [compSign]

section Potential

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d : ℝ}

theorem orderedSum_ge' {ϑ ϖ : ℝ → ℝ} (hϑ : MonotoneOn ϑ (Icc 0 bbar))
    (hψ : ∀ i : Fin 2, ∀ s ∈ Icc 0 bbar, compSign i * ϑ s ≤ sellerPotential bbar (law i) d ϖ s)
    {s₁ s₂ : ℝ} (h1 : 0 ≤ s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ bbar) :
    ϑ s₂ - ϑ s₁ ≤ sellerPotential bbar (law 0) d ϖ s₁ + sellerPotential bbar (law 1) d ϖ s₂ ∧
      0 ≤ ϑ s₂ - ϑ s₁ := by
  have hm1 : s₁ ∈ Icc 0 bbar := ⟨h1, h12.trans h2⟩
  have hm2 : s₂ ∈ Icc 0 bbar := ⟨h1.trans h12, h2⟩
  have a := hψ 0 s₁ hm1
  have b := hψ 1 s₂ hm2
  rw [compSign_zero] at a
  rw [compSign_one] at b
  exact ⟨by linarith, sub_nonneg.mpr (hϑ hm1 hm2 h12)⟩

theorem sellerPotential_rightContinuous (hB : IsBuyerBodies bbar law) (i : Fin 2) {ϖ : ℝ → ℝ}
    (hϖ : IsCumulativeMass bbar ϖ) {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    ContinuousWithinAt (sellerPotential bbar (law i) d ϖ) (Icc s bbar) s := by
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  have hL := (Lbar_lipschitz' hsupp).continuous
  have hK := continuous_kernelIntegral hsupp (goodMass_of_antitoneOn hsupp hϖ.antitoneOn)
  have h : ContinuousWithinAt (fun t => d * t - Lbar (law i) t +
      (Lbar (law i) t * ϖ t - kernelIntegral bbar (law i) ϖ t)) (Icc s bbar) s :=
    (((continuous_const.mul continuous_id).continuousWithinAt).sub hL.continuousWithinAt).add
      ((hL.continuousWithinAt.mul (hϖ.rightContinuous s hs)).sub hK.continuousWithinAt)
  exact h

/-- A uniform bound on the potentials of masses in `[0, M]`. -/
theorem abs_sellerPotential_le (hB : IsBuyerBodies bbar law) (hd : 0 < d) (i : Fin 2)
    {ϖ : ℝ → ℝ} {M : ℝ} (hM : ∀ t ∈ Icc 0 bbar, 0 ≤ ϖ t ∧ ϖ t ≤ M) {t : ℝ}
    (ht : t ∈ Icc 0 bbar) :
    |sellerPotential bbar (law i) d ϖ t| ≤ d * bbar + (1 + bbar) + (1 + bbar) * M + bbar * M := by
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  have hb := bbar_nonneg_of_supp hsupp
  have hL1 : 1 ≤ Lbar (law i) t := one_le_Lbar' _ _
  have hLb : Lbar (law i) t ≤ 1 + bbar := Lbar_le_one_add' hsupp ht.1
  have hM0 : 0 ≤ M := (hM 0 ⟨le_rfl, hb⟩).1.trans (hM 0 ⟨le_rfl, hb⟩).2
  have habs : ∀ x ∈ Icc 0 bbar, |ϖ x| ≤ M := fun x hx => by
    rw [abs_of_nonneg (hM x hx).1]; exact (hM x hx).2
  have hK := abs_kernelIntegral_le hsupp habs t
  have hKb : |kernelIntegral bbar (law i) ϖ t| ≤ bbar * M := by
    calc _ ≤ M * (Lbar (law i) t - 1) := hK
      _ ≤ M * bbar := mul_le_mul_of_nonneg_left (by linarith) hM0
      _ = bbar * M := mul_comm _ _
  have hLϖ : |Lbar (law i) t * ϖ t| ≤ (1 + bbar) * M := by
    rw [abs_mul, abs_of_pos (by linarith)]
    exact mul_le_mul hLb (habs t ht) (abs_nonneg _) (by linarith)
  have hdt : |d * t| ≤ d * bbar := by
    rw [abs_of_nonneg (mul_nonneg hd.le ht.1)]
    exact mul_le_mul_of_nonneg_left ht.2 hd.le
  unfold sellerPotential gainFromMass
  have a1 := abs_le.mp hKb
  have a2 := abs_le.mp hLϖ
  have a3 := abs_le.mp hdt
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

end Potential

/-! ### Running infima -/

section RunningInf

variable {bbar : ℝ}

/-- The running infimum of a right-continuous function bounded below is right-continuous. -/
theorem runningInf_rightContinuous {f : ℝ → ℝ} {lo : ℝ} (hlo : ∀ t ∈ Icc 0 bbar, lo ≤ f t)
    (hf : ∀ s ∈ Icc 0 bbar, ContinuousWithinAt f (Icc s bbar) s) {s : ℝ}
    (hs : s ∈ Icc 0 bbar) :
    ContinuousWithinAt (fun u => sInf (f '' Icc 0 u)) (Icc s bbar) s := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hbdd : ∀ u ∈ Icc 0 bbar, BddBelow (f '' Icc 0 u) := fun u hu =>
    ⟨lo, by rintro _ ⟨t, ht, rfl⟩; exact hlo t ⟨ht.1, ht.2.trans hu.2⟩⟩
  have hne : ∀ u ∈ Icc 0 bbar, (Icc 0 u).Nonempty := fun u hu => ⟨0, le_rfl, hu.1⟩
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.mp (hf s hs) (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun {u} hu hdu => ?_⟩
  have hu0 : u ∈ Icc 0 bbar := ⟨hs.1.trans hu.1, hu.2⟩
  have hle : sInf (f '' Icc 0 u) ≤ sInf (f '' Icc 0 s) :=
    csInf_le_csInf (hbdd u hu0) ((hne s hs).image f) (image_mono (Icc_subset_Icc le_rfl hu.1))
  have hge : sInf (f '' Icc 0 s) - ε / 2 ≤ sInf (f '' Icc 0 u) := by
    apply le_csInf ((hne u hu0).image f)
    rintro _ ⟨t, ht, rfl⟩
    rcases le_or_gt t s with hts | hts
    · have := csInf_le (hbdd s hs) ⟨t, ⟨ht.1, hts⟩, rfl⟩
      linarith
    · have htmem : t ∈ Icc s bbar := ⟨hts.le, ht.2.trans hu.2⟩
      have hdt : dist t s < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])] at hdu
        linarith [ht.2]
      have h1 := hδf htmem hdt
      rw [Real.dist_eq, abs_lt] at h1
      have := csInf_le (hbdd s hs) ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩
      linarith [h1.1]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end RunningInf

/-! ### The canonical compensation -/

section Canonical

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d : ℝ}

theorem canonicalCompensation_spec' (hB : IsBuyerBodies bbar law) {ϖ : ℝ → ℝ}
    (hϖ : IsCumulativeMass bbar ϖ)
    (hsum : ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ bbar →
      0 ≤ sellerPotential bbar (law 0) d ϖ s₁ + sellerPotential bbar (law 1) d ϖ s₂) :
    canonicalCompensation bbar law d ϖ ∈ compensationClass bbar ∧
      IsFeasibleMass bbar law d (canonicalCompensation bbar law d ϖ) ϖ := by
  have hb := bbar_nonneg_of_bodies hB
  set ψ₀ := sellerPotential bbar (law 0) d ϖ with hψ₀
  set ψ₁ := sellerPotential bbar (law 1) d ϖ with hψ₁
  have hlo : ∀ t ∈ Icc 0 bbar, -ψ₁ bbar ≤ ψ₀ t := fun t ht => by
    have := hsum t bbar ht.1 ht.2 le_rfl
    linarith
  have hbdd : ∀ u ∈ Icc 0 bbar, BddBelow (ψ₀ '' Icc 0 u) := fun u hu =>
    ⟨-ψ₁ bbar, by rintro _ ⟨t, ht, rfl⟩; exact hlo t ⟨ht.1, ht.2.trans hu.2⟩⟩
  have hne : ∀ u ∈ Icc 0 bbar, (Icc 0 u).Nonempty := fun u hu => ⟨0, le_rfl, hu.1⟩
  have hΘ : ∀ u, canonicalCompensation bbar law d ϖ u = -sInf (ψ₀ '' Icc 0 u) := fun u => rfl
  -- lower bound `Θ ≥ -ψ₀(0)` and the second constraint `Θ ≤ ψ₁`
  have hΘlo : ∀ u ∈ Icc 0 bbar, -ψ₀ 0 ≤ canonicalCompensation bbar law d ϖ u := fun u hu => by
    rw [hΘ]
    have := csInf_le (hbdd u hu) ⟨0, ⟨le_rfl, hu.1⟩, rfl⟩
    linarith
  have hΘψ₁ : ∀ u ∈ Icc 0 bbar, canonicalCompensation bbar law d ϖ u ≤ ψ₁ u := fun u hu => by
    rw [hΘ]
    have : -ψ₁ u ≤ sInf (ψ₀ '' Icc 0 u) := by
      apply le_csInf ((hne u hu).image ψ₀)
      rintro _ ⟨t, ht, rfl⟩
      have := hsum t u ht.1 ht.2 hu.2
      linarith
    linarith
  have hΘhi : ∀ u ∈ Icc 0 bbar, canonicalCompensation bbar law d ϖ u ≤ ψ₁ bbar := fun u hu => by
    rw [hΘ]
    have : -ψ₁ bbar ≤ sInf (ψ₀ '' Icc 0 u) :=
      le_csInf ((hne u hu).image ψ₀) (by
        rintro _ ⟨t, ht, rfl⟩; exact hlo t ⟨ht.1, ht.2.trans hu.2⟩)
    linarith
  have hmono : MonotoneOn (canonicalCompensation bbar law d ϖ) (Icc 0 bbar) := by
    intro a ha b hb' hab
    rw [hΘ, hΘ]
    have := csInf_le_csInf (hbdd b hb') ((hne a ha).image ψ₀)
      (image_mono (Icc_subset_Icc le_rfl hab))
    linarith
  have hrc : ∀ s ∈ Icc 0 bbar,
      ContinuousWithinAt (canonicalCompensation bbar law d ϖ) (Icc s bbar) s := fun s hs => by
    have h := (runningInf_rightContinuous hlo
      (fun u hu => sellerPotential_rightContinuous (d := d) hB 0 hϖ hu) hs).neg
    exact h
  refine ⟨⟨⟨max |ψ₀ 0| |ψ₁ bbar|, fun u hu => ?_⟩, hmono, hrc⟩, hϖ, ?_⟩
  · have h1 := hΘlo u hu
    have h2 := hΘhi u hu
    have h3 := le_abs_self (ψ₀ 0)
    have h4 := le_abs_self (ψ₁ bbar)
    have h5 := le_max_left |ψ₀ 0| |ψ₁ bbar|
    have h6 := le_max_right |ψ₀ 0| |ψ₁ bbar|
    rw [abs_le]
    constructor <;> linarith
  · intro i s hs
    fin_cases i
    · show compSign 0 * canonicalCompensation bbar law d ϖ s ≤ ψ₀ s
      rw [compSign_zero, hΘ]
      have := csInf_le (hbdd s hs) ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩
      linarith
    · show compSign 1 * canonicalCompensation bbar law d ϖ s ≤ ψ₁ s
      rw [compSign_one, one_mul]
      exact hΘψ₁ s hs

end Canonical

/-! ### Convexity -/

section Convexity

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ}

theorem compensationClass_convex : Convex ℝ (compensationClass bbar) := by
  intro ϑ₁ h₁ ϑ₂ h₂ a b ha hb hab
  have h₁' : IsCompensation bbar ϑ₁ := h₁
  have h₂' : IsCompensation bbar ϑ₂ := h₂
  obtain ⟨C₁, hC₁⟩ := h₁'.bounded
  obtain ⟨C₂, hC₂⟩ := h₂'.bounded
  refine ⟨⟨a * C₁ + b * C₂, fun s hs => ?_⟩, ?_, fun s hs => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * ϑ₁ s + b * ϑ₂ s| ≤ |a * ϑ₁ s| + |b * ϑ₂ s| := abs_add_le _ _
      _ = a * |ϑ₁ s| + b * |ϑ₂ s| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * C₁ + b * C₂ := add_le_add (mul_le_mul_of_nonneg_left (hC₁ s hs) ha)
          (mul_le_mul_of_nonneg_left (hC₂ s hs) hb)
  · intro x hx y hy hxy
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := h₁'.monotoneOn hx hy hxy
    have := h₂'.monotoneOn hx hy hxy
    nlinarith
  · have h := ((continuousWithinAt_const (b := a)).mul (h₁'.rightContinuous s hs)).add
      ((continuousWithinAt_const (b := b)).mul (h₂'.rightContinuous s hs))
    refine h.congr (fun y _ => ?_) ?_ <;> simp [smul_eq_mul]

variable (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)

include cert hB in
/-- A convex combination of two least masses is feasible for the combined data. -/
theorem isFeasibleMass_convexComb {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) {ϑ₁ ϑ₂ : ℝ → ℝ}
    (hϑ₁ : ϑ₁ ∈ compensationClass bbar) (hϑ₂ : ϑ₂ ∈ compensationClass bbar) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    IsFeasibleMass bbar law (a * d₁ + (1 - a) * d₂) (fun t => a * ϑ₁ t + (1 - a) * ϑ₂ t)
      (fun t => a * leastMass bbar law d₁ ϑ₁ t + (1 - a) * leastMass bbar law d₂ ϑ₂ t) := by
  have F₁ := leastMass_isFeasible' cert hB hd₁ hϑ₁
  have F₂ := leastMass_isFeasible' cert hB hd₂ hϑ₂
  have hb1 : 0 ≤ 1 - a := by linarith
  refine ⟨⟨fun s hs => ?_, fun x hx y hy hxy => ?_, fun s hs => ?_⟩, fun i s hs => ?_⟩
  · have := F₁.cumulative.nonneg s hs
    have := F₂.cumulative.nonneg s hs
    positivity
  · have := F₁.cumulative.antitoneOn hx hy hxy
    have := F₂.cumulative.antitoneOn hx hy hxy
    nlinarith
  · exact ((continuousWithinAt_const.mul (F₁.cumulative.rightContinuous s hs)).add
      (continuousWithinAt_const.mul (F₂.cumulative.rightContinuous s hs)))
  · haveI := hB.isProbability i
    have hsupp := hB.supported i
    have h1 := F₁.potential_ge i s hs
    have h2 := F₂.potential_ge i s hs
    have hlin := kernelIntegral_linear hsupp
      (goodMass_of_antitoneOn hsupp F₁.cumulative.antitoneOn)
      (goodMass_of_antitoneOn hsupp F₂.cumulative.antitoneOn) a (1 - a) s
    -- the combined slack is the convex combination of the two slacks
    have key := cert.affine_slack a (Lbar (law i) s) s d₁ d₂ (leastMass bbar law d₁ ϑ₁ s)
      (leastMass bbar law d₂ ϑ₂ s) (kernelIntegral bbar (law i) (leastMass bbar law d₁ ϑ₁) s)
      (kernelIntegral bbar (law i) (leastMass bbar law d₂ ϑ₂) s) (ϑ₁ s) (ϑ₂ s) (compSign i)
    unfold sellerPotential gainFromMass at h1 h2 ⊢
    rw [hlin]
    have e1 : 0 ≤ a * (-kernelIntegral bbar (law i) (leastMass bbar law d₁ ϑ₁) s +
        Lbar (law i) s * leastMass bbar law d₁ ϑ₁ s - Lbar (law i) s + d₁ * s -
          compSign i * ϑ₁ s) := mul_nonneg ha (by linarith)
    have e2 : 0 ≤ (1 - a) * (-kernelIntegral bbar (law i) (leastMass bbar law d₂ ϑ₂) s +
        Lbar (law i) s * leastMass bbar law d₂ ϑ₂ s - Lbar (law i) s + d₂ * s -
          compSign i * ϑ₂ s) := mul_nonneg hb1 (by linarith)
    linarith

include cert hB in
/-- Joint convexity of `(d, ϑ) ↦ ϖ_{d,ϑ}(0)`. -/
theorem leastMass_convexOn :
    ConvexOn ℝ {p : ℝ × (ℝ → ℝ) | 0 < p.1 ∧ p.2 ∈ compensationClass bbar}
      (fun p => leastMass bbar law p.1 p.2 0) := by
  have hb := bbar_nonneg_of_bodies hB
  have hconv : Convex ℝ {p : ℝ × (ℝ → ℝ) | 0 < p.1 ∧ p.2 ∈ compensationClass bbar} := by
    rintro ⟨d₁, ϑ₁⟩ ⟨hd₁, hϑ₁⟩ ⟨d₂, ϑ₂⟩ ⟨hd₂, hϑ₂⟩ a b ha hb' hab
    refine ⟨?_, ?_⟩
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      rcases eq_or_lt_of_le ha with h | h
      · subst h; simp only [zero_mul, zero_add] at hab ⊢; subst hab; simpa using hd₂
      · have : 0 ≤ b * d₂ := mul_nonneg hb' hd₂.le
        nlinarith
    · simp only [Prod.smul_mk, Prod.mk_add_mk]
      exact compensationClass_convex hϑ₁ hϑ₂ ha hb' hab
  refine ⟨hconv, ?_⟩
  rintro ⟨d₁, ϑ₁⟩ ⟨hd₁, hϑ₁⟩ ⟨d₂, ϑ₂⟩ ⟨hd₂, hϑ₂⟩ a b ha hb' hab
  obtain rfl : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  have hmem := hconv ⟨hd₁, hϑ₁⟩ ⟨hd₂, hϑ₂⟩ ha hb' hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mem_setOf_eq] at hmem
  have hF := isFeasibleMass_convexComb cert hB hd₁ hd₂ hϑ₁ hϑ₂ ha ha1
  have hϑ' : (a • ϑ₁ + (1 - a) • ϑ₂) = fun t => a * ϑ₁ t + (1 - a) * ϑ₂ t := by
    funext t; simp [smul_eq_mul]
  rw [hϑ'] at hmem ⊢
  exact leastMass_le_of_isFeasible' cert hB hmem.1 hmem.2 hF 0 ⟨le_rfl, hb⟩

end Convexity

/-! ### The functional -/

section Functional

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d : ℝ}

theorem zero_mem_compensationClass : (fun _ => (0 : ℝ)) ∈ compensationClass bbar :=
  ⟨⟨0, fun _ _ => by simp⟩, fun _ _ _ _ _ => le_rfl, fun _ _ => continuousWithinAt_const⟩

theorem leastMass_zero_nonneg (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) {ϑ : ℝ → ℝ} (hϑ : ϑ ∈ compensationClass bbar) :
    0 ≤ leastMass bbar law d ϑ 0 := by
  have hϑc : IsCompensation bbar ϑ := hϑ
  obtain ⟨C, hC⟩ := hϑc.bounded
  exact leastMass_nonneg cert hB hd hC ⟨le_rfl, bbar_nonneg_of_bodies hB⟩

theorem pricingValue_bddBelow (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) :
    BddBelow (range fun ϑ : compensationClass bbar => leastMass bbar law d ϑ 0) :=
  ⟨0, by rintro _ ⟨ϑ, rfl⟩; exact leastMass_zero_nonneg cert hB hd ϑ.2⟩

theorem pricingValue_le (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) {ϑ : ℝ → ℝ} (hϑ : ϑ ∈ compensationClass bbar) :
    pricingValue bbar law d ≤ leastMass bbar law d ϑ 0 :=
  ciInf_le (pricingValue_bddBelow cert hB hd) ⟨ϑ, hϑ⟩

theorem pricingValue_nonneg (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) : 0 ≤ pricingValue bbar law d := by
  haveI : Nonempty (compensationClass bbar) := ⟨⟨_, zero_mem_compensationClass⟩⟩
  exact le_ciInf fun ϑ => leastMass_zero_nonneg cert hB hd ϑ.2

theorem exists_lt_pricingValue_add {ε : ℝ} (hε : 0 < ε) :
    ∃ ϑ ∈ compensationClass bbar, leastMass bbar law d ϑ 0 < pricingValue bbar law d + ε := by
  haveI : Nonempty (compensationClass bbar) := ⟨⟨_, zero_mem_compensationClass⟩⟩
  obtain ⟨ϑ, hϑ⟩ := exists_lt_of_ciInf_lt (show pricingValue bbar law d <
    pricingValue bbar law d + ε by linarith)
  exact ⟨ϑ, ϑ.2, hϑ⟩

end Functional

end FixedPrice.TwoUnit.Pricing
