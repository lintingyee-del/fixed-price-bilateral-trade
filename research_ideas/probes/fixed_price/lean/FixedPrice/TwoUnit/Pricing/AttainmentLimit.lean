import FixedPrice.TwoUnit.Pricing.AttainmentBasic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Theorem E, package C, part 2: the minimum is attained

A minimizing sequence of compensations gives least masses `ϖ_n` with `ϖ_n(0) → 𝒥`. Replacing
each compensation by the canonical one keeps feasibility and bounds all compensations uniformly.
On the countable dense set of points `pt r` (`r` rational, clamped to `[0, b̄]`) a single
subsequence makes both `ϖ_n` and `Θ_n` converge (Tychonoff and first countability of a countable
product). The limit is regularized on the right:
`ϖ⁺(s) = sup_{pt r > s} A(r)`, `ϑ⁺(s) = inf_{pt r > s} C(r)`.

The constraints pass to the limit at the dense points through the tail infima
`h_N = inf_{n ≥ N} ϖ_n`: `K_{h_N} ≤ K_{ϖ_m}` for `m ≥ N` and the constraint bounds `K_{ϖ_m}`;
dominated convergence (`h_N ↑ g`) then bounds `K_g`, hence `K_{ϖ⁺}` since `ϖ⁺ ≤ g`. This replaces
the paper's bounded convergence after a second diagonal extraction. Letting the dense point
decrease to `s` (continuity of `L̄` and of the kernel) gives feasibility of `(ϖ⁺, ϑ⁺)` at every
`s`, and leastness gives `ϖ_{d,ϑ⁺}(0) ≤ ϖ⁺(0) ≤ 𝒥`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-! ### Dense points -/

/-- The rational `r` clamped to `[0, b̄]`. -/
def pt (bbar : ℝ) (r : ℚ) : ℝ := max 0 (min (r : ℝ) bbar)

section Points

variable {bbar : ℝ}

theorem pt_mem (hb : 0 ≤ bbar) (r : ℚ) : pt bbar r ∈ Icc 0 bbar :=
  ⟨le_max_left _ _, max_le hb (min_le_right _ _)⟩

theorem pt_of_mem {r : ℚ} (h : (r : ℝ) ∈ Icc 0 bbar) : pt bbar r = r := by
  unfold pt; rw [min_eq_left h.2, max_eq_right h.1]

theorem pt_of_ge (hb : 0 ≤ bbar) {r : ℚ} (h : bbar ≤ (r : ℝ)) : pt bbar r = bbar := by
  unfold pt; rw [min_eq_right h, max_eq_right hb]

/-- The index set of dense points strictly to the right of `s` (or at `b̄`). -/
def idx (bbar s : ℝ) : Set ℚ := {r | s < (r : ℝ) ∨ bbar ≤ (r : ℝ)}

theorem idx_nonempty (s : ℝ) : (idx bbar s).Nonempty := by
  obtain ⟨r, hr⟩ := exists_rat_gt bbar
  exact ⟨r, Or.inr hr.le⟩

theorem idx_anti {s s' : ℝ} (h : s ≤ s') : idx bbar s' ⊆ idx bbar s := fun _ hr =>
  hr.elim (fun h' => Or.inl (h.trans_lt h')) Or.inr

theorem pt_gt_of_idx {s : ℝ} (hs : s ∈ Icc 0 bbar) (hsb : s < bbar) {r : ℚ}
    (hr : r ∈ idx bbar s) : s < pt bbar r := by
  have hb : 0 ≤ bbar := hs.1.trans hsb.le
  rcases hr with h | h
  · exact (lt_min h hsb).trans_le (le_max_right _ _)
  · rw [pt_of_ge hb h]; exact hsb

theorem pt_ge_of_idx {s : ℝ} (hs : s ∈ Icc 0 bbar) {r : ℚ} (hr : r ∈ idx bbar s) :
    s ≤ pt bbar r := by
  rcases lt_or_eq_of_le hs.2 with hsb | hsb
  · exact (pt_gt_of_idx hs hsb hr).le
  · have hb : 0 ≤ bbar := hs.1.trans hs.2
    subst hsb
    rcases hr with h | h
    · rw [pt_of_ge hb h.le]
    · rw [pt_of_ge hb h]

theorem pt_eq_of_idx_bbar (hb : 0 ≤ bbar) {r : ℚ} (hr : r ∈ idx bbar bbar) : pt bbar r = bbar :=
  hr.elim (fun h => pt_of_ge hb h.le) (fun h => pt_of_ge hb h)

end Points

/-! ### The extracted data -/

/-- A minimizing sequence after extraction: feasible masses and compensations, uniformly
bounded, converging at every dense point, with `ϖ_n(0) → 𝒥`. -/
structure ExtractData (bbar : ℝ) (law : Fin 2 → Measure ℝ) (d J Bψ : ℝ) where
  ϖ : ℕ → ℝ → ℝ
  Θ : ℕ → ℝ → ℝ
  A : ℚ → ℝ
  C : ℚ → ℝ
  hΘ : ∀ n, Θ n ∈ compensationClass bbar
  feas : ∀ n, IsFeasibleMass bbar law d (Θ n) (ϖ n)
  bound : ∀ n, ∀ t ∈ Icc 0 bbar, 0 ≤ ϖ n t ∧ ϖ n t ≤ J + 1
  hA : ∀ r, Tendsto (fun n => ϖ n (pt bbar r)) atTop (𝓝 (A r))
  hC : ∀ r, Tendsto (fun n => Θ n (pt bbar r)) atTop (𝓝 (C r))
  hA0 : Tendsto (fun n => ϖ n 0) atTop (𝓝 J)
  hAb : ∀ r, A r ∈ Icc 0 (J + 1)
  hCb : ∀ r, C r ∈ Icc (-Bψ) Bψ

namespace ExtractData

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d J Bψ : ℝ} (E : ExtractData bbar law d J Bψ)

theorem A_anti (hb : 0 ≤ bbar) {r r' : ℚ} (h : pt bbar r ≤ pt bbar r') : E.A r' ≤ E.A r :=
  le_of_tendsto_of_tendsto' (E.hA r') (E.hA r) fun n =>
    (E.feas n).cumulative.antitoneOn (pt_mem hb r) (pt_mem hb r') h

theorem C_mono (hb : 0 ≤ bbar) {r r' : ℚ} (h : pt bbar r ≤ pt bbar r') : E.C r ≤ E.C r' :=
  le_of_tendsto_of_tendsto' (E.hC r) (E.hC r') fun n =>
    (show IsCompensation bbar (E.Θ n) from E.hΘ n).monotoneOn (pt_mem hb r) (pt_mem hb r') h

theorem A_congr (hb : 0 ≤ bbar) {r r' : ℚ} (h : pt bbar r = pt bbar r') : E.A r = E.A r' :=
  le_antisymm (E.A_anti hb h.ge) (E.A_anti hb h.le)

theorem C_congr (hb : 0 ≤ bbar) {r r' : ℚ} (h : pt bbar r = pt bbar r') : E.C r = E.C r' :=
  le_antisymm (E.C_mono hb h.le) (E.C_mono hb h.ge)

/-! #### Tail infima and their limit -/

/-- `h_N(t) = inf_{n} ϖ_{N+n}(t)`. -/
def hfun (N : ℕ) (t : ℝ) : ℝ := ⨅ n : ℕ, E.ϖ (N + n) t

/-- `g(t) = sup_N h_N(t)`, the lower limit of `ϖ_n(t)`. -/
def gfun (t : ℝ) : ℝ := ⨆ N : ℕ, E.hfun N t

theorem bddBelow_tail {t : ℝ} (ht : t ∈ Icc 0 bbar) (N : ℕ) :
    BddBelow (range fun n => E.ϖ (N + n) t) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact (E.bound (N + n) t ht).1⟩

theorem hfun_nonneg {t : ℝ} (ht : t ∈ Icc 0 bbar) (N : ℕ) : 0 ≤ E.hfun N t :=
  le_ciInf fun n => (E.bound (N + n) t ht).1

theorem hfun_le {t : ℝ} (ht : t ∈ Icc 0 bbar) {N m : ℕ} (hm : N ≤ m) : E.hfun N t ≤ E.ϖ m t := by
  have := ciInf_le (E.bddBelow_tail ht N) (m - N)
  rwa [Nat.add_sub_cancel' hm] at this

theorem hfun_le_bound {t : ℝ} (ht : t ∈ Icc 0 bbar) (N : ℕ) : E.hfun N t ≤ J + 1 :=
  (E.hfun_le ht le_rfl).trans (E.bound N t ht).2

theorem hfun_mono {t : ℝ} (ht : t ∈ Icc 0 bbar) : Monotone fun N => E.hfun N t := by
  refine monotone_nat_of_le_succ fun N => le_ciInf fun n => ?_
  have := ciInf_le (E.bddBelow_tail ht N) (n + 1)
  rwa [show N + (n + 1) = N + 1 + n by ring] at this

theorem bddAbove_hfun {t : ℝ} (ht : t ∈ Icc 0 bbar) : BddAbove (range fun N => E.hfun N t) :=
  ⟨J + 1, by rintro _ ⟨N, rfl⟩; exact E.hfun_le_bound ht N⟩

theorem hfun_antitoneOn (N : ℕ) : AntitoneOn (E.hfun N) (Icc 0 bbar) :=
  fun _ ha _ hb hab => ciInf_mono (E.bddBelow_tail hb N) fun n =>
    (E.feas (N + n)).cumulative.antitoneOn ha hb hab

theorem le_gfun {t : ℝ} (ht : t ∈ Icc 0 bbar) (N : ℕ) : E.hfun N t ≤ E.gfun t :=
  le_ciSup (E.bddAbove_hfun ht) N

theorem gfun_nonneg {t : ℝ} (ht : t ∈ Icc 0 bbar) : 0 ≤ E.gfun t :=
  (E.hfun_nonneg ht 0).trans (E.le_gfun ht 0)

theorem gfun_le_bound {t : ℝ} (ht : t ∈ Icc 0 bbar) : E.gfun t ≤ J + 1 :=
  ciSup_le fun N => E.hfun_le_bound ht N

theorem gfun_antitoneOn : AntitoneOn E.gfun (Icc 0 bbar) :=
  fun _ ha _ hb hab => ciSup_mono (E.bddAbove_hfun ha) fun N => E.hfun_antitoneOn N ha hb hab

theorem tendsto_hfun {t : ℝ} (ht : t ∈ Icc 0 bbar) :
    Tendsto (fun N => E.hfun N t) atTop (𝓝 (E.gfun t)) :=
  tendsto_atTop_ciSup (E.hfun_mono ht) (E.bddAbove_hfun ht)

/-- At a dense point the lower limit is the limit. -/
theorem gfun_pt (hb : 0 ≤ bbar) (r : ℚ) : E.gfun (pt bbar r) = E.A r := by
  have ht := pt_mem hb r
  apply le_antisymm
  · refine ciSup_le fun N => ?_
    have hshift : Tendsto (fun m => E.ϖ (m + N) (pt bbar r)) atTop (𝓝 (E.A r)) :=
      (tendsto_add_atTop_iff_nat N).mpr (E.hA r)
    exact ge_of_tendsto hshift (Eventually.of_forall fun m => E.hfun_le ht (by omega))
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (E.hA r)) (ε / 2) (by linarith)
    have hh : E.A r - ε / 2 ≤ E.hfun N (pt bbar r) := le_ciInf fun n => by
      have := hN (N + n) (by omega)
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have := E.le_gfun ht N
    linarith

/-! #### Right regularization -/

/-- `ϖ⁺(s) = sup_{r ∈ idx s} A(r)`. -/
def ϖplus (s : ℝ) : ℝ := ⨆ r : idx bbar s, E.A r

/-- `ϑ⁺(s) = inf_{r ∈ idx s} C(r)`. -/
def ϑplus (s : ℝ) : ℝ := ⨅ r : idx bbar s, E.C r

theorem bddAbove_A (s : ℝ) : BddAbove (range fun r : idx bbar s => E.A r) :=
  ⟨J + 1, by rintro _ ⟨r, rfl⟩; exact (E.hAb r).2⟩

theorem bddBelow_C (s : ℝ) : BddBelow (range fun r : idx bbar s => E.C r) :=
  ⟨-Bψ, by rintro _ ⟨r, rfl⟩; exact (E.hCb r).1⟩

instance (s : ℝ) : Nonempty (idx bbar s) := (idx_nonempty (bbar := bbar) s).to_subtype

theorem A_le_ϖplus {s : ℝ} {r : ℚ} (hr : r ∈ idx bbar s) : E.A r ≤ E.ϖplus s :=
  le_ciSup (E.bddAbove_A s) ⟨r, hr⟩

theorem ϑplus_le_C {s : ℝ} {r : ℚ} (hr : r ∈ idx bbar s) : E.ϑplus s ≤ E.C r :=
  ciInf_le (E.bddBelow_C s) ⟨r, hr⟩

theorem ϖplus_nonneg (s : ℝ) : 0 ≤ E.ϖplus s := by
  obtain ⟨r, hr⟩ := idx_nonempty (bbar := bbar) s
  exact (E.hAb r).1.trans (E.A_le_ϖplus hr)

theorem ϖplus_le_bound (s : ℝ) : E.ϖplus s ≤ J + 1 := ciSup_le fun r => (E.hAb r).2

theorem ϑplus_abs_le (s : ℝ) : |E.ϑplus s| ≤ Bψ := by
  obtain ⟨r, hr⟩ := idx_nonempty (bbar := bbar) s
  have h1 : E.ϑplus s ≤ E.C r := E.ϑplus_le_C hr
  have h2 : -Bψ ≤ E.ϑplus s := le_ciInf fun r => (E.hCb r).1
  have h3 := (E.hCb r).2
  rw [abs_le]; constructor <;> linarith

theorem ϖplus_antitone {s s' : ℝ} (h : s ≤ s') : E.ϖplus s' ≤ E.ϖplus s :=
  ciSup_le fun r => E.A_le_ϖplus (idx_anti h r.2)

theorem ϑplus_monotone {s s' : ℝ} (h : s ≤ s') : E.ϑplus s ≤ E.ϑplus s' :=
  le_ciInf fun r => E.ϑplus_le_C (idx_anti h r.2)

theorem ϖplus_le_gfun (hb : 0 ≤ bbar) {s : ℝ} (hs : s ∈ Icc 0 bbar) : E.ϖplus s ≤ E.gfun s :=
  ciSup_le fun r => by
    rw [← E.gfun_pt hb r]
    exact E.gfun_antitoneOn hs (pt_mem hb r) (pt_ge_of_idx hs r.2)

theorem ϖplus_zero_le (hb : 0 ≤ bbar) : E.ϖplus 0 ≤ J := by
  have h1 := E.ϖplus_le_gfun hb (s := 0) ⟨le_rfl, hb⟩
  have hpt : pt bbar 0 = 0 := by
    rw [pt_of_mem (r := 0) (by simp [hb])]
    simp
  have h2 : E.gfun 0 = E.A 0 := by rw [← E.gfun_pt hb 0, hpt]
  have h3 : E.A 0 = J := by
    have := E.hA 0
    rw [hpt] at this
    exact tendsto_nhds_unique this E.hA0
  linarith

/-- Values at `b̄`. -/
theorem ϖplus_bbar (hb : 0 ≤ bbar) {r₀ : ℚ} (hr₀ : bbar ≤ (r₀ : ℝ)) :
    E.ϖplus bbar = E.A r₀ := by
  apply le_antisymm
  · exact ciSup_le fun r => (E.A_congr hb ((pt_eq_of_idx_bbar hb r.2).trans
      (pt_of_ge hb hr₀).symm)).le
  · exact E.A_le_ϖplus (Or.inr hr₀)

theorem ϑplus_bbar (hb : 0 ≤ bbar) {r₀ : ℚ} (hr₀ : bbar ≤ (r₀ : ℝ)) :
    E.ϑplus bbar = E.C r₀ := by
  apply le_antisymm
  · exact E.ϑplus_le_C (Or.inr hr₀)
  · exact le_ciInf fun r => (E.C_congr hb ((pt_eq_of_idx_bbar hb r.2).trans
      (pt_of_ge hb hr₀).symm)).ge

/-- A dense point strictly between `s` and any bound, with the dense value. -/
theorem exists_rat_idx {s u : ℝ} (hs : s ∈ Icc 0 bbar) (hsu : s < u) (hub : u ≤ bbar) :
    ∃ r : ℚ, r ∈ idx bbar s ∧ pt bbar r = r ∧ s < r ∧ (r : ℝ) < u := by
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hsu
  exact ⟨r, Or.inl hr1, pt_of_mem ⟨hs.1.trans hr1.le, (hr2.trans_le hub).le⟩, hr1, hr2⟩

theorem ϖplus_rightContinuous (hb : 0 ≤ bbar) {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    ContinuousWithinAt E.ϖplus (Icc s bbar) s := by
  rcases lt_or_eq_of_le hs.2 with hsb | hsb
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨⟨r, hr⟩, hrε⟩ := exists_lt_of_lt_ciSup
      (show E.ϖplus s - ε < E.ϖplus s by linarith)
    have hgt := pt_gt_of_idx hs hsb hr
    refine ⟨pt bbar r - s, by linarith, fun {u} hu hdu => ?_⟩
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])] at hdu
    have hur : u < pt bbar r := by linarith
    have hru : r ∈ idx bbar u := by
      rcases hr with h | h
      · left
        have : pt bbar r ≤ r := max_le (by exact_mod_cast (hs.1.trans_lt h).le)
          (min_le_left _ _)
        linarith
      · exact Or.inr h
    have h1 := E.A_le_ϖplus hru
    have h2 := E.ϖplus_antitone hu.1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · subst hsb
    rw [Icc_self]
    exact continuousWithinAt_singleton

theorem ϑplus_rightContinuous (hb : 0 ≤ bbar) {s : ℝ} (hs : s ∈ Icc 0 bbar) :
    ContinuousWithinAt E.ϑplus (Icc s bbar) s := by
  rcases lt_or_eq_of_le hs.2 with hsb | hsb
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨⟨r, hr⟩, hrε⟩ := exists_lt_of_ciInf_lt
      (show E.ϑplus s < E.ϑplus s + ε by linarith)
    have hgt := pt_gt_of_idx hs hsb hr
    refine ⟨pt bbar r - s, by linarith, fun {u} hu hdu => ?_⟩
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])] at hdu
    have hur : u < pt bbar r := by linarith
    have hru : r ∈ idx bbar u := by
      rcases hr with h | h
      · left
        have : pt bbar r ≤ r := max_le (by exact_mod_cast (hs.1.trans_lt h).le)
          (min_le_left _ _)
        linarith
      · exact Or.inr h
    have h1 := E.ϑplus_le_C hru
    have h2 := E.ϑplus_monotone hu.1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · subst hsb
    rw [Icc_self]
    exact continuousWithinAt_singleton

theorem ϑplus_mem (hb : 0 ≤ bbar) : E.ϑplus ∈ compensationClass bbar :=
  ⟨⟨Bψ, fun s _ => E.ϑplus_abs_le s⟩, fun _ _ _ _ hab => E.ϑplus_monotone hab,
    fun _ hs => E.ϑplus_rightContinuous hb hs⟩

theorem ϖplus_cumulative (hb : 0 ≤ bbar) : IsCumulativeMass bbar E.ϖplus :=
  ⟨fun s _ => E.ϖplus_nonneg s, fun _ _ _ _ hab => E.ϖplus_antitone hab,
    fun _ hs => E.ϖplus_rightContinuous hb hs⟩

/-! #### Passing the constraints to the limit -/

variable (hB : IsBuyerBodies bbar law)
include hB

/-- The kernel of the lower limit at a dense point is bounded by the limit of the constraint. -/
theorem kernel_gfun_le (i : Fin 2) (r : ℚ) :
    kernelIntegral bbar (law i) E.gfun (pt bbar r) ≤
      d * pt bbar r - Lbar (law i) (pt bbar r) + Lbar (law i) (pt bbar r) * E.A r -
        compSign i * E.C r := by
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  have hb := bbar_nonneg_of_bodies hB
  have hq := pt_mem hb r
  set q := pt bbar r with hq_def
  set R := d * q - Lbar (law i) q + Lbar (law i) q * E.A r - compSign i * E.C r with hR
  -- the constraint bound converges
  have hRHS : Tendsto (fun m => d * q - Lbar (law i) q + Lbar (law i) q * E.ϖ m q -
      compSign i * E.Θ m q) atTop (𝓝 R) :=
    ((tendsto_const_nhds.add ((E.hA r).const_mul _)).sub ((E.hC r).const_mul _))
  -- each tail infimum is bounded by the limit
  have hN : ∀ N, kernelIntegral bbar (law i) (E.hfun N) q ≤ R := fun N => by
    refine ge_of_tendsto hRHS (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    have hK := kernelIntegral_mono_of_le hsupp
      (goodMass_of_antitoneOn hsupp (E.hfun_antitoneOn N))
      (goodMass_of_antitoneOn hsupp (E.feas m).cumulative.antitoneOn) (s := q)
      (fun t ht => E.hfun_le ⟨hq.1.trans ht.1.le, ht.2⟩ hm)
    have hf := (E.feas m).potential_ge i q hq
    unfold sellerPotential gainFromMass at hf
    linarith
  -- dominated convergence along the tail infima
  have hmeasN : ∀ N, GoodMass bbar (law i) (E.hfun N) := fun N =>
    goodMass_of_antitoneOn hsupp (E.hfun_antitoneOn N)
  have hlim : Tendsto (fun N => kernelIntegral bbar (law i) (E.hfun N) q) atTop
      (𝓝 (kernelIntegral bbar (law i) E.gfun q)) := by
    simp only [kernelIntegral_eq_integral_max hsupp]
    refine tendsto_integral_of_dominated_convergence (fun t => max (t - q) 0 * (J + 1))
      (fun N => ((hmeasN N).integrable_max_sub_mul hsupp q).aestronglyMeasurable)
      (integrable_max_sub_mul hsupp (f := fun _ => J + 1) aestronglyMeasurable_const
        (B := |J + 1|) (fun _ _ => le_rfl) q) (fun N => ?_) ?_
    · filter_upwards [ae_mem_Icc_of_supp hsupp] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_max_right _ _),
        abs_of_nonneg (E.hfun_nonneg ht N)]
      exact mul_le_mul_of_nonneg_left (E.hfun_le_bound ht N) (le_max_right _ _)
    · filter_upwards [ae_mem_Icc_of_supp hsupp] with t ht
      exact (E.tendsto_hfun ht).const_mul _
  exact le_of_tendsto hlim (Eventually.of_forall hN)

/-- The kernel of `ϖ⁺` at a dense point. -/
theorem kernel_ϖplus_le (i : Fin 2) (r : ℚ) :
    kernelIntegral bbar (law i) E.ϖplus (pt bbar r) ≤
      d * pt bbar r - Lbar (law i) (pt bbar r) + Lbar (law i) (pt bbar r) * E.A r -
        compSign i * E.C r := by
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  have hb := bbar_nonneg_of_bodies hB
  have hq := pt_mem hb r
  refine le_trans ?_ (E.kernel_gfun_le hB i r)
  exact kernelIntegral_mono_of_le hsupp
    (goodMass_of_antitoneOn hsupp (E.ϖplus_cumulative hb).antitoneOn)
    (goodMass_of_antitoneOn hsupp E.gfun_antitoneOn)
    (fun t ht => E.ϖplus_le_gfun hb ⟨hq.1.trans ht.1.le, ht.2⟩)

/-- `(ϖ⁺, ϑ⁺)` is feasible. -/
theorem feasible_plus (hd : 0 < d) :
    IsFeasibleMass bbar law d E.ϑplus E.ϖplus := by
  have hb := bbar_nonneg_of_bodies hB
  refine ⟨E.ϖplus_cumulative hb, fun i s hs => ?_⟩
  haveI := hB.isProbability i
  have hsupp := hB.supported i
  unfold sellerPotential gainFromMass
  rcases lt_or_eq_of_le hs.2 with hsb | hsb
  · -- approach `s` from the right through dense points
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hL := Lbar_lipschitz' hsupp
    have hK := continuous_kernelIntegral hsupp
      (goodMass_of_antitoneOn hsupp (E.ϖplus_cumulative hb).antitoneOn)
    set c := d + 2 + (J + 1) with hc
    have hc0 : 0 < c := by
      have := E.hAb 0
      linarith [this.1, this.2]
    obtain ⟨δ, hδ, hδK⟩ := Metric.continuous_iff.mp hK s (η / 3) (by linarith)
    -- a dense point with `C` close to `ϑ⁺(s)`
    obtain ⟨⟨r₁, hr₁⟩, hr₁ε⟩ := exists_lt_of_ciInf_lt
      (show E.ϑplus s < E.ϑplus s + η / 3 by linarith)
    have hgt₁ := pt_gt_of_idx hs hsb hr₁
    set u := min (pt bbar r₁) (min (s + δ) (s + η / (3 * c))) with hu
    have hsu : s < u := lt_min hgt₁ (lt_min (by linarith) (by
      have : 0 < η / (3 * c) := by positivity
      linarith))
    have hub : u ≤ bbar := (min_le_left _ _).trans (pt_mem hb r₁).2
    obtain ⟨r, hr, hptr, hsr, hru⟩ := exists_rat_idx hs hsu hub
    have hq := pt_mem hb r
    have hkey := E.kernel_ϖplus_le hB i r
    rw [hptr] at hkey hq
    -- estimates at the dense point
    have hrδ : (r : ℝ) - s < δ := by
      have := min_le_right (pt bbar r₁) (min (s + δ) (s + η / (3 * c)))
      have := min_le_left (s + δ) (s + η / (3 * c))
      linarith
    have hrη : (r : ℝ) - s ≤ η / (3 * c) := by
      have := min_le_right (pt bbar r₁) (min (s + δ) (s + η / (3 * c)))
      have := min_le_right (s + δ) (s + η / (3 * c))
      linarith
    have hKs : kernelIntegral bbar (law i) E.ϖplus s ≤
        kernelIntegral bbar (law i) E.ϖplus r + η / 3 := by
      have h := hδK r (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; exact hrδ)
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.1]
    have hLr : |Lbar (law i) r - Lbar (law i) s| ≤ r - s := by
      have := hL.dist_le_mul r s
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ r - s)] at this
      exact this
    have hLr1 : 1 ≤ Lbar (law i) r := one_le_Lbar' _ _
    have hAr : E.A r ≤ E.ϖplus s := E.A_le_ϖplus hr
    have hAr0 : 0 ≤ E.A r := (E.hAb r).1
    have hϖs : E.ϖplus s ≤ J + 1 := E.ϖplus_le_bound s
    have hϖs0 : 0 ≤ E.ϖplus s := E.ϖplus_nonneg s
    have hCr : E.ϑplus s ≤ E.C r := E.ϑplus_le_C hr
    have hCr₁ : E.C r ≤ E.C r₁ := E.C_mono hb (by rw [hptr]; exact hru.le.trans (min_le_left _ _))
    have hLA : Lbar (law i) r * E.A r ≤ Lbar (law i) r * E.ϖplus s :=
      mul_le_mul_of_nonneg_left hAr (by linarith)
    have hLϖ : Lbar (law i) r * E.ϖplus s ≤ Lbar (law i) s * E.ϖplus s + (r - s) * (J + 1) := by
      have h1 := (abs_le.mp hLr).2
      have : (Lbar (law i) r - Lbar (law i) s) * E.ϖplus s ≤ (r - s) * (J + 1) :=
        mul_le_mul h1 hϖs hϖs0 (by linarith)
      linarith
    have hcη : (r - s) * c ≤ η / 3 := by
      have := mul_le_mul_of_nonneg_right hrη hc0.le
      rwa [div_mul_eq_mul_div, mul_div_mul_right _ _ hc0.ne'] at this
    have hLlow := (abs_le.mp hLr).1
    -- the compensation term: `ε ϑ⁺(s) - ε C(r) ≤ η/3` for both signs
    have hεC : compSign i * E.ϑplus s - compSign i * E.C r ≤ η / 3 := by
      have hr₁C : E.C r₁ < E.ϑplus s + η / 3 := hr₁ε
      have hsign : compSign i = -1 ∨ compSign i = 1 := by
        unfold compSign; split_ifs <;> simp
      rcases hsign with h | h <;> rw [h] <;> linarith
    have hcη2 : d * ((r : ℝ) - s) + 2 * ((r : ℝ) - s) + ((r : ℝ) - s) * (J + 1) ≤ η / 3 := by
      have e : ((r : ℝ) - s) * c =
          d * ((r : ℝ) - s) + 2 * ((r : ℝ) - s) + ((r : ℝ) - s) * (J + 1) := by rw [hc]; ring
      linarith
    have hdr : d * (r : ℝ) = d * s + d * ((r : ℝ) - s) := by ring
    linarith
  · -- at `b̄` the dense point `b̄` itself
    subst hsb
    obtain ⟨r₀, hr₀'⟩ := exists_rat_gt s
    have hr₀ : s ≤ (r₀ : ℝ) := hr₀'.le
    have hpt := pt_of_ge hb hr₀
    have hkey := E.kernel_ϖplus_le hB i r₀
    rw [hpt] at hkey
    rw [E.ϖplus_bbar hb hr₀, E.ϑplus_bbar hb hr₀]
    linarith

end ExtractData

/-! ### Extraction and attainment -/

section Attainment

variable {bbar : ℝ} {law : Fin 2 → Measure ℝ} {d : ℝ}

theorem exists_extractData (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) :
    ∃ Bψ : ℝ, Nonempty (ExtractData bbar law d (pricingValue bbar law d) Bψ) := by
  have hb := bbar_nonneg_of_bodies hB
  set J := pricingValue bbar law d with hJ
  have hJ0 : 0 ≤ J := pricingValue_nonneg cert hB hd
  -- a minimizing sequence
  have hseq : ∀ n : ℕ, ∃ ϑ ∈ compensationClass bbar,
      leastMass bbar law d ϑ 0 < J + 1 / ((n : ℝ) + 1) := fun n =>
    exists_lt_pricingValue_add (by positivity)
  choose ϑ hϑ hϑlt using hseq
  set ϖ₀ : ℕ → ℝ → ℝ := fun n => leastMass bbar law d (ϑ n) with hϖ₀
  have F : ∀ n, IsFeasibleMass bbar law d (ϑ n) (ϖ₀ n) := fun n =>
    leastMass_isFeasible' cert hB hd (hϑ n)
  have hsum : ∀ n, ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ bbar →
      0 ≤ sellerPotential bbar (law 0) d (ϖ₀ n) s₁ +
        sellerPotential bbar (law 1) d (ϖ₀ n) s₂ := fun n s₁ s₂ h1 h12 h2 => by
    have := orderedSum_ge' (show IsCompensation bbar (ϑ n) from hϑ n).monotoneOn
      (F n).potential_ge h1 h12 h2
    linarith [this.1, this.2]
  set Θ₀ : ℕ → ℝ → ℝ := fun n => canonicalCompensation bbar law d (ϖ₀ n) with hΘ₀
  have hΘspec := fun n => canonicalCompensation_spec' hB (F n).cumulative (hsum n)
  -- uniform bounds
  have h0mem : (0 : ℝ) ∈ Icc 0 bbar := ⟨le_rfl, hb⟩
  have hbound : ∀ n, ∀ t ∈ Icc 0 bbar, 0 ≤ ϖ₀ n t ∧ ϖ₀ n t ≤ J + 1 := fun n t ht => by
    refine ⟨(F n).cumulative.nonneg t ht, ?_⟩
    have h1 := (F n).cumulative.antitoneOn h0mem ht ht.1
    have h2 := hϑlt n
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith
  set Bψ := d * bbar + (1 + bbar) + (1 + bbar) * (J + 1) + bbar * (J + 1) with hBψ
  have hΘb : ∀ n, ∀ t ∈ Icc 0 bbar, Θ₀ n t ∈ Icc (-Bψ) Bψ := fun n t ht => by
    have hf := (hΘspec n).2
    have a0 := hf.potential_ge 0 t ht
    have a1 := hf.potential_ge 1 t ht
    rw [compSign_zero] at a0
    rw [compSign_one, one_mul] at a1
    have b0 := abs_sellerPotential_le hB hd 0 (hbound n) ht
    have b1 := abs_sellerPotential_le hB hd 1 (hbound n) ht
    constructor <;> linarith [(abs_le.mp b0).2, (abs_le.mp b1).2]
  -- extraction on the dense points
  set x : ℕ → ℚ → ℝ × ℝ := fun n r => (ϖ₀ n (pt bbar r), Θ₀ n (pt bbar r)) with hx
  set K : Set (ℚ → ℝ × ℝ) := Set.pi univ fun _ => Icc (0 : ℝ) (J + 1) ×ˢ Icc (-Bψ) Bψ with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc.prod isCompact_Icc
  have hxK : ∀ n, x n ∈ K := fun n r _ =>
    ⟨hbound n _ (pt_mem hb r), hΘb n _ (pt_mem hb r)⟩
  obtain ⟨xl, hxlK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hxK
  have hcoord : ∀ r, Tendsto (fun n => x (φ n) r) atTop (𝓝 (xl r)) := fun r =>
    tendsto_pi_nhds.mp hlim r
  have hJlim : Tendsto (fun n => ϖ₀ n 0) atTop (𝓝 J) := by
    have hlo : ∀ n, J ≤ ϖ₀ n 0 := fun n => pricingValue_le cert hB hd (hϑ n)
    have hup : Tendsto (fun n : ℕ => J + 1 / ((n : ℝ) + 1)) atTop (𝓝 J) := by
      simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlo
      fun n => (hϑlt n).le
  refine ⟨Bψ, ⟨{
    ϖ := fun n => ϖ₀ (φ n)
    Θ := fun n => Θ₀ (φ n)
    A := fun r => (xl r).1
    C := fun r => (xl r).2
    hΘ := fun n => (hΘspec (φ n)).1
    feas := fun n => (hΘspec (φ n)).2
    bound := fun n => hbound (φ n)
    hA := fun r => ((continuous_fst.tendsto _).comp (hcoord r))
    hC := fun r => ((continuous_snd.tendsto _).comp (hcoord r))
    hA0 := hJlim.comp hφ.tendsto_atTop
    hAb := fun r => (hxlK r (mem_univ r)).1
    hCb := fun r => (hxlK r (mem_univ r)).2 }⟩⟩

/-- **Attainment.** The infimum `𝒥` is attained. -/
theorem pricingValue_isLeast' (cert : PricingScalarCertificates) (hB : IsBuyerBodies bbar law)
    (hd : 0 < d) :
    IsLeast ((fun ϑ => leastMass bbar law d ϑ 0) '' compensationClass bbar)
      (pricingValue bbar law d) := by
  have hb := bbar_nonneg_of_bodies hB
  refine ⟨?_, fun y ⟨ϑ, hϑ, hy⟩ => hy ▸ pricingValue_le cert hB hd hϑ⟩
  obtain ⟨Bψ, ⟨E⟩⟩ := exists_extractData cert hB hd
  have hF := E.feasible_plus hB hd
  have hmem := E.ϑplus_mem hb
  have h1 : leastMass bbar law d E.ϑplus 0 ≤ E.ϖplus 0 :=
    leastMass_le_of_isFeasible' cert hB hd hmem hF 0 ⟨le_rfl, hb⟩
  have h2 := E.ϖplus_zero_le hb
  have h3 := pricingValue_le cert hB hd hmem
  exact ⟨E.ϑplus, hmem, le_antisymm (h1.trans h2) h3⟩

end Attainment

end FixedPrice.TwoUnit.Pricing
