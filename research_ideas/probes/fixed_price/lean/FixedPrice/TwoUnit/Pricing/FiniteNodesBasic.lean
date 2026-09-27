import FixedPrice.TwoUnit.Pricing.FiniteNodes
import FixedPrice.TwoUnit.Pricing.AttainmentBasic

/-!
# Finite-node evaluation, part 1: node laws, cells, the backward solution

* Integrals against a finite sum of weighted Dirac masses are finite sums; the node laws are
  probability measures on `[0, b̄]`.
* On the cell of node `j` (`v_j ≤ u` and every later node lies above `u`) the step mass is
  `ϖ_j`, `L̄_i(u) = 1 + Σ_{ℓ>j} p_{iℓ}(v_ℓ - u)`, and the kernel is
  `Σ_{ℓ>j} p_{iℓ}(v_ℓ - u)ϖ_ℓ`; hence the potential is affine on the cell.
* At a node, `ψ_i(v_j) = L̄_{ij}(ϖ_j - A_{ij}) + ε_i ϑ_j` (certified field `obstacle_identity`),
  so the node inequalities are the potential constraints at the nodes.
* The price body telescopes to the step mass.
* The backward pass sets each entry once; it satisfies `eq:two-backward` and is the least node
  solution (certified fields `step_least`, `step_mono`, `summand_mono`).
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-! ### Finite sums of Dirac masses -/

theorem integral_sum_dirac (s : Finset ℕ) (c x : ℕ → ℝ) (hc : ∀ ℓ ∈ s, 0 ≤ c ℓ)
    (f : ℝ → ℝ) :
    ∫ t, f t ∂(∑ ℓ ∈ s, ENNReal.ofReal (c ℓ) • Measure.dirac (x ℓ)) =
      ∑ ℓ ∈ s, c ℓ * f (x ℓ) := by
  rw [integral_finsetSum_measure fun ℓ _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc ℓ hℓ), smul_eq_mul]

theorem real_sum_dirac (s : Finset ℕ) (c x : ℕ → ℝ) (hc : ∀ ℓ ∈ s, 0 ≤ c ℓ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    (∑ ℓ ∈ s, ENNReal.ofReal (c ℓ) • Measure.dirac (x ℓ)).real S =
      ∑ ℓ ∈ s, c ℓ * S.indicator 1 (x ℓ) := by
  rw [← integral_indicator_one hS, integral_sum_dirac s c x hc]

theorem compSign_cases (i : Fin 2) : compSign i = -1 ∨ compSign i = 1 := by
  unfold compSign; split_ifs <;> simp

/-- Sums over `0, …, n` of terms vanishing up to `j` are sums over `(j, n]`. -/
theorem sum_range_eq_sum_Ioc {n j : ℕ} (_hj : j ≤ n) (f : ℕ → ℝ) (hf : ∀ ℓ ≤ j, f ℓ = 0) :
    ∑ ℓ ∈ Finset.range (n + 1), f ℓ = ∑ ℓ ∈ Finset.Ioc j n, f ℓ := by
  symm
  refine Finset.sum_subset (fun ℓ hℓ => ?_) (fun ℓ hℓ hnot => ?_)
  · rw [Finset.mem_Ioc] at hℓ; rw [Finset.mem_range]; omega
  · rw [Finset.mem_range] at hℓ; rw [Finset.mem_Ioc] at hnot; exact hf ℓ (by omega)

namespace NodeData

variable {n : ℕ} (D : NodeData n)

/-! ### Order of the nodes -/

theorem v_lt {j k : ℕ} (hjk : j < k) (hk : k ≤ n) : D.v j < D.v k :=
  D.v_strictMonoOn (show j ∈ Iic n from (hjk.le.trans hk : j ≤ n)) (show k ∈ Iic n from hk) hjk

theorem v_le {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ n) : D.v j ≤ D.v k := by
  rcases hjk.lt_or_eq with h | h
  · exact (D.v_lt h hk).le
  · rw [h]

theorem v_nonneg {j : ℕ} (hj : j ≤ n) : 0 ≤ D.v j := by
  rw [← D.v_zero]; exact D.v_le (Nat.zero_le j) hj

theorem v_le_bbar {j : ℕ} (hj : j ≤ n) : D.v j ≤ D.bbar := D.v_le hj le_rfl

theorem bbar_nonneg : 0 ≤ D.bbar := D.v_nonneg le_rfl

/-! ### The node laws -/

theorem integral_law (i : Fin 2) (f : ℝ → ℝ) :
    ∫ t, f t ∂(D.law i) = ∑ ℓ ∈ Finset.range (n + 1), D.p i ℓ * f (D.v ℓ) :=
  integral_sum_dirac _ _ _ (fun ℓ _ => D.p_nonneg i ℓ) f

theorem law_real (i : Fin 2) {S : Set ℝ} (hS : MeasurableSet S) :
    (D.law i).real S = ∑ ℓ ∈ Finset.range (n + 1), D.p i ℓ * S.indicator 1 (D.v ℓ) :=
  real_sum_dirac _ _ _ (fun ℓ _ => D.p_nonneg i ℓ) hS

instance isProbabilityMeasure_law (i : Fin 2) : IsProbabilityMeasure (D.law i) := by
  constructor
  simp only [law, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ℓ _ => D.p_nonneg i ℓ, D.p_sum i, ENNReal.ofReal_one]

theorem law_supported (i : Fin 2) : D.law i (Icc 0 D.bbar)ᶜ = 0 := by
  simp only [law, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
  refine Finset.sum_eq_zero fun ℓ hℓ => ?_
  have hℓ' : ℓ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl,
    indicator_of_notMem (show D.v ℓ ∉ (Icc 0 D.bbar)ᶜ from
      fun h => h ⟨D.v_nonneg hℓ', D.v_le_bbar hℓ'⟩), smul_zero]

theorem isBuyerBodies : IsBuyerBodies D.bbar D.law :=
  ⟨D.isProbabilityMeasure_law, D.law_supported⟩

theorem p_Ioc_le_one (i : Fin 2) (j : ℕ) : ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ ≤ 1 := by
  rw [← D.p_sum i]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => ?_) fun ℓ _ _ => D.p_nonneg i ℓ
  rw [Finset.mem_Ioc] at hℓ; rw [Finset.mem_range]; omega

/-! ### Cells -/

/-- `u` lies in the cell of node `j`: `v_j ≤ u`, and every later node lies above `u`. -/
structure InCell (j : ℕ) (u : ℝ) : Prop where
  le_n : j ≤ n
  node_le : D.v j ≤ u
  lt_next : ∀ ℓ, j < ℓ → ℓ ≤ n → u < D.v ℓ

theorem inCell_node {j : ℕ} (hj : j ≤ n) : D.InCell j (D.v j) :=
  ⟨hj, le_rfl, fun _ h1 h2 => D.v_lt h1 h2⟩

theorem inCell_Ico {j : ℕ} (hj : j < n) {u : ℝ} (hu : u ∈ Ico (D.v j) (D.v (j + 1))) :
    D.InCell j u :=
  ⟨hj.le, hu.1, fun _ h1 h2 => hu.2.trans_le (D.v_le (Nat.succ_le_of_lt h1) h2)⟩

theorem inCell_findGreatest {u : ℝ} (hu : 0 ≤ u) :
    D.InCell (Nat.findGreatest (fun j => D.v j ≤ u) n) u :=
  ⟨Nat.findGreatest_le n, Nat.findGreatest_spec (P := fun j => D.v j ≤ u) (m := 0) (Nat.zero_le n)
    (by show D.v 0 ≤ u; rw [D.v_zero]; exact hu),
    fun _ h1 h2 => not_le.mp (Nat.findGreatest_is_greatest h1 h2)⟩

theorem stepMass_of_cell {j : ℕ} {u : ℝ} (hc : D.InCell j u) (w : ℕ → ℝ) :
    D.stepMass w u = w j := by
  unfold stepMass
  rw [Nat.findGreatest_eq_iff.mpr ⟨hc.le_n, fun _ => hc.node_le,
    fun k hk hkn => not_le.mpr (hc.lt_next k hk hkn)⟩]

theorem stepMass_node (w : ℕ → ℝ) {j : ℕ} (hj : j ≤ n) : D.stepMass w (D.v j) = w j :=
  D.stepMass_of_cell (D.inCell_node hj) w

theorem Lbar_of_cell (i : Fin 2) {j : ℕ} {u : ℝ} (hc : D.InCell j u) :
    Lbar (D.law i) u = 1 + ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * (D.v ℓ - u) := by
  unfold Lbar
  rw [D.integral_law i, sum_range_eq_sum_Ioc hc.le_n (fun ℓ => D.p i ℓ * max (D.v ℓ - u) 0)
    (fun ℓ hℓ => by
      show D.p i ℓ * max (D.v ℓ - u) 0 = 0
      rw [max_eq_right (by linarith [D.v_le hℓ hc.le_n, hc.node_le]), mul_zero])]
  congr 1
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [Finset.mem_Ioc] at hℓ
  rw [max_eq_left (by linarith [hc.lt_next ℓ hℓ.1 hℓ.2])]

theorem kernelIntegral_of_cell (i : Fin 2) (ϖ : ℝ → ℝ) {j : ℕ} {u : ℝ} (hc : D.InCell j u) :
    kernelIntegral D.bbar (D.law i) ϖ u =
      ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * ((D.v ℓ - u) * ϖ (D.v ℓ)) := by
  unfold kernelIntegral
  rw [← integral_indicator measurableSet_Ioc, D.integral_law i,
    sum_range_eq_sum_Ioc hc.le_n
      (fun ℓ => D.p i ℓ * (Ioc u D.bbar).indicator (fun t => (t - u) * ϖ t) (D.v ℓ))
      (fun ℓ hℓ => by
        show D.p i ℓ * (Ioc u D.bbar).indicator (fun t => (t - u) * ϖ t) (D.v ℓ) = 0
        rw [indicator_of_notMem (show D.v ℓ ∉ Ioc u D.bbar from fun h => absurd h.1
          (not_lt.mpr ((D.v_le hℓ hc.le_n).trans hc.node_le))), mul_zero])]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [Finset.mem_Ioc] at hℓ
  rw [indicator_of_mem (show D.v ℓ ∈ Ioc u D.bbar from ⟨hc.lt_next ℓ hℓ.1 hℓ.2, D.v_le_bbar hℓ.2⟩)]

/-- The potential on the cell of node `j`. -/
theorem sellerPotential_of_cell (i : Fin 2) (d : ℝ) (w : ℕ → ℝ) {j : ℕ} {u : ℝ}
    (hc : D.InCell j u) :
    sellerPotential D.bbar (D.law i) d (D.stepMass w) u =
      d * u + (w j - 1) * (1 + ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * (D.v ℓ - u)) -
        ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * ((D.v ℓ - u) * w ℓ) := by
  unfold sellerPotential gainFromMass
  rw [D.Lbar_of_cell i hc, D.kernelIntegral_of_cell i _ hc, D.stepMass_of_cell hc w]
  have hk : ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * ((D.v ℓ - u) * D.stepMass w (D.v ℓ)) =
      ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * ((D.v ℓ - u) * w ℓ) :=
    Finset.sum_congr rfl fun ℓ hℓ => by
      rw [D.stepMass_node w (Finset.mem_Ioc.mp hℓ).2]
  rw [hk]
  ring

/-- At a node, the node inequality is the potential constraint (certified field
`obstacle_identity`). -/
theorem compSign_mul_le_sellerPotential_node (cert : PricingScalarCertificates) {d : ℝ}
    {ϑ w : ℕ → ℝ} (hw : D.IsNodeSolution d ϑ w) (i : Fin 2) {j : ℕ} (hj : j ≤ n) :
    compSign i * ϑ j ≤ sellerPotential D.bbar (D.law i) d (D.stepMass w) (D.v j) := by
  have hle := hw.obstacle_le i j hj
  unfold nodeObstacle Lnode at hle
  have hL := D.Lbar_of_cell i (D.inCell_node hj)
  have hL1 := one_le_Lbar' (D.law i) (D.v j)
  rw [D.sellerPotential_of_cell i d w (D.inCell_node hj), ← hL]
  have hsum : ∑ ℓ ∈ Finset.Ioc j n,
      (D.v ℓ - D.v j) * D.p i ℓ / Lbar (D.law i) (D.v j) * w ℓ =
      (∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * ((D.v ℓ - D.v j) * w ℓ)) / Lbar (D.law i) (D.v j) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  rw [hsum] at hle
  have hid := cert.obstacle_identity (Lbar (D.law i) (D.v j)) (w j) d (D.v j) (compSign i) (ϑ j)
    (∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * ((D.v ℓ - D.v j) * w ℓ)) (by linarith)
  have hpos := mul_nonneg (show (0 : ℝ) ≤ Lbar (D.law i) (D.v j) by linarith) (sub_nonneg.mpr hle)
  rw [hid] at hpos
  linarith

/-! ### The price body -/

theorem priceBody_real {w : ℕ → ℝ} (hwa : ∀ j < n, w (j + 1) ≤ w j) {S : Set ℝ}
    (hS : MeasurableSet S) :
    (D.priceBody w).real S =
      ∑ ℓ ∈ Finset.Icc 1 n, (w (ℓ - 1) - w ℓ) * S.indicator 1 (D.v ℓ) :=
  real_sum_dirac _ _ _ (fun ℓ hℓ => by
    rw [Finset.mem_Icc] at hℓ
    have := hwa (ℓ - 1) (by omega)
    rw [Nat.sub_add_cancel hℓ.1] at this
    linarith) hS

theorem sum_Ioc_telescope (f : ℕ → ℝ) {j : ℕ} : ∀ m, j ≤ m →
    ∑ ℓ ∈ Finset.Ioc j m, (f (ℓ - 1) - f ℓ) = f j - f m := by
  intro m hjm
  induction m, hjm using Nat.le_induction with
  | base => simp
  | succ m hjm ih =>
    rw [Finset.sum_Ioc_succ_top hjm, ih, Nat.add_sub_cancel]
    ring

theorem priceBody_spec' {w : ℕ → ℝ} (hwa : ∀ j < n, w (j + 1) ≤ w j) :
    (∀ s ∈ Icc 0 D.bbar, w n + (D.priceBody w).real (Ioc s D.bbar) = D.stepMass w s) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ n → D.priceBody w {D.v j} = ENNReal.ofReal (w (j - 1) - w j) := by
  constructor
  · intro s hs
    have hc := D.inCell_findGreatest hs.1
    set J := Nat.findGreatest (fun j => D.v j ≤ s) n with hJ
    rw [D.stepMass_of_cell hc w, D.priceBody_real hwa measurableSet_Ioc]
    have hsub : ∑ ℓ ∈ Finset.Icc 1 n, (w (ℓ - 1) - w ℓ) * (Ioc s D.bbar).indicator 1 (D.v ℓ) =
        ∑ ℓ ∈ Finset.Ioc J n, (w (ℓ - 1) - w ℓ) := by
      symm
      refine Finset.sum_subset_zero_on_sdiff (fun ℓ hℓ => ?_) (fun ℓ hℓ => ?_) (fun ℓ hℓ => ?_)
      · rw [Finset.mem_Ioc] at hℓ; rw [Finset.mem_Icc]; omega
      · rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc] at hℓ
        have hℓJ : ℓ ≤ J := by omega
        rw [indicator_of_notMem (show D.v ℓ ∉ Ioc s D.bbar from fun h => absurd h.1
          (not_lt.mpr ((D.v_le hℓJ hc.le_n).trans hc.node_le))), mul_zero]
      · rw [Finset.mem_Ioc] at hℓ
        rw [indicator_of_mem (show D.v ℓ ∈ Ioc s D.bbar from
          ⟨hc.lt_next ℓ hℓ.1 hℓ.2, D.v_le_bbar hℓ.2⟩), Pi.one_apply, mul_one]
    rw [hsub, sum_Ioc_telescope w n hc.le_n]
    ring
  · intro j hj1 hjn
    simp only [priceBody, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton _), smul_eq_mul]
    rw [Finset.sum_eq_single j (fun ℓ hℓ hne => ?_) (fun h => absurd (Finset.mem_Icc.mpr ⟨hj1, hjn⟩) h),
      indicator_of_mem (mem_singleton _), Pi.one_apply, mul_one]
    rw [Finset.mem_Icc] at hℓ
    have hv : D.v ℓ ≠ D.v j := fun h => hne (D.v_strictMonoOn.injOn (show ℓ ∈ Iic n from hℓ.2)
      (show j ∈ Iic n from hjn) h)
    rw [indicator_of_notMem (show D.v ℓ ∉ ({D.v j} : Set ℝ) from
      fun h => hv (mem_singleton_iff.mp h)), mul_zero]

/-! ### The backward pass -/

theorem nodeObstacle_congr (d : ℝ) (ϑ : ℕ → ℝ) (i : Fin 2) (j : ℕ) {w w' : ℕ → ℝ}
    (h : ∀ ℓ ∈ Finset.Ioc j n, w ℓ = w' ℓ) :
    D.nodeObstacle d ϑ i j w = D.nodeObstacle d ϑ i j w' := by
  unfold nodeObstacle
  congr 1
  exact Finset.sum_congr rfl fun ℓ hℓ => by rw [h ℓ hℓ]

theorem backwardPass_stable (d : ℝ) (ϑ : ℕ → ℝ) {k m : ℕ} (hkm : k ≤ m) (hm : m ≤ n) {ℓ : ℕ}
    (hℓ : n - k ≤ ℓ) : D.backwardPass d ϑ m ℓ = D.backwardPass d ϑ k ℓ := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    simp only [backwardPass]
    rw [Function.update_of_ne (by omega), ih (by omega)]

theorem nodeMass_last' (d : ℝ) (ϑ : ℕ → ℝ) : D.nodeMass d ϑ n = D.terminalMass d ϑ := by
  unfold nodeMass
  rw [D.backwardPass_stable d ϑ (Nat.zero_le n) le_rfl (by omega)]
  rfl

theorem nodeMass_backward' (d : ℝ) (ϑ : ℕ → ℝ) {j : ℕ} (hj : j < n) :
    D.nodeMass d ϑ j =
      max (D.nodeMass d ϑ (j + 1))
        (max (D.nodeObstacle d ϑ 0 j (D.nodeMass d ϑ)) (D.nodeObstacle d ϑ 1 j (D.nodeMass d ϑ))) := by
  obtain ⟨k, hk⟩ : ∃ k, n = j + k + 1 := ⟨n - j - 1, by omega⟩
  have hkn : k + 1 ≤ n := by omega
  have hj' : n - (k + 1) = j := by omega
  have hstab : ∀ ℓ, j + 1 ≤ ℓ → D.backwardPass d ϑ k ℓ = D.nodeMass d ϑ ℓ := fun ℓ hℓ =>
    (D.backwardPass_stable d ϑ (by omega : k ≤ n) le_rfl (by omega)).symm
  unfold nodeMass
  rw [D.backwardPass_stable d ϑ hkn le_rfl (by omega : n - (k + 1) ≤ j)]
  simp only [backwardPass]
  rw [hj', Function.update_self]
  unfold nodeMass at hstab
  rw [hstab (j + 1) le_rfl,
    D.nodeObstacle_congr d ϑ 0 j fun ℓ hℓ => hstab ℓ (Finset.mem_Ioc.mp hℓ).1,
    D.nodeObstacle_congr d ϑ 1 j fun ℓ hℓ => hstab ℓ (Finset.mem_Ioc.mp hℓ).1]

theorem Lnode_last (i : Fin 2) : D.Lnode i n = 1 := by
  unfold Lnode
  rw [D.Lbar_of_cell i (D.inCell_node le_rfl), Finset.Ioc_self, Finset.sum_empty, add_zero]

theorem nodeObstacle_last (d : ℝ) (ϑ : ℕ → ℝ) (i : Fin 2) (w : ℕ → ℝ) :
    D.nodeObstacle d ϑ i n w = 1 - d * D.v n + compSign i * ϑ n := by
  unfold nodeObstacle
  rw [D.Lnode_last i, Finset.Ioc_self, Finset.sum_empty]
  ring

theorem nodeObstacle_mono (ncert : NodeScalarCertificates) (d : ℝ) (ϑ : ℕ → ℝ) (i : Fin 2)
    {j : ℕ} {w w' : ℕ → ℝ} (h : ∀ ℓ ∈ Finset.Ioc j n, w ℓ ≤ w' ℓ) :
    D.nodeObstacle d ϑ i j w ≤ D.nodeObstacle d ϑ i j w' := by
  unfold nodeObstacle
  have hL : 0 < D.Lnode i j := lt_of_lt_of_le one_pos (one_le_Lbar' _ _)
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro ℓ hℓ
  rw [Finset.mem_Ioc] at hℓ
  have hc : 0 ≤ (D.v ℓ - D.v j) * D.p i ℓ / D.Lnode i j :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr (D.v_lt hℓ.1 hℓ.2).le) (D.p_nonneg i ℓ)) hL.le
  have := ncert.summand_mono (w ℓ) (w' ℓ) _ hc (h ℓ (Finset.mem_Ioc.mpr hℓ))
  linarith [mul_comm (w ℓ) ((D.v ℓ - D.v j) * D.p i ℓ / D.Lnode i j),
    mul_comm (w' ℓ) ((D.v ℓ - D.v j) * D.p i ℓ / D.Lnode i j)]

/-- The backward pass is the least node solution. -/
theorem nodeMass_isLeastSolution' (ncert : NodeScalarCertificates) (d : ℝ) (ϑ : ℕ → ℝ) :
    D.IsNodeSolution d ϑ (D.nodeMass d ϑ) ∧
      ∀ w : ℕ → ℝ, D.IsNodeSolution d ϑ w → ∀ j ≤ n, D.nodeMass d ϑ j ≤ w j := by
  -- nonnegativity by descending induction
  have hnn : ∀ k, ∀ j, n - k ≤ j → j ≤ n → 0 ≤ D.nodeMass d ϑ j := by
    intro k
    induction k with
    | zero =>
      intro j hj1 hj2
      have : j = n := by omega
      rw [this, D.nodeMass_last']
      exact le_max_left _ _
    | succ k ih =>
      intro j hj1 hj2
      rcases (show n - k ≤ j ∨ j < n - k by omega) with h | h
      · exact ih j h hj2
      · rw [D.nodeMass_backward' d ϑ (by omega)]
        exact (ih (j + 1) (by omega) (by omega)).trans (le_max_left _ _)
  refine ⟨⟨fun j hj => hnn n j (by omega) hj, fun j hj => ?_, fun i j hj => ?_⟩, ?_⟩
  · rw [D.nodeMass_backward' d ϑ hj]
    exact le_max_left _ _
  · rcases hj.lt_or_eq with h | h
    · rw [D.nodeMass_backward' d ϑ h]
      fin_cases i
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    · subst h
      rw [D.nodeObstacle_last, D.nodeMass_last']
      unfold terminalMass
      rcases compSign_cases i with hi | hi <;> rw [hi]
      · exact (le_of_eq (by ring)).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (le_of_eq (by ring)).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro w hw
    have key : ∀ k, ∀ j, n - k ≤ j → j ≤ n → D.nodeMass d ϑ j ≤ w j := by
      intro k
      induction k with
      | zero =>
        intro j hj1 hj2
        have : j = n := by omega
        subst this
        rw [D.nodeMass_last']
        have h0 := hw.obstacle_le 0 j le_rfl
        have h1 := hw.obstacle_le 1 j le_rfl
        rw [D.nodeObstacle_last, compSign_zero] at h0
        rw [D.nodeObstacle_last, compSign_one] at h1
        exact (ncert.step_least (w j) 0 _ _ le_rfl (hw.nonneg j le_rfl)
          (by linarith) (by linarith)).2.2.2.2
      | succ k ih =>
        intro j hj1 hj2
        rcases (show n - k ≤ j ∨ j < n - k by omega) with h | h
        · exact ih j h hj2
        · have hjn : j < n := by omega
          have hfut : ∀ ℓ ∈ Finset.Ioc j n, D.nodeMass d ϑ ℓ ≤ w ℓ := fun ℓ hℓ =>
            ih ℓ (by rw [Finset.mem_Ioc] at hℓ; omega) (Finset.mem_Ioc.mp hℓ).2
          rw [D.nodeMass_backward' d ϑ hjn]
          refine (ncert.step_mono _ _ _ _ _ _ (ih (j + 1) (by omega) (by omega))
            (D.nodeObstacle_mono ncert d ϑ 0 hfut) (D.nodeObstacle_mono ncert d ϑ 1 hfut)).trans ?_
          exact (ncert.step_least (w j) (w (j + 1)) _ _ (hw.nonneg (j + 1) (by omega))
            (hw.antitone j hjn) (hw.obstacle_le 0 j hjn.le) (hw.obstacle_le 1 j hjn.le)).2.2.2.2
    exact fun j hj => key n j (by omega) hj

end NodeData

end FixedPrice.TwoUnit.Pricing
