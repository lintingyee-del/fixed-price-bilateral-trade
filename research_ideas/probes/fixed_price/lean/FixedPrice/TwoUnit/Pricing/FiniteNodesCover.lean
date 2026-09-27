import FixedPrice.TwoUnit.Pricing.FiniteNodesAffine
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Finite-node evaluation, part 3: between the nodes

On the cell of node `j` the potential is `α + βu` with slope
`β = d - (ϖ_j - 1) H + Σ_{ℓ>j} p_{iℓ} ϖ_ℓ`, where `H = Σ_{ℓ>j} p_{iℓ} = H_i(u)`. Abel summation
turns this into the paper's form `d + H_i(s) - ∫_{(s,b̄]} Pr(Z_i ≥ z) π̂₀(dz)`, and
`β ≥ d - H (ϖ_0 - 1) ≥ 0` at the budget `ϖ_0 ≤ 1 + d`. So on each cell the potential is at
least its value at the node, the left limit at a node exceeds the value there by the price atom
times `L̄_i`, and the node constraints give the ordered potential sums at all real seller values
(certified field `ordered_farkas`).
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

namespace FixedPrice.TwoUnit.Pricing

/-- Abel summation over the cells above node `j`. -/
theorem abel_Ioc (w p : ℕ → ℝ) (j : ℕ) : ∀ N, j ≤ N →
    ∑ ℓ ∈ Finset.Ioc j N, (w (ℓ - 1) - w ℓ) * ∑ m ∈ Finset.Icc ℓ N, p m =
      w j * ∑ m ∈ Finset.Ioc j N, p m - ∑ ℓ ∈ Finset.Ioc j N, p ℓ * w ℓ := by
  intro N hjN
  induction N, hjN using Nat.le_induction with
  | base => simp
  | succ N hjN ih =>
    have h1 : ∑ ℓ ∈ Finset.Ioc j (N + 1), (w (ℓ - 1) - w ℓ) * ∑ m ∈ Finset.Icc ℓ (N + 1), p m =
        ∑ ℓ ∈ Finset.Ioc j N, (w (ℓ - 1) - w ℓ) * ∑ m ∈ Finset.Icc ℓ N, p m +
          (∑ ℓ ∈ Finset.Ioc j N, (w (ℓ - 1) - w ℓ)) * p (N + 1) +
            (w N - w (N + 1)) * p (N + 1) := by
      rw [Finset.sum_Ioc_succ_top hjN, Nat.add_sub_cancel, Finset.Icc_self, Finset.sum_singleton,
        Finset.sum_mul, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      rw [Finset.mem_Ioc] at hℓ
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring
    have h2 : ∑ m ∈ Finset.Ioc j (N + 1), p m = ∑ m ∈ Finset.Ioc j N, p m + p (N + 1) :=
      Finset.sum_Ioc_succ_top hjN p
    have h3 : ∑ ℓ ∈ Finset.Ioc j (N + 1), p ℓ * w ℓ =
        ∑ ℓ ∈ Finset.Ioc j N, p ℓ * w ℓ + p (N + 1) * w (N + 1) :=
      Finset.sum_Ioc_succ_top hjN (fun ℓ => p ℓ * w ℓ)
    rw [h1, h2, h3, ih, NodeData.sum_Ioc_telescope w N hjN]
    ring

namespace NodeData

variable {n : ℕ} (D : NodeData n)

theorem law_real_Ioi_of_cell (i : Fin 2) {j : ℕ} {s : ℝ} (hc : D.InCell j s) :
    (D.law i).real (Ioi s) = ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ := by
  rw [D.law_real i measurableSet_Ioi, sum_range_eq_sum_Ioc hc.le_n
    (fun ℓ => D.p i ℓ * (Ioi s).indicator 1 (D.v ℓ)) (fun ℓ hℓ => by
      show D.p i ℓ * (Ioi s).indicator 1 (D.v ℓ) = 0
      rw [indicator_of_notMem (show D.v ℓ ∉ Ioi s from
        not_lt.mpr ((D.v_le hℓ hc.le_n).trans hc.node_le)), mul_zero])]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [Finset.mem_Ioc] at hℓ
  rw [indicator_of_mem (show D.v ℓ ∈ Ioi s from hc.lt_next ℓ hℓ.1 hℓ.2), Pi.one_apply, mul_one]

theorem law_real_Ici_node (i : Fin 2) {ℓ₀ : ℕ} (hℓ₀ : ℓ₀ ≤ n) :
    (D.law i).real (Ici (D.v ℓ₀)) = ∑ m ∈ Finset.Icc ℓ₀ n, D.p i m := by
  rw [D.law_real i measurableSet_Ici]
  symm
  refine Finset.sum_subset_zero_on_sdiff (fun m hm => ?_) (fun m hm => ?_) (fun m hm => ?_)
  · rw [Finset.mem_Icc] at hm; rw [Finset.mem_range]; omega
  · rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc] at hm
    have hm' : m < ℓ₀ := by omega
    rw [indicator_of_notMem (show D.v m ∉ Ici (D.v ℓ₀) from
      not_le.mpr (D.v_lt hm' hℓ₀)), mul_zero]
  · rw [Finset.mem_Icc] at hm
    rw [indicator_of_mem (show D.v m ∈ Ici (D.v ℓ₀) from D.v_le hm.1 hm.2), Pi.one_apply, mul_one]

theorem sum_p_sub (i : Fin 2) (j : ℕ) (u : ℝ) :
    ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * (D.v ℓ - u) =
      ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * D.v ℓ - u * ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sum_pw_sub (i : Fin 2) (j : ℕ) (u : ℝ) (w : ℕ → ℝ) :
    ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * ((D.v ℓ - u) * w ℓ) =
      ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * D.v ℓ * w ℓ -
        u * ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * w ℓ := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The potential on a cell as an affine function of the seller value. -/
theorem sellerPotential_of_cell_affine (i : Fin 2) (d : ℝ) (w : ℕ → ℝ) {j : ℕ} {u : ℝ}
    (hc : D.InCell j u) :
    sellerPotential D.bbar (D.law i) d (D.stepMass w) u =
      ((w j - 1) * (1 + ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * D.v ℓ) -
          ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * D.v ℓ * w ℓ) +
        (d - (w j - 1) * ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ +
          ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * w ℓ) * u := by
  rw [D.sellerPotential_of_cell i d w hc, D.sum_p_sub i j u, D.sum_pw_sub i j u w]
  ring

theorem le_w_zero {w : ℕ → ℝ} (hwa : ∀ j < n, w (j + 1) ≤ w j) : ∀ j ≤ n, w j ≤ w 0 := by
  intro j
  induction j with
  | zero => exact fun _ => le_rfl
  | succ j ih => exact fun hj => (hwa j (by omega)).trans (ih (by omega))

/-- The slope on a cell is at least `d - H (ϖ_0 - 1)`, which is nonnegative at the budget. -/
theorem slope_ge {d : ℝ} (hd : 0 < d) {w : ℕ → ℝ} (hw₀ : ∀ j ≤ n, 0 ≤ w j)
    (hwa : ∀ j < n, w (j + 1) ≤ w j) (i : Fin 2) {j : ℕ} (hj : j ≤ n) :
    d - (∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ) * (w 0 - 1) ≤
        d - (w j - 1) * ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ + ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * w ℓ ∧
      (w 0 ≤ 1 + d → 0 ≤ d - (∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ) * (w 0 - 1)) := by
  have hH0 : 0 ≤ ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ := Finset.sum_nonneg fun ℓ _ => D.p_nonneg i ℓ
  have hH1 := D.p_Ioc_le_one i j
  have hC : 0 ≤ ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * w ℓ := Finset.sum_nonneg fun ℓ hℓ =>
    mul_nonneg (D.p_nonneg i ℓ) (hw₀ ℓ (Finset.mem_Ioc.mp hℓ).2)
  have hwj := le_w_zero hwa j hj
  constructor
  · have := mul_le_mul_of_nonneg_left hwj hH0
    nlinarith
  · intro hb
    rcases le_total (w 0) 1 with h | h
    · have := mul_nonpos_of_nonneg_of_nonpos hH0 (by linarith : w 0 - 1 ≤ 0)
      linarith
    · have := mul_le_mul_of_nonneg_right hH1 (by linarith : (0 : ℝ) ≤ w 0 - 1)
      linarith

/-- "Between price events, `(ψ_i)'(s) = d + H_i(s) - ∫_{(s,b̄]} Pr(Z_i ≥ z) π̂₀(dz)
≥ d - H_i(s)(ϖ_0 - 1) ≥ 0`." -/
theorem sellerPotential_hasDerivAt' {d : ℝ} (hd : 0 < d) {w : ℕ → ℝ}
    (hw₀ : ∀ j ≤ n, 0 ≤ w j) (hwa : ∀ j < n, w (j + 1) ≤ w j) (i : Fin 2) {j : ℕ}
    (hj : j < n) {s : ℝ} (hs : s ∈ Ioo (D.v j) (D.v (j + 1))) :
    HasDerivAt (sellerPotential D.bbar (D.law i) d (D.stepMass w))
      (d + (D.law i).real (Ioi s) -
        ∑ ℓ ∈ Finset.Ioc j n, (w (ℓ - 1) - w ℓ) * (D.law i).real (Ici (D.v ℓ))) s ∧
    d - (D.law i).real (Ioi s) * (w 0 - 1) ≤
      d + (D.law i).real (Ioi s) -
        ∑ ℓ ∈ Finset.Ioc j n, (w (ℓ - 1) - w ℓ) * (D.law i).real (Ici (D.v ℓ)) ∧
    (w 0 ≤ 1 + d → 0 ≤ d - (D.law i).real (Ioi s) * (w 0 - 1)) := by
  have hc := D.inCell_Ico hj ⟨hs.1.le, hs.2⟩
  -- the paper's slope equals the cell slope
  have hIci : ∑ ℓ ∈ Finset.Ioc j n, (w (ℓ - 1) - w ℓ) * (D.law i).real (Ici (D.v ℓ)) =
      w j * ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ - ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * w ℓ := by
    rw [← abel_Ioc w (D.p i) j n hj.le]
    exact Finset.sum_congr rfl fun ℓ hℓ => by
      rw [D.law_real_Ici_node i (Finset.mem_Ioc.mp hℓ).2]
  rw [D.law_real_Ioi_of_cell i hc, hIci]
  obtain ⟨hsl, hbud⟩ := D.slope_ge hd hw₀ hwa i hj.le
  refine ⟨?_, by linarith, hbud⟩
  -- the potential agrees near `s` with an affine function
  set α := (w j - 1) * (1 + ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * D.v ℓ) -
    ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * D.v ℓ * w ℓ with hα
  set β := d - (w j - 1) * ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ + ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * w ℓ
    with hβ
  have hF : HasDerivAt (fun u => α + β * u) β s := by
    simpa using ((hasDerivAt_id s).const_mul β).const_add α
  have heq : (fun u => α + β * u) =ᶠ[𝓝 s] sellerPotential D.bbar (D.law i) d (D.stepMass w) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    rw [D.sellerPotential_of_cell_affine i d w (D.inCell_Ico hj ⟨hu.1.le, hu.2⟩)]
  have hval : d + ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ -
      (w j * ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ - ∑ ℓ ∈ Finset.Ioc j n, D.p i ℓ * w ℓ) = β := by
    rw [hβ]; ring
  rw [hval]
  exact hF.congr_of_eventuallyEq heq.symm

/-- "At an event, the potential drops by the price atom's mass times `L̄_i(s)`." -/
theorem sellerPotential_jump' (d : ℝ) (w : ℕ → ℝ) (i : Fin 2) {j : ℕ} (hj₁ : 1 ≤ j)
    (hj : j ≤ n) :
    Tendsto (sellerPotential D.bbar (D.law i) d (D.stepMass w)) (𝓝[<] (D.v j))
      (𝓝 (sellerPotential D.bbar (D.law i) d (D.stepMass w) (D.v j) +
        (w (j - 1) - w j) * Lbar (D.law i) (D.v j))) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < n := by omega
  simp only [Nat.add_sub_cancel]
  -- the affine function of the cell of node `k`
  set F : ℝ → ℝ := fun u => d * u +
    (w k - 1) * (1 + ∑ ℓ ∈ Finset.Ioc k n, D.p i ℓ * (D.v ℓ - u)) -
      ∑ ℓ ∈ Finset.Ioc k n, D.p i ℓ * ((D.v ℓ - u) * w ℓ) with hF
  have hFc : Continuous F := by rw [hF]; fun_prop
  have heq : F =ᶠ[𝓝[<] (D.v (k + 1))] sellerPotential D.bbar (D.law i) d (D.stepMass w) := by
    filter_upwards [Ioo_mem_nhdsLT (D.v_lt (Nat.lt_succ_self k) hj)] with u hu
    rw [D.sellerPotential_of_cell i d w (D.inCell_Ico hk ⟨hu.1.le, hu.2⟩)]
  -- the value of `F` at the node
  have hsplit : ∀ f : ℕ → ℝ, f (k + 1) = 0 →
      ∑ ℓ ∈ Finset.Ioc k n, f ℓ = ∑ ℓ ∈ Finset.Ioc (k + 1) n, f ℓ := fun f hf => by
    rw [← Finset.sum_Ioc_consecutive f (Nat.le_succ k) hj, Nat.Ioc_succ_singleton,
      Finset.sum_singleton, hf, zero_add]
  have hval : F (D.v (k + 1)) = sellerPotential D.bbar (D.law i) d (D.stepMass w) (D.v (k + 1)) +
      (w k - w (k + 1)) * Lbar (D.law i) (D.v (k + 1)) := by
    rw [D.sellerPotential_of_cell i d w (D.inCell_node hj), D.Lbar_of_cell i (D.inCell_node hj), hF]
    simp only
    rw [hsplit (fun ℓ => D.p i ℓ * (D.v ℓ - D.v (k + 1))) (by simp),
      hsplit (fun ℓ => D.p i ℓ * ((D.v ℓ - D.v (k + 1)) * w ℓ)) (by simp)]
    ring
  rw [← hval]
  exact ((hFc.tendsto _).mono_left nhdsWithin_le_nhds).congr' heq

/-- On a cell the potential is at least its value at the node (budget `ϖ_0 ≤ 1 + d`). -/
theorem sellerPotential_node_le_of_cell {d : ℝ} (hd : 0 < d) {w : ℕ → ℝ}
    (hw₀ : ∀ j ≤ n, 0 ≤ w j) (hwa : ∀ j < n, w (j + 1) ≤ w j) (hbudget : w 0 ≤ 1 + d)
    (i : Fin 2) {j : ℕ} {u : ℝ} (hc : D.InCell j u) :
    sellerPotential D.bbar (D.law i) d (D.stepMass w) (D.v j) ≤
      sellerPotential D.bbar (D.law i) d (D.stepMass w) u := by
  rw [D.sellerPotential_of_cell_affine i d w hc,
    D.sellerPotential_of_cell_affine i d w (D.inCell_node hc.le_n)]
  obtain ⟨hsl, hbud⟩ := D.slope_ge hd hw₀ hwa i hc.le_n
  have hslope := (hbud hbudget).trans hsl
  have := mul_le_mul_of_nonneg_left hc.node_le hslope
  linarith

/-- "Ordered node constraints cover all ordered real seller values." -/
theorem nodeSolution_orderedSum_nonneg' (cert : PricingScalarCertificates) {d : ℝ} (hd : 0 < d)
    {ϑ : ℕ → ℝ} (hϑ : MonotoneOn ϑ (Iic n)) {w : ℕ → ℝ} (hw : D.IsNodeSolution d ϑ w)
    (hbudget : w 0 ≤ 1 + d) (s₁ s₂ : ℝ) (h₁ : 0 ≤ s₁) (h₁₂ : s₁ ≤ s₂) :
    0 ≤ sellerPotential D.bbar (D.law 0) d (D.stepMass w) s₁ +
      sellerPotential D.bbar (D.law 1) d (D.stepMass w) s₂ := by
  have hc₁ := D.inCell_findGreatest h₁
  have hc₂ := D.inCell_findGreatest (h₁.trans h₁₂)
  set J₁ := Nat.findGreatest (fun j => D.v j ≤ s₁) n
  set J₂ := Nat.findGreatest (fun j => D.v j ≤ s₂) n
  have hJ : J₁ ≤ J₂ := Nat.findGreatest_mono_left (fun k hk => le_trans hk h₁₂) n
  have e₁ := D.sellerPotential_node_le_of_cell hd hw.nonneg hw.antitone hbudget 0 hc₁
  have e₂ := D.sellerPotential_node_le_of_cell hd hw.nonneg hw.antitone hbudget 1 hc₂
  have c₁ := D.compSign_mul_le_sellerPotential_node cert hw 0 hc₁.le_n
  have c₂ := D.compSign_mul_le_sellerPotential_node cert hw 1 hc₂.le_n
  rw [compSign_zero] at c₁
  rw [compSign_one, one_mul] at c₂
  have hmono : ϑ J₁ ≤ ϑ J₂ := hϑ (show J₁ ∈ Iic n from hc₁.le_n) (show J₂ ∈ Iic n from hc₂.le_n) hJ
  exact cert.ordered_farkas _ _ (ϑ J₁) (ϑ J₂) (by linarith) (by linarith) (by linarith)

end NodeData

end FixedPrice.TwoUnit.Pricing
