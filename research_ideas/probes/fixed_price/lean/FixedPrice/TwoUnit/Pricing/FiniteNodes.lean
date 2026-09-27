import FixedPrice.TwoUnit.Pricing.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Finite-node evaluation (secondary target)

Source: `manuscript/two_unit_pricing_proofs.tex`, `app:two-recurrence`, equation
`eq:two-backward` and the paragraph on covering the intervals between nodes. This is a secondary
target: Theorem E does not depend on it. It is the certificate used by the numerical search of
`sec:two-open`.

Definitions, the machine-certified scalar facts for the node steps, and one `Prop`
abbreviation `<Name>Statement` per claim (a definition, with no proof obligation of its own).
Nothing in this file is proved. Proofs go to `FiniteNodesProofs.lean` as
`theorem <name>_proof : <Name>Statement`.

Conventions. Nodes are `v : ℕ → ℝ` read on `0, …, n`; node probabilities `p i ℓ = Pr(Z_i = v_ℓ)`
for the Lean unit index `i : Fin 2` (index `0` is the paper's unit 1); node compensations
`ϑ : ℕ → ℝ` with `ϑ j = ϑ(v_j)`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

/- The claims are `Prop` abbreviations whose hypothesis binders keep the names of the original
signatures (for readability and for `intro` in the package proofs). A `∀`-bound hypothesis is
never referenced inside the proposition itself, so the unused-variables linter would flag every
one of them; it is switched off for this file only. -/
set_option linter.unusedVariables false

namespace FixedPrice.TwoUnit.Pricing

/-- Scalar facts for the backward recursion that the ledger already certifies by machine; not
re-proved in Lean (standing user rule). Formulas in
`manuscript/checks/first_layer_20260921/results.json` (group `recurrence`) and
`manuscript/checks/first_layer_20260921/max_convexity_exact.json`; paper graph nodes
`L_20260921_finite_node_steps` and `L_20260921_max_convexity`. -/
structure NodeScalarCertificates : Prop where
  /-- One backward step is the least value above the next mass and both obstacles. Ledger
  `fpm_20260921_finite_node_max_steps_smt` (z3 and cvc5), check
  `one_backward_step_is_least_feasible`. -/
  step_least : ∀ c next o₁ o₂ : ℝ, 0 ≤ next → next ≤ c → o₁ ≤ c → o₂ ≤ c →
    0 ≤ max next (max o₁ o₂) ∧ next ≤ max next (max o₁ o₂) ∧ o₁ ≤ max next (max o₁ o₂) ∧
      o₂ ≤ max next (max o₁ o₂) ∧ max next (max o₁ o₂) ≤ c
  /-- One backward step is order-preserving. Same ledger entry, check
  `one_backward_step_is_order_preserving`. -/
  step_mono : ∀ n₁ n₂ a₁ a₂ b₁ b₂ : ℝ, n₁ ≤ n₂ → a₁ ≤ a₂ → b₁ ≤ b₂ →
    max n₁ (max a₁ b₁) ≤ max n₂ (max a₂ b₂)
  /-- Termwise comparison in the positive finite kernel. Same ledger entry, check
  `positive_kernel_summand_preserves_future_bounds`. -/
  summand_mono : ∀ lo up w : ℝ, 0 ≤ w → lo ≤ up → lo * w ≤ up * w
  /-- Convexity of the three-way maximum. Ledger `fpm_20260921_finite_node_max_convexity_exact`
  (exact, 27 branch certificates). -/
  max_convexity : ∀ x₀ x₁ x₂ y₀ y₁ y₂ a : ℝ, 0 ≤ a → a ≤ 1 →
    max (a * x₀ + (1 - a) * y₀) (max (a * x₁ + (1 - a) * y₁) (a * x₂ + (1 - a) * y₂)) ≤
      a * max x₀ (max x₁ x₂) + (1 - a) * max y₀ (max y₁ y₂)

/-- Finite node data: nodes `0 = v 0 < v 1 < ⋯ < v n = b̄` and node probabilities. -/
structure NodeData (n : ℕ) where
  v : ℕ → ℝ
  p : Fin 2 → ℕ → ℝ
  v_zero : v 0 = 0
  v_strictMonoOn : StrictMonoOn v (Iic n)
  p_nonneg : ∀ i ℓ, 0 ≤ p i ℓ
  p_sum : ∀ i, ∑ ℓ ∈ Finset.range (n + 1), p i ℓ = 1

namespace NodeData

variable {n : ℕ} (D : NodeData n)

/-- The top node `b̄ = v_n`. -/
def bbar : ℝ := D.v n

/-- The buyer body law `Σ_ℓ p_{iℓ} δ_{v_ℓ}`. -/
def law (i : Fin 2) : Measure ℝ :=
  ∑ ℓ ∈ Finset.range (n + 1), ENNReal.ofReal (D.p i ℓ) • Measure.dirac (D.v ℓ)

/-- `L̄_{ij} = L̄_i(v_j)`. -/
def Lnode (i : Fin 2) (j : ℕ) : ℝ := Lbar (D.law i) (D.v j)

/-- The bracket of `eq:two-backward`:
`1 - d v_j / L̄_{ij} + ε_i ϑ_j / L̄_{ij} + Σ_{ℓ > j} (v_ℓ - v_j) p_{iℓ} ϖ_ℓ / L̄_{ij}`. -/
def nodeObstacle (d : ℝ) (ϑ : ℕ → ℝ) (i : Fin 2) (j : ℕ) (w : ℕ → ℝ) : ℝ :=
  1 - d * D.v j / D.Lnode i j + compSign i * ϑ j / D.Lnode i j
    + ∑ ℓ ∈ Finset.Ioc j n, (D.v ℓ - D.v j) * D.p i ℓ / D.Lnode i j * w ℓ

/-- `ϖ_n = max {0, 1 - d b̄ - ϑ_n, 1 - d b̄ + ϑ_n}` (`eq:two-backward`, first line). -/
def terminalMass (d : ℝ) (ϑ : ℕ → ℝ) : ℝ :=
  max 0 (max (1 - d * D.v n - ϑ n) (1 - d * D.v n + ϑ n))

/-- The backward pass: after `k` steps the entries `n - k, …, n` hold their final values. -/
def backwardPass (d : ℝ) (ϑ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => D.terminalMass d ϑ
  | k + 1 =>
    let w := backwardPass d ϑ k
    Function.update w (n - (k + 1))
      (max (w (n - (k + 1) + 1))
        (max (D.nodeObstacle d ϑ 0 (n - (k + 1)) w) (D.nodeObstacle d ϑ 1 (n - (k + 1)) w)))

/-- The node solution `(ϖ_j)_{j ≤ n}` computed backwards by `eq:two-backward`. -/
def nodeMass (d : ℝ) (ϑ : ℕ → ℝ) : ℕ → ℝ := D.backwardPass d ϑ n

/-- The node inequalities: nonnegative, nonincreasing, and above both node obstacles. -/
structure IsNodeSolution (d : ℝ) (ϑ w : ℕ → ℝ) : Prop where
  nonneg : ∀ j ≤ n, 0 ≤ w j
  antitone : ∀ j < n, w (j + 1) ≤ w j
  obstacle_le : ∀ i : Fin 2, ∀ j ≤ n, D.nodeObstacle d ϑ i j w ≤ w j

/-- The step cumulative mass of node values: `ϖ(s) = ϖ_j` for `v_j ≤ s < v_{j+1}`. -/
def stepMass (w : ℕ → ℝ) (s : ℝ) : ℝ := w (Nat.findGreatest (fun j => D.v j ≤ s) n)

/-- The normalized price body `π̂₀` of node masses `w`: an atom `ϖ_{ℓ-1} - ϖ_ℓ` at each node
`v_ℓ`, `1 ≤ ℓ ≤ n` (`app:two-recurrence`, "The price at `v_j` has normalized mass
`ϖ_{j-1} - ϖ_j`"). With the ideal tail mass `ϖ_n` its cumulative mass is
`ϖ(s) = ϖ_n + π̂₀((s, b̄])` (`sec:two-pricing`). -/
def priceBody (w : ℕ → ℝ) : Measure ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 n, ENNReal.ofReal (w (ℓ - 1) - w ℓ) • Measure.dirac (D.v ℓ)

/-- Node compensations `(ϑ_0, …, ϑ_n)` as a function on `ℕ` (zero beyond `n`). -/
def extendNodes (θ : Fin (n + 1) → ℝ) : ℕ → ℝ :=
  fun j => if h : j < n + 1 then θ ⟨j, h⟩ else 0

end NodeData

/-! ### Claims of `app:two-recurrence` -/

namespace NodeData

/-- `eq:two-backward`, first line. -/
abbrev NodeMassLastStatement : Prop :=
  ∀ {n : ℕ} (D : NodeData n) (d : ℝ) (ϑ : ℕ → ℝ),
    D.nodeMass d ϑ n = D.terminalMass d ϑ

/-- `eq:two-backward`, second line. -/
abbrev NodeMassBackwardStatement : Prop :=
  ∀ {n : ℕ} (D : NodeData n) (d : ℝ) (ϑ : ℕ → ℝ) {j : ℕ} (hj : j < n),
    D.nodeMass d ϑ j =
      max (D.nodeMass d ϑ (j + 1))
        (max (D.nodeObstacle d ϑ 0 j (D.nodeMass d ϑ)) (D.nodeObstacle d ϑ 1 j (D.nodeMass d ϑ)))

/-- "For prescribed nondecreasing node compensations, the least solution of the node
inequalities is obtained backwards." -/
abbrev NodeMassIsLeastSolutionStatement : Prop :=
  ∀ {n : ℕ} (cert : NodeScalarCertificates) (D : NodeData n) {d : ℝ}
    (hd : 0 < d) {ϑ : ℕ → ℝ} (hϑ : MonotoneOn ϑ (Iic n)),
    D.IsNodeSolution d ϑ (D.nodeMass d ϑ) ∧
      ∀ w : ℕ → ℝ, D.IsNodeSolution d ϑ w → ∀ j ≤ n, D.nodeMass d ϑ j ≤ w j

/-- "The value is piecewise affine and convex in `(d, ϑ_0, …, ϑ_n)`": it is convex and equals a
maximum of finitely many affine functions of `(d, ϑ_0, …, ϑ_n)`. -/
abbrev NodeValueConvexPiecewiseAffineStatement : Prop :=
  ∀ {n : ℕ} (cert : NodeScalarCertificates) (D : NodeData n),
    ConvexOn ℝ univ (fun x : ℝ × (Fin (n + 1) → ℝ) => D.nodeMass x.1 (extendNodes x.2) 0) ∧
      ∃ (m : ℕ) (A : Fin (m + 1) → ((ℝ × (Fin (n + 1) → ℝ)) →ᵃ[ℝ] ℝ)),
        ∀ x : ℝ × (Fin (n + 1) → ℝ),
          D.nodeMass x.1 (extendNodes x.2) 0 = Finset.univ.sup' Finset.univ_nonempty (fun k => A k x)

/-- Auxiliary to "The price at `v_j` has normalized mass `ϖ_{j-1} - ϖ_j`" (whose direct
rendering is `PriceBodySpecStatement`): the step cumulative mass equals `ϖ_j` on
`[v_j, v_{j+1})` and at `v_j`, so it jumps by `ϖ_{j-1} - ϖ_j` at `v_j`. -/
abbrev StepMassEqOnCellStatement : Prop :=
  ∀ {n : ℕ} (D : NodeData n) (w : ℕ → ℝ) {j : ℕ} (hj : j ≤ n),
    D.stepMass w (D.v j) = w j ∧
      (j < n → ∀ s ∈ Ico (D.v j) (D.v (j + 1)), D.stepMass w s = w j)

/-- "The price at `v_j` has normalized mass `ϖ_{j-1} - ϖ_j`" (`app:two-recurrence`). For
nonnegative nonincreasing node masses `w`, the normalized price body `π̂₀ = priceBody w` has
cumulative mass `ϖ_n + π̂₀((s, b̄]) = ϖ(s)` (the step mass) on `[0, b̄]`, and its atom at `v_j`,
`1 ≤ j ≤ n`, is `ϖ_{j-1} - ϖ_j`. -/
abbrev PriceBodySpecStatement : Prop :=
  ∀ {n : ℕ} (D : NodeData n) {w : ℕ → ℝ} (hw₀ : ∀ j ≤ n, 0 ≤ w j)
    (hwa : ∀ j < n, w (j + 1) ≤ w j),
    (∀ s ∈ Icc 0 D.bbar, w n + (D.priceBody w).real (Ioc s D.bbar) = D.stepMass w s) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ n → D.priceBody w {D.v j} = ENNReal.ofReal (w (j - 1) - w j)

/-- "Between price events, `(ψ_i^ϖ)'(s) = d + H_i(s) - ∫_{(s,b̄]} Pr(Z_i ≥ z) π̂₀(dz)
≥ d - H_i(s)(ϖ_0 - 1) ≥ 0`" (the last inequality at the budget `ϖ_0 ≤ 1 + d`). The price body
`π̂₀` of the step mass has atoms `ϖ_{ℓ-1} - ϖ_ℓ` at `v_ℓ` (`priceBody`). "Between price events"
is rendered as the open cells `(v_j, v_{j+1})` between consecutive nodes: at a node with a buyer
atom and no price atom the potential has a concave kink and the displayed formula is only its
right derivative (gap G7 of `blueprints/theoremE.md`). -/
abbrev SellerPotentialHasDerivAtBetweenNodesStatement : Prop :=
  ∀ {n : ℕ} (D : NodeData n) {d : ℝ} (hd : 0 < d)
    {w : ℕ → ℝ} (hw₀ : ∀ j ≤ n, 0 ≤ w j) (hwa : ∀ j < n, w (j + 1) ≤ w j) (i : Fin 2) {j : ℕ}
    (hj : j < n) {s : ℝ} (hs : s ∈ Ioo (D.v j) (D.v (j + 1))),
    HasDerivAt (sellerPotential D.bbar (D.law i) d (D.stepMass w))
      (d + (D.law i).real (Ioi s) -
        ∑ ℓ ∈ Finset.Ioc j n, (w (ℓ - 1) - w ℓ) * (D.law i).real (Ici (D.v ℓ))) s ∧
    d - (D.law i).real (Ioi s) * (w 0 - 1) ≤
      d + (D.law i).real (Ioi s) -
        ∑ ℓ ∈ Finset.Ioc j n, (w (ℓ - 1) - w ℓ) * (D.law i).real (Ici (D.v ℓ)) ∧
    (w 0 ≤ 1 + d → 0 ≤ d - (D.law i).real (Ioi s) * (w 0 - 1))

/-- "At an event, the potential drops by the price atom's mass times `L̄_i(s)`": the left limit
at `v_j` exceeds the value at `v_j` by `(ϖ_{j-1} - ϖ_j) L̄_i(v_j)`. -/
abbrev SellerPotentialJumpAtNodeStatement : Prop :=
  ∀ {n : ℕ} (D : NodeData n) (d : ℝ) (w : ℕ → ℝ) (i : Fin 2) {j : ℕ}
    (hj₁ : 1 ≤ j) (hj : j ≤ n),
    Tendsto (sellerPotential D.bbar (D.law i) d (D.stepMass w)) (𝓝[<] (D.v j))
      (𝓝 (sellerPotential D.bbar (D.law i) d (D.stepMass w) (D.v j) +
        (w (j - 1) - w j) * Lbar (D.law i) (D.v j)))

/-- "Its minimum on each interval is therefore its right trace at the preceding event, and
ordered node constraints cover all ordered real seller values" (at the budget `ϖ_0 ≤ 1 + d`).
Stated for every node solution, which includes the backward solution, and for all ordered real
seller values `0 ≤ s₁ ≤ s₂` (beyond `b̄ = v_n` the potential is the ideal-tail potential
`d s - 1 + ϖ_n`, which is nondecreasing). -/
abbrev NodeSolutionOrderedSumNonnegStatement : Prop :=
  ∀ {n : ℕ} (cert : PricingScalarCertificates)
    (ncert : NodeScalarCertificates) (D : NodeData n) {d : ℝ} (hd : 0 < d) {ϑ : ℕ → ℝ}
    (hϑ : MonotoneOn ϑ (Iic n)) {w : ℕ → ℝ} (hw : D.IsNodeSolution d ϑ w)
    (hbudget : w 0 ≤ 1 + d),
    ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ →
      0 ≤ sellerPotential D.bbar (D.law 0) d (D.stepMass w) s₁ +
        sellerPotential D.bbar (D.law 1) d (D.stepMass w) s₂

end NodeData

end FixedPrice.TwoUnit.Pricing
