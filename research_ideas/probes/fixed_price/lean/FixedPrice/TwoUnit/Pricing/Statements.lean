import FixedPrice.TwoUnit.Pricing.Defs

/-!
# Theorem E (two units): statements

Every statement of `two_units.tex` `sec:two-pricing` and of the proof in
`two_unit_pricing_proofs.tex` `app:two-pricing` that the Lean development renders is one
`Prop` abbreviation `<Name>Statement` here: a definition, with no proof obligation of its own.
Nothing in this file is proved. Each package proves the statements it owns in its own file, as
`theorem <name>_proof : <Name>Statement`, so a proof can never drift from the statement fixed
here, and the only unproved declarations of the library are package exports not yet done (see
`blueprints/theoremE.md`, "Work packages").

Owners: `[A]` operator package, `[B]` price package, `[C]` convexity/attainment package,
`[D]` rounding package. The finite-node recurrence (secondary target) is in `FiniteNodes.lean`.

Standing hypotheses. `cert : PricingScalarCertificates` carries the scalar facts that the ledger
already certifies by machine (exact / z3 / cvc5); it is not a weakening, since each field is a
closed, true arithmetic statement, and by the user's rule it is not re-proved in Lean.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal

/- The statements are `Prop` abbreviations whose hypothesis binders keep the names of the
original signatures (for readability and for `intro` in the package proofs). A `∀`-bound
hypothesis is never referenced inside the proposition itself, so the unused-variables linter
would flag every one of them; it is switched off for this file only. -/
set_option linter.unusedVariables false

namespace FixedPrice.TwoUnit.Pricing

/-! ## Claims in the text of `sec:two-pricing` and in the proof of Theorem E -/

section TextClaims

/-- [A] "Thus `s + L̄_i(s) = 1 + E max {Z_i, s}` is normalized efficient welfare."
(`two_units.tex`, after `eq:two-kernel`.) -/
abbrev SelfAddLbarStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Icc 0 bbar)ᶜ = 0) (s : ℝ),
    s + Lbar μ s = 1 + ∫ x, max x s ∂μ

/-- [B] "Its cumulative mass `ϖ(s) = ϖ(b̄) + π̂₀((s, b̄])` is nonnegative, nonincreasing, and
right-continuous." (`two_units.tex`, `sec:two-pricing`.) -/
abbrev IsCumulativeMassOfPriceStatement : Prop :=
  ∀ {bbar : ℝ} (π₀ : Measure ℝ) [IsFiniteMeasure π₀]
    (hπ₀ : π₀ (Ioc 0 bbar)ᶜ = 0) {tail : ℝ} (htail : 0 ≤ tail),
    IsCumulativeMass bbar (fun s => tail + π₀.real (Ioc s bbar))

/-- [B] Gain representation (`sec:two-pricing`: "A nonnegative price measure `π` gives
conditional gain `∫ g_i(s,z) π(dz)`", the ideal tail "contributes one unit of gain per unit of
mass", and the proof's "Integration gives `eq:two-potential`"). The cumulative mass of a finite
price measure `π` is `t ↦ π((t, ∞))`; prices above `b̄` act as ideal tail mass. -/
abbrev IntegralGainKernelEqGainFromMassStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Icc 0 bbar)ᶜ = 0) (π : Measure ℝ) [IsFiniteMeasure π] {s : ℝ} (hs : 0 ≤ s),
    ∫ z, gainKernel μ s z ∂π = gainFromMass bbar μ (fun t => π.real (Ioi t)) s

/-- [C] "If `ψ₁^ϖ ≥ -ϑ` and `ψ₂^ϖ ≥ ϑ`, then `ψ₁^ϖ(s₁) + ψ₂^ϖ(s₂) ≥ ϑ(s₂) - ϑ(s₁) ≥ 0` whenever
`s₁ ≤ s₂`, because `ϑ` is nondecreasing." (`sec:two-pricing`.) -/
abbrev OrderedSumGeOfCompensationStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) {bbar : ℝ}
    {law : Fin 2 → Measure ℝ} {d : ℝ} {ϑ ϖ : ℝ → ℝ} (hϑ : MonotoneOn ϑ (Icc 0 bbar))
    (hψ : ∀ i : Fin 2, ∀ s ∈ Icc 0 bbar, compSign i * ϑ s ≤ sellerPotential bbar (law i) d ϖ s),
    ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ bbar →
      ϑ s₂ - ϑ s₁ ≤ sellerPotential bbar (law 0) d ϖ s₁ + sellerPotential bbar (law 1) d ϖ s₂ ∧
        0 ≤ ϑ s₂ - ϑ s₁

/-- [C] "Conversely, a nonnegative potential sum permits the canonical compensation
`Θ_ϖ(s) = -inf_{t ≤ s} ψ₁^ϖ(t)`" (`sec:two-pricing`), with the proof's "the canonical prefix
satisfies both constraints. It is bounded and right-continuous because the potentials are
bounded and right-continuous." -/
abbrev CanonicalCompensationSpecStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) {bbar : ℝ}
    {law : Fin 2 → Measure ℝ} (hB : IsBuyerBodies bbar law) {d : ℝ} (hd : 0 < d)
    {ϖ : ℝ → ℝ} (hϖ : IsCumulativeMass bbar ϖ)
    (hsum : ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ bbar →
      0 ≤ sellerPotential bbar (law 0) d ϖ s₁ + sellerPotential bbar (law 1) d ϖ s₂),
    canonicalCompensation bbar law d ϖ ∈ compensationClass bbar ∧
      IsFeasibleMass bbar law d (canonicalCompensation bbar law d ϖ) ϖ

/-- [A] "For nonnegative nonincreasing `ϖ`, the potential constraints are equivalent to
`ϖ ≥ 𝒯_{d,ϑ} ϖ`." (`app:two-pricing`, first paragraph.) -/
abbrev PotentialGeIffOperatorLeStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) {bbar : ℝ}
    {law : Fin 2 → Measure ℝ} (hB : IsBuyerBodies bbar law) {d : ℝ} (hd : 0 < d)
    {ϑ : ℝ → ℝ} (hϑ : ϑ ∈ compensationClass bbar) {ϖ : ℝ → ℝ}
    (hϖ₀ : ∀ s ∈ Icc 0 bbar, 0 ≤ ϖ s) (hϖ : AntitoneOn ϖ (Icc 0 bbar)),
    (∀ i : Fin 2, ∀ s ∈ Icc 0 bbar, compSign i * ϑ s ≤ sellerPotential bbar (law i) d ϖ s) ↔
      ∀ s ∈ Icc 0 bbar, pricingOperator bbar law d ϑ ϖ s ≤ ϖ s

end TextClaims

/-! ## Interface lemmas (cross-package) -/

section Interfaces

/-- [A] `L̄ ≥ 1`. -/
abbrev OneLeLbarStatement : Prop :=
  ∀ (μ : Measure ℝ) (s : ℝ), 1 ≤ Lbar μ s

/-- [A] `L̄(s) ≤ 1 + b̄` for sellers `s ≥ 0`. -/
abbrev LbarLeOneAddStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0) {s : ℝ}
    (hs : 0 ≤ s), Lbar μ s ≤ 1 + bbar

/-- [A] `L̄(s) = 1` above the bodies. -/
abbrev LbarEqOneOfLeStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0) {s : ℝ}
    (hs : bbar ≤ s), Lbar μ s = 1

/-- [A] `L̄` is `1`-Lipschitz. -/
abbrev LbarLipschitzStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0),
    LipschitzWith 1 (Lbar μ)

/-- [A] Kernel mass: `∫_{(s,b̄]} (t - s) c (-dH)(t) = c (L̄(s) - 1)`; with `c = 1` this is the
proof's "A unit of ideal tail mass contributes `L̄_i(s) - ∫_{(s,b̄]} (t-s)(-dH_i(t)) = 1`". -/
abbrev KernelIntegralConstStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0)
    (c s : ℝ), kernelIntegral bbar μ (fun _ => c) s = c * (Lbar μ s - 1)

/-- [A] The positive kernel is order-preserving on nonincreasing masses. -/
abbrev KernelIntegralMonoStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0)
    {ϖ ϖ' : ℝ → ℝ} (hϖ : AntitoneOn ϖ (Icc 0 bbar)) (hϖ' : AntitoneOn ϖ' (Icc 0 bbar))
    {s : ℝ} (hs : 0 ≤ s) (hle : ∀ t ∈ Ioc s bbar, ϖ t ≤ ϖ' t),
    kernelIntegral bbar μ ϖ s ≤ kernelIntegral bbar μ ϖ' s

/-- [A] "The integral terms are continuous in `t`" (for nonincreasing masses). -/
abbrev KernelIntegralContinuousOnStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0)
    {ϖ : ℝ → ℝ} (hϖ : AntitoneOn ϖ (Icc 0 bbar)),
    ContinuousOn (kernelIntegral bbar μ ϖ) (Icc 0 bbar)

/-- [A] The gain written as `ϖ(s) + E[(Z - s)_+ (ϖ(s) - ϖ(Z))]`. -/
abbrev GainFromMassEqStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0)
    {ϖ : ℝ → ℝ} (hϖ : AntitoneOn ϖ (Icc 0 bbar)) {s : ℝ} (hs : s ∈ Icc 0 bbar),
    gainFromMass bbar μ ϖ s = ϖ s + ∫ t in Ioc s bbar, (t - s) * (ϖ s - ϖ t) ∂μ

/-- [A] The potential is affine in `(d, ϖ)` (proof of (ii): "The potential inequalities are
affine in `(ϖ, d, ϑ)`"). -/
abbrev SellerPotentialConvexCombStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0)
    {ϖ₁ ϖ₂ : ℝ → ℝ} (hϖ₁ : AntitoneOn ϖ₁ (Icc 0 bbar)) (hϖ₂ : AntitoneOn ϖ₂ (Icc 0 bbar))
    {a d₁ d₂ s : ℝ} (hs : s ∈ Icc 0 bbar),
    sellerPotential bbar μ (a * d₁ + (1 - a) * d₂) (fun t => a * ϖ₁ t + (1 - a) * ϖ₂ t) s =
      a * sellerPotential bbar μ d₁ ϖ₁ s + (1 - a) * sellerPotential bbar μ d₂ ϖ₂ s

/-- [A] Adding ideal tail mass `c` adds `c` to every potential (proof of (iv)). -/
abbrev SellerPotentialAddConstStatement : Prop :=
  ∀ {bbar : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hsupp : μ (Icc 0 bbar)ᶜ = 0)
    {ϖ : ℝ → ℝ} (hϖ : AntitoneOn ϖ (Icc 0 bbar)) (d c : ℝ) {s : ℝ} (hs : 0 ≤ s),
    sellerPotential bbar μ d (fun t => ϖ t + c) s = sellerPotential bbar μ d ϖ s + c

/-- [A] `ϖ_{d,ϑ}` is a feasible cumulative mass. -/
abbrev LeastMassIsFeasibleStatement : Prop :=
  ∀ {bbar : ℝ} (cert : PricingScalarCertificates) {law : Fin 2 → Measure ℝ}
    (hB : IsBuyerBodies bbar law) {d : ℝ} (hd : 0 < d) {ϑ : ℝ → ℝ}
    (hϑ : ϑ ∈ compensationClass bbar),
    IsFeasibleMass bbar law d ϑ (leastMass bbar law d ϑ)

/-- [A] `ϖ_{d,ϑ}` lies below every feasible cumulative mass. -/
abbrev LeastMassLeOfIsFeasibleStatement : Prop :=
  ∀ {bbar : ℝ} (cert : PricingScalarCertificates)
    {law : Fin 2 → Measure ℝ} (hB : IsBuyerBodies bbar law) {d : ℝ} (hd : 0 < d)
    {ϑ : ℝ → ℝ} (hϑ : ϑ ∈ compensationClass bbar) {ϖ : ℝ → ℝ}
    (hϖ : IsFeasibleMass bbar law d ϑ ϖ),
    ∀ s ∈ Icc 0 bbar, leastMass bbar law d ϑ s ≤ ϖ s

/-- [C] The minimum in `eq:two-functional` exists and equals `pricingValue`. -/
abbrev PricingValueIsLeastStatement : Prop :=
  ∀ {bbar : ℝ} (cert : PricingScalarCertificates) {law : Fin 2 → Measure ℝ}
    (hB : IsBuyerBodies bbar law) {d : ℝ} (hd : 0 < d),
    IsLeast ((fun ϑ => leastMass bbar law d ϑ 0) '' compensationClass bbar)
      (pricingValue bbar law d)

end Interfaces

/-! ## Theorem E (`two_units.tex`, `thm:two-pricing`) -/

/-- [A] **Theorem E (i).** For each `ϑ ∈ 𝒱`, the operator `𝒯_{d,ϑ}` has a unique bounded fixed
point `ϖ_{d,ϑ}`, the pointwise least feasible cumulative mass. Iteration from zero converges
uniformly with contraction factor `b̄/(1+b̄)`.

Rendering: bounded fixed point on `[0,b̄]`; uniqueness among all bounded fixed points; feasible
and least among feasible cumulative masses; the `b̄/(1+b̄)`-contraction on bounded Borel
functions (the space of `eq:two-operator`); uniform convergence of the iterates from zero with
the rate `(b̄/(1+b̄))^n ϖ_{d,ϑ}(0)`. -/
abbrev TheoremEPartIStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) (P : OrderedBuyerPair) {d : ℝ}
    (hd : 0 < d) {ϑ : ℝ → ℝ} (hϑ : ϑ ∈ compensationClass P.bbar),
    IsBoundedOn P.bbar (leastMass P.bbar P.law d ϑ) ∧
    (∀ s ∈ Icc 0 P.bbar,
      pricingOperator P.bbar P.law d ϑ (leastMass P.bbar P.law d ϑ) s =
        leastMass P.bbar P.law d ϑ s) ∧
    (∀ ϖ : ℝ → ℝ, IsBoundedOn P.bbar ϖ →
      (∀ s ∈ Icc 0 P.bbar, pricingOperator P.bbar P.law d ϑ ϖ s = ϖ s) →
      ∀ s ∈ Icc 0 P.bbar, ϖ s = leastMass P.bbar P.law d ϑ s) ∧
    IsFeasibleMass P.bbar P.law d ϑ (leastMass P.bbar P.law d ϑ) ∧
    (∀ ϖ : ℝ → ℝ, IsFeasibleMass P.bbar P.law d ϑ ϖ →
      ∀ s ∈ Icc 0 P.bbar, leastMass P.bbar P.law d ϑ s ≤ ϖ s) ∧
    (∀ ϖ₁ ϖ₂ : ℝ → ℝ, Measurable ϖ₁ → Measurable ϖ₂ →
      IsBoundedOn P.bbar ϖ₁ → IsBoundedOn P.bbar ϖ₂ →
      ∀ E : ℝ, (∀ t ∈ Icc 0 P.bbar, |ϖ₁ t - ϖ₂ t| ≤ E) →
      ∀ s ∈ Icc 0 P.bbar,
        |pricingOperator P.bbar P.law d ϑ ϖ₁ s - pricingOperator P.bbar P.law d ϑ ϖ₂ s| ≤
          P.bbar / (1 + P.bbar) * E) ∧
    TendstoUniformlyOn (fun n : ℕ => (pricingOperator P.bbar P.law d ϑ)^[n] 0)
      (leastMass P.bbar P.law d ϑ) atTop (Icc 0 P.bbar) ∧
    (∀ n : ℕ, ∀ s ∈ Icc 0 P.bbar,
      |(pricingOperator P.bbar P.law d ϑ)^[n] 0 s - leastMass P.bbar P.law d ϑ s| ≤
        (P.bbar / (1 + P.bbar)) ^ n * leastMass P.bbar P.law d ϑ 0)

/-- [C] **Theorem E (ii).** The value `ϖ_{d,ϑ}(0)` is jointly convex in `(d, ϑ)`, and the
minimum `𝒥_d^{(2)}(H₁,H₂) = min_{ϑ ∈ 𝒱} ϖ_{d,ϑ}(0)` is attained. -/
abbrev TheoremEPartIIStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) (P : OrderedBuyerPair),
    ConvexOn ℝ {p : ℝ × (ℝ → ℝ) | 0 < p.1 ∧ p.2 ∈ compensationClass P.bbar}
      (fun p => leastMass P.bbar P.law p.1 p.2 0) ∧
    ∀ d : ℝ, 0 < d →
      IsLeast ((fun ϑ => leastMass P.bbar P.law d ϑ 0) '' compensationClass P.bbar)
        (P.value d)

/-- [B] **Theorem E (iii), first sentence.** For `0 < β < 1` there is a price probability with
bounded support satisfying `eq:two-price-target` if and only if `β 𝒥_d^{(2)}(H₁,H₂) ≤ 1`. -/
abbrev TheoremEPartIIIStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) (P : OrderedBuyerPair) {d β : ℝ}
    (hd : 0 < d) (hβ₀ : 0 < β) (hβ₁ : β < 1),
    (∃ π : Measure ℝ, IsBoundedPriceLaw π ∧ PriceTarget P.law d β π) ↔ β * P.value d ≤ 1

/-- [B] **Theorem E (iii), second sentence.** At `d = (1-β)/β`, a price satisfying
`eq:two-price-target` is a welfare guarantee of `β` against every ordered seller distribution
in the normalized model (`eq:two-body`): bounded seller bodies `0 ≤ Y₁ ≤ Y₂`, drawn
independently of the buyer bodies. -/
abbrev TheoremEPartIIIWelfareStatement : Prop :=
  ∀ (P : OrderedBuyerPair) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    {π : Measure ℝ} (hπ : IsBoundedPriceLaw π) (htarget : PriceTarget P.law ((1 - β) / β) β π)
    (ν : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ y ∂ν, 0 ≤ y 0 ∧ y 0 ≤ y 1) (hνb : ∃ C : ℝ, ∀ᵐ y ∂ν, y 1 ≤ C),
    β * normalizedEfficientWelfare P.law ν ≤ ∫ z, normalizedWelfare P.law ν z ∂π

/-- [B] **Theorem E (iii), the realized price.** `two_units.tex`, after `thm:two-pricing`: "The
tail is realized by density `βd` on `(b̄, b̄ + ϖ_{d,ϑ}(b̄)/d)`, an empty interval when the tail
mass is zero", together with the construction in the proof of (iii)
(`two_unit_pricing_proofs.tex`, "A bounded price interval and the reverse implication": "We
choose an optimal compensation and write `ϖ = ϖ_{d,ϑ}`. We put `-β dϖ` on `(0, b̄]` and density
`βd` on `(b̄, b̄ + ϖ(b̄)/d)`. Its mass is `βϖ(0) ≤ 1`, and the remainder is put at zero.").

For an optimal `ϑ ∈ 𝒱` and `β 𝒥 ≤ 1`, the price `realizedPrice` built from `ϖ_{d,ϑ}` is a price
probability with bounded support satisfying `eq:two-price-target`; its mass above each
`t ∈ [0, b̄]` is `βϖ_{d,ϑ}(t)` (body `-βdϖ` plus the realized tail, which contributes
`βϖ(b̄)` exactly as the ideal tail does); and above `b̄` it is exactly the density `βd` on
`(b̄, b̄ + ϖ_{d,ϑ}(b̄)/d)`. -/
abbrev RealizedPriceSpecStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) (P : OrderedBuyerPair) {d β : ℝ}
    (hd : 0 < d) (hβ₀ : 0 < β) (hβ₁ : β < 1) {ϑ : ℝ → ℝ} (hϑ : ϑ ∈ compensationClass P.bbar)
    (hopt : leastMass P.bbar P.law d ϑ 0 = P.value d) (hβJ : β * P.value d ≤ 1),
    IsBoundedPriceLaw (realizedPrice P.bbar d β (leastMass P.bbar P.law d ϑ)) ∧
    PriceTarget P.law d β (realizedPrice P.bbar d β (leastMass P.bbar P.law d ϑ)) ∧
    (∀ t ∈ Icc 0 P.bbar,
      (realizedPrice P.bbar d β (leastMass P.bbar P.law d ϑ)).real (Ioi t) =
        β * leastMass P.bbar P.law d ϑ t) ∧
    (realizedPrice P.bbar d β (leastMass P.bbar P.law d ϑ)).restrict (Ioi P.bbar) =
      ENNReal.ofReal (β * d) •
        (volume : Measure ℝ).restrict
          (Ioo P.bbar (P.bbar + leastMass P.bbar P.law d ϑ P.bbar / d))

/-- [D] **Theorem E (iv), inequality.** With `H_i^δ` the survival function of `δ ⌊Z_i / δ⌋`,
`𝒥_d^{(2)}(H₁,H₂) ≤ 𝒥_d^{(2)}(H₁^δ,H₂^δ) + δ`. Both values are computed on the pair's interval
`[0, b̄]`, which also contains the rounded bodies (see `PricingValueEqOfBoundLeStatement`). -/
abbrev TheoremEPartIVStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) (P : OrderedBuyerPair) {d δ : ℝ}
    (hd : 0 < d) (hδ : 0 < δ),
    P.value d ≤ pricingValue P.bbar (roundedLaw δ P.law) d + δ

/-- [D] **Theorem E (iv), last sentence.** The supremum of `𝒥_d^{(2)}` over bounded ordered
buyer bodies equals the supremum over finite-support ordered buyer bodies (suprema in
`[0, ∞]`). -/
abbrev TheoremEPartIVSupStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) {d : ℝ} (hd : 0 < d),
    ⨆ P : OrderedBuyerPair, ENNReal.ofReal (P.value d) =
      ⨆ P : {P : OrderedBuyerPair // P.HasFiniteSupport}, ENNReal.ofReal (P.1.value d)

/-- [D] The rounded bodies `δ ⌊Z_i / δ⌋` form an ordered pair on the same interval, with finite
support (used by the last sentence of (iv)). -/
abbrev RoundedLawSpecStatement : Prop :=
  ∀ (P : OrderedBuyerPair) {δ : ℝ} (hδ : 0 < δ),
    IsBuyerBodies P.bbar (roundedLaw δ P.law) ∧
    (∀ s : ℝ, roundedLaw δ P.law 1 (Ioi s) ≤ roundedLaw δ P.law 0 (Ioi s)) ∧
    ∃ S : Finset ℝ, ∀ i, roundedLaw δ P.law i (↑S)ᶜ = 0

/-- [D] The notation `𝒥_d^{(2)}(H₁,H₂)` does not depend on the interval `[0, b̄]` chosen to
contain the bodies (implicit in `eq:two-functional`, `eq:two-open-budget`, and in the proof of
(iv): "its compensation extends constantly to the common endpoint"). -/
abbrev PricingValueEqOfBoundLeStatement : Prop :=
  ∀ (cert : PricingScalarCertificates) {b b' : ℝ}
    {law : Fin 2 → Measure ℝ} (hB : IsBuyerBodies b law) (hbb' : b ≤ b') {d : ℝ} (hd : 0 < d),
    pricingValue b' law d = pricingValue b law d

end FixedPrice.TwoUnit.Pricing
