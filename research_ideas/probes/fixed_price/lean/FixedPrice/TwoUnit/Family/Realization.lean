import FixedPrice.TwoUnit.Family.Statements
import FixedPrice.TwoUnit.Family.RealizationLimits

/-!
# Work package E, part 1: realization by limiting instances (export theorem)

Owned by work package E. The theorem proves `RealizationEscapingStatement` (the construction in
the proof of `lem:2fam-realization`) and keeps exactly the signature below. Blueprint:
`lean/blueprints/family.md`, section 3.5.

Construction (helper files `Realization*.lean`, namespace `Realize`). The body laws are images of
the uniform law under the monotone quantile maps (`RealizationQuantile`); the right derivative
`P'_+` of a class member is antitone and right-continuous, so the two curve distribution functions
are nondecreasing and right-continuous and the quantiles are their Galois adjoints
(`RealizationDeriv`). The `n`-th instance (`RealizationInstance`) gives both buyer bodies weight
`1 - η_n`, shifts them up by `η_n`, adds a common buyer atom of mass `η_n = 1/x_n` at
`x_n = b_f + 3 + n`, and shifts both sellers up by `2η_n`. Its laws converge weakly to the body
laws. Expectations of the body variables follow from `(s_f(η₁) - s_f(η₂))₊ = ∫ 1{η₂ ≤ r < η₁} P⁻²`,
Tonelli and the fundamental theorem of calculus (`RealizationIntegrals`): `E(Y₁ + Y₂) = M_f`,
`E(Z₁ - Y₁)₊ + E(Z₂ - Y₂)₊ = G_f - 2` (`RealizationPhi`). Every price gain is at most the
right-limit gain `Φ(w) ≤ 2` at `w = z - 2η_n` (certified `low_price_balance` on `[0, a_f)` and
`first_unit_equalizer` on the body), and the price `x_n` gains `2 - η_n(M_f + 4η_n)`
(`RealizationLimits`).
-/

namespace FixedPrice.TwoUnit.Family

/-- `RealizationEscapingStatement`. -/
theorem realization_escaping_proof (hI : FamilyIdentities) (hCB : ClassBasicsStatement) :
    RealizationEscapingStatement := by
  intro θ P hP
  exact ⟨Realize.inst θ P, Realize.inst_valid hI hP, Realize.inst_escaping hP,
    Realize.inst_laws hI hP, Realize.tendsto_sellerWelfare hI hP,
    Realize.tendsto_efficientGains hI hP, Realize.tendsto_bestGain hI hP,
    Realize.tendsto_bestRatio hI hP⟩

end FixedPrice.TwoUnit.Family
