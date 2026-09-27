import FixedPrice.TwoUnit.Family.Certificates
import FixedPrice.TwoUnit.Family.GeneralModel

/-!
# Proposition `prop:2fam-optimum` and its lemmas: statements

Formalize mode. Every TeX statement of the family appendix, and every interface step that several
work packages share, is a `Prop`-valued definition `…Statement`. This file contains no `sorry`.
The only theorems here are projections between statements (`coverMonotonicity_of_domain`,
`lem_2fam_realization_of`, `lem_2fam_cover_of`, `lem_2fam_witness_of`).

Each statement is proved by one work package, as `theorem <name>_proof … : <Name>Statement` in a
file the package owns (currently a `sorry` stub):

* A: `Basic.lean` (`class_basics_proof`, `positivity_proof`, `comparison_proof`,
  `globalMax_energyMinimizer_proof`) and `Compactness.lean` (`seq_compact_proof`,
  `small_mass_mono_proof`, `lem_2fam_compact_proof`, `ratio_attained_proof`);
* B: `Shape.lean` (`lem_2fam_shape_proof`);
* C: `Boundary.lean` (`endpoint_slopes_proof`, `affine_functionals_proof`,
  `lem_2fam_boundary_proof`);
* D: `Stationary.lean` (`quadratures_proof`, `stationary_reduction_proof`,
  `connI_eq_connJ_proof`, `phys_to_coverRoot_proof`, `cover_atMostOne_proof`), `Domain.lean`
  (`lem_2fam_domain_proof`), `Reconstruction.lean` (`reconstruction_proof`) and `Witness.lean`
  (`polygon_curve_proof`);
* E: `Realization.lean` (`realization_escaping_proof`) and `OfFinite.lean` (`ofFinite_spec_proof`);
* F: `Assembly.lean` (`prop_2fam_optimum_of_proof`, `self_consistency_of_proof`).

Dependencies are injected: an export theorem takes the statements it relies on as hypotheses, so
each package proves its theorems without calling another package's `sorry`. `Final.lean` chains
the export theorems into the end-to-end results.

TeX sources: `manuscript/two_units.tex` (`prop:2fam-optimum`) and
`manuscript/two_unit_family.tex` (`lem:2fam-realization`, `lem:2fam-compact`, `lem:2fam-shape`,
`lem:2fam-boundary`, `lem:2fam-domain`, `lem:2fam-cover`, `lem:2fam-witness`, the proof of the
proposition). Blueprint: `lean/blueprints/family.md`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal
open FixedPrice.TwoUnit (GenInstance HasCommonEscapingAtom LawsConvergeTo ofFinite)

namespace FixedPrice.TwoUnit.Family

/-! ## Statements of the TeX lemmas -/

/-- `lem:2fam-realization`. Every member of `𝔉` is the limit of strictly positive, finite-mean,
ordered two-unit instances with independent buyer and seller vectors: their buyer and seller laws
converge weakly to the body laws of the curve (`buyerBodyLaw`, `sellerBodyLaw`, built from
`(eq:2fam-physical-time)` and `(eq:2fam-laws)` as described before the lemma), their seller welfare,
efficient gains and best price gains converge to `M_f`, `G_f` and `2`, and their optimal
common-price welfare ratios converge to `R_f`. -/
def RealizationStatement : Prop :=
  ∀ (θ : Params) (P : ℝ → ℝ), InClass θ P →
    ∃ I : ℕ → GenInstance, (∀ n, (I n).Valid) ∧
      LawsConvergeTo I (buyerBodyLaw θ P) (sellerBodyLaw θ P) ∧
      Tendsto (fun n => (I n).sellerWelfare) atTop (𝓝 (Mf θ P)) ∧
      Tendsto (fun n => (I n).efficientGains) atTop (𝓝 (Gf θ P)) ∧
      Tendsto (fun n => (I n).bestGain) atTop (𝓝 2) ∧
      Tendsto (fun n => (I n).bestRatio) atTop (𝓝 (Rf θ P))

/-- `lem:2fam-compact`. For `0 < β ≤ 3/4`: every curve with `R_f < β` has `1/32 < m_f < 3/4`,
`ξ₀ < 600` and `p_f < 1`; if `K_f` takes a positive value, its positive supremum is attained in
this parameter region. -/
def CompactStatement : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 3 / 4 →
    (∀ (θ : Params) (P : ℝ → ℝ), InClass θ P → Rf θ P < β →
      1 / 32 < θ.m ∧ θ.m < 3 / 4 ∧ θ.ξ₀ < 600 ∧ θ.p < 1) ∧
    ((∃ (θ : Params) (P : ℝ → ℝ), InClass θ P ∧ 0 < Kf β θ P) →
      ∃ (θ : Params) (P : ℝ → ℝ), IsGlobalMaxK β θ P ∧ 0 < Kf β θ P ∧
        1 / 32 < θ.m ∧ θ.m < 3 / 4 ∧ θ.ξ₀ < 600 ∧ θ.p < 1)

/-- `lem:2fam-shape`. At every fixed feasible parameter triple (the class is nonempty) and trial
ratio, `E_f` has a unique minimizer in `(eq:2fam-class)`; it is entirely affine or consists of an
initial affine contact, one strictly concave free interval with `(eq:2fam-euler)` for a constant
`C_f > 0`, and a final affine contact (either contact of possibly zero length); if `c_f = 0`,
every non-affine minimizer has a positive initial contact. -/
def ShapeStatement : Prop :=
  ∀ (β : ℝ) (θ : Params), 0 < β → β < 1 → (∃ P, InClass θ P) →
    (∃ P, IsEnergyMinimizer β θ P) ∧
    (∀ P Q, IsEnergyMinimizer β θ P → IsEnergyMinimizer β θ Q → EqOn P Q (Icc θ.c θ.ξ₀)) ∧
    (∀ P, IsEnergyMinimizer β θ P →
      EntirelyAffine θ P ∨ ∃ ξl ξr C, ThreeArc (dOf β) θ P ξl ξr C) ∧
    (θ.c = 0 → ∀ P, IsEnergyMinimizer β θ P → ¬ EntirelyAffine θ P →
      ∀ ξl ξr C, ThreeArc (dOf β) θ P ξl ξr C → 0 < ξl)

/-- `lem:2fam-boundary`. For `β_f ∈ [18227/25000, 729081/10⁶]`, at a positive global maximum of
`K_f`, or at a global minimum of `R_f` of value `β_f`: `t_f < p_f < 1`, the curve is three-arc
with both affine contacts of positive length, and the derivatives of `K_f` in `(t_f, p_f, h_f)`
vanish, i.e. the three expressions of `(eq:2fam-stationarity)` are zero at the contact data
`P_ℓ = ξ_ℓ + δ_f`, `P_r = h_f ξ_r + e_f`. -/
def BoundaryStatement : Prop :=
  ∀ β ∈ Icc βlo βhi, ∀ (θ : Params) (P : ℝ → ℝ),
    ((IsGlobalMaxK β θ P ∧ 0 < Kf β θ P) ∨ (IsGlobalMinR θ P ∧ Rf θ P = β)) →
    θ.t < θ.p ∧ θ.p < 1 ∧
      ∃ ξl ξr C, ThreeArc (dOf β) θ P ξl ξr C ∧ θ.c < ξl ∧ ξr < θ.ξ₀ ∧
        statP (dOf β) θ (θ.line₁ ξl) = 0 ∧ statH (dOf β) θ (θ.line₂ ξr) = 0 ∧
        statT (dOf β) θ (θ.line₁ ξl) (θ.line₂ ξr) = 0

/-- `lem:2fam-domain`. For `37/100 ≤ d_f ≤ 3/8` every physical stationary point has
`1/5 < t_f < 421/1000`; on the algebraic branch (`0 < t_f < p_f < 1`) `∂_{p_f} 𝒜_f > 0`.

The second conjunct is stated for every `d_f > 0`. If the lemma's hypothesis
`37/100 ≤ d_f ≤ 3/8` is read as scoping the second sentence too, this is a documented
strengthening: the TeX proof of the sign does not use the range of `d_f`, and the certificate's
monotonicity premises only ask `λ > 0`. The covers use it on `d ∈ [270919/729081, 6773/18227]`
(`CoverMonotonicity`, `coverMonotonicity_of_domain`). A Lean target (work package D,
`Domain.lean`): the machine-checked inputs are the `branch_*` identities of `FamilyIdentities`
and `FamilyNumerics.branch_positive_constants`. -/
def DomainStatement : Prop :=
  (∀ d, 37 / 100 ≤ d → d ≤ 3 / 8 → ∀ t p : ℝ, PhysStationary d t p →
      1 / 5 < t ∧ t < 421 / 1000) ∧
  (∀ d, 0 < d → ∀ t p : ℝ, 0 < t → t < p → p < 1 →
      0 < deriv (fun p' => Elim.algResidual d t p') p)

/-- `lem:2fam-cover`. For every `β_f ∈ [18227/25000, 729081/10⁶]` the system
`(eq:2fam-algebraic)`–`(eq:2fam-connection)` has exactly one physical stationary point; at
`β_f = 18227/25000` its curve has `β_f G_f - (1-β_f) M_f - 2 < 0`. -/
def CoverStatement : Prop :=
  (∀ β ∈ Icc βlo βhi, ∃! tp : ℝ × ℝ, PhysStationary (dOf β) tp.1 tp.2) ∧
  (∀ t p : ℝ, PhysStationary (dOf βlo) t p → ∀ P : ℝ → ℝ,
    InClass (Elim.params (dOf βlo) t p) P →
    ThreeArc (dOf βlo) (Elim.params (dOf βlo) t p) P
      (Elim.ξl (dOf βlo) t p) (Elim.ξr (dOf βlo) t p) (Elim.C (dOf βlo) t p) →
    βlo * Gf (Elim.params (dOf βlo) t p) P - (1 - βlo) * Mf (Elim.params (dOf βlo) t p) P - 2
      < 0)

/-- `lem:2fam-witness`. The class `𝔉` contains a rational concave polygon (a concave polygon with
rational vertices, at rational parameters) with `R_f < 729081/10⁶`. -/
def WitnessStatement : Prop :=
  ∃ (θ : Params) (P : ℝ → ℝ), θ.IsRational ∧ InClass θ P ∧
    IsRationalConcavePolygon P θ.c θ.ξ₀ ∧ Rf θ P < βhi

/-- `prop:2fam-optimum`. `r_fam = inf_𝔉 R_f` is attained at a unique curve and parameter triple;
the curve is a positive initial affine contact, one strictly concave interval with
`P'' + C_f P/ξ² = 0` for a constant `C_f > 0`, and a positive final affine contact; the infimum
over the subclass with endpoint slopes `1, h_f` is the same; `18227/25000 < r_fam < 729081/10⁶`;
and the minimizing body laws are approached by strictly positive finite-mean ordered instances
with a common escaping buyer atom (their laws converge weakly to the body laws of the minimizer,
with the scalar limits of `lem:2fam-realization`). -/
def OptimumStatement : Prop :=
  (∃ (θ : Params) (P : ℝ → ℝ), InClass θ P ∧ Rf θ P = rFam ∧
    (∀ (θ' : Params) (P' : ℝ → ℝ), InClass θ' P' → Rf θ' P' = rFam →
      θ' = θ ∧ EqOn P' P (Icc θ.c θ.ξ₀)) ∧
    (∃ ξl ξr C : ℝ, 0 < C ∧ θ.c < ξl ∧ ξl < ξr ∧ ξr < θ.ξ₀ ∧
      (∀ ξ ∈ Icc θ.c ξl, P ξ = θ.line₁ ξ) ∧ (∀ ξ ∈ Icc ξr θ.ξ₀, P ξ = θ.line₂ ξ) ∧
      StrictConcaveOn ℝ (Icc ξl ξr) P ∧ ContDiffOn ℝ 2 P (Ioo ξl ξr) ∧
      ∀ ξ ∈ Ioo ξl ξr, deriv (deriv P) ξ + C / ξ ^ 2 * P ξ = 0) ∧
    (∃ I : ℕ → GenInstance, (∀ n, (I n).Valid) ∧ HasCommonEscapingAtom I ∧
      LawsConvergeTo I (buyerBodyLaw θ P) (sellerBodyLaw θ P) ∧
      Tendsto (fun n => (I n).sellerWelfare) atTop (𝓝 (Mf θ P)) ∧
      Tendsto (fun n => (I n).efficientGains) atTop (𝓝 (Gf θ P)) ∧
      Tendsto (fun n => (I n).bestGain) atTop (𝓝 2) ∧
      Tendsto (fun n => (I n).bestRatio) atTop (𝓝 rFam))) ∧
  rFamSlopes = rFam ∧ βlo < rFam ∧ rFam < βhi

/-- Proof of `prop:2fam-optimum`, "Self-consistency": a physical stationary solution in the trial
interval whose curve has `K_f = 0` is the family minimum. -/
def SelfConsistencyStatement : Prop :=
  ∀ β ∈ Icc βlo βhi, ∀ t p : ℝ, PhysStationary (dOf β) t p → ∀ P : ℝ → ℝ,
    InClass (Elim.params (dOf β) t p) P →
    ThreeArc (dOf β) (Elim.params (dOf β) t p) P
      (Elim.ξl (dOf β) t p) (Elim.ξr (dOf β) t p) (Elim.C (dOf β) t p) →
    Kf β (Elim.params (dOf β) t p) P = 0 →
    IsGlobalMinR (Elim.params (dOf β) t p) P ∧ β = rFam

/-! ## Interface statements (steps of the proofs that several packages share) -/

/-- Moving endpoints under dominated convergence: if `g n → g₀` almost everywhere on `[L, U]`,
uniformly bounded, and the endpoints `a n ≤ b n` in `[L, U]` converge, then
`∫_{a n}^{b n} g n → ∫_{a₀}^{b₀} g₀`. Used for `T_f`, `Q_f`, `E_f` along sequences of curves with
moving parameters (proof of `lem:2fam-compact`) and in the outer variations. -/
def MovingEndpointStatement : Prop :=
  ∀ (g : ℕ → ℝ → ℝ) (g₀ : ℝ → ℝ) (a b : ℕ → ℝ) (a₀ b₀ L U B : ℝ),
    (∀ n, L ≤ a n ∧ a n ≤ b n ∧ b n ≤ U) →
    Tendsto a atTop (𝓝 a₀) → Tendsto b atTop (𝓝 b₀) →
    (∀ n, AEStronglyMeasurable (g n) (volume.restrict (Icc L U))) →
    (∀ n, ∀ᵐ x ∂(volume.restrict (Icc L U)), ‖g n x‖ ≤ B) →
    (∀ᵐ x ∂(volume.restrict (Icc L U)), Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) →
    Tendsto (fun n => ∫ x in a n..b n, g n x) atTop (𝓝 (∫ x in a₀..b₀, g₀ x))

/-- Basic facts about class members that every package uses (text after `(eq:2fam-class)` and the
proofs of `lem:2fam-compact`, `lem:2fam-shape`): continuity on the curve interval, the lower bound
`P ≥ p_f`, the slope bounds `h_f ≤ P' ≤ 1` almost everywhere, `(log P)' = P'/P` almost
everywhere, integrability of the integrands of `T_f`, `Q_f` and `E_f`, the derivative
`s_f' = P⁻²` of the physical time, and the moving-endpoint lemma. Work package A (`Basic.lean`). -/
def ClassBasicsStatement : Prop :=
  (∀ (θ : Params) (P : ℝ → ℝ), InClass θ P →
    ContinuousOn P (Icc θ.c θ.ξ₀) ∧
    (∀ ξ ∈ Icc θ.c θ.ξ₀, θ.p ≤ P ξ) ∧
    (∀ᵐ ξ ∂(volume.restrict (Icc θ.c θ.ξ₀)), θ.h ≤ deriv P ξ ∧ deriv P ξ ≤ 1) ∧
    (∀ᵐ ξ ∂(volume.restrict (Icc θ.c θ.ξ₀)),
      deriv (fun x => Real.log (P x)) ξ = deriv P ξ / P ξ) ∧
    IntervalIntegrable (fun ξ => (P ξ ^ 2)⁻¹) volume θ.c θ.ξ₀ ∧
    IntervalIntegrable (fun ξ => ξ * (deriv P ξ / P ξ) ^ 2) volume θ.c θ.ξ₀ ∧
    IntervalIntegrable (fun ξ => ξ * deriv (fun x => Real.log (P x)) ξ ^ 2) volume θ.c θ.ξ₀ ∧
    (∀ x ∈ Icc θ.c θ.ξ₀, HasDerivWithinAt (sF θ P) ((P x ^ 2)⁻¹) (Icc θ.c θ.ξ₀) x)) ∧
  MovingEndpointStatement

/-- Basic bounds on a class member (proof of `lem:2fam-compact`: `F_1 ∈ [m, 1]`, `H_1 ∈ [0, 1]`,
`G_f ≤ 2/m_f`, `R_f ≥ m_f`, `M_f ≥ (1-m_f) b_f ≥ 0`): positivity of the normalizations. -/
def PositivityStatement : Prop :=
  ∀ (θ : Params) (P : ℝ → ℝ), InClass θ P →
    0 < θ.N ∧ 0 ≤ Mf θ P ∧ 2 ≤ Gf θ P ∧ Gf θ P ≤ 2 / θ.m ∧ θ.m ≤ Rf θ P ∧ Rf θ P ≤ 1

/-- `(eq:2fam-comparison)` for class members and the ratio form used in the proof of
`lem:2fam-boundary`. -/
def ComparisonStatement : Prop :=
  ∀ (β : ℝ) (θ : Params) (P : ℝ → ℝ), InClass θ P → 0 < β →
    Ef β θ P = Qf θ P + dOf β * Tf θ P ∧ Kf β θ P = Kconst β θ - Ef β θ P ∧
    Kf β θ P = (Mf θ P + Gf θ P) / θ.N * (1 - Rf θ P / β)

/-- The "compact extension" in the proof of `lem:2fam-compact`: on the region
`1/32 ≤ m_f ≤ 3/4`, `ξ₀ ≤ 600`, every sequence in the family has a subsequence whose parameters
converge to those of a class member and whose `T_f`, `Q_f` converge to that member's values. -/
def SeqCompactStatement : Prop :=
  ∀ (θ : ℕ → Params) (P : ℕ → ℝ → ℝ), (∀ n, InClass (θ n) (P n)) →
    (∀ n, 1 / 32 ≤ (θ n).m ∧ (θ n).m ≤ 3 / 4 ∧ (θ n).ξ₀ ≤ 600) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (θ' : Params) (P' : ℝ → ℝ), InClass θ' P' ∧
      Tendsto (fun n => (θ (φ n)).t) atTop (𝓝 θ'.t) ∧
      Tendsto (fun n => (θ (φ n)).p) atTop (𝓝 θ'.p) ∧
      Tendsto (fun n => (θ (φ n)).ξ₀) atTop (𝓝 θ'.ξ₀) ∧
      Tendsto (fun n => Tf (θ (φ n)) (P (φ n))) atTop (𝓝 (Tf θ' P')) ∧
      Tendsto (fun n => Qf (θ (φ n)) (P (φ n))) atTop (𝓝 (Qf θ' P'))

/-- Proof of `lem:2fam-compact`, after `(eq:2fam-small-mass)`: "The scalar expression increases on
this interval". The machine check records only a lower bound `207/1024` of the derivative
numerator at `m = 1/32` (see `FamilyNumerics.small_mass_endpoint`); on the interval,
`m² · smallMassBound'(m) = 1/4 - 3m/2 - m²/4 > 0`. A Lean target (work package A). -/
def SmallMassMonoStatement : Prop := StrictMonoOn smallMassBound (Ioc 0 (1 / 32))

/-- Proof of `prop:2fam-optimum`, "Attainment": if some curve has `R_f < 3/4`, the infimum is
attained. -/
def RatioAttainedStatement : Prop :=
  (∃ (θ : Params) (P : ℝ → ℝ), InClass θ P ∧ Rf θ P < 3 / 4) →
    ∃ (θ : Params) (P : ℝ → ℝ), IsGlobalMinR θ P ∧ Rf θ P = rFam

/-- A global maximizer of `K_f` minimizes `E_f` at its own parameters (`(eq:2fam-comparison)`). -/
def GlobalMaxEnergyStatement : Prop :=
  ∀ (β : ℝ) (θ : Params) (P : ℝ → ℝ), 0 < β → β < 1 → IsGlobalMaxK β θ P →
    IsEnergyMinimizer β θ P

/-- Positive contacts give the endpoint slopes `1, h_f`. -/
def EndpointSlopesStatement : Prop :=
  ∀ (d : ℝ) (θ : Params) (P : ℝ → ℝ) (ξl ξr C : ℝ), InClass θ P → ThreeArc d θ P ξl ξr C →
    θ.c < ξl → ξr < θ.ξ₀ → EndpointSlopes θ P

/-- The two entirely affine curves have the functionals `(eq:2fam-affine-boundaries)`. -/
def AffineFunctionalsStatement : Prop :=
  ∀ (θ : Params) (P : ℝ → ℝ), InClass θ P →
    ((∀ ξ ∈ Icc θ.c θ.ξ₀, P ξ = θ.line₁ ξ) → θ.p < 1 →
        Mf θ P = affineML θ.t θ.p ∧ Gf θ P = affineGL θ.t θ.p) ∧
    ((∀ ξ ∈ Icc θ.c θ.ξ₀, P ξ = θ.line₂ ξ) → θ.p < 1 →
        (1 + θ.t) / 2 < θ.p ∧ Mf θ P = affineMR θ.t θ.p ∧ Gf θ P = affineGR θ.t θ.p)

/-- `(eq:2fam-quadratures)` for a three-arc curve with positive contacts. -/
def QuadratureStatement : Prop :=
  ∀ (d : ℝ) (θ : Params) (P : ℝ → ℝ) (ξl ξr C : ℝ), 0 < d → InClass θ P →
    ThreeArc d θ P ξl ξr C → θ.c < ξl → ξr < θ.ξ₀ →
    Tf θ P = quadT d θ ξl ξr ∧ Qf θ P = quadQ θ ξl ξr C ∧ Gf θ P = quadG θ ξl ξr C

/-- The stationary reduction (text between `lem:2fam-boundary` and `lem:2fam-domain`, used in the
proof of `prop:2fam-optimum`): an interior three-arc stationary curve gives a physical stationary
point whose recovery formulas reproduce its parameters and contact data. The TeX writes only the
reverse direction ("Reconstructing the curve"); it never derives the connection equation
`(eq:2fam-connection)` for a given curve and never shows `q_r < v_f`, which identifies the contact
slope with the closed-form root (paper gap G9 of the blueprint, repair class free: the substitution
`dξ/ξ = -dω/𝒟(ω)` of `lem:2fam-shape`, and `C_f(v_f² - q_r²) = v_f² q_r (1 - q_r) > 0`). -/
def ReductionStatement : Prop :=
  ∀ (d : ℝ) (θ : Params) (P : ℝ → ℝ) (ξl ξr C : ℝ), 0 < d → InClass θ P →
    ThreeArc d θ P ξl ξr C → θ.c < ξl → ξr < θ.ξ₀ → θ.t < θ.p → θ.p < 1 →
    statP d θ (θ.line₁ ξl) = 0 → statH d θ (θ.line₂ ξr) = 0 →
    statT d θ (θ.line₁ ξl) (θ.line₂ ξr) = 0 →
    PhysStationary d θ.t θ.p ∧ θ.ξ₀ = Elim.ξ₀ d θ.t θ.p ∧ ξl = Elim.ξl d θ.t θ.p ∧
      ξr = Elim.ξr d θ.t θ.p ∧ C = Elim.C d θ.t θ.p

/-- The connection integral in closed form when `C > 1/4`. -/
def ConnectionArctanStatement : Prop :=
  ∀ d t p : ℝ, 1 / 4 < Elim.C d t p → Elim.connI d t p = Elim.connJ d t p

/-- A physical stationary point in the trial interval is a root of the covers (it lies in the
cover domain by `lem:2fam-domain`, has `C > 1/4` by the cover, and the connection integral equals
its arctan form). -/
def PhysToCoverRootStatement : Prop :=
  ∀ β ∈ Icc βlo βhi, ∀ t p : ℝ, PhysStationary (dOf β) t p → CoverRoot (dOf β) t p

/-- "Reconstructing the curve" in the proof of `lem:2fam-cover`: a cover root in the certified
root strip is a physical stationary point (the recovered three-arc curve lies in the class). -/
def ReconstructionStatement : Prop :=
  ∀ β ∈ Icc βlo βhi, ∀ t p : ℝ, t ∈ rootStripT → p ∈ rootStripP →
    CoverRoot (dOf β) t p → PhysStationary (dOf β) t p

/-- The half of `lem:2fam-cover` that the proof of `prop:2fam-optimum` uses: at most one physical
stationary point on the trial interval, and the lower-endpoint sign. It does not need the curve
reconstruction. -/
def CoverAtMostOneStatement : Prop :=
  (∀ β ∈ Icc βlo βhi, ∀ t p t' p' : ℝ, PhysStationary (dOf β) t p →
      PhysStationary (dOf β) t' p' → t = t' ∧ p = p') ∧
  (∀ t p : ℝ, PhysStationary (dOf βlo) t p → ∀ P : ℝ → ℝ,
    InClass (Elim.params (dOf βlo) t p) P →
    ThreeArc (dOf βlo) (Elim.params (dOf βlo) t p) P
      (Elim.ξl (dOf βlo) t p) (Elim.ξr (dOf βlo) t p) (Elim.C (dOf βlo) t p) →
    βlo * Gf (Elim.params (dOf βlo) t p) P - (1 - βlo) * Mf (Elim.params (dOf βlo) t p) P - 2
      < 0)

/-- Exact segment integration: valid polygon data give a class member that is a rational
concave polygon, with `R_f` equal to the segment ratio. -/
def PolygonCurveStatement : Prop :=
  ∀ D : PolygonData, D.Valid →
    InClass D.params D.curve ∧ IsRationalConcavePolygon D.curve D.params.c D.params.ξ₀ ∧
      Rf D.params D.curve = (D.segmentRatio : ℝ)

/-- The realization with the common escaping buyer atom exposed (the construction in the proof
of `lem:2fam-realization`; needed by the last sentence of `prop:2fam-optimum`). -/
def RealizationEscapingStatement : Prop :=
  ∀ (θ : Params) (P : ℝ → ℝ), InClass θ P →
    ∃ I : ℕ → GenInstance, (∀ n, (I n).Valid) ∧ HasCommonEscapingAtom I ∧
      LawsConvergeTo I (buyerBodyLaw θ P) (sellerBodyLaw θ P) ∧
      Tendsto (fun n => (I n).sellerWelfare) atTop (𝓝 (Mf θ P)) ∧
      Tendsto (fun n => (I n).efficientGains) atTop (𝓝 (Gf θ P)) ∧
      Tendsto (fun n => (I n).bestGain) atTop (𝓝 2) ∧
      Tendsto (fun n => (I n).bestRatio) atTop (𝓝 (Rf θ P))

/-- The finite model of `Model.lean` is the special case of the general model (appendix
introduction): for a valid finite instance, the general instance `ofFinite B S` is valid and its
seller welfare, efficient welfare and price gains are `mean2 S`, `opt2 B S` and `gain2 B S z`. -/
def OfFiniteStatement : Prop :=
  ∀ (B S : RLaw), ValidInstance B S →
    (ofFinite B S).Valid ∧ (ofFinite B S).sellerWelfare = mean2 S ∧
      (ofFinite B S).optimalWelfare = opt2 B S ∧
      ∀ z, (ofFinite B S).priceGain z = gain2 B S z

/-! ## Projections between statements (proved, no `sorry`) -/

/-- The covers' premise `CoverMonotonicity` is the second claim of `lem:2fam-domain` on the trial
range of `d`. -/
theorem coverMonotonicity_of_domain (hDom : DomainStatement) : CoverMonotonicity :=
  fun d hd t p ht htp hp1 => hDom.2 d (lt_of_lt_of_le (by norm_num) hd.1) t p ht htp hp1

/-- `lem:2fam-realization` follows from the escaping-atom version. -/
theorem lem_2fam_realization_of (h : RealizationEscapingStatement) : RealizationStatement :=
  fun θ P hP => by
    obtain ⟨I, hI, -, hL, h₁, h₂, h₃, h₄⟩ := h θ P hP
    exact ⟨I, hI, hL, h₁, h₂, h₃, h₄⟩

/-- `lem:2fam-cover`: existence from the certified cover and the reconstruction, uniqueness and
sign from the at-most-one half. -/
theorem lem_2fam_cover_of (hN : FamilyNumerics) (hDom : DomainStatement)
    (hR : ReconstructionStatement) (hU : CoverAtMostOneStatement) : CoverStatement := by
  refine ⟨fun β hβ => ?_, hU.2⟩
  obtain ⟨t, p, ht, hp, hroot⟩ := hN.cover_exists (coverMonotonicity_of_domain hDom) β hβ
  refine ⟨(t, p), hR β hβ t p ht hp hroot, ?_⟩
  rintro ⟨t', p'⟩ h'
  obtain ⟨h1, h2⟩ := hU.1 β hβ t' p' t p h' (hR β hβ t p ht hp hroot)
  simp [h1, h2]

/-- `lem:2fam-witness` from the exact polygon certificate and the segment integration. -/
theorem lem_2fam_witness_of (hN : FamilyNumerics) (hPoly : PolygonCurveStatement) :
    WitnessStatement := by
  obtain ⟨D, hD, hR⟩ := hN.polygon_witness
  obtain ⟨hC, hPolyg, hEq⟩ := hPoly D hD
  refine ⟨D.params, D.curve, ⟨D.t, D.p, D.ξ₀, rfl, rfl, rfl⟩, hC, hPolyg, ?_⟩
  rw [hEq]
  have hR' : ((D.segmentRatio : ℚ) : ℝ) < ((729081 / 10 ^ 6 : ℚ) : ℝ) := by exact_mod_cast hR
  simpa [βhi] using hR'

end FixedPrice.TwoUnit.Family
