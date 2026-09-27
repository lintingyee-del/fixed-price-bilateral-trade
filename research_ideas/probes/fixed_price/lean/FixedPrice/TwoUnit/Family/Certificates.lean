import FixedPrice.TwoUnit.Family.Defs

/-!
# Machine-certified facts of the two-unit family, as explicit hypotheses

Standing rule of this development: a fact that already has a machine certificate (ledger layers
`exact`, `arb`, `sympy`, `z3`, `cvc5`, or the replay `manuscript/supplement/verify.py`) is **not**
proved in Lean. It enters as a field of one of two hypothesis structures:

* `FamilyNumerics`: the computer-assisted numerical claims of the appendix
  (interval evaluation, Bernstein certificates, the exact positive constants recorded by
  `branch_monotonicity.py`, the rational covers of `lem:2fam-cover`, the exact polygon value of
  `lem:2fam-witness`);
* `FamilyIdentities`: the symbolic identities recorded with `exact`/`sympy`/`z3`/`cvc5` receipts
  that the analytic proofs use as algebraic steps, restated for the Lean definitions of
  `Defs.lean`.

Each field names the TeX location and the ledger key (`proof_factgraph/ledger.toml`) or the
supplement file that certifies it, and says what the certificate checks and no more. Ledger keys
refer to `[claims.<key>]` entries. The independent replay `fp_supplement_independent_replay_20260921`
(layers exact/arb/sympy, `verify.py`, 37/37 checks) re-evaluates the Bernstein trees, both
stationary covers and the root strip; for the identity and enclosure files it only confirms
recorded zero residuals and signs.

Two ledger statements claim more than their scripts check. The fields follow the scripts, and the
unchecked deductions are Lean targets:

* `fp_ext_k2_branch_positive_factors_20260913` says the factors "prove strict p0 monotonicity of
  the algebraic residual and 1/5<t<421/1000". `branch_monotonicity.py` checks eleven identity
  residuals and asserts that seven rational constants are positive. The sign case split, the
  monotone-factor bounds, the combination of the constants and the identification of the implicit
  derivative with the derivative of the closed-form residual are hand reasoning (paper factgraph
  node `P_two_family_domain`: `rethlas` only). The identities are the `branch_*` fields of
  `FamilyIdentities`, the constants are `FamilyNumerics.branch_positive_constants`, and the lemma
  is the Lean target `DomainStatement`.
* `fp_ext_k2_outer_boundary_algebra_20260913` says "the stated small-m bound is increasing on
  (0,1/32]". `outer_boundary_algebra.py` checks one rational number (`207/1024 > 0`, a lower bound of
  the derivative numerator at `m = 1/32`) and nothing on the interval. The monotonicity is the
  Lean target `SmallMassMonoStatement`.

No Lean proof may re-derive a field; a proof that needs a further certified identity adds it here
with its receipt. Every field is evaluated over its full stated range by the discovery probe
`lean/blueprints/family_probe.py` (not a credential).
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

/-! ### Objects referenced by the certificates -/

/-- The small-mass bound of `(eq:2fam-small-mass)`:
`(3/4){4 + 2 log(2/m)} - (1-m)²/(4m) - 2`. -/
def smallMassBound (m : ℝ) : ℝ := 3 / 4 * (4 + 2 * Real.log (2 / m)) - (1 - m) ^ 2 / (4 * m) - 2

/-- The bound in the proof of `lem:2fam-domain` that excludes large `t`:
`-3/(8t²) + 111/100 + 1 + t - (1-t)/(1+t)` (`bound` in `branch_monotonicity.py`, written there
as `-3/(8t²) + 3·37/100 + 1 + t - (1-t)/(1+t)`). -/
def largeTBound (t : ℝ) : ℝ := -(3 / 8) / t ^ 2 + 3 * (37 / 100) + 1 + t - (1 - t) / (1 + t)

/-- The `t`-projection of the common root strip of `stationary_uniform_cover.json`
(`root_t_interval`). -/
def rootStripT : Set ℝ := Icc (1332853481 / 4194304000) (1333276033 / 4194304000)

/-- The `p`-projection of the common root strip of `stationary_uniform_cover.json`
(`root_p_interval`). -/
def rootStripP : Set ℝ :=
  Icc (754340808478301733 / 1125899906842624000) (757970502520020517 / 1125899906842624000)

/-- A root of the eliminated system in the sense of the supplement's covers (`verify.py`,
`check_cover`): `t` in the cover domain `[1/5, 421/1000]`, `t < p ≤ 1`, algebraic residual zero,
`P_ℓ ≤ 1` (else the leaf is `Pl_above_one`), `q_r ≤ q_ℓ` (else `wrong_phase_order`), `C > 1/4`
(the connection is evaluated only for `C > 1/4`), and the arctan form of the connection equation
vanishes. -/
structure CoverRoot (d t p : ℝ) : Prop where
  t_ge : 1 / 5 ≤ t
  t_le : t ≤ 421 / 1000
  t_lt_p : t < p
  p_le_one : p ≤ 1
  alg : Elim.algResidual d t p = 0
  Pl_le_one : Elim.Pl d t p ≤ 1
  qR_le_qL : Elim.qR d t p ≤ Elim.qL d t p
  C_gt : 1 / 4 < Elim.C d t p
  conn : Elim.connectionArctan d t p = 0

/-- The strict physical inequalities certified on the whole root strip. The first thirteen are the
margins of `fpm_repair_20260921_stationary_physical_cartesian_arb`
(`stationary_physical_conditions.json`: `0 < t < p < 1`, `C > 1/4`, `c < ξ_ℓ < ξ_r < ξ₀`,
`0 < q_r < q_ℓ < 1`, `0 < h < 1`, `q_r < v`); the last two are the `verify.py` root-strip check
`P_ℓ < P_r < 1`. The discriminant of `q_r` is not certified there; its positivity
(`disc = (2C - v²)² + v²(1 - v²) > 0` for `0 < v < 1`) is elementary and proved where it is used. -/
structure PhysicalMargins (d t p : ℝ) : Prop where
  t_pos : 0 < t
  t_lt_p : t < p
  p_lt_one : p < 1
  C_gt : 1 / 4 < Elim.C d t p
  c_lt_ξl : cF t p < Elim.ξl d t p
  ξl_lt_ξr : Elim.ξl d t p < Elim.ξr d t p
  ξr_lt_ξ₀ : Elim.ξr d t p < Elim.ξ₀ d t p
  qR_pos : 0 < Elim.qR d t p
  qR_lt_qL : Elim.qR d t p < Elim.qL d t p
  qL_lt_one : Elim.qL d t p < 1
  h_pos : 0 < Elim.h d t p
  h_lt_one : Elim.h d t p < 1
  qR_lt_v : Elim.qR d t p < vF t
  Pl_lt_Pr : Elim.Pl d t p < Elim.Pr d t p
  Pr_lt_one : Elim.Pr d t p < 1

/-- The premise under which the stationary covers are certified ("p0 monotonicity" in their
ledger statements): the algebraic residual has positive `p`-derivative on `0 < t < p < 1` for every
`d` in the trial range `[d(729081/10⁶), d(18227/25000)] = [270919/729081, 6773/18227]`. The cover
leaves `no_algebraic_root` and the `p`-brackets locate every root only under this premise. It
follows from the second claim of `lem:2fam-domain` (`DomainStatement`), a Lean target. -/
def CoverMonotonicity : Prop :=
  ∀ d ∈ Icc (270919 / 729081 : ℝ) (6773 / 18227), ∀ t p : ℝ, 0 < t → t < p → p < 1 →
    0 < deriv (fun p' => Elim.algResidual d t p') p

/-! ### Numerical certificates -/

/-- The computer-assisted numerical claims of the family appendix, one field per certified
fact. -/
structure FamilyNumerics : Prop where
  /-- `two_unit_family.tex`, proof of `lem:2fam-compact`, after `(eq:2fam-small-mass)`: "... and
  is less than `-2694/10000` at `1/32`, by interval evaluation". Ledger
  `fp_ext_k2_outer_boundary_algebra_20260913` (arb, 160 bits). The script asserts that the Arb
  ball of the expression at `m = 1/32` is negative and records the ball as
  `compact_upper_at_one_over_32 = [-0.26948787496049… ± 4.45e-47]` (supplement
  `boundary_identities.json`); the bound `-2694/10000` is read off this recorded ball. The same
  script records `positive_derivative_numerator_lower = 207/1024 = 1/4 - (3/2)(1/32) - (1/32)²`,
  which is a lower bound of the true numerator `1/4 - 3m/2 - m²/4 = 831/4096` of
  `m² · smallMassBound'(m)` at `m = 1/32` (`m²` in place of `m²/4`). It is a single point value:
  the monotonicity "increases on this interval" is not machine-checked and is the Lean target
  `SmallMassMonoStatement`. -/
  small_mass_endpoint : smallMassBound (1 / 32) < -2694 / 10000
  /-- `two_unit_family.tex` after `(eq:2fam-affine-boundaries)`: `R_f ≥ 73/100` on the left
  affine boundary, in the multiplied form `(M+2) - (73/100)(M+G) ≥ 0`, on the closed face
  `0 < t < 1`, `t ≤ p < 1`. The Bernstein certificate covers the closed square `(t, u) ∈ [0,1]²`
  with `p = t + u(1 - t)` (nonnegative Bernstein coefficients on closed boxes) and positive
  multiplier `p t (1 + t)`, so the face `p = t` (`u = 0`, `c_f = 0`), which `lem:2fam-boundary`
  needs, is certified directly; the TeX states the open domain `t < p < 1`. Ledger
  `fp_ext_k2_straight_boundaries_073_20260913` (exact, Bernstein); replay
  `fp_supplement_independent_replay_20260921`; supplement `affine_boundary_coefficients.json`
  (boundary `left`, 10 nonnegative leaves). -/
  affine_left : ∀ t p : ℝ, 0 < t → t < 1 → t ≤ p → p < 1 →
    73 / 100 * (affineML t p + affineGL t p) ≤ affineML t p + 2
  /-- Same, right affine boundary, domain `(1+t)/2 < p < 1` (boundary `right`, 12 leaves; the
  multiplier `p t (1+t)(2p - t - 1)` vanishes on the face `p = (1+t)/2`, which is therefore not
  covered). -/
  affine_right : ∀ t p : ℝ, 0 < t → t < 1 → (1 + t) / 2 < p → p < 1 →
    73 / 100 * (affineMR t p + affineGR t p) ≤ affineMR t p + 2
  /-- Proof of `lem:2fam-domain`: the seven rational constants of `branch_monotonicity.py`
  (supplement `branch_positive_factors.json`, `positive_constants`), in the script's order:
  `r_squared_coefficient_lower = 851/2500`, `r_times_t_coefficient_lower = 4957/5000`,
  `t_squared_coefficient_lower = 4899/40000` (for the polynomial in `r` of
  `FamilyIdentities.branch_small_t_expansion`: the coefficient of `r²`, the coefficient of `r`
  divided by `t`, and the constant term divided by `t²`, evaluated at `t = 1/5`, `λ = 37/100`),
  `square_root_comparison_gap = 53/8550` (`(16/15)² - 43/38`), `k_upper_gap_below_three_tenths =
  41/1120` (`3/10 - 59/224`), `phase_threshold_square_gap = 23/2064` (`74/129 - 9/16`), and
  `large_t_exclusion_margin = 1958756791/251859461000` (`largeTBound (421/1000)`). The script
  asserts exactly that each constant is positive. That these three quantities are bounded below by
  the first three constants on `0 < t ≤ 1/5`, `37/100 ≤ λ ≤ 3/8` ("monotone factors") is a comment
  in the script, not a check. Ledger `fp_ext_k2_branch_positive_factors_20260913` (exact), whose
  statement claims more than the script checks (module docstring). -/
  branch_positive_constants :
    0 < (37 / 100 : ℝ) * (1 - 2 * (1 / 5) ^ 2) ∧
    0 < (7 / 2 : ℝ) * (37 / 100) * (1 - 2 * (1 / 5) ^ 2) - 1 / 5 ∧
    0 < ((33 : ℝ) - 98 * (1 / 5) ^ 2) * (37 / 100) / 16 - 11 * (1 / 5) / 4 ∧
    0 < (256 / 225 : ℝ) - 43 / 38 ∧
    0 < (3 / 10 : ℝ) - 59 / 224 ∧
    0 < (74 / 129 : ℝ) - 9 / 16 ∧
    0 < largeTBound (421 / 1000)
  /-- `lem:2fam-cover`, the reduced root (implicit in the cover): on the whole trial interval,
  every algebraic root in the cover domain with `P_ℓ ≤ 1` and `q_r ≤ q_ℓ` has `C > 1/4`. Every leaf
  not excluded by `no_algebraic_root`, `Pl_above_one` or `wrong_phase_order` evaluates the
  connection, which `verify.py` does only when the whole ball of `C` exceeds `1/4`. The exclusions
  and the `p`-brackets locate every root only because the residual is increasing in `p`, so the
  field carries the credential's premise `CoverMonotonicity`. The credential's other premise, the
  bounds `1/5 < t < 421/1000` of `lem:2fam-domain`, enters as the restriction to the cover domain
  `1/5 ≤ t ≤ 421/1000`; the passage to every physical stationary point is
  `PhysToCoverRootStatement`. Ledger `fp_ext_k2_stationary_branch_uniform_arb_20260913` (arb,
  192 bits, "conditional on ... p0 monotonicity and 1/5<t<421/1000 bounds"); replay
  `fp_supplement_independent_replay_20260921`; supplement `stationary_uniform_cover.json`
  (6827 leaves). -/
  cover_C : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∀ t p : ℝ, 1 / 5 ≤ t → t ≤ 421 / 1000 →
    t < p → p ≤ 1 → Elim.algResidual (dOf β) t p = 0 → Elim.Pl (dOf β) t p ≤ 1 →
    Elim.qR (dOf β) t p ≤ Elim.qL (dOf β) t p → 1 / 4 < Elim.C (dOf β) t p
  /-- `lem:2fam-cover`: at most one cover root for every trial ratio in the interval (retained
  cells contiguous, positive branch derivative, nonzero connection elsewhere), under the premise
  `CoverMonotonicity` (see `cover_C` for the premises). Same ledger key and supplement file; the
  lower endpoint is also covered by `fp_ext_k2_stationary_branch_arb_20260913` and
  `stationary_lower_endpoint.json` (12749 leaves). -/
  cover_unique : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∀ t p t' p' : ℝ,
    CoverRoot (dOf β) t p → CoverRoot (dOf β) t' p' → t = t' ∧ p = p'
  /-- `lem:2fam-cover`: a cover root exists in the common root strip for every trial ratio in the
  interval, under the premise `CoverMonotonicity`. The root comes from the sign change of the
  connection equation across the retained cells (`fp_ext_k2_stationary_branch_uniform_arb_20260913`,
  replay `fp_supplement_independent_replay_20260921`); its conditions `P_ℓ ≤ 1`, `q_r ≤ q_ℓ` and
  `C > 1/4` hold on the whole strip by `fpm_repair_20260921_stationary_physical_cartesian_arb`
  (`stationary_physical_conditions.json`) and the `verify.py` root-strip check. -/
  cover_exists : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∃ t p : ℝ, t ∈ rootStripT ∧
    p ∈ rootStripP ∧ CoverRoot (dOf β) t p
  /-- `lem:2fam-cover`, "Reconstructing the curve": interval evaluation of `(eq:2fam-algebraic)`
  and `(eq:2fam-recovery)` over the whole root strip and trial interval. Ledger
  `fpm_repair_20260921_stationary_physical_cartesian_arb` (arb, 256 bits); supplement
  `stationary_physical_conditions.json`; the orders `P_ℓ < P_r < 1` are the `verify.py`
  root-strip check in `fp_supplement_independent_replay_20260921`. -/
  physical_box : ∀ β ∈ Icc βlo βhi, ∀ t ∈ rootStripT, ∀ p ∈ rootStripP,
    PhysicalMargins (dOf β) t p
  /-- `lem:2fam-cover`, "The lower trial value": at `β = 18227/25000` every cover root has
  `β G_f - (1-β) M_f - 2 ∈ [-2.116·10⁻⁶, -1.157·10⁻⁶] < 0`, under the premise
  `CoverMonotonicity` (which places every root in the certified strip). Ledger
  `fp_ext_k2_stationary_branch_arb_20260913` (arb, "conditional on ... p0 monotonicity"); replay
  `fp_supplement_independent_replay_20260921`; supplement `stationary_lower_endpoint.json`
  (`root_comparison_K`). -/
  lower_endpoint_sign : CoverMonotonicity → ∀ t p : ℝ, CoverRoot (dOf βlo) t p →
    Elim.comparisonJ t p βlo < 0
  /-- `lem:2fam-witness`, and `two_unit_computation.tex` (`app:two-finite`): the rational concave
  polygon with 130 segments passes the exact checks of `polygon_witness.py` and its exact segment
  integration gives `R_f < 729081/10⁶`. Ledger `fp_ext_k2_polygon_finite_upper_20260913`
  (exact); data `extension_screen_20260913/continuation/results/polygon_witness.json`
  (`polygon_ratio`) and `manuscript/supplement/general_instance.json`. -/
  polygon_witness : ∃ D : PolygonData, D.Valid ∧ D.segmentRatio < 729081 / 10 ^ 6

/-! ### Symbolic identities -/

/-- The coefficients of the differential `dE` of the minimal energy at a three-arc minimizer with
positive contacts, as split by `endpoint_algebra.py` (its input formula `dE`) over the directions
`(dc, dδ, dξ₀, dh, de)`.

They are not five independent partial derivatives. In the script `ξ₀ = (1 - e)/h` is tied to
`(h, e)`, so `dξ₀ = -(ξ₀ dh + de)/h`: the energy is defined only on outer data with
`P(c) = c + δ = p` and `P(ξ₀) = h ξ₀ + e = 1`. At fixed `(c, δ, h, e)`, for example, extending the
final contact changes the energy at rate `ξ₀h² + d`, not `Eξ₀ = d - ξ₀h²`; the split differs from
unconstrained partial derivatives by a multiple of `(h, ξ₀, 1)`, the gradient of `h ξ₀ + e` in
`(ξ₀, h, e)`. Only combinations along admissible directions are meaningful. The analytic target of
`lem:2fam-boundary` is the directional derivative of the minimal energy along each constructed
outer variation that keeps `P(c) = p` and `P(ξ₀) = 1`, i.e. along `(dc, dδ, dξ₀, dh, de)` with
`dc + dδ = dp` and `h dξ₀ + ξ₀ dh + de = 0`; for these directions it is
`Ec dc + Eδ dδ + Eξ₀ dξ₀ + Eh dh + Ee de`. The directions of `(eq:2fam-stationarity)` are those of
`FamilyIdentities.envelope_p`, `envelope_t` and `envelope_h`, whose conversion to `statP`,
`statT`, `statH` is certified. -/
structure EnvelopeCoeffs where
  Ec : ℝ
  Eδ : ℝ
  Eξ₀ : ℝ
  Eh : ℝ
  Ee : ℝ

/-- The coefficients `dE` of `endpoint_algebra.py` in terms of the contact data. -/
def envelopeCoeffs (d : ℝ) (θ : Params) (Pl Pr : ℝ) : EnvelopeCoeffs where
  Ec := -(θ.c + d) / θ.p ^ 2
  Eδ := -(2 * θ.c + θ.δ + d) / θ.p ^ 2 + (θ.δ + d) / Pl ^ 2
  Eξ₀ := d - θ.ξ₀ * θ.h ^ 2
  Eh := -2 * (θ.h * θ.e + d) * ((Pr⁻¹ - 1 + θ.e * (1 - (Pr ^ 2)⁻¹) / 2) / θ.h ^ 2)
  Ee := -2 * (θ.h * θ.e + d) * (((Pr ^ 2)⁻¹ - 1) / (2 * θ.h))

/-- The machine-certified symbolic identities used as algebraic steps. Each is the recorded
identity restated for the definitions of `Defs.lean`, evaluated where its denominators do not
vanish. -/
structure FamilyIdentities : Prop where
  /-- `(eq:2fam-comparison)`, first line = second line, with `E_f = Q_f + d_f T_f`.
  Ledger `fp_ext_k2_shifted_clock_algebra_20260913` (sympy), residual `ratio_energy_reduction`;
  replay `fpm_repair_20260921_shifted`. -/
  comparison_second_form : ∀ (β : ℝ) (θ : Params) (T Q : ℝ), θ.Admissible → 0 < β →
    (β * (2 + 2 * θ.m * θ.a - θ.N * Real.log θ.p - θ.N * Q)
        - (1 - β) * (θ.N * (θ.a + T - θ.ξ₀)) - 2) / (β * θ.N)
      = Kconst β θ - (Q + dOf β * T)
  /-- Proof of `lem:2fam-boundary`: `K_f = ((M+G)/N)(1 - R/β)`. Ledger
  `fpm_repair_20260921_d4_ratio_comparison_algebra` (sympy), residual
  `normalized_comparison_ratio_identity`. -/
  ratio_comparison : ∀ β M G N : ℝ, β ≠ 0 → N ≠ 0 → M + G ≠ 0 →
    (β * G - (1 - β) * M - 2) / (β * N) = (M + G) / N * (1 - (M + 2) / (M + G) / β)
  /-- Proof of `lem:2fam-boundary` / `prop:2fam-optimum`: with `β N K = O (β - R)` and positive
  `β, N, O`, `R ≥ β` gives `K ≤ 0`, and `K = 0 ↔ R = β`. Ledger
  `fpm_repair_20260921_d4_ratio_minimum_comparison` (z3, cvc5). -/
  ratio_minimum_signs : ∀ β N O K R : ℝ, 0 < β → 0 < N → 0 < O → β * N * K = O * (β - R) →
    (β ≤ R → K ≤ 0) ∧ (K = 0 ↔ R = β)
  /-- Proof of `lem:2fam-compact`: `z̄_f + a_f = 2(1-m_f)/m_f`, as `2a + 1/p - 1 = 1/t - 1`.
  Ledger `fp_ext_k2_outer_boundary_algebra_20260913` (sympy), residual `buyer_mean_identity`;
  replay `fpm_repair_20260921_outer_boundary`. -/
  buyer_mean : ∀ t p : ℝ, 0 < t → 0 < p → 2 * aF t p + 1 / p - 1 = 1 / t - 1
  /-- Proof of `lem:2fam-compact`, the case `p_f = 1`. Same keys, residual `p_equals_one_gap`. -/
  p_one_ratio : ∀ t : ℝ, 0 < t →
    (1 + 3 * t ^ 2) / (1 + t) ^ 2 = 3 / 4 + (3 * t - 1) ^ 2 / (4 * (1 + t) ^ 2)
  /-- `(eq:2fam-left-variation)`: `∂_p Kconst` at fixed `(t, ξ₀)` minus the endpoint variation
  `-(cH² + d)/(2p²) - 2cH(1 - H/2)/p²` of the energy equals `-c(H-2)²/(2p²)`. Same keys, residual
  `zero_left_contact`. -/
  left_variation : ∀ t p d H : ℝ, 0 < t → 0 < p →
    (t / p ^ 2 - 1 / p - d / (2 * p ^ 2))
        - (-(cF t p * H ^ 2 + d) / (2 * p ^ 2) - 2 * cF t p * H / p ^ 2 * (1 - H / 2))
      = -(cF t p * (H - 2) ^ 2 / (2 * p ^ 2))
  /-- `(eq:2fam-right-variation)`: `∂_{ξ₀} Kconst = d` minus the free-endpoint variation
  `(ξ₀H² + d) - 2ξ₀H²` equals `ξ₀ H²`. Same keys, residual `zero_right_contact`. -/
  right_variation : ∀ ξ₀ H d : ℝ, d - ((ξ₀ * H ^ 2 + d) - 2 * ξ₀ * H ^ 2) = ξ₀ * H ^ 2
  /-- `(eq:2fam-stationarity)`, first line: the `p`-coefficient of `dK` built from
  `envelopeCoeffs` equals `∂_p K_f = statP/2`. Ledger `fp_ext_k2_inverse_endpoint_algebra_20260913`
  (sympy), residual `envelope_p0`; replay `fpm_repair_20260921_endpoint`. -/
  envelope_p : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.t → 0 < θ.p → 0 < Pl →
    (θ.t / θ.p ^ 2 - 1 / θ.p - d / (2 * θ.p ^ 2))
        - ((envelopeCoeffs d θ Pl Pr).Ec / 2 + (envelopeCoeffs d θ Pl Pr).Eδ / 2)
      = statP d θ Pl / 2
  /-- `(eq:2fam-stationarity)`, third line (`∂_t`): with `dc = -dt/2`, `dδ = dt/2`,
  `de = dt/2`, `dξ₀ = -dt/(2h)` at fixed `(p, h)`. Same keys, residual `envelope_t`. -/
  envelope_t : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.t → 0 < θ.p → 0 < θ.ξ₀ → 0 < θ.v →
      0 < Pl → 0 < Pr →
    (-1 / θ.p + d / (2 * θ.t ^ 2) - d) + d * (-1 / (2 * θ.h))
        - ((envelopeCoeffs d θ Pl Pr).Ec * (-1 / 2) + (envelopeCoeffs d θ Pl Pr).Eδ / 2
            + (envelopeCoeffs d θ Pl Pr).Eξ₀ * (-1 / (2 * θ.h))
            + (envelopeCoeffs d θ Pl Pr).Ee / 2)
      = statT d θ Pl Pr
  /-- `(eq:2fam-stationarity)`, second line (`∂_h`): with `dξ₀ = -ξ₀ dh/h` at fixed `(t, p)`.
  Same keys, residual `envelope_h`. -/
  envelope_h : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.ξ₀ → 0 < θ.v → 0 < Pr →
    d * (-θ.ξ₀ / θ.h)
        - ((envelopeCoeffs d θ Pl Pr).Eξ₀ * (-θ.ξ₀ / θ.h) + (envelopeCoeffs d θ Pl Pr).Eh)
      = statH d θ Pr
  /-- `(eq:2fam-quadratures)`, second line: the three arc contributions to `Q_f` (contact
  integrals and the free-arc quadrature `d T_mid + log(P_r/P_ℓ) - C Y`, with
  `d T_mid = ξ_ℓ/P_ℓ - h ξ_r/P_r`) sum to `-log p - C Y - δ/p + e`. Ledger
  `fp_ext_k2_inverse_endpoint_algebra_20260913` (sympy), residual
  `total_gradient_endpoint_formula`; replay `fpm_repair_20260921_endpoint`. -/
  quadrature_Q_sum : ∀ p δ e h Pl Pr C Y : ℝ, 0 < p → 0 < Pl → 0 < Pr → h ≠ 0 →
    (Real.log (Pl / p) + δ * (1 / Pl - 1 / p))
        + ((Pl - δ) / Pl - h * ((Pr - e) / h) / Pr + Real.log (Pr / Pl) - C * Y)
        + (-Real.log Pr + e * (1 - 1 / Pr))
      = -Real.log p - C * Y - δ / p + e
  /-- Free-arc quadrature: along `P' = H`, `H' = -C P/ξ²`, the derivative of `ω = ξH/P` equals
  `-(ξH² - PH + CP²/ξ)/P²` (so `ω' = -d/P²` on the first integral). Same keys, residual
  `q_derivative_quadrature`. -/
  omega_derivative : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
    H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
      = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)
  /-- Free-arc quadrature of `Q_f`: `ξ(P'/P)² = (first integral)/P² + P'/P - C/ξ`. Same keys,
  residual `gradient_quadrature`. -/
  gradient_integrand : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
    ξ * H ^ 2 / P ^ 2 = (ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2 + H / P - C / ξ
  /-- `(eq:2fam-euler)`: the first integral `ξH² - PH + CP²/ξ` is constant along
  `P'' = -CP/ξ²` (its total derivative vanishes). Ledger
  `fp_ext_k2_shifted_clock_algebra_20260913` (sympy), residual `Euler_first_integral`. -/
  euler_first_integral : ∀ ξ P H C : ℝ, ξ ≠ 0 →
    (H ^ 2 - C * P ^ 2 / ξ ^ 2) + (-H + 2 * C * P / ξ) * H + (2 * ξ * H - P) * (-C * P / ξ ^ 2) = 0
  /-- `(eq:2fam-euler)`: the Euler–Lagrange expression `PH + ξ(PH' - H²) + first` vanishes when
  `H' = -CP/ξ²`. Same key, residual `Euler_equation_from_first_integral`. -/
  euler_from_first_integral : ∀ ξ P H C : ℝ, ξ ≠ 0 →
    P * H + ξ * (P * (-C * P / ξ ^ 2) - H ^ 2) + (ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) = 0
  /-- `(eq:2fam-multiplier)` on the initial contact: the multiplier density is
  `(δ + d)/(ξ + δ)²`. Same key, residual `left_contact_density`. -/
  left_contact_density : ∀ ξ δ d : ℝ, ξ + δ ≠ 0 →
    1 / (ξ + δ) + ξ * (0 / (ξ + δ) - 1 / (ξ + δ) ^ 2) + d / (ξ + δ) ^ 2 = (δ + d) / (ξ + δ) ^ 2
  /-- `(eq:2fam-multiplier)` on the final contact: the multiplier density is
  `(h e + d)/(hξ + e)²`. Same key, residual `right_contact_density`. -/
  right_contact_density : ∀ ξ h e d : ℝ, h * ξ + e ≠ 0 →
    h / (h * ξ + e) + ξ * (0 / (h * ξ + e) - h ^ 2 / (h * ξ + e) ^ 2) + d / (h * ξ + e) ^ 2
      = (h * e + d) / (h * ξ + e) ^ 2
  /-- `(eq:2fam-gap)`: pointwise gap density. Same key, residual `gap_density_identity`. -/
  gap_density : ∀ ξ P zp rp r d : ℝ, P ≠ 0 →
    ξ * ((zp + rp) ^ 2 - zp ^ 2) + d / P ^ 2 * (Real.exp (-2 * r) - 1)
      = ξ * rp ^ 2 + d / P ^ 2 * (Real.exp (-2 * r) - 1 + 2 * r) + 2 * ξ * zp * rp
        - 2 * d / P ^ 2 * r
  /-- Proof of `lem:2fam-cover`: `𝒟(u) = (u - 1/2)² + C - 1/4`. Ledger
  `fpm_repair_20260921_stationary_reverse_construction_algebra` (sympy), residual
  `quadratic_complete_square`; replay `fpm_repair_20260921_stationary_reconstruction_replay`. -/
  quadratic_complete_square : ∀ u C : ℝ, Elim.Dq C u = (u - 1 / 2) ^ 2 + C - 1 / 4
  /-- Reconstruction: with `ξ_q = -ξ/𝒟(q)` and `P² = dξ/𝒟(q)`, `(log P)_q = -q/𝒟(q)`. Same keys,
  residual `reconstructed_logP_q`. -/
  reconstructed_logP_q : ∀ q ξ C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    ((-ξ / Elim.Dq C q) / ξ - (2 * q - 1) / Elim.Dq C q) / 2 = -(q / Elim.Dq C q)
  /-- Reconstruction: `P_ξ = P_q/ξ_q = qP/ξ`. Same keys, residual `reconstructed_P_xi`. -/
  reconstructed_P_xi : ∀ q ξ P C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    (-q * P / Elim.Dq C q) / (-ξ / Elim.Dq C q) = q * P / ξ
  /-- Reconstruction: `P_ξξ = -CP/ξ²` (total `q`-derivative of `qP/ξ` divided by `ξ_q`). Same
  keys, residual `reconstructed_P_xixi`. -/
  reconstructed_P_xixi : ∀ q ξ P C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    (P / ξ + q / ξ * (-q * P / Elim.Dq C q) + (-q * P / ξ ^ 2) * (-ξ / Elim.Dq C q))
        / (-ξ / Elim.Dq C q) + C * P / ξ ^ 2 = 0
  /-- Reconstruction: `𝒟(q_ℓ) = d ξ_ℓ / P_ℓ²` with `q_ℓ = (P_ℓ - δ)/P_ℓ` and
  `C = (δ + d)(P_ℓ - δ)/P_ℓ²`. Same keys, residual `left_endpoint_D_identity`. -/
  left_endpoint_D : ∀ Pl δ d : ℝ, Pl ≠ 0 →
    Elim.Dq ((δ + d) * (Pl - δ) / Pl ^ 2) ((Pl - δ) / Pl) = d * (Pl - δ) / Pl ^ 2
  /-- Reconstruction: `ξ_r = q P_r / h = P_r² 𝒟(q)/d` with `P_r = e/(1-q)`,
  `h = d q(1-q)/(e 𝒟(q))`. Same keys, residual `right_endpoint_xi_identity`. -/
  right_endpoint_ξ : ∀ q e d C : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 → Elim.Dq C q ≠ 0 →
    q * (e / (1 - q)) / (d * q * (1 - q) / (e * Elim.Dq C q))
      = (e / (1 - q)) ^ 2 * Elim.Dq C q / d
  /-- Reconstruction: `h² ∂_h K = -v² h + 2(he + d) J = d(v²𝒟(q) - Cq²)/(e𝒟(q))` at the
  recovered `h`, `P_r`, with `e = 1 - v`. Same keys, residual `h_stationarity_numerator_factor`. -/
  h_stationarity : ∀ q v d C e hr Pr : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 → Elim.Dq C q ≠ 0 →
    e = 1 - v → hr = d * q * (1 - q) / (e * Elim.Dq C q) → Pr = e / (1 - q) →
    -v ^ 2 * hr + 2 * (hr * e + d) * (1 / Pr - 1 + e * (1 - 1 / Pr ^ 2) / 2)
      = d * (v ^ 2 * Elim.Dq C q - C * q ^ 2) / (e * Elim.Dq C q)
  /-- Reconstruction: when `v²𝒟(q) = Cq²`, `2 ∂_t K = -γ - v + (he+d)/h (P_r⁻² - 1)` equals
  `𝒜 = -γ + v(v-q)/(e(v+q))` at the recovered `h`, `P_r`, with `e = 1 - v`. Same keys, residual
  `t_stationarity_mod_quadratic`. -/
  t_stationarity : ∀ q v d C t p e hr Pr : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 →
    Elim.Dq C q ≠ 0 → v + q ≠ 0 → t ≠ 0 → p ≠ 0 →
    e = 1 - v → hr = d * q * (1 - q) / (e * Elim.Dq C q) → Pr = e / (1 - q) →
    v ^ 2 * Elim.Dq C q = C * q ^ 2 →
    -Elim.γ d t p - v + (hr * e + d) / hr * (1 / Pr ^ 2 - 1)
      = -Elim.γ d t p + v * (v - q) / (e * (v + q))
  /-- Reconstruction: `(t + d)/p² = (δ + d)/P_ℓ²` when `P_ℓ² = p²(δ + d)/(t + d)`. Same keys,
  residual `p_stationarity_from_Pl_definition`. -/
  p_stationarity : ∀ t p δ d : ℝ, p ≠ 0 → t + d ≠ 0 → δ + d ≠ 0 →
    (t + d) / p ^ 2 - (δ + d) / (p ^ 2 * (δ + d) / (t + d)) = 0
  /-- `(eq:2fam-affine-boundaries)`, left family: with `ξ₀ = 1 - δ`, `T = 1/p - 1` and
  `Q + log p = δ(1 - 1/p)`, the functionals are the displayed rational forms. Ledger
  `fp_ext_k2_straight_boundaries_073_20260913` (exact; the displayed forms are the script's
  `factor(M)`, `factor(G)`, stored in `affine_boundary_coefficients.json`). -/
  affine_left_closed_form : ∀ t p : ℝ, 0 < t → 0 < p →
    NF t * (aF t p + (1 / p - 1) - (1 - δF t p)) = affineML t p ∧
      2 + 2 * mF t * aF t p - NF t * (δF t p * (1 - 1 / p)) = affineGL t p
  /-- Same, right family: `h = (p - e)/c`, `ξ₀ = v/h`, `T = (1/p - 1)/h`, `Q + log p = e(1 - 1/p)`.
  Same key. -/
  affine_right_closed_form : ∀ t p : ℝ, 0 < t → t < 1 → (1 + t) / 2 < p →
    NF t * (aF t p + (1 / p - 1) / ((p - eF t) / cF t p) - vF t / ((p - eF t) / cF t p))
        = affineMR t p ∧
      2 + 2 * mF t * aF t p - NF t * (eF t * (1 - 1 / p)) = affineGR t p
  /-- Proof of `lem:2fam-realization`: `F_{1,f} L̄_{1,f} + H_{1,f} A_{1,f} = N_f` with
  `L̄ = 1/P`, `A = Nξ/P`, `F = N(P - ξH)`. Ledger `fp_ext_k2_shifted_clock_algebra_20260913`
  (sympy), residual `first_unit_equalizer`. -/
  first_unit_equalizer : ∀ ξ P H N : ℝ, P ≠ 0 →
    N * (P - ξ * H) / P + H * (N * ξ / P) = N
  /-- Proof of `lem:2fam-realization`: `dA_{1,f}/ds = F_{1,f}` in the curve coordinate
  (`ds/dξ = P⁻²`). Same key, residual `area_derivative_in_price`. -/
  area_derivative_in_price : ∀ ξ P H N : ℝ, P ≠ 0 →
    (N / P - N * ξ * H / P ^ 2) * P ^ 2 = N * (P - ξ * H)
  /-- Proof of `lem:2fam-realization`: `dF_{1,f}/dξ = -N ξ P''`. Same key, residual
  `seller_cdf_derivative`. -/
  seller_cdf_derivative : ∀ ξ H H' N : ℝ,
    N * H + (-(N * ξ)) * H' + (-N) * H = -(N * ξ * H')
  /-- Proof of `lem:2fam-realization`, prices `s ≤ a_f`: `m(2 + z̄ + a) = 2` with
  `z̄ = a + 1/p - 1`. Same key, residual `low_price_balance`. -/
  low_price_balance : ∀ t p : ℝ, 0 < t → 0 < p → mF t * (1 + 1 / p + 2 * aF t p) = 2
  /-- Proof of `lem:2fam-realization`, the seller law at `a_f`: `N(p - c) = m + m a p`. Same key,
  residual `initial_seller_atom`. -/
  initial_seller_atom : ∀ t p : ℝ, 0 < t → 0 < p →
    NF t * (p - cF t p) = mF t + mF t * aF t p * p
  /-- Proof of `lem:2fam-realization`, efficient gains: `F H P⁻² = N H/P - N ξ H²/P²`. Same key,
  residual `gain_density`. -/
  gain_density : ∀ ξ P H N : ℝ, P ≠ 0 →
    N * (P - ξ * H) * H / P ^ 2 = N * H / P - N * ξ * H ^ 2 / P ^ 2
  /-- Proof of `lem:2fam-realization`: the four price regions `s ≤ a`, `a < s < a + ε`,
  `a + ε ≤ s < b + ε`, `s ≥ b + ε` are exhaustive and disjoint. Ledger
  `fpm_repair_20260921_d1_price_regions` (z3, cvc5), check `price_partition`. -/
  realization_price_partition : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε →
    ¬ (z ≤ a ∧ b + ε ≤ z) ∧ ¬ (z ≤ a ∧ a + ε ≤ z ∧ z < b + ε) ∧
      ¬ (a < z ∧ b + ε ≤ z ∧ z < a + ε) ∧
      (z ≤ a ∨ b + ε ≤ z ∨ (a < z ∧ z < a + ε) ∨ (a + ε ≤ z ∧ z < b + ε))
  /-- Same key, check `middle_trace_is_half_open`. -/
  realization_middle_trace : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε → a + ε ≤ z → z < b + ε →
    a ≤ z - ε ∧ z - ε < b
  /-- Same key, check `only_tail_buys_in_terminal_region`. -/
  realization_tail_only : ∀ a b ε z w : ℝ, 0 ≤ a → a ≤ b → 0 < ε → b + ε ≤ z → w ≤ b → w < z
  /-- Same key, checks `second_seller_terminal_rejects_before_tail` and
  `second_buyer_body_rejects_middle`. -/
  realization_middle_rejects : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε →
    ((a < z ∧ z < a + ε) ∨ (a + ε ≤ z ∧ z < b + ε)) → z < b + ε ∧ a < z
  /-- Same key, check `second_unit_tail_only_low_mass_bound`. -/
  realization_low_mass : ∀ m η ε : ℝ, 0 ≤ m → m ≤ 1 → 0 ≤ η → 0 < ε → ε * η ≤ 1 →
    0 ≤ m * (1 - η * ε) ∧ m * (1 - η * ε) ≤ m
  /-- Same key, check `combined_tail_bound`. -/
  realization_combined_tail : ∀ η M₁ M₂ : ℝ, 0 ≤ η → 0 ≤ M₁ → 0 ≤ M₂ → 2 - η * (M₁ + M₂) ≤ 2
  /-- Proof of `lem:2fam-domain`, `∂_p C_f`: with `δ = (p+t)/2`, `C = (λ+δ)(z-δ)/z²` (`z = P_ℓ`)
  and `z' = z/p + z/(4(λ+δ))` (the `p`-derivative of `z` on `z²(λ+t) = p²(λ+δ)`), the total
  derivative `∂_p C + ∂_z C · z'`, written with the quotient rule, equals
  `((λ+t)/p³)(t + p/2 - z + zp/(4(λ+δ)))` on `z²(λ+t) = p²(λ+δ)`. The script checks that the
  numerator of the difference has remainder zero modulo `z²(λ+t) - p²(λ+δ)` as a polynomial in
  `z`; the field is that check evaluated where the denominators `z`, `p`, `λ+δ` do not vanish.
  Ledger `fp_ext_k2_branch_positive_factors_20260913` (exact), residual
  `C_p_mod_left_stationarity`; supplement `branch_positive_factors.json`. The ledger statement of
  this key claims more than its script checks (module docstring). -/
  branch_C_p : ∀ t p z lam : ℝ, z ≠ 0 → p ≠ 0 → lam + (p + t) / 2 ≠ 0 →
    z ^ 2 * (lam + t) = p ^ 2 * (lam + (p + t) / 2) →
    ((z - (p + t) / 2) / 2 - (lam + (p + t) / 2) / 2) / z ^ 2
        + (lam + (p + t) / 2) * (z ^ 2 - (z - (p + t) / 2) * (2 * z)) / (z ^ 2) ^ 2
          * (z / p + z / (4 * (lam + (p + t) / 2)))
      = (lam + t) / p ^ 3 * (t + p / 2 - z + z * p / (4 * (lam + (p + t) / 2)))
  /-- Proof of `lem:2fam-domain`: `t - (t + p/2 - z + zp/(4(λ+δ))) = (z-p)/2 + z(2λ+t)/(4(λ+δ))`,
  so the bracket of `∂_p C_f` is below `t` when `z > p` and `λ, t > 0`. Same key, residual
  `C_p_upper_positive_gap`. -/
  branch_C_p_gap : ∀ t p z lam : ℝ, lam + (p + t) / 2 ≠ 0 →
    t - (t + p / 2 - z + z * p / (4 * (lam + (p + t) / 2)))
      = (z - p) / 2 + z * (2 * lam + t) / (4 * (lam + (p + t) / 2))
  /-- Proof of `lem:2fam-domain`, `χ'_f`: with `f(q) = v(v-q)/(e(v+q))` and
  `C(q) = v²q(1-q)/(v²-q²)` (the equation for `q_r` solved for `C`), the ratio of their
  `q`-derivatives, written with the quotient rule, is `-2(v-q)²/(e(v²(1-2q) + q²))`. The script
  checks `factor(diff(f,q)/diff(C,q) - form) = 0`; the field evaluates it where the denominators do
  not vanish. Same key, residual `f_C_derivative`. -/
  branch_f_C : ∀ v q e : ℝ, e ≠ 0 → v ≠ 0 → v ^ 2 - q ^ 2 ≠ 0 →
    v ^ 2 * (1 - 2 * q) + q ^ 2 ≠ 0 →
    ((v * (-1) * (e * (v + q)) - v * (v - q) * e) / (e * (v + q)) ^ 2)
        / (((v ^ 2 * (1 - q) + v ^ 2 * q * (-1)) * (v ^ 2 - q ^ 2)
            - v ^ 2 * q * (1 - q) * (-2 * q)) / (v ^ 2 - q ^ 2) ^ 2)
      = -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2))
  /-- Proof of `lem:2fam-domain`: `-2(v-q)²/(e𝔡) + 2/e = 4vq(1-v)/(e𝔡)` with
  `𝔡 = v²(1-2q) + q²`. Same key, residual `f_C_lower_positive_gap`. -/
  branch_f_C_gap : ∀ v q e : ℝ, e ≠ 0 → v ^ 2 * (1 - 2 * q) + q ^ 2 ≠ 0 →
    -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)) + 2 / e
      = 4 * v * q * (1 - v) / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2))
  /-- Proof of `lem:2fam-domain`: `v²(1-2q) + q² = (v-q)² + 2vq(1-v)`. Same key, residual
  `f_C_positive_denominator`. -/
  branch_den : ∀ v q : ℝ, v ^ 2 * (1 - 2 * q) + q ^ 2 = (v - q) ^ 2 + 2 * v * q * (1 - v)
  /-- Proof of `lem:2fam-domain`, the case `∂_p C_f ≥ 0`: with `R_p = 1/p² + 2(λ+t)/p³ + f_C C_p`,
  `R_p = 1/p² + 2(λ+t)(e-t)/(e p³) + 2 slack/e + increment · C_p` for
  `slack = t(λ+t)/p³ - C_p` and `increment = f_C + 2/e`. The script declares `f_C` and `C_p` as
  positive sympy symbols, which does not affect this polynomial identity in them. Same key,
  residual `R_p_positive_decomposition`. -/
  branch_R_p : ∀ p lam t e fC Cp : ℝ, p ≠ 0 → e ≠ 0 →
    1 / p ^ 2 + 2 * (lam + t) / p ^ 3 + fC * Cp
      = 1 / p ^ 2 + 2 * (lam + t) * (e - t) / (e * p ^ 3) + 2 * (t * (lam + t) / p ^ 3 - Cp) / e
        + (fC + 2 / e) * Cp
  /-- Proof of `lem:2fam-domain`, exclusion of `t ≤ 1/5`: `-γ p² t²` at `p = 7t/4 + r` equals
  `λ(1-2t²) r² + t((7/2)λ(1-2t²) - t) r + t²((33-98t²)λ/16 - 11t/4)`. Same key, residual
  `small_t_large_p_exclusion`. -/
  branch_small_t_expansion : ∀ t lam r : ℝ, t ≠ 0 → 7 * t / 4 + r ≠ 0 →
    -Elim.γ lam t (7 * t / 4 + r) * (7 * t / 4 + r) ^ 2 * t ^ 2
      = lam * (1 - 2 * t ^ 2) * r ^ 2 + t * (7 / 2 * lam * (1 - 2 * t ^ 2) - t) * r
        + t ^ 2 * ((33 - 98 * t ^ 2) * lam / 16 - 11 * t / 4)
  /-- Proof of `lem:2fam-domain`: `43(λ+t) - 38(λ + 11t/8) = 5(λ - 37/100) + (37/4)(1/5 - t)`
  (for `P_ℓ/p ≤ √(43/38)`). Same key, residual `Pl_ratio_bound`. -/
  branch_Pl_ratio : ∀ lam t : ℝ,
    43 * (lam + t) - 38 * (lam + 11 * t / 8) = 5 * (lam - 37 / 100) + 37 / 4 * (1 / 5 - t)
  /-- Proof of `lem:2fam-domain`: `129λ - 74(λ+δ) = 55(λ - 37/100) + 74(11/40 - δ)` (for
  `λ/(λ+δ) ≥ 74/129`). Same key, residual `lambda_delta_ratio_bound`. -/
  branch_lambda_delta : ∀ lam δ : ℝ,
    129 * lam - 74 * (lam + δ) = 55 * (lam - 37 / 100) + 74 * (11 / 40 - δ)
  /-- Proof of `lem:2fam-domain`: at `C = (λ+δ)k(1-k)/δ` (`k = q_ℓ`),
  `v²𝒟(k) - Ck² = (k(1-k)/δ)(λv² - (λ+δ)k²)`, so the order `q_r < q_ℓ` fixes the sign of
  `λv² - (λ+δ)q_ℓ²`. Same key, residual `ordered_phase_mass_sign`. -/
  branch_ordered_phase : ∀ v k lam δ : ℝ, δ ≠ 0 →
    v ^ 2 * Elim.Dq ((lam + δ) * k * (1 - k) / δ) k - (lam + δ) * k * (1 - k) / δ * k ^ 2
      = k * (1 - k) / δ * (lam * v ^ 2 - (lam + δ) * k ^ 2)
  /-- Proof of `lem:2fam-domain`, the upper bound on `t`:
  `largeTBound t - largeTBound b₀ = (t - b₀)(1 + (3/8)(t + b₀)/(t² b₀²) + 2/((1+t)(1+b₀)))`
  with `b₀ = 421/1000`. Same key, residual `large_t_bound_increasing`. -/
  branch_large_t : ∀ t : ℝ, t ≠ 0 → 1 + t ≠ 0 →
    largeTBound t - largeTBound (421 / 1000)
      = (t - 421 / 1000) * (1 + 3 / 8 * (t + 421 / 1000) / (t ^ 2 * (421 / 1000) ^ 2)
        + 2 / ((1 + t) * (1 + 421 / 1000)))

end FixedPrice.TwoUnit.Family
