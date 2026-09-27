import FixedPrice.TwoUnit.Model

/-!
# The two-unit structured family: definitions

Definitions for Proposition `prop:2fam-optimum` of `manuscript/two_units.tex` and the family
appendix `manuscript/two_unit_family.tex`:

* the scalar parameters `(eq:2fam-parameters)`,
* the closed curve class `𝔉` of `(eq:2fam-class)` and the subclass with endpoint slopes `1, h_f`,
* the functionals `T_f, Q_f, M_f, G_f, R_f` of `(eq:2fam-functionals)`,
* the energy `E_f` and the comparison `K_f` of `(eq:2fam-comparison)`,
* the physical-time map and body laws `(eq:2fam-physical-time)`, `(eq:2fam-laws)`, and the buyer
  and seller body vector laws of the proof of `lem:2fam-realization` (common quantiles),
* the affine boundary functionals `(eq:2fam-affine-boundaries)`,
* the three outer stationarity expressions `(eq:2fam-stationarity)` and the quadratures
  `(eq:2fam-quadratures)`,
* the eliminated stationary system `(eq:2fam-algebraic)`, `(eq:2fam-connection)`,
  `(eq:2fam-recovery)` and the notion of a physical stationary point,
* the three-arc shape of `(eq:2fam-euler)`,
* rational concave polygons (Lemma `lem:2fam-witness`).

Conventions.
* A curve is a function `P : ℝ → ℝ`; only its values on `[c_f, ξ₀]` matter.
* The paper's `P'` is the almost-everywhere derivative of a concave curve; here it is `deriv P`,
  which agrees with it wherever `P` is differentiable (off a countable set). The right
  derivative `P'_+` of `(eq:2fam-laws)` is `derivWithin P (Ici ξ) ξ`.
* The trial ratio `β_f` enters through `d_f = (1 - β_f)/β_f` (`dOf`).
* No numerical fact is proved here; the machine-certified facts are hypotheses in
  `FixedPrice/TwoUnit/Family/Certificates.lean`.
-/

noncomputable section

open Set MeasureTheory Filter Function
open scoped Interval Topology ENNReal NNReal

namespace FixedPrice.TwoUnit.Family

/-! ### Scalar parameters `(eq:2fam-parameters)` -/

/-- `m_f = 2t/(1+t)`, the common initial seller mass. -/
def mF (t : ℝ) : ℝ := 2 * t / (1 + t)
/-- `N_f = 2/(1+t)`, the scale of the first seller CDF on the body. -/
def NF (t : ℝ) : ℝ := 2 / (1 + t)
/-- `c_f = (p - t)/2`, the left end of the curve interval. -/
def cF (t p : ℝ) : ℝ := (p - t) / 2
/-- `δ_f = (p + t)/2`, the intercept of the first obstacle `ξ + δ_f`. -/
def δF (t p : ℝ) : ℝ := (p + t) / 2
/-- `e_f = (1 + t)/2`, the intercept of the second obstacle `h_f ξ + e_f`. -/
def eF (t : ℝ) : ℝ := (1 + t) / 2
/-- `v_f = 1 - e_f`. -/
def vF (t : ℝ) : ℝ := 1 - eF t
/-- `a_f = c_f/(t p)`, the second buyer's body value and the first body's lower end. -/
def aF (t p : ℝ) : ℝ := cF t p / (t * p)
/-- `d_f = (1 - β_f)/β_f` for a trial ratio `β_f`. -/
def dOf (β : ℝ) : ℝ := (1 - β) / β

/-- The lower end `18227/25000` of the validated trial interval. -/
def βlo : ℝ := 18227 / 25000
/-- The upper end `729081/10⁶` of the validated trial interval. -/
def βhi : ℝ := 729081 / 10 ^ 6

/-- The outer parameter triple `(t_f, p_f, ξ₀)`. -/
structure Params where
  t : ℝ
  p : ℝ
  ξ₀ : ℝ

namespace Params

variable (θ : Params)

def m : ℝ := mF θ.t
def N : ℝ := NF θ.t
def c : ℝ := cF θ.t θ.p
def δ : ℝ := δF θ.t θ.p
def e : ℝ := eF θ.t
def v : ℝ := vF θ.t
def a : ℝ := aF θ.t θ.p
/-- `h_f = v_f/ξ₀`: the second obstacle passes through `(ξ₀, 1)`. -/
def h : ℝ := θ.v / θ.ξ₀

/-- The first affine obstacle `ξ + δ_f`. -/
def line₁ (ξ : ℝ) : ℝ := ξ + θ.δ
/-- The second affine obstacle `h_f ξ + e_f`. -/
def line₂ (ξ : ℝ) : ℝ := θ.h * ξ + θ.e
/-- The obstacle `U_f = min {ξ + δ_f, h_f ξ + e_f}` of `(eq:2fam-class)`. -/
def U (ξ : ℝ) : ℝ := min (θ.line₁ ξ) (θ.line₂ ξ)

/-- The parameter range of `(eq:2fam-parameters)`: `0 < t < 1`, `t ≤ p ≤ 1`, `ξ₀ > 0`, and the
requirement `ξ₀ ≥ c_f`. -/
structure Admissible : Prop where
  t_pos : 0 < θ.t
  t_lt_one : θ.t < 1
  t_le_p : θ.t ≤ θ.p
  p_le_one : θ.p ≤ 1
  ξ₀_pos : 0 < θ.ξ₀
  c_le_ξ₀ : θ.c ≤ θ.ξ₀

end Params

/-! ### The curve class `(eq:2fam-class)` -/

/-- `P ∈ 𝔉` at the parameters `θ`: a positive, concave, Lipschitz function on `[c_f, ξ₀]` with
`P(c_f) = p_f`, `P(ξ₀) = 1` and `P ≤ U_f`. The degenerate case `p_f = 1` is the single-point
interval `c_f = ξ₀`, which these conditions force. -/
structure InClass (θ : Params) (P : ℝ → ℝ) : Prop where
  admissible : θ.Admissible
  pos : ∀ ξ ∈ Icc θ.c θ.ξ₀, 0 < P ξ
  concave : ConcaveOn ℝ (Icc θ.c θ.ξ₀) P
  lipschitz : ∃ K : ℝ≥0, LipschitzOnWith K P (Icc θ.c θ.ξ₀)
  left_end : P θ.c = θ.p
  right_end : P θ.ξ₀ = 1
  obstacle : ∀ ξ ∈ Icc θ.c θ.ξ₀, P ξ ≤ θ.U ξ

/-- The subclass with endpoint slopes `1` at `c_f` and `h_f` at `ξ₀` (one-sided derivatives
within the curve interval). On the degenerate face `p_f = 1`, where `c_f = ξ₀` and the interval is
a single point, `HasDerivWithinAt` within a singleton holds for every value, so every degenerate
class member belongs to the subclass vacuously. This does not change `rFamSlopes`: degenerate
curves have `R_f = (1 + 3t²)/(1 + t)² ≥ 3/4`, above the family minimum. -/
def EndpointSlopes (θ : Params) (P : ℝ → ℝ) : Prop :=
  HasDerivWithinAt P 1 (Icc θ.c θ.ξ₀) θ.c ∧ HasDerivWithinAt P θ.h (Icc θ.c θ.ξ₀) θ.ξ₀

/-! ### Functionals `(eq:2fam-functionals)` -/

/-- `T_f = ∫_{c_f}^{ξ₀} P⁻²`. -/
def Tf (θ : Params) (P : ℝ → ℝ) : ℝ := ∫ ξ in θ.c..θ.ξ₀, (P ξ ^ 2)⁻¹

/-- `Q_f = ∫_{c_f}^{ξ₀} ξ (P'/P)²`. -/
def Qf (θ : Params) (P : ℝ → ℝ) : ℝ := ∫ ξ in θ.c..θ.ξ₀, ξ * (deriv P ξ / P ξ) ^ 2

/-- `M_f = N_f (a_f + T_f - ξ₀)`, the limiting seller welfare. -/
def Mf (θ : Params) (P : ℝ → ℝ) : ℝ := θ.N * (θ.a + Tf θ P - θ.ξ₀)

/-- `G_f = 2 + 2 m_f a_f - N_f log p_f - N_f Q_f`, the limiting efficient gains. -/
def Gf (θ : Params) (P : ℝ → ℝ) : ℝ :=
  2 + 2 * θ.m * θ.a - θ.N * Real.log θ.p - θ.N * Qf θ P

/-- `R_f = (M_f + 2)/(M_f + G_f)`, the welfare ratio of the family. -/
def Rf (θ : Params) (P : ℝ → ℝ) : ℝ := (Mf θ P + 2) / (Mf θ P + Gf θ P)

/-- `r_fam = inf_𝔉 R_f`. -/
def rFam : ℝ := sInf {r | ∃ θ P, InClass θ P ∧ Rf θ P = r}

/-- The infimum of `R_f` over the subclass with endpoint slopes `1, h_f`. -/
def rFamSlopes : ℝ := sInf {r | ∃ θ P, InClass θ P ∧ EndpointSlopes θ P ∧ Rf θ P = r}

/-! ### Energy and comparison `(eq:2fam-comparison)` -/

/-- `E_f(P) = ∫_{c_f}^{ξ₀} {ξ (log P)'² + d_f P⁻²}`. -/
def Ef (β : ℝ) (θ : Params) (P : ℝ → ℝ) : ℝ :=
  ∫ ξ in θ.c..θ.ξ₀, (ξ * deriv (fun x => Real.log (P x)) ξ ^ 2 + dOf β * (P ξ ^ 2)⁻¹)

/-- `K_f = (β G_f - (1-β) M_f - 2)/(β N_f)`, the first line of `(eq:2fam-comparison)`. -/
def Kf (β : ℝ) (θ : Params) (P : ℝ → ℝ) : ℝ :=
  (β * Gf θ P - (1 - β) * Mf θ P - 2) / (β * θ.N)

/-- The curve-independent part of the second line of `(eq:2fam-comparison)`:
`K_f = Kconst - E_f`. -/
def Kconst (β : ℝ) (θ : Params) : ℝ :=
  1 - θ.t / θ.p - Real.log θ.p - dOf β * θ.a - dOf β * (1 + θ.t) + dOf β * θ.ξ₀

/-- A global maximizer of `K_f` over the whole family (all parameters and curves). -/
def IsGlobalMaxK (β : ℝ) (θ : Params) (P : ℝ → ℝ) : Prop :=
  InClass θ P ∧ ∀ θ' P', InClass θ' P' → Kf β θ' P' ≤ Kf β θ P

/-- A global minimizer of `R_f` over the whole family. -/
def IsGlobalMinR (θ : Params) (P : ℝ → ℝ) : Prop :=
  InClass θ P ∧ ∀ θ' P', InClass θ' P' → Rf θ P ≤ Rf θ' P'

/-- A minimizer of `E_f` in the class at fixed parameters. -/
def IsEnergyMinimizer (β : ℝ) (θ : Params) (P : ℝ → ℝ) : Prop :=
  InClass θ P ∧ ∀ Q, InClass θ Q → Ef β θ P ≤ Ef β θ Q

/-! ### Physical time and body laws `(eq:2fam-physical-time)`, `(eq:2fam-laws)` -/

/-- `s_f(ξ) = a_f + ∫_{c_f}^{ξ} P⁻²`. -/
def sF (θ : Params) (P : ℝ → ℝ) (ξ : ℝ) : ℝ := θ.a + ∫ r in θ.c..ξ, (P r ^ 2)⁻¹

/-- `b_f = s_f(ξ₀)`, the upper end of the body. -/
def bF (θ : Params) (P : ℝ → ℝ) : ℝ := sF θ P θ.ξ₀

/-- The first buyer body survival at `s_f(ξ)`: `H_{1,f}(s_f(ξ)) = P'_+(ξ)`. -/
def bodySurvival (P : ℝ → ℝ) (ξ : ℝ) : ℝ := derivWithin P (Ici ξ) ξ

/-- The first seller CDF at `s_f(ξ)`: `F_{1,f}(s_f(ξ)) = N_f {P(ξ) - ξ P'_+(ξ)}`. -/
def bodySellerCDF (θ : Params) (P : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  θ.N * (P ξ - ξ * derivWithin P (Ici ξ) ξ)

/-! ### Body vector laws (the laws described after `(eq:2fam-laws)`)

The two body vector laws are built as images of the uniform law on `(0, 1)` under quantile
maps, which is the common-quantile construction of the proof of `lem:2fam-realization`. The
curve-coordinate distribution functions below are the displayed formulas; the quantile map needs
no monotonicity or right-continuity hypothesis to be defined, so the laws are defined for every
`P`. For a class member they are the laws the TeX describes (the quantile image of the uniform law
has the given distribution function when that function is nondecreasing, right-continuous, with
limits `0` and `1`), and `s_f` carries the curve coordinate to the value coordinate. -/

/-- The left-continuous generalized inverse `u ↦ inf {x | u ≤ G x}` of a distribution
function `G`. -/
def quantile (G : ℝ → ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ G x}

/-- The uniform law on `(0, 1)`. -/
def unifLaw : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- The distribution function of the first buyer body in the curve coordinate: `0` below `c_f`,
`1 - P'_+(ξ)` on `[c_f, ξ₀)`, and `1` from `ξ₀` on. Through `s_f` this is survival `1` below `a_f`
and `H_{1,f}(s_f(ξ)) = P'_+(ξ)` on the body (`(eq:2fam-laws)`); the jumps `1 - P'_+(c_f)` at `c_f`
and `lim_{ξ ↑ ξ₀} P'_+(ξ)` at `ξ₀` are the endpoint atoms that complete the survival function to a
probability law. -/
def buyerCurveCDF (θ : Params) (P : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  if ξ < θ.c then 0 else if ξ < θ.ξ₀ then 1 - bodySurvival P ξ else 1

/-- The distribution function of the first seller in the curve coordinate: `m_f` below `c_f`,
`N_f {P(ξ) - ξ P'_+(ξ)}` on `[c_f, ξ₀)` (`(eq:2fam-laws)`), and `1` from `ξ₀` on (completion to
mass one at `b_f`). The value `m_f` below `c_f` is the mass at `0` together with the constant
distribution function `m_f` on `(0, a_f)`, which lie below `s_f(c_f) = a_f`. -/
def sellerCurveCDF (θ : Params) (P : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  if ξ < θ.c then θ.m else if ξ < θ.ξ₀ then bodySellerCDF θ P ξ else 1

/-- The buyer body vector law: the law of `(Z₁, Z₂) = (s_f(Ξ), a_f)`, where `Ξ` has distribution
function `buyerCurveCDF θ P`. So `Z₁` has survival function `1` below `a_f`, `P'_+(ξ)` at `s_f(ξ)`
for `c_f ≤ ξ < ξ₀` and `0` from `b_f` on, and the second buyer body is the single value `a_f`, below
`Z₁`. -/
def buyerBodyLaw (θ : Params) (P : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  unifLaw.map fun u => (sF θ P (quantile (buyerCurveCDF θ P) u), θ.a)

/-- The seller body vector law: the common-quantile (comonotone) coupling of the first seller
`Y₁` (mass `m_f` at `0`, constant distribution function `m_f` on `(0, a_f)`, `(eq:2fam-laws)` on
the body, completed to mass one at `b_f`) and the second seller
`Y₂ = m_f δ_0 + (1 - m_f) δ_{b_f}`. At a uniform quantile `u ≤ m_f` both sellers are at `0`; for
`u > m_f`, `Y₁ = s_f(Ξ)` with `Ξ` drawn from `sellerCurveCDF θ P` and `Y₂ = b_f`. Equivalently,
`m_f δ_{(0,0)}` plus the law of `Y₁` restricted to `(0, ∞)` mapped by `y ↦ (y, b_f)`. -/
def sellerBodyLaw (θ : Params) (P : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  unifLaw.map fun u =>
    if u ≤ θ.m then ((0 : ℝ), (0 : ℝ))
    else (sF θ P (quantile (sellerCurveCDF θ P) u), bF θ P)

/-! ### Affine boundary functionals `(eq:2fam-affine-boundaries)` -/

/-- `M_{f,L}`: the curve lies on `ξ + δ_f` throughout. -/
def affineML (t p : ℝ) : ℝ :=
  (p ^ 2 * t + p * t ^ 2 - 4 * p * t + p + t) / (p * t * (1 + t))
/-- `G_{f,L}`. -/
def affineGL (t p : ℝ) : ℝ := (-p ^ 2 + p * t + 5 * p - t) / (p * (1 + t))
/-- `M_{f,R}`: the curve lies on `h_f ξ + e_f` throughout. -/
def affineMR (t p : ℝ) : ℝ :=
  (p - t) * (t - 1) * (p * t - 2 * p + 1) / (p * t * (1 + t) * (2 * p - t - 1))
/-- `G_{f,R}`. -/
def affineGR (t p : ℝ) : ℝ := (p * t + 3 * p - t + 1) / (p * (1 + t))

/-- The two entirely affine curves. -/
def EntirelyAffine (θ : Params) (P : ℝ → ℝ) : Prop :=
  (∀ ξ ∈ Icc θ.c θ.ξ₀, P ξ = θ.line₁ ξ) ∨ (∀ ξ ∈ Icc θ.c θ.ξ₀, P ξ = θ.line₂ ξ)

/-! ### The three-arc shape `(eq:2fam-euler)` -/

/-- `P` consists of an initial affine contact `[c_f, ξ_ℓ]` on `ξ + δ_f` (possibly of zero
length), one strictly concave free interval `(ξ_ℓ, ξ_r)` on which
`P'' + (C/ξ²) P = 0` and `d = ξ P'² - P P' + C P²/ξ` with a constant `C > 0`, and a final
affine contact `[ξ_r, ξ₀]` on `h_f ξ + e_f` (possibly of zero length). At a contact point
interior to `[c_f, ξ₀]` the curve is differentiable with the obstacle slope (smooth fit, proof of
`lem:2fam-shape`, "Contact and curvature"). -/
structure ThreeArc (d : ℝ) (θ : Params) (P : ℝ → ℝ) (ξl ξr C : ℝ) : Prop where
  c_le : θ.c ≤ ξl
  l_lt_r : ξl < ξr
  r_le : ξr ≤ θ.ξ₀
  C_pos : 0 < C
  left_contact : ∀ ξ ∈ Icc θ.c ξl, P ξ = θ.line₁ ξ
  right_contact : ∀ ξ ∈ Icc ξr θ.ξ₀, P ξ = θ.line₂ ξ
  fit_left : θ.c < ξl → HasDerivAt P 1 ξl
  fit_right : ξr < θ.ξ₀ → HasDerivAt P θ.h ξr
  smooth : ContDiffOn ℝ 2 P (Ioo ξl ξr)
  euler : ∀ ξ ∈ Ioo ξl ξr, deriv (deriv P) ξ + C / ξ ^ 2 * P ξ = 0
  first_integral : ∀ ξ ∈ Ioo ξl ξr,
    d = ξ * deriv P ξ ^ 2 - P ξ * deriv P ξ + C * P ξ ^ 2 / ξ
  strictConcave : StrictConcaveOn ℝ (Icc ξl ξr) P

/-! ### Outer stationarity `(eq:2fam-stationarity)` and quadratures `(eq:2fam-quadratures)` -/

/-- `2 ∂_{p_f} K_f = (t+d)/p² - (δ+d)/P_ℓ²`. -/
def statP (d : ℝ) (θ : Params) (Pl : ℝ) : ℝ :=
  (θ.t + d) / θ.p ^ 2 - (θ.δ + d) / Pl ^ 2

/-- `∂_{h_f} K_f = -ξ₀² h + 2(h e + d)/h² {P_r⁻¹ - 1 + (e/2)(1 - P_r⁻²)}`. -/
def statH (d : ℝ) (θ : Params) (Pr : ℝ) : ℝ :=
  -θ.ξ₀ ^ 2 * θ.h + 2 * (θ.h * θ.e + d) / θ.h ^ 2 * (Pr⁻¹ - 1 + θ.e / 2 * (1 - (Pr ^ 2)⁻¹))

/-- `∂_{t_f} K_f = -1/(2p) + d/(2t²) - d - (δ+d)/(2P_ℓ²) - ξ₀ h/2 + (h e + d)/(2h) (P_r⁻² - 1)`. -/
def statT (d : ℝ) (θ : Params) (Pl Pr : ℝ) : ℝ :=
  -1 / (2 * θ.p) + d / (2 * θ.t ^ 2) - d - (θ.δ + d) / (2 * Pl ^ 2) - θ.ξ₀ * θ.h / 2
    + (θ.h * θ.e + d) / (2 * θ.h) * ((Pr ^ 2)⁻¹ - 1)

/-- `T_f` of a three-arc curve, first line of `(eq:2fam-quadratures)`, with
`P_ℓ = ξ_ℓ + δ_f`, `P_r = h_f ξ_r + e_f`, `q_ℓ = ξ_ℓ/P_ℓ`, `q_r = h_f ξ_r/P_r`. -/
def quadT (d : ℝ) (θ : Params) (ξl ξr : ℝ) : ℝ :=
  θ.p⁻¹ - (θ.line₁ ξl)⁻¹ + (ξl / θ.line₁ ξl - θ.h * ξr / θ.line₂ ξr) / d
    + ((θ.line₂ ξr)⁻¹ - 1) / θ.h

/-- `Q_f` of a three-arc curve, second line of `(eq:2fam-quadratures)`. -/
def quadQ (θ : Params) (ξl ξr C : ℝ) : ℝ :=
  -Real.log θ.p - C * Real.log (ξr / ξl) - θ.δ / θ.p + θ.e

/-- `G_f` of a three-arc curve, third line of `(eq:2fam-quadratures)`. -/
def quadG (θ : Params) (ξl ξr C : ℝ) : ℝ :=
  3 - θ.m + θ.m * θ.a + θ.N * C * Real.log (ξr / ξl)

/-! ### The eliminated stationary system `(eq:2fam-algebraic)`–`(eq:2fam-recovery)` -/

namespace Elim

variable (d t p : ℝ)

/-- `P_ℓ = p √((δ+d)/(t+d))`. -/
def Pl : ℝ := p * Real.sqrt ((δF t p + d) / (t + d))
/-- `ξ_ℓ = P_ℓ - δ`. -/
def ξl : ℝ := Pl d t p - δF t p
/-- `C_f = (δ+d) ξ_ℓ / P_ℓ²`. -/
def C : ℝ := (δF t p + d) * ξl d t p / Pl d t p ^ 2
/-- `q_ℓ = ξ_ℓ/P_ℓ`. -/
def qL : ℝ := ξl d t p / Pl d t p
/-- `q_r`: the root in `(0, v)` of `v²(q² - q + C) = C q²`, in the closed form evaluated by the
supplement (`physical_conditions.json`, `verify.py`). -/
def qR : ℝ :=
  2 * vF t * C d t p / (vF t + Real.sqrt (vF t ^ 2 - 4 * (vF t ^ 2 - C d t p) * C d t p))
/-- `γ_f = -d/t² + 2d + 1/p + (t+d)/p²`. -/
def γ : ℝ := -d / t ^ 2 + 2 * d + 1 / p + (t + d) / p ^ 2
/-- The algebraic residual `𝒜_f(t,p) = -γ_f + v(v - q_r)/(e(v + q_r))`. -/
def algResidual : ℝ := -γ d t p + vF t * (vF t - qR d t p) / (eF t * (vF t + qR d t p))
/-- `𝒟_f(u) = u² - u + C`. -/
def Dq (C u : ℝ) : ℝ := u ^ 2 - u + C
/-- `ℐ_f = ∫_{q_r}^{q_ℓ} du/𝒟_f(u)`. -/
def connI : ℝ := ∫ u in qR d t p..qL d t p, (Dq (C d t p) u)⁻¹
/-- The connection residual `ℱ_f(t,p)` of `(eq:2fam-connection)`. -/
def connection : ℝ :=
  Real.log ((1 - qR d t p) / (1 - qL d t p))
    + 1 / 2 * Real.log (Dq (C d t p) (qL d t p) / Dq (C d t p) (qR d t p))
    + connI d t p / 2 - Real.log (eF t / δF t p)
/-- Recovered slope `h_f = d q_r (1 - q_r)/(e 𝒟(q_r))`. -/
def h : ℝ := d * qR d t p * (1 - qR d t p) / (eF t * Dq (C d t p) (qR d t p))
/-- Recovered `P_r = e/(1 - q_r)`. -/
def Pr : ℝ := eF t / (1 - qR d t p)
/-- Recovered `ξ_r = q_r P_r / h_f`. -/
def ξr : ℝ := qR d t p * Pr d t p / h d t p
/-- Recovered `ξ₀ = v/h_f`. -/
def ξ₀ : ℝ := vF t / h d t p
/-- The recovered parameter triple. -/
def params : Params := ⟨t, p, ξ₀ d t p⟩

/-- The discriminant under the square root in `qR`. -/
def disc : ℝ := vF t ^ 2 - 4 * (vF t ^ 2 - C d t p) * C d t p

/-- `ℐ_f` in the closed form evaluated by the covers when `C > 1/4`:
`(arctan((q_ℓ - 1/2)/w) - arctan((q_r - 1/2)/w))/w`, `w = √(C - 1/4)` (`verify.py`, `states`). -/
def connJ : ℝ :=
  (Real.arctan ((qL d t p - 1 / 2) / Real.sqrt (C d t p - 1 / 4))
      - Real.arctan ((qR d t p - 1 / 2) / Real.sqrt (C d t p - 1 / 4)))
    / Real.sqrt (C d t p - 1 / 4)

/-- The connection residual with `ℐ_f` in the arctan form (`verify.py`, `states`). -/
def connectionArctan : ℝ :=
  Real.log ((1 - qR d t p) / (1 - qL d t p))
    + (Real.log (Dq (C d t p) (qL d t p) / Dq (C d t p) (qR d t p)) + connJ d t p) / 2
    - Real.log (eF t / δF t p)

/-- `T_f` from `(eq:2fam-quadratures)` with the eliminated contact data (`verify.py`). -/
def T : ℝ := 1 / p - 1 / Pl d t p + (qL d t p - qR d t p) / d + (1 / Pr d t p - 1) / h d t p
/-- `M_f = N(a + T - v/h)` with the eliminated data (`verify.py`). -/
def M : ℝ := NF t * (aF t p + T d t p - vF t / h d t p)
/-- `G_f = 3 - m + m a + N C ℐ` with `ℐ` in the arctan form (`verify.py`). -/
def GJ : ℝ := 3 - mF t + mF t * aF t p + NF t * C d t p * connJ d t p
/-- `β G_f - (1-β) M_f - 2` at the eliminated point, as evaluated by the covers. -/
def comparisonJ (β : ℝ) : ℝ := β * GJ (dOf β) t p - (1 - β) * M (dOf β) t p - 2

end Elim

/-- A physical stationary point (text before Lemma `lem:2fam-domain`): the eliminated system
holds, the recovery formulas `(eq:2fam-recovery)` satisfy `c < ξ_ℓ < ξ_r < ξ₀`,
`0 < q_r < q_ℓ < 1`, `𝒟 > 0` on `[q_r, q_ℓ]`, and they produce a curve in `(eq:2fam-class)`:
a class member at the recovered parameters with the three-arc shape and these contact data.

This strengthens the TeX notion. The TeX asks only that the formulas "produce a curve in
`(eq:2fam-class)`" with the stated orders. The clause `curve` also asks for the `ThreeArc`
conditions at the recovered contact data: the two affine contacts, `C_f > 0`, `C²` regularity and
the Euler equation `P'' + C_f P/ξ² = 0` on the free interval, the first integral, strict
concavity, and smooth fit at `ξ_ℓ` and `ξ_r`. All of these are consequences of the reconstruction
in the proof of `lem:2fam-cover` ("Reconstructing the curve": `P' = uP/ξ`,
`P'' = -C_f P/ξ² < 0`, `P'(ξ_ℓ) = 1`, `P'(ξ_r) = h_f`, the curve continuously differentiable),
so the curve the formulas produce satisfies them. The strengthening makes the existence half of
`CoverStatement` and the hypothesis of `DomainStatement`'s first conjunct stronger, and the
uniqueness half of `CoverStatement` weaker; since the recovered curve is unique and satisfies all
the clauses, the difference is harmless. -/
structure PhysStationary (d t p : ℝ) : Prop where
  t_pos : 0 < t
  t_lt_p : t < p
  p_lt_one : p < 1
  alg : Elim.algResidual d t p = 0
  conn : Elim.connection d t p = 0
  c_lt_ξl : cF t p < Elim.ξl d t p
  ξl_lt_ξr : Elim.ξl d t p < Elim.ξr d t p
  ξr_lt_ξ₀ : Elim.ξr d t p < Elim.ξ₀ d t p
  qR_pos : 0 < Elim.qR d t p
  qR_lt_qL : Elim.qR d t p < Elim.qL d t p
  qL_lt_one : Elim.qL d t p < 1
  D_pos : ∀ u ∈ Icc (Elim.qR d t p) (Elim.qL d t p), 0 < Elim.Dq (Elim.C d t p) u
  curve : ∃ P, InClass (Elim.params d t p) P ∧
    ThreeArc d (Elim.params d t p) P (Elim.ξl d t p) (Elim.ξr d t p) (Elim.C d t p)

/-! ### Rational concave polygons (Lemma `lem:2fam-witness`) -/

/-- The parameter triple is rational. -/
def Params.IsRational (θ : Params) : Prop := ∃ t p ξ₀ : ℚ, θ.t = t ∧ θ.p = p ∧ θ.ξ₀ = ξ₀

/-- `P` is a rational concave polygon on `[a, b]`: the endpoints `a` and `b` are rational and, on
`[a, b]`, `P` is the minimum of finitely many affine functions with rational coefficients. Its
vertices are then rational: the endpoints `(a, P a)`, `(b, P b)` and every breakpoint, which is
the intersection of two rational lines. Conversely, a concave piecewise-linear function with
rational vertices is the minimum of the lines through consecutive vertices, which are rational.
So this is exactly "a concave polygon with rational vertices". -/
def IsRationalConcavePolygon (P : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∃ a' b' : ℚ, a = a' ∧ b = b') ∧
    ∃ (n : ℕ) (k l : Fin (n + 1) → ℚ), ∀ ξ ∈ Icc a b,
      P ξ = Finset.univ.inf' Finset.univ_nonempty (fun j => (k j : ℝ) * ξ + l j)

/-- Finite polygon data with rational vertices `(X j, Y j)`, `j = 0, …, n + 1` (so segments
`j = 0, …, n`), and rational parameters, as stored in
`extension_screen_20260913/continuation/results/polygon_witness.json` and
`manuscript/supplement/general_instance.json` (there, `n + 1 = 130` segments). -/
structure PolygonData where
  n : ℕ
  X : ℕ → ℚ
  Y : ℕ → ℚ
  t : ℚ
  p : ℚ
  ξ₀ : ℚ

namespace PolygonData

variable (D : PolygonData)

def params : Params := ⟨D.t, D.p, D.ξ₀⟩

/-- Slope of segment `j`. -/
def slope (j : ℕ) : ℚ := (D.Y (j + 1) - D.Y j) / (D.X (j + 1) - D.X j)

/-- The polygon as the minimum of its segment lines (equal to the interpolant for concave
data). -/
def curve (ξ : ℝ) : ℝ :=
  (Finset.range (D.n + 1)).inf' Finset.nonempty_range_add_one
    (fun j => (D.slope j : ℝ) * (ξ - D.X j) + D.Y j)

/-- The rational checks of `polygon_witness.py`: vertices ordered, positive ordinates, endpoint
values `p` and `1` at `c_f` and `ξ₀`, slopes nonincreasing in `(0, 1]`, first slope `1`, last
slope `h_f`, and parameters with `0 < t < p < 1`. -/
structure Valid : Prop where
  X_strictMono : ∀ j ≤ D.n, D.X j < D.X (j + 1)
  Y_pos : ∀ j ≤ D.n + 1, 0 < D.Y j
  X_zero : D.X 0 = (D.p - D.t) / 2
  Y_zero : D.Y 0 = D.p
  X_last : D.X (D.n + 1) = D.ξ₀
  Y_last : D.Y (D.n + 1) = 1
  slope_first : D.slope 0 = 1
  slope_last : D.slope D.n = (1 - (1 + D.t) / 2) / D.ξ₀
  slope_antitone : ∀ j < D.n, D.slope (j + 1) ≤ D.slope j
  slope_pos : ∀ j ≤ D.n, 0 < D.slope j
  t_pos : 0 < D.t
  t_lt_one : D.t < 1
  t_lt_p : D.t < D.p
  p_lt_one : D.p < 1

/-- Physical length of segment `j`: `(X_{j+1} - X_j)/(Y_j Y_{j+1})`. -/
def ds (j : ℕ) : ℚ := (D.X (j + 1) - D.X j) / (D.Y j * D.Y (j + 1))

/-- `N_f = 2/(1+t)`, rational. -/
def Nq : ℚ := 2 / (1 + D.t)
/-- `m_f = 2t/(1+t)`, rational. -/
def mq : ℚ := 2 * D.t / (1 + D.t)
/-- `a_f = c_f/(t p)`, rational. -/
def aq : ℚ := ((D.p - D.t) / 2) / (D.t * D.p)

/-- `M_f` by exact segment integration. -/
def segmentM : ℚ := D.Nq * (D.aq + ∑ j ∈ Finset.range (D.n + 1), D.ds j - D.ξ₀)
/-- `G_f` by exact segment integration:
`2 + 2 m a + Σ_j N (Y_j - X_j H_j) H_j ds_j`. -/
def segmentG : ℚ :=
  2 + 2 * D.mq * D.aq
    + ∑ j ∈ Finset.range (D.n + 1), D.Nq * (D.Y j - D.X j * D.slope j) * D.slope j * D.ds j
/-- `R_f` by exact segment integration. -/
def segmentRatio : ℚ := (D.segmentM + 2) / (D.segmentM + D.segmentG)

end PolygonData

end FixedPrice.TwoUnit.Family
