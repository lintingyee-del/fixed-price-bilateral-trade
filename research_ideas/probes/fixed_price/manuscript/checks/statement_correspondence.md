# TeX / Lean source correspondence

Source correspondence only; no automatic semantic-equivalence verdict.

Source mode: exported TeX excerpts; use --tex-dir to compare a new manuscript.

Quantifiers, assumptions, definitions, equality cases and certificate hypotheses require semantic review. Source lookup success does not establish equivalence.

The JSON companion contains the full excerpts, expanded statements and certificate structures.

## sec:model

Printed source: paper.tex:183

```tex
\section{Model and the scalar curve}\label{sec:model}
```

[hasDerivAt_optimalValue](../../lean/FixedPrice/ScalarCurve.lean#L82)

```lean
theorem hasDerivAt_optimalValue {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt optimalValue
      (((2 * C - 1) * primitive C (endParameter C) + 8 * C - 6) / (4 * C - 1)) C
```

[optimalValue_strictAntiOn](../../lean/FixedPrice/ScalarCurve.lean#L119)

```lean
theorem optimalValue_strictAntiOn : StrictAntiOn optimalValue (Ioo (1 / 4 : ℝ) (1 / 2))
```

[initialState_strictMonoOn](../../lean/FixedPrice/ScalarCurve.lean#L142)

```lean
theorem initialState_strictMonoOn : StrictMonoOn initialState (Ioo (1 / 4 : ℝ) (1 / 2))
```

[optimalValue_tendsto_left](../../lean/FixedPrice/FrontierCurve.lean#L205)

```lean
theorem optimalValue_tendsto_left : Tendsto optimalValue (𝓝[>] (1 / 4)) atTop
```

[existsUnique_optimalValue_eq](../../lean/FixedPrice/FrontierCurve.lean#L400)

```lean
theorem existsUnique_optimalValue_eq {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃! C : ℝ, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ optimalValue C = β⁻¹
```

## thm:exact

Printed source: paper.tex:895

```tex
\begin{theoremA}[Exact welfare guarantee]\label{thm:exact}
Let \(V_s,V_b\) be independent nonnegative values with \(0<\mathbb E\max\{V_s,V_b\}<\infty\). A fixed price trades when \(V_s\le z\le V_b\). Its optimal universal welfare guarantee is
\[
\inf_{F_s,F_b}\max_{z\ge0}
\frac{\mathbb EV_s+\mathbb E[(V_b-V_s)\mathbf1_{\{V_s\le z\le V_b\}}]}
{\mathbb E\max\{V_s,V_b\}}
=\beta_*\approx0.73802.
\]
The constant is \(\beta_*=[C_*(2+\mathcal I(C_*))]^{-1}\), where \(C_*\) is the unique root in \((1/4,1/2)\) of
\begin{equation}
\begin{aligned}
C(2+\mathcal I(C))&=1+\frac{C^2}{1-2C}e^{-\mathcal I(C)/2},\\
\mathcal I(C)&=\frac{1}{\sqrt{C-1/4}}
\left[\arctan\frac{1-3C}{2(1-C)\sqrt{C-1/4}}
+\arctan\frac{1}{2\sqrt{C-1/4}}\right].
\end{aligned}
\label{eq:rootintro}
\end{equation}
Every pair has ratio strictly greater than \(\beta_*\). For every \(\varepsilon>0\), the explicit bounded family in Lemma~\ref{lem:hard} contains a pair with ratio below \(\beta_*+\varepsilon\).
\end{theoremA}
```

[theoremA](../../lean/FixedPrice/TheoremA.lean#L118)

```lean
theorem theoremA {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) :
    (∀ μs μb : Measure ℝ, AdmissiblePair μs μb → (optimalValue C)⁻¹ < fixedPriceRatio μs μb) ∧
    (∀ ε > 0, ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧
      (∀ᵐ s ∂μs, s ∈ Icc (0 : ℝ) 1) ∧ (∃ R : ℝ, ∀ᵐ b ∂μb, b ∈ Icc (0 : ℝ) R) ∧
      fixedPriceRatio μs μb < (optimalValue C)⁻¹ + ε) ∧
    IsGLB {r | ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧ fixedPriceRatio μs μb = r}
      (optimalValue C)⁻¹
```

[existsUnique_root](../../lean/FixedPrice/ScalarCurve.lean#L220)

```lean
theorem existsUnique_root :
    ∃! C : ℝ, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ optimalValue C = 1 + initialState C
```

## thm:frontier

Printed source: paper.tex:286

```tex
\begin{theoremB}[Sharp affine and conditional GFT guarantees]\label{thm:frontier}
The scalar curve \eqref{eq:4} gives the entire frontier:
\begin{equation}
\beta(C)=\frac1{S(C)},\qquad
\delta(\beta(C))=\frac{\tau(C)}{S(C)},
\qquad \frac14<C<\frac12.
\label{eq:47}
\end{equation}
Every coefficient smaller than \(\delta(\beta)\) is refuted by a bounded hard pair of independent distributions.

The function \(\delta\) is strictly increasing and strictly convex on \((0,1)\). Its derivative ranges from zero to infinity.

With \(u=1-2C\), the map
\begin{equation}
\kappa(C)=\frac{\tau(C)(S(C)+u)}u
\label{eq:51}
\end{equation}
is a strictly increasing bijection from \((1/4,1/2)\) onto \((0,\infty)\), and
\begin{equation}
\rho(\kappa(C))
=\frac1{S(C)+u}
=\frac1{1+C\mathcal I(C)}.
\label{eq:52}
\end{equation}
Equivalently, extending \(\delta\) by \(+\infty\) outside \((0,1)\) for the purpose of conjugation,
\begin{equation}
\kappa\rho(\kappa)=\delta^*(\kappa)
:=\sup_{0<\beta<1}\{\kappa\beta-\delta(\beta)\}.
\label{eq:53}
\end{equation}
For each fixed \(\kappa\), bounded hard pairs with exactly \(G/M=\kappa\) approach \eqref{eq:52}.

\end{theoremB}
```

[theoremB_affine](../../lean/FixedPrice/FrontierAffine.lean#L115)

```lean
theorem theoremB_affine (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (δ : ℝ) :
    AffineValid (optimalValue C)⁻¹ δ ↔ initialState C / optimalValue C ≤ δ
```

[frontierDelta_eq](../../lean/FixedPrice/FrontierAffine.lean#L180)

```lean
theorem frontierDelta_eq (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    frontierDelta (optimalValue C)⁻¹ = initialState C / optimalValue C
```

[frontierDelta_strictMonoOn](../../lean/FixedPrice/FrontierConvex.lean#L132)

```lean
theorem frontierDelta_strictMonoOn : StrictMonoOn frontierDelta (Ioo (0 : ℝ) 1)
```

[frontierDelta_strictConvexOn](../../lean/FixedPrice/FrontierConvex.lean#L140)

```lean
theorem frontierDelta_strictConvexOn : StrictConvexOn ℝ (Ioo (0 : ℝ) 1) frontierDelta
```

[frontierDelta_deriv_image](../../lean/FixedPrice/FrontierConvex.lean#L149)

```lean
theorem frontierDelta_deriv_image :
    (fun β => deriv frontierDelta β) '' Ioo (0 : ℝ) 1 = Ioi 0
```

[kappaOf_strictMonoOn](../../lean/FixedPrice/FrontierCurve.lean#L104)

```lean
theorem kappaOf_strictMonoOn : StrictMonoOn kappaOf (Ioo (1 / 4 : ℝ) (1 / 2))
```

[existsUnique_kappaOf_eq](../../lean/FixedPrice/FrontierCurve.lean#L421)

```lean
theorem existsUnique_kappaOf_eq {κ : ℝ} (hκ : 0 < κ) :
    ∃! C : ℝ, C ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ kappaOf C = κ
```

[theoremB_conditional](../../lean/FixedPrice/FrontierConditional.lean#L305)

```lean
theorem theoremB_conditional (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    IsGLB (condRatioSet (kappaOf C)) (optimalValue C + (1 - 2 * C))⁻¹
```

[condRatio_eq](../../lean/FixedPrice/FrontierConditional.lean#L411)

```lean
theorem condRatio_eq (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    condRatio (kappaOf C) = (1 + C * scalarI C)⁻¹
```

[theoremB_conjugate](../../lean/FixedPrice/FrontierConvex.lean#L165)

```lean
theorem theoremB_conjugate {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) :
    IsGreatest {x | ∃ β ∈ Ioo (0 : ℝ) 1, x = kappaOf C * β - frontierDelta β}
      (kappaOf C * condRatio (kappaOf C))
```

## cor:asymptotics

Printed source: paper.tex:320

```tex
\begin{corollaryB}[Endpoint asymptotics]\label{cor:asymptotics}
The sharp curves satisfy
\begin{equation}
\begin{aligned}
\delta(\beta)&\sim\frac e8\,\beta e^{-2/\beta}
&&(\beta\downarrow0),&
\delta(\beta)&\sim\frac1{4(1-\beta)}
&&(\beta\uparrow1),\\
\rho(\kappa)&\sim\frac2{\log(1/\kappa)}
&&(\kappa\downarrow0),&
1-\rho(\kappa)&\sim\frac1{\sqrt\kappa}
&&(\kappa\to\infty).
\end{aligned}
\label{eq:55}
\end{equation}
\end{corollaryB}
```

[frontierDelta_isEquivalent_zero](../../lean/FixedPrice/Asymptotics.lean#L443)

```lean
theorem frontierDelta_isEquivalent_zero :
    frontierDelta ~[𝓝[>] 0] fun β => Real.exp 1 / 8 * β * Real.exp (-2 / β)
```

[frontierDelta_isEquivalent_one](../../lean/FixedPrice/Asymptotics.lean#L473)

```lean
theorem frontierDelta_isEquivalent_one :
    frontierDelta ~[𝓝[<] 1] fun β => 1 / (4 * (1 - β))
```

[condRatio_isEquivalent_zero](../../lean/FixedPrice/Asymptotics.lean#L488)

```lean
theorem condRatio_isEquivalent_zero :
    condRatio ~[𝓝[>] 0] fun κ => 2 / Real.log (1 / κ)
```

[condRatio_isEquivalent_top](../../lean/FixedPrice/Asymptotics.lean#L522)

```lean
theorem condRatio_isEquivalent_top :
    (fun κ => 1 - condRatio κ) ~[atTop] fun κ => 1 / Real.sqrt κ
```

## lem:energy

Printed source: paper.tex:352

```tex
\begin{lemma}[energy representation]\label{lem:energy}
For every \(d>0\), a measurable \(h:[0,1]\to[0,1]\) induces through \eqref{eq:11} an absolutely continuous \(p\) with
\begin{equation}
p'(A(t))=h(t)\quad\text{a.e.},\qquad
p(a)\le \min\{x+a,1/d\},\qquad
\frac1{d+1}\le x\le\frac1d,
\label{eq:12}
\end{equation}
and satisfies
\begin{equation}
\mathcal J_d(h)-1=\mathcal F_d[p]
:=-\log(dx)+\int_0^\infty
\left[d^2-p^{-2}-a((\log p)')^2\right]\,\mathrm da.
\tag{E}\label{eq:13}
\end{equation}
\end{lemma}
```

[reciprocalState_hasDerivAt_at_tailTime](../../lean/FixedPrice/Reciprocal.lean#L262)

```lean
theorem reciprocalState_hasDerivAt_at_tailTime {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hder : HasDerivAt (state d h) (h t) t) :
    HasDerivAt (reciprocalState d h) (h t) (tailTime d h t)
```

[reciprocalState_bounds](../../lean/FixedPrice/Reciprocal.lean#L217)

```lean
theorem reciprocalState_bounds {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) (a : ℝ) :
    (d + 1)⁻¹ ≤ reciprocalState d h a ∧ reciprocalState d h a ≤ d⁻¹
```

[reciprocalState_line_obstacle](../../lean/FixedPrice/Reciprocal.lean#L421)

```lean
theorem reciprocalState_line_obstacle {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d) (hi : IntervalIntegrable h volume 0 1)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    {a : ℝ} (ha : 0 ≤ a) : reciprocalState d h a ≤ reciprocalState d h 0 + a
```

[reciprocal_energy_identity_extended](../../lean/FixedPrice/Reciprocal.lean#L506)

```lean
theorem reciprocal_energy_identity_extended {d R : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1)
    (hR : tailTime d h 0 ≤ R) :
    objective d h - 1 = logEnergy d R (fun a => Real.log (reciprocalState d h a))
```

[objective_originalTime_identity](../../lean/FixedPrice/Controls.lean#L197)

```lean
theorem objective_originalTime_identity {d : ℝ} {h : ℝ → ℝ}
    (hd : 0 < d)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    objective d h = Real.log (state d h 1) - Real.log d +
      d ^ 2 * tailTime d h 0 - ∫ t in (0 : ℝ)..1, tailTime d h t * h t ^ 2
```

## lem:reference

Printed source: paper.tex:437

```tex
\begin{lemma}[reference curves for every endpoint]\label{lem:reference}
For \(d>0\), there is \(\bar C(d)>1/4\) such that \(Y_d\) from \eqref{eq:14} exists uniquely on \(0<C<\bar C(d)\). The map \(C\mapsto x(C)\) is a continuous strictly decreasing bijection from this interval onto \((0,1/d)\). For each such endpoint, using the contact data \eqref{eq:15}, the function
\begin{equation}
\begin{gathered}
P_x(a)=
\begin{cases}
x+a,&0\le a\le a_e,\\
\text{the middle arc below},&a_e\le a\le a_a,\\
1/d,&a\ge a_a,
\end{cases}\\[4pt]
a(r)=\frac C{d^2}e^{-\mathcal I_C(r)},\quad
P_x(a(r))=\frac{e^{-\mathcal I_C(r)/2}}{d\sqrt{D_C(r)}}
\quad(0\le r\le Y_d(C))
\end{gathered}
\label{eq:16}
\end{equation}
is continuously differentiable and lies below both obstacles in \eqref{eq:12}. The function
\begin{equation}
Q_x=P_x^{-2}+\bigl(a(\log P_x)'\bigr)'
\label{eq:17}
\end{equation}
has no atoms and is given almost everywhere by
\begin{equation}
Q_x(a)=
\begin{cases}
(1+x)/(x+a)^2,&0<a<a_e,\\
0,&a_e<a<a_a,\\
d^2,&a>a_a.
\end{cases}
\label{eq:18}
\end{equation}
\end{lemma}
```

[local_contact_branch_exists](../../lean/FixedPrice/BranchRegularity.lean#L148)

```lean
theorem local_contact_branch_exists {C y : ℝ} (hy : 0 < y)
    (hD : ∀ r ∈ Icc (0 : ℝ) y, 0 < denominator C r) :
    ∃ Y : ℝ → ℝ, Y C = y ∧
      HasDerivAt Y ((y ^ 3 + y * denominator C y * secondPrimitive C y) / 2) C ∧
      (∀ᶠ x in 𝓝 C, contactLog x (Y x) = contactLog C y) ∧
      (∀ᶠ q : ℝ × ℝ in 𝓝 (C, y), contactLog q.1 q.2 = contactLog C y ↔ Y q.1 = q.2)
```

[hasBranchRoot_of_le](../../lean/FixedPrice/GlobalBranch.lean#L129)

```lean
theorem hasBranchRoot_of_le {d C C' : ℝ} (hd : 0 < d) (hC' : 0 < C') (hle : C' ≤ C)
    (h : HasBranchRoot d C) : HasBranchRoot d C'
```

[hasBranchRoot_eventually](../../lean/FixedPrice/GlobalBranch.lean#L225)

```lean
theorem hasBranchRoot_eventually {d C : ℝ} (h : HasBranchRoot d C) :
    ∀ᶠ C' in 𝓝 C, HasBranchRoot d C'
```

[exists_branch_point](../../lean/FixedPrice/Coverage.lean#L60)

```lean
theorem exists_branch_point {d D : ℝ} (hd : 0 < d) (hD : D ∈ Ioo (0 : ℝ) 1)
    (hdD : d * (1 - D) < D) :
    ∃ C y : ℝ, 0 < C ∧ IsBranchRoot d C y ∧ denominator C y = D
```

[IsBranchRoot.contact_line](../../lean/FixedPrice/ReferenceCurve.lean#L456)

```lean
theorem IsBranchRoot.contact_line (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo 0 (lineEnd C Y)) :
    Real.exp (-2 * refLog d C Y a) + deriv (refWeight d C Y) a =
      (1 + lineIntercept C Y) / (lineIntercept C Y + a) ^ 2
```

[IsBranchRoot.contact_arc](../../lean/FixedPrice/ReferenceCurve.lean#L469)

```lean
theorem IsBranchRoot.contact_arc (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : a ∈ Ioo (lineEnd C Y) (capStart d C)) :
    Real.exp (-2 * refLog d C Y a) + deriv (refWeight d C Y) a = 0
```

[IsBranchRoot.contact_cap](../../lean/FixedPrice/ReferenceCurve.lean#L496)

```lean
theorem IsBranchRoot.contact_cap (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {a : ℝ} (ha : capStart d C < a) :
    Real.exp (-2 * refLog d C Y a) + deriv (refWeight d C Y) a = d ^ 2
```

[IsBranchRoot.logEnergy_refLog](../../lean/FixedPrice/ReferenceEnergy.lean#L192)

```lean
theorem IsBranchRoot.logEnergy_refLog (hd : 0 < d) (hC : 0 < C) (hY : IsBranchRoot d C Y)
    {R : ℝ} (hR : capStart d C ≤ R) :
    logEnergy d R (refLog d C Y) = endpointValue C Y
```

## lem:gaps

Printed source: paper.tex:554

```tex
\begin{lemma}[nonnegative gaps]\label{lem:gaps}
For \(p\) from \eqref{eq:11} and the notation \eqref{eq:23}, the fixed-endpoint gap is
\begin{equation}
\Phi_d(x)-\mathcal F_d[p]
=\int_0^\infty
\left[
a(v')^2+\frac{e^{-2v}-1+2v}{P_x^2}-2Q_xv
\right]\,\mathrm da\ \ge0.
\tag{G1}\label{eq:24}
\end{equation}
It vanishes exactly when \(p=P_x\). The endpoint envelope has a unique maximum at \(C=C_d\), and
\begin{equation}
\begin{aligned}
\Phi_d(x(C))&=C\mathcal I_C(Y_d(C))-\frac{C^2Y_d(C)}{1-CY_d(C)},\\
\frac{\mathrm d}{\mathrm dC}\Phi_d(x(C))
&=-\frac{(Y_d(C)+U_d(C))\mathcal B_d(C)}{(1-CY_d(C))^2},\\
\Phi_d(x(C_d))-\Phi_d(x(C))
&=\int_{\min\{C,C_d\}}^{\max\{C,C_d\}}
\frac{(Y_d(u)+U_d(u))|\mathcal B_d(u)|}
{(1-uY_d(u))^2}\,\mathrm du.
\end{aligned}
\tag{G2}\label{eq:25}
\end{equation}
\end{lemma}
```

[logEnergy_gap_identity_weight](../../lean/FixedPrice/CalibrationAE.lean#L15)

```lean
theorem logEnergy_gap_identity_weight {d R : ℝ} {ell v w : ℝ → ℝ}
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval w 0 R)
    (hw_ae : ∀ᵐ a, a ∈ Ι (0 : ℝ) R → w a = a * deriv ell a)
    (hellSq : IntervalIntegrable (fun a => a * (deriv ell a) ^ 2) volume 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R)
    (hv0 : v 0 = 0) (hvR : v R = 0) :
    logEnergy d R ell - logEnergy d R (fun a => ell a + v a) =
      ∫ a in 0..R, gapIntegrand ell v
        (fun a => Real.exp (-2 * ell a) + deriv w a) a
```

[logEnergy_le_of_weight_calibration](../../lean/FixedPrice/CalibrationAE.lean#L84)

```lean
theorem logEnergy_le_of_weight_calibration {d R : ℝ} {ell v w : ℝ → ℝ} (hR : 0 ≤ R)
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval w 0 R)
    (hw_ae : ∀ᵐ a, a ∈ Ι (0 : ℝ) R → w a = a * deriv ell a)
    (hellSq : IntervalIntegrable (fun a => a * (deriv ell a) ^ 2) volume 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R)
    (hv0 : v 0 = 0) (hvR : v R = 0)
    (hc : ∀ᵐ a, a ∈ Icc (0 : ℝ) R →
      (Real.exp (-2 * ell a) + deriv w a) * v a ≤ 0) :
    logEnergy d R (fun a => ell a + v a) ≤ logEnergy d R ell
```

[eqOn_zero_of_weight_calibration](../../lean/FixedPrice/CalibrationAE.lean#L123)

```lean
theorem eqOn_zero_of_weight_calibration {d R : ℝ} {ell v w : ℝ → ℝ} (hR : 0 < R)
    (hell : AbsolutelyContinuousOnInterval ell 0 R)
    (hv : AbsolutelyContinuousOnInterval v 0 R)
    (hw : AbsolutelyContinuousOnInterval w 0 R)
    (hw_ae : ∀ᵐ a, a ∈ Ι (0 : ℝ) R → w a = a * deriv ell a)
    (hellSq : IntervalIntegrable (fun a => a * (deriv ell a) ^ 2) volume 0 R)
    (hvSq : IntervalIntegrable (fun a => a * (deriv v a) ^ 2) volume 0 R)
    (hv0 : v 0 = 0) (hvR : v R = 0)
    (hc : ∀ᵐ a, a ∈ Icc (0 : ℝ) R →
      (Real.exp (-2 * ell a) + deriv w a) * v a ≤ 0)
    (heq : logEnergy d R (fun a => ell a + v a) = logEnergy d R ell) :
    EqOn v (fun _ => 0) (Icc 0 R)
```

[hasDerivAt_endpointValue](../../lean/FixedPrice/EndpointDerivative.lean#L86)

```lean
theorem hasDerivAt_endpointValue {Y : ℝ → ℝ} {C Y' d : ℝ}
    (hY : HasDerivAt Y Y' C) (hy : 0 < Y C) (hline : C * Y C < 1)
    (hD : ∀ r ∈ Icc (0 : ℝ) (Y C), 0 < denominator C r)
    (hcontact : ∀ᶠ x in 𝓝 C, contactLog x (Y x) = Real.log d) :
    HasDerivAt (fun x => endpointValue x (Y x))
      (-((Y C + contactWeight C (Y C)) / (1 - C * Y C) ^ 2) * branchDefect C (Y C)) C
```

[physicalEndpoint_calibration](../../lean/FixedPrice/PhysicalBranch.lean#L84)

```lean
theorem physicalEndpoint_calibration {Y : ℝ → ℝ} {d Cstar Cbar : ℝ}
    (hd : 0 < d) (hstar : Cstar ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState Cstar = d) (hbar : Cstar < Cbar)
    (hphysical : ∀ C ∈ Ioo (0 : ℝ) Cbar,
      0 < Y C ∧ C * Y C < 1 ∧
      (∀ r ∈ Icc (0 : ℝ) (Y C), 0 < denominator C r) ∧ contactLog C (Y C) = Real.log d)
    {C : ℝ} (hC : C ∈ Ioo (0 : ℝ) Cbar) :
    endpointValue Cstar (Y Cstar) - endpointValue C (Y C) =
      ∫ u in min C Cstar..max C Cstar,
        (Y u + contactWeight u (Y u)) * |branchDefect u (Y u)| / (1 - u * Y u) ^ 2 ∧
    endpointValue C (Y C) ≤ endpointValue Cstar (Y Cstar) ∧
      (endpointValue C (Y C) = endpointValue Cstar (Y Cstar) ↔ C = Cstar)
```

[endpointValue_branch_le](../../lean/FixedPrice/GlobalBranch.lean#L250)

```lean
theorem endpointValue_branch_le {d Cstar C : ℝ} (hd : 0 < d)
    (hstar : Cstar ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState Cstar = d)
    (hC : 0 < C) (h : HasBranchRoot d C) :
    endpointValue C (branchRoot d C) ≤ endpointValue Cstar (endParameter Cstar)
```

## thm:calibration

Printed source: paper.tex:686

```tex
\begin{theoremC}[Global bound and maximizing control]\label{thm:calibration}
Let \(d>0\), let \(h:[0,1]\to[0,1]\) be measurable, and let \(C_d\in(1/4,1/2)\) satisfy \(\tau(C_d)=d\). Set \(x=(d+\int_0^1h(t)\,\mathrm dt)^{-1}\). For \(x<1/d\), let \(C\in(0,\bar C(d))\) be the unique solution of \(D_C(Y_d(C))=(1+x)^{-1}\); for \(x=1/d\), set \(C=0\) and \(P_x\equiv1/d\). With the reciprocal state \(p\), reference curve \(P_x\), and logarithmic difference \(v\) from \eqref{eq:11}, \eqref{eq:16}, and \eqref{eq:23}, respectively,
\begin{equation}
\begin{aligned}
S(C_d)-\mathcal J_d(h)
={}&\int_{\min\{C,C_d\}}^{\max\{C,C_d\}}
\frac{(Y_d(u)+U_d(u))|\mathcal B_d(u)|}
{(1-uY_d(u))^2}\,\mathrm du\\
&+\int_0^\infty
\left[
a(v')^2+\frac{e^{-2v}-1+2v}{P_x^2}-2Q_xv
\right]\,\mathrm da
\ \ge0.
\end{aligned}
\tag{G}\label{eq:29}
\end{equation}
Consequently,
\begin{equation}
\max_{0\le h\le1}\mathcal J_d(h)=S(C_d).
\label{eq:30}
\end{equation}
The maximizing control is unique up to equality almost everywhere. It has a zero arc of length \(C_d\), a strictly increasing arc of length \((1-2C_d)/(1-C_d)\), and a one arc of length \(C_d^2/(1-C_d)\). On the middle arc,
\begin{equation}
t=C_d(1+y),\qquad
g(t)=d\sqrt{D_{C_d}(y)}\,e^{\mathcal I_{C_d}(y)/2},\qquad
h(t)=\frac{y\,g(t)}{D_{C_d}(y)},\qquad 0\le y\le y_e(C_d).
\label{eq:31}
\end{equation}
\end{theoremC}
```

[theoremC](../../lean/FixedPrice/TheoremC.lean#L28)

```lean
theorem theoremC {d C : ℝ} (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) :
    AEStronglyMeasurable (maximizingControl d C) (volume.restrict (Icc 0 1)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, maximizingControl d C t ∈ Icc (0 : ℝ) 1) ∧
    objective d (maximizingControl d C) = optimalValue C ∧
    StrictMonoOn (maximizingControl d C) (Ioo C (C * (1 + endParameter C))) ∧
    ∀ h : ℝ → ℝ,
      AEStronglyMeasurable h (volume.restrict (Icc 0 1)) →
      (∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) →
      objective d h ≤ optimalValue C ∧
        (objective d h = optimalValue C ↔
          h =ᵐ[volume.restrict (Icc 0 1)] maximizingControl d C)
```

[objective_le_optimalValue](../../lean/FixedPrice/UpperBound.lean#L265)

```lean
theorem objective_le_optimalValue {d C : ℝ} (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hinit : initialState C = d) {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    objective d h ≤ optimalValue C
```

[maximizingControl_attains](../../lean/FixedPrice/Attainment.lean#L436)

```lean
theorem maximizingControl_attains {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) :
    objective d (maximizingControl d C) = optimalValue C
```

[objective_eq_optimalValue_iff](../../lean/FixedPrice/Uniqueness.lean#L270)

```lean
theorem objective_eq_optimalValue_iff {d C : ℝ} (hd : 0 < d)
    (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hinit : initialState C = d) {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    objective d h = optimalValue C ↔
      h =ᵐ[volume.restrict (Icc 0 1)] maximizingControl d C
```

## prop:nonexponential

Printed source: paper.tex:747

```tex
\begin{proposition}[No exponential subarc]\label{prop:nonexponential}
For \(d>0\), let \(h\) be the maximizing control of Theorem~\ref{thm:calibration}, represented by \eqref{eq:31} on its middle arc. There is no nonempty open subinterval of that arc on which \(h(t)=\lambda_0+\lambda_1e^{\lambda_2t}\) for real constants \(\lambda_0,\lambda_1,\lambda_2\) with \(h'>0\).
\end{proposition}
```

[proposition_nonexponential](../../lean/FixedPrice/NoExponential.lean#L34)

```lean
theorem proposition_nonexponential (hd : 0 < d) (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ Ioo C (C * (1 + endParameter C))) :
    ¬ ∃ l₀ l₁ l₂ : ℝ, ∀ t ∈ Ioo a b, maximizingControl d C t = l₀ + l₁ * Real.exp (l₂ * t)
```

## lem:pricing

Printed source: paper.tex:766

```tex
\begin{lemma}[pricing from the variational bound]\label{lem:pricing}
Let \(0<\beta<1\) and \(d>0\). If
\begin{equation}
\beta\sup_{0\le h\le1}\mathcal J_d(h)\le1,
\label{eq:35}
\end{equation}
then every independent pair of finite-mean distributions admits a price with
\begin{equation}
\Gamma(z)\ge \beta G-\beta d M.
\label{eq:36}
\end{equation}
\end{lemma}
```

[exists_price_of_variational_bound](../../lean/FixedPrice/PricingLemma.lean#L421)

```lean
theorem exists_price_of_variational_bound {β d : ℝ} (hβ : 0 ≤ β) (hd : 0 < d)
    (hJ : ∀ h : ℝ → ℝ, AEStronglyMeasurable h (volume.restrict (Icc 0 1)) →
      (∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) → β * objective d h ≤ 1)
    (hs0 : ∀ᵐ s ∂μs, 0 ≤ s)
    (hsint : Integrable (fun s => s) μs) (hbint : Integrable (fun b => b) μb) :
    ∃ z : ℝ, 0 ≤ z ∧
      β * gainsFromTrade μs μb - β * d * sellerMean μs ≤ gain μs μb z
```

## lem:hard

Printed source: paper.tex:821

```tex
\begin{lemma}[bounded hard pairs]\label{lem:hard}
Let \(H:[0,1]\to[0,1]\) be continuous and nonincreasing, with \(H(1)=\eta>0\), and let \(d>0\). Extend \(H\) to a buyer survival function by keeping it equal to \(\eta\) on \([1,R_\eta)\), where \(R_\eta=1+d/\eta\), and setting it to zero at and above \(R_\eta\). Include an atom of size \(1-H(0)\) at zero if needed. Using the tail integral \(L\), define the auxiliary integral \(T\) and seller CDF \(F_s\) by
\begin{equation}
L(s)=d+\int_s^1H(u)\,\mathrm du,\qquad
T(s)=\int_0^sL(u)^{-2}\,\mathrm du,
\qquad
F_s(s)=d\bigl(L(s)^{-1}-H(s)T(s)\bigr)\quad(0\le s<1),
\label{eq:39}
\end{equation}
and complete \(F_s\) with an atom at one. This is a valid seller CDF. With
\(T_\eta=T(1)\) and \(J_\eta=\mathcal J_d(H(1-\cdot))\), the pair satisfies
\begin{equation}
M_\eta=1-d^2T_\eta,\qquad
\Gamma_{\max,\eta}=d+\eta d^2T_\eta,\qquad
G_\eta=d+dJ_\eta-d^3T_\eta.
\label{eq:40}
\end{equation}
In particular, for every \(\beta\),
\begin{equation}
\Gamma_{\max,\eta}-\beta G_\eta+\beta dM_\eta
=d(1-\beta J_\eta)+\eta d^2T_\eta.
\label{eq:41}
\end{equation}
\end{lemma}
```

[HardPairData.sellerMean_eq](../../lean/FixedPrice/HardPair.lean#L149)

```lean
theorem HardPairData.sellerMean_eq (P : HardPairData d η H) :
    sellerMean P.sellerLaw = 1 - d ^ 2 * timeT d H 1
```

[HardPairData.gainsFromTrade_eq](../../lean/FixedPrice/HardPair.lean#L250)

```lean
theorem HardPairData.gainsFromTrade_eq (P : HardPairData d η H) :
    gainsFromTrade P.sellerLaw P.buyerLaw =
      d * objective d (cutControl P.buyerLaw 1) + d * sellerMean P.sellerLaw
```

[HardPairData.gain_le](../../lean/FixedPrice/HardPair.lean#L200)

```lean
theorem HardPairData.gain_le (P : HardPairData d η H) (z : ℝ) :
    gain P.sellerLaw P.buyerLaw z ≤ d + η * (d ^ 2 * timeT d H 1)
```

[HardPairData.welfare_gap_le](../../lean/FixedPrice/HardPair.lean#L298)

```lean
theorem HardPairData.welfare_gap_le (P : HardPairData d η H) {β : ℝ} (hβ : β * (1 + d) = 1)
    (z : ℝ) :
    (sellerMean P.sellerLaw + gain P.sellerLaw P.buyerLaw z) -
        β * (sellerMean P.sellerLaw + gainsFromTrade P.sellerLaw P.buyerLaw) ≤
      d * (1 - β * objective d (cutControl P.buyerLaw 1)) + η * (d ^ 2 * timeT d H 1)
```

## lem:smoothing

Printed source: paper.tex:1050

```tex
\begin{lemma}[smoothing bounded hard pairs]\label{lem:smoothing}
An independent pair supported on \([0,\Lambda]\) has independent absolutely continuous approximations with full support on \((0,\Lambda)\) for which first-best welfare converges and the limit superior of best fixed-price welfare is at most the original optimum.
\end{lemma}
```

[lemma_smoothing](../../lean/FixedPrice/Smoothing.lean#L524)

```lean
theorem lemma_smoothing {Λ : ℝ} (hΛ : 0 < Λ) {μs μb : Measure ℝ}
    [IsProbabilityMeasure μs] [IsProbabilityMeasure μb]
    (hs : ∀ᵐ s ∂μs, s ∈ Icc 0 Λ) (hb : ∀ᵐ b ∂μb, b ∈ Icc 0 Λ) {η : ℝ} (hη : 0 < η) :
    ∃ μs' μb' : Measure ℝ, IsProbabilityMeasure μs' ∧ IsProbabilityMeasure μb' ∧
      μs' ≪ volume ∧ μb' ≪ volume ∧
      (∀ᵐ s ∂μs', s ∈ Ioo 0 Λ) ∧ (∀ᵐ b ∂μb', b ∈ Ioo 0 Λ) ∧
      |firstBest (μs'.prod μb') - (sellerMean μs + gainsFromTrade μs μb)| ≤ η ∧
      ∀ z : ℝ, jointPriceWelfare (μs'.prod μb') z ≤
        sellerMean μs + (⨆ z : Ici (0 : ℝ), gain μs μb z) + η
```

## lem:representation

Printed source: paper.tex:1080

```tex
\begin{proposition}[Price representation under absolutely continuous priors]\label{lem:representation}
Fix a common report interval \((0,\Lambda)\), where \(\Lambda>0\). For every measurable, risk-neutral DSIC mechanism with realizationwise individual rationality and strong budget balance, there is a positive Borel measure \(\nu\) on \((0,\Lambda)\) of mass \(m\le1\) such that its allocation probability \(\varphi\) and expected transfer \(\Pi\) satisfy
\begin{equation}
\varphi(s,b)=\nu((s,b]),\qquad
\Pi(s,b)=\int_{(s,b]}z\,\nu(\mathrm dz)
\quad\text{for Lebesgue-a.e. }0<s<b<\Lambda.
\label{eq:56}
\end{equation}
Under any absolutely continuous joint prior on this report square, its expected welfare is at most that of the best deterministic price.
\end{proposition}
```

[DSICOn.representation](../../lean/FixedPrice/Mechanism.lean#L657)

```lean
theorem DSICOn.representation (M : DSICOn Λ φ pay) :
    ∃ F : ℝ → ℝ, MonotoneOn F (Ioo 0 Λ) ∧ (∀ x ∈ Ioo 0 Λ, F x ∈ Icc (0 : ℝ) 1) ∧
      ∃ E : Set ℝ, E.Countable ∧
        (∀ s ∈ Ioo 0 Λ, s ∉ E → ∀ b ∈ Ioo 0 Λ, s < b →
          φ s b = F b - F s ∧ pay s b = b * (F b - F s) - ∫ t in s..b, (F t - F s)) ∧
        (∀ s ∈ Ioo 0 Λ, ∀ b ∈ Ioo 0 Λ, b < s → φ s b = 0 ∧ pay s b = 0)
```

[DSICOn.mechWelfare_le](../../lean/FixedPrice/MechanismWelfare.lean#L94)

```lean
theorem DSICOn.mechWelfare_le (M : DSICOn Λ φ pay)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    (hsupp : ∀ᵐ p ∂μ, p ∈ Ioo 0 Λ ×ˢ Ioo 0 Λ) :
    mechWelfare μ φ ≤ ⨆ z : ℝ, jointPriceWelfare μ z
```

## cor:dsic

Printed source: paper.tex:1093

```tex
\begin{corollary}[exact dominant-strategy guarantee]\label{cor:dsic}
For the independent-prior model of Section~\ref{sec:model} and measurable mechanisms on the common nonnegative real report domain, suppose traders are risk neutral, truthfulness is dominant in expected lottery payoffs, and individual rationality and strong budget balance hold in every realization. The optimal universal welfare guarantee, allowing full prior information, is \(\beta_*\).
\end{corollary}
```

[corollary_dsic](../../lean/FixedPrice/CorollaryDSIC.lean#L170)

```lean
theorem corollary_dsic {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) :
    (∀ μs μb : Measure ℝ, AdmissiblePair μs μb → (optimalValue C)⁻¹ < dsicRatio μs μb) ∧
    (∀ ε > 0, ∃ Λ : ℝ, 0 < Λ ∧ ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧
      μs ≪ volume ∧ μb ≪ volume ∧ (∀ᵐ s ∂μs, s ∈ Ioo 0 Λ) ∧ (∀ᵐ b ∂μb, b ∈ Ioo 0 Λ) ∧
      ∀ φ pay : ℝ → ℝ → ℝ, DSICOn Λ φ pay →
        mechWelfare (μs.prod μb) φ < ((optimalValue C)⁻¹ + ε) * firstBest (μs.prod μb)) ∧
    IsGLB {r | ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧ dsicRatio μs μb = r}
      (optimalValue C)⁻¹
```

[dsic_guarantee](../../lean/FixedPrice/DSICClass.lean#L151)

```lean
theorem dsic_guarantee {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) {μs μb : Measure ℝ}
    (A : AdmissiblePair μs μb) :
    ∃ z : ℝ, 0 ≤ z ∧ DSICNonneg (fpAlloc z) (fpPay z) ∧ Measurable (uncurry (fpAlloc z)) ∧
      (optimalValue C)⁻¹ * firstBest (μs.prod μb) < mechWelfare (μs.prod μb) (fpAlloc z)
```

[dsic_ceiling](../../lean/FixedPrice/CorollaryDSIC.lean#L20)

```lean
theorem dsic_ceiling {C : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) {ε : ℝ} (hε : 0 < ε) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ μs μb : Measure ℝ, AdmissiblePair μs μb ∧ μs ≪ volume ∧ μb ≪ volume ∧
      (∀ᵐ s ∂μs, s ∈ Ioo 0 Λ) ∧ (∀ᵐ b ∂μb, b ∈ Ioo 0 Λ) ∧
      ∀ φ pay : ℝ → ℝ → ℝ, DSICOn Λ φ pay →
        mechWelfare (μs.prod μb) φ < ((optimalValue C)⁻¹ + ε) * firstBest (μs.prod μb)
```

## thm:two-separation

Printed source: two_units.tex:26

```tex
\begin{theoremD}[Two units are strictly harder]\label{thm:two-separation}
There are independent, finitely supported laws of strictly positive
ordered buyer and seller vectors for which every common price has
welfare ratio less than \(0.7290804\).
There is also a symmetric such instance with ratio less than \(0.83693\).
Consequently
\[
r_2^*<0.7290804<0.738024<\beta_*,
\qquad r_{2,\mathrm{sym}}^*<0.83693.
\]
\end{theoremD}
```

[theoremD_general](../../lean/FixedPrice/TwoUnit/TheoremD.lean#L23)

```lean
theorem theoremD_general :
    ValidInstance generalB generalS ∧ 0 < opt2 generalB generalS ∧
      (∀ z : ℝ, (mean2 generalS + gain2 generalB generalS z) / opt2 generalB generalS <
        7290804 / 10 ^ 7) ∧
      ∃ c : ℝ, c < 7290804 / 10 ^ 7 ∧ ∀ z : ℝ,
        (mean2 generalS + gain2 generalB generalS z) / opt2 generalB generalS ≤ c
```

[theoremD_symmetric](../../lean/FixedPrice/TwoUnit/TheoremD.lean#L65)

```lean
theorem theoremD_symmetric :
    symmetricB = symmetricS.map (fun p => ((p.1.2, p.1.1), p.2)) ∧
    ValidInstance symmetricB symmetricS ∧ 0 < opt2 symmetricB symmetricS ∧
      (∀ z : ℝ, (mean2 symmetricS + gain2 symmetricB symmetricS z) / opt2 symmetricB symmetricS <
        83693 / 10 ^ 5) ∧
      ∃ c : ℝ, c < 83693 / 10 ^ 5 ∧ ∀ z : ℝ,
        (mean2 symmetricS + gain2 symmetricB symmetricS z) / opt2 symmetricB symmetricS ≤ c
```

## prop:two-tail

Printed source: two_units.tex:68

```tex
\begin{proposition}[A common escaping tail]\label{prop:two-tail}
For the admissible bodies and normalized ratio defined in
\eqref{eq:two-body},
\[
r_2^*=\inf_{(Z,Y)\ \mathrm{admissible}}\mathcal R_2(Z,Y).
\]
Every admissible body pair is approached by independent, strictly
positive, finite-mean ordered instances whose best common-price welfare
ratios tend to \(\mathcal R_2(Z,Y)\).
\end{proposition}
```

## thm:two-pricing

Printed source: two_units.tex:158

```tex
\begin{theoremE}[Pricing for ordered buyer pairs]\label{thm:two-pricing}
For every ordered buyer pair supported on \([0,\bar b]\) and every \(d>0\):
\begin{enumerate}
\renewcommand{\labelenumi}{(\roman{enumi})}
\item For each \(\vartheta\in\mathcal V\), the operator
\(\mathcal T_{d,\vartheta}\) has a unique bounded fixed point
\(\varpi_{d,\vartheta}\), the pointwise least feasible cumulative mass.
Iteration from zero converges uniformly with contraction factor
\(\bar b/(1+\bar b)\).
\item The value \(\varpi_{d,\vartheta}(0)\) is jointly convex in
\((d,\vartheta)\), and the minimum
\begin{equation}\label{eq:two-functional}
\mathcal J_d^{(2)}(H_1,H_2)
 =\min_{\vartheta\in\mathcal V}\varpi_{d,\vartheta}(0)
\end{equation}
is attained.
\item For \(0<\beta<1\), there is a price probability with bounded support satisfying
\begin{equation}\label{eq:two-price-target}
\sum_{i=1}^2\int g_i(s_i,z)\,\pi(\mathrm dz)
\ge\beta\sum_{i=1}^2\bar L_i(s_i)-\beta d(s_1+s_2)
\quad(0\le s_1\le s_2)
\end{equation}
if and only if \(\beta\mathcal J_d^{(2)}(H_1,H_2)\le1\).
At \(d=(1-\beta)/\beta\), this is a welfare guarantee of \(\beta\)
against every ordered seller distribution in the normalized model.
\item If \(H_i^\delta\) is the survival function of
\(\delta\lfloor Z_i/\delta\rfloor\), then
\[
\mathcal J_d^{(2)}(H_1,H_2)
\le\mathcal J_d^{(2)}(H_1^\delta,H_2^\delta)+\delta.
\]
The supremum over bounded ordered buyer bodies consequently equals
the supremum over finite-support ordered buyer bodies.
\end{enumerate}
\end{theoremE}
```

[theoremE_part_i_proof](../../lean/FixedPrice/TwoUnit/Pricing/Operator.lean#L81)

```lean
theorem theoremE_part_i_proof : TheoremEPartIStatement
```

[theoremE_part_ii_proof](../../lean/FixedPrice/TwoUnit/Pricing/Attainment.lean#L35)

```lean
theorem theoremE_part_ii_proof : TheoremEPartIIStatement
```

[theoremE_part_iii_proof](../../lean/FixedPrice/TwoUnit/Pricing/PriceTarget.lean#L32)

```lean
theorem theoremE_part_iii_proof : TheoremEPartIIIStatement
```

[theoremE_part_iii_welfare_proof](../../lean/FixedPrice/TwoUnit/Pricing/PriceTarget.lean#L47)

```lean
theorem theoremE_part_iii_welfare_proof : TheoremEPartIIIWelfareStatement
```

[theoremE_part_iv_proof](../../lean/FixedPrice/TwoUnit/Pricing/Rounding.lean#L31)

```lean
theorem theoremE_part_iv_proof : TheoremEPartIVStatement
```

[theoremE_part_iv_sup_proof](../../lean/FixedPrice/TwoUnit/Pricing/Rounding.lean#L35)

```lean
theorem theoremE_part_iv_sup_proof : TheoremEPartIVSupStatement
```

[pricingValue_eq_of_bound_le_proof](../../lean/FixedPrice/TwoUnit/Pricing/Rounding.lean#L27)

```lean
theorem pricingValue_eq_of_bound_le_proof : PricingValueEqOfBoundLeStatement
```

[PricingScalarCertificates](../../lean/FixedPrice/TwoUnit/Pricing/Defs.lean#L231)

```lean
structure PricingScalarCertificates : Prop where



  obstacle_identity : ∀ L u d s ε θ I : ℝ, L ≠ 0 →
    L * (u - (1 - d * s / L + ε * θ / L + I / L)) = (d * s - L + L * u - I) - ε * θ



  affine_slack : ∀ a L s d₀ d₁ u₀ u₁ I₀ I₁ θ₀ θ₁ ε : ℝ,
    -(a * I₀ + (1 - a) * I₁) + L * (a * u₀ + (1 - a) * u₁) - L + (a * d₀ + (1 - a) * d₁) * s
        - ε * (a * θ₀ + (1 - a) * θ₁) =
      a * (-I₀ + L * u₀ - L + d₀ * s - ε * θ₀) + (1 - a) * (-I₁ + L * u₁ - L + d₁ * s - ε * θ₁)



  ordered_farkas : ∀ ψ₁ ψ₂ θ₁ θ₂ : ℝ, 0 ≤ ψ₁ + θ₁ → 0 ≤ ψ₂ - θ₂ → 0 ≤ θ₂ - θ₁ → 0 ≤ ψ₁ + ψ₂



  tail_repair : ∀ ΔL ΔG δ : ℝ, 0 ≤ ΔL → ΔL ≤ δ → 0 ≤ ΔG → 0 ≤ -ΔL + ΔG + δ




  kernel_contraction : ∀ b L E k : ℝ, 0 ≤ b → 1 ≤ L → L ≤ b + 1 → 0 ≤ E →
    |k| ≤ E * (L - 1) → (b + 1) * |k| ≤ E * L * b


  max_nonexpansive : ∀ E x₁ x₂ y₁ y₂ : ℝ, 0 ≤ E → |x₁ - y₁| ≤ E → |x₂ - y₂| ≤ E →
    |max 0 (max x₁ x₂) - max 0 (max y₁ y₂)| ≤ E



  constant_mass_feasible : ∀ L b d s : ℝ, 0 < d → 0 ≤ s → s ≤ b → 1 ≤ L → L ≤ b + 1 →
    0 ≤ -L + b + d * s + 1


  prefix_extension : ∀ old ψ₁ ψ₂ : ℝ, old ≤ ψ₂ → 0 ≤ ψ₁ + ψ₂ →
    old ≤ max old (-ψ₁) ∧ max old (-ψ₁) ≤ ψ₂ ∧ -ψ₁ ≤ max old (-ψ₁)



  rounded_stopLoss : ∀ r x δ s : ℝ, 0 ≤ r → r ≤ x → x < δ + r → 0 < δ → 0 ≤ s →
    0 ≤ max 0 (x - s) - max 0 (r - s) ∧ max 0 (x - s) - max 0 (r - s) ≤ δ


  rounded_gain_both : ∀ x z r s : ℝ, 0 ≤ s → s < z → z ≤ r → r ≤ x → 0 ≤ x - r


  rounded_gain_original_only : ∀ x z r s : ℝ, 0 ≤ r → r < z → z ≤ x → 0 ≤ s → s < z →
    0 ≤ x - s



  rounded_branches : ∀ x z r s : ℝ, r ≤ x →
    z ≤ s ∨ (z ≤ r ∧ s < z) ∨ (x < z ∧ s < z) ∨ (z ≤ x ∧ r < z ∧ s < z)
```

## thm:two-pricing

Printed source: two_units.tex:158

```tex
\begin{theoremE}[Pricing for ordered buyer pairs]\label{thm:two-pricing}
For every ordered buyer pair supported on \([0,\bar b]\) and every \(d>0\):
\begin{enumerate}
\renewcommand{\labelenumi}{(\roman{enumi})}
\item For each \(\vartheta\in\mathcal V\), the operator
\(\mathcal T_{d,\vartheta}\) has a unique bounded fixed point
\(\varpi_{d,\vartheta}\), the pointwise least feasible cumulative mass.
Iteration from zero converges uniformly with contraction factor
\(\bar b/(1+\bar b)\).
\item The value \(\varpi_{d,\vartheta}(0)\) is jointly convex in
\((d,\vartheta)\), and the minimum
\begin{equation}\label{eq:two-functional}
\mathcal J_d^{(2)}(H_1,H_2)
 =\min_{\vartheta\in\mathcal V}\varpi_{d,\vartheta}(0)
\end{equation}
is attained.
\item For \(0<\beta<1\), there is a price probability with bounded support satisfying
\begin{equation}\label{eq:two-price-target}
\sum_{i=1}^2\int g_i(s_i,z)\,\pi(\mathrm dz)
\ge\beta\sum_{i=1}^2\bar L_i(s_i)-\beta d(s_1+s_2)
\quad(0\le s_1\le s_2)
\end{equation}
if and only if \(\beta\mathcal J_d^{(2)}(H_1,H_2)\le1\).
At \(d=(1-\beta)/\beta\), this is a welfare guarantee of \(\beta\)
against every ordered seller distribution in the normalized model.
\item If \(H_i^\delta\) is the survival function of
\(\delta\lfloor Z_i/\delta\rfloor\), then
\[
\mathcal J_d^{(2)}(H_1,H_2)
\le\mathcal J_d^{(2)}(H_1^\delta,H_2^\delta)+\delta.
\]
The supremum over bounded ordered buyer bodies consequently equals
the supremum over finite-support ordered buyer bodies.
\end{enumerate}
\end{theoremE}
```

[realizedPrice_spec_proof](../../lean/FixedPrice/TwoUnit/Pricing/PriceTarget.lean#L51)

```lean
theorem realizedPrice_spec_proof : RealizedPriceSpecStatement
```

[PricingScalarCertificates](../../lean/FixedPrice/TwoUnit/Pricing/Defs.lean#L231)

```lean
structure PricingScalarCertificates : Prop where



  obstacle_identity : ∀ L u d s ε θ I : ℝ, L ≠ 0 →
    L * (u - (1 - d * s / L + ε * θ / L + I / L)) = (d * s - L + L * u - I) - ε * θ



  affine_slack : ∀ a L s d₀ d₁ u₀ u₁ I₀ I₁ θ₀ θ₁ ε : ℝ,
    -(a * I₀ + (1 - a) * I₁) + L * (a * u₀ + (1 - a) * u₁) - L + (a * d₀ + (1 - a) * d₁) * s
        - ε * (a * θ₀ + (1 - a) * θ₁) =
      a * (-I₀ + L * u₀ - L + d₀ * s - ε * θ₀) + (1 - a) * (-I₁ + L * u₁ - L + d₁ * s - ε * θ₁)



  ordered_farkas : ∀ ψ₁ ψ₂ θ₁ θ₂ : ℝ, 0 ≤ ψ₁ + θ₁ → 0 ≤ ψ₂ - θ₂ → 0 ≤ θ₂ - θ₁ → 0 ≤ ψ₁ + ψ₂



  tail_repair : ∀ ΔL ΔG δ : ℝ, 0 ≤ ΔL → ΔL ≤ δ → 0 ≤ ΔG → 0 ≤ -ΔL + ΔG + δ




  kernel_contraction : ∀ b L E k : ℝ, 0 ≤ b → 1 ≤ L → L ≤ b + 1 → 0 ≤ E →
    |k| ≤ E * (L - 1) → (b + 1) * |k| ≤ E * L * b


  max_nonexpansive : ∀ E x₁ x₂ y₁ y₂ : ℝ, 0 ≤ E → |x₁ - y₁| ≤ E → |x₂ - y₂| ≤ E →
    |max 0 (max x₁ x₂) - max 0 (max y₁ y₂)| ≤ E



  constant_mass_feasible : ∀ L b d s : ℝ, 0 < d → 0 ≤ s → s ≤ b → 1 ≤ L → L ≤ b + 1 →
    0 ≤ -L + b + d * s + 1


  prefix_extension : ∀ old ψ₁ ψ₂ : ℝ, old ≤ ψ₂ → 0 ≤ ψ₁ + ψ₂ →
    old ≤ max old (-ψ₁) ∧ max old (-ψ₁) ≤ ψ₂ ∧ -ψ₁ ≤ max old (-ψ₁)



  rounded_stopLoss : ∀ r x δ s : ℝ, 0 ≤ r → r ≤ x → x < δ + r → 0 < δ → 0 ≤ s →
    0 ≤ max 0 (x - s) - max 0 (r - s) ∧ max 0 (x - s) - max 0 (r - s) ≤ δ


  rounded_gain_both : ∀ x z r s : ℝ, 0 ≤ s → s < z → z ≤ r → r ≤ x → 0 ≤ x - r


  rounded_gain_original_only : ∀ x z r s : ℝ, 0 ≤ r → r < z → z ≤ x → 0 ≤ s → s < z →
    0 ≤ x - s



  rounded_branches : ∀ x z r s : ℝ, r ≤ x →
    z ≤ s ∨ (z ≤ r ∧ s < z) ∨ (x < z ∧ s < z) ∨ (z ≤ x ∧ r < z ∧ s < z)
```

## prop:2fam-optimum

Printed source: two_units.tex:268

```tex
\begin{proposition}[The minimum within the two-unit curve family]
\label{prop:2fam-optimum}
Let $\mathfrak F$ and $R_{\mathrm f}$ be defined by
\eqref{eq:2fam-parameters}--\eqref{eq:2fam-functionals}.
The infimum
$ r_{\mathrm{fam}}=\inf_{\mathfrak F}R_{\mathrm f}$
is attained at a unique curve and parameter triple $(t_{\mathrm f},p_{\mathrm f},\xi_0)$.
Its curve consists of a positive initial affine contact, one strictly
concave interval satisfying
$\mathcal P''+C_{\mathrm f}\mathcal P/\xi^2=0$ for a constant $C_{\mathrm f}>0$,
and a positive final affine contact. The same infimum holds in the
subclass with endpoint slopes $1,h_{\mathrm f}$, and
\[
\frac{18227}{25000}<r_{\mathrm{fam}}<\frac{729081}{10^6}.
\]
The minimizing body laws are approached by strictly positive finite-mean
ordered instances with a common escaping buyer atom.
\end{proposition}
```

[prop_2fam_optimum](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L76)

```lean
theorem prop_2fam_optimum (hN : FamilyNumerics) (hI : FamilyIdentities) : OptimumStatement
```

[self_consistency](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L88)

```lean
theorem self_consistency (hN : FamilyNumerics) (hI : FamilyIdentities) :
    SelfConsistencyStatement
```

[FamilyNumerics](../../lean/FixedPrice/TwoUnit/Family/Certificates.lean#L125)

```lean
structure FamilyNumerics : Prop where











  small_mass_endpoint : smallMassBound (1 / 32) < -2694 / 10000









  affine_left : ∀ t p : ℝ, 0 < t → t < 1 → t ≤ p → p < 1 →
    73 / 100 * (affineML t p + affineGL t p) ≤ affineML t p + 2



  affine_right : ∀ t p : ℝ, 0 < t → t < 1 → (1 + t) / 2 < p → p < 1 →
    73 / 100 * (affineMR t p + affineGR t p) ≤ affineMR t p + 2













  branch_positive_constants :
    0 < (37 / 100 : ℝ) * (1 - 2 * (1 / 5) ^ 2) ∧
    0 < (7 / 2 : ℝ) * (37 / 100) * (1 - 2 * (1 / 5) ^ 2) - 1 / 5 ∧
    0 < ((33 : ℝ) - 98 * (1 / 5) ^ 2) * (37 / 100) / 16 - 11 * (1 / 5) / 4 ∧
    0 < (256 / 225 : ℝ) - 43 / 38 ∧
    0 < (3 / 10 : ℝ) - 59 / 224 ∧
    0 < (74 / 129 : ℝ) - 9 / 16 ∧
    0 < largeTBound (421 / 1000)












  cover_C : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∀ t p : ℝ, 1 / 5 ≤ t → t ≤ 421 / 1000 →
    t < p → p ≤ 1 → Elim.algResidual (dOf β) t p = 0 → Elim.Pl (dOf β) t p ≤ 1 →
    Elim.qR (dOf β) t p ≤ Elim.qL (dOf β) t p → 1 / 4 < Elim.C (dOf β) t p





  cover_unique : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∀ t p t' p' : ℝ,
    CoverRoot (dOf β) t p → CoverRoot (dOf β) t' p' → t = t' ∧ p = p'






  cover_exists : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∃ t p : ℝ, t ∈ rootStripT ∧
    p ∈ rootStripP ∧ CoverRoot (dOf β) t p





  physical_box : ∀ β ∈ Icc βlo βhi, ∀ t ∈ rootStripT, ∀ p ∈ rootStripP,
    PhysicalMargins (dOf β) t p






  lower_endpoint_sign : CoverMonotonicity → ∀ t p : ℝ, CoverRoot (dOf βlo) t p →
    Elim.comparisonJ t p βlo < 0





  polygon_witness : ∃ D : PolygonData, D.Valid ∧ D.segmentRatio < 729081 / 10 ^ 6
```

[FamilyIdentities](../../lean/FixedPrice/TwoUnit/Family/Certificates.lean#L263)

```lean
structure FamilyIdentities : Prop where



  comparison_second_form : ∀ (β : ℝ) (θ : Params) (T Q : ℝ), θ.Admissible → 0 < β →
    (β * (2 + 2 * θ.m * θ.a - θ.N * Real.log θ.p - θ.N * Q)
        - (1 - β) * (θ.N * (θ.a + T - θ.ξ₀)) - 2) / (β * θ.N)
      = Kconst β θ - (Q + dOf β * T)



  ratio_comparison : ∀ β M G N : ℝ, β ≠ 0 → N ≠ 0 → M + G ≠ 0 →
    (β * G - (1 - β) * M - 2) / (β * N) = (M + G) / N * (1 - (M + 2) / (M + G) / β)



  ratio_minimum_signs : ∀ β N O K R : ℝ, 0 < β → 0 < N → 0 < O → β * N * K = O * (β - R) →
    (β ≤ R → K ≤ 0) ∧ (K = 0 ↔ R = β)



  buyer_mean : ∀ t p : ℝ, 0 < t → 0 < p → 2 * aF t p + 1 / p - 1 = 1 / t - 1

  p_one_ratio : ∀ t : ℝ, 0 < t →
    (1 + 3 * t ^ 2) / (1 + t) ^ 2 = 3 / 4 + (3 * t - 1) ^ 2 / (4 * (1 + t) ^ 2)



  left_variation : ∀ t p d H : ℝ, 0 < t → 0 < p →
    (t / p ^ 2 - 1 / p - d / (2 * p ^ 2))
        - (-(cF t p * H ^ 2 + d) / (2 * p ^ 2) - 2 * cF t p * H / p ^ 2 * (1 - H / 2))
      = -(cF t p * (H - 2) ^ 2 / (2 * p ^ 2))


  right_variation : ∀ ξ₀ H d : ℝ, d - ((ξ₀ * H ^ 2 + d) - 2 * ξ₀ * H ^ 2) = ξ₀ * H ^ 2



  envelope_p : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.t → 0 < θ.p → 0 < Pl →
    (θ.t / θ.p ^ 2 - 1 / θ.p - d / (2 * θ.p ^ 2))
        - ((envelopeCoeffs d θ Pl Pr).Ec / 2 + (envelopeCoeffs d θ Pl Pr).Eδ / 2)
      = statP d θ Pl / 2


  envelope_t : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.t → 0 < θ.p → 0 < θ.ξ₀ → 0 < θ.v →
      0 < Pl → 0 < Pr →
    (-1 / θ.p + d / (2 * θ.t ^ 2) - d) + d * (-1 / (2 * θ.h))
        - ((envelopeCoeffs d θ Pl Pr).Ec * (-1 / 2) + (envelopeCoeffs d θ Pl Pr).Eδ / 2
            + (envelopeCoeffs d θ Pl Pr).Eξ₀ * (-1 / (2 * θ.h))
            + (envelopeCoeffs d θ Pl Pr).Ee / 2)
      = statT d θ Pl Pr


  envelope_h : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.ξ₀ → 0 < θ.v → 0 < Pr →
    d * (-θ.ξ₀ / θ.h)
        - ((envelopeCoeffs d θ Pl Pr).Eξ₀ * (-θ.ξ₀ / θ.h) + (envelopeCoeffs d θ Pl Pr).Eh)
      = statH d θ Pr





  quadrature_Q_sum : ∀ p δ e h Pl Pr C Y : ℝ, 0 < p → 0 < Pl → 0 < Pr → h ≠ 0 →
    (Real.log (Pl / p) + δ * (1 / Pl - 1 / p))
        + ((Pl - δ) / Pl - h * ((Pr - e) / h) / Pr + Real.log (Pr / Pl) - C * Y)
        + (-Real.log Pr + e * (1 - 1 / Pr))
      = -Real.log p - C * Y - δ / p + e



  omega_derivative : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
    H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
      = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)


  gradient_integrand : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
    ξ * H ^ 2 / P ^ 2 = (ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2 + H / P - C / ξ



  euler_first_integral : ∀ ξ P H C : ℝ, ξ ≠ 0 →
    (H ^ 2 - C * P ^ 2 / ξ ^ 2) + (-H + 2 * C * P / ξ) * H + (2 * ξ * H - P) * (-C * P / ξ ^ 2) = 0


  euler_from_first_integral : ∀ ξ P H C : ℝ, ξ ≠ 0 →
    P * H + ξ * (P * (-C * P / ξ ^ 2) - H ^ 2) + (ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) = 0


  left_contact_density : ∀ ξ δ d : ℝ, ξ + δ ≠ 0 →
    1 / (ξ + δ) + ξ * (0 / (ξ + δ) - 1 / (ξ + δ) ^ 2) + d / (ξ + δ) ^ 2 = (δ + d) / (ξ + δ) ^ 2


  right_contact_density : ∀ ξ h e d : ℝ, h * ξ + e ≠ 0 →
    h / (h * ξ + e) + ξ * (0 / (h * ξ + e) - h ^ 2 / (h * ξ + e) ^ 2) + d / (h * ξ + e) ^ 2
      = (h * e + d) / (h * ξ + e) ^ 2

  gap_density : ∀ ξ P zp rp r d : ℝ, P ≠ 0 →
    ξ * ((zp + rp) ^ 2 - zp ^ 2) + d / P ^ 2 * (Real.exp (-2 * r) - 1)
      = ξ * rp ^ 2 + d / P ^ 2 * (Real.exp (-2 * r) - 1 + 2 * r) + 2 * ξ * zp * rp
        - 2 * d / P ^ 2 * r



  quadratic_complete_square : ∀ u C : ℝ, Elim.Dq C u = (u - 1 / 2) ^ 2 + C - 1 / 4


  reconstructed_logP_q : ∀ q ξ C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    ((-ξ / Elim.Dq C q) / ξ - (2 * q - 1) / Elim.Dq C q) / 2 = -(q / Elim.Dq C q)

  reconstructed_P_xi : ∀ q ξ P C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    (-q * P / Elim.Dq C q) / (-ξ / Elim.Dq C q) = q * P / ξ


  reconstructed_P_xixi : ∀ q ξ P C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    (P / ξ + q / ξ * (-q * P / Elim.Dq C q) + (-q * P / ξ ^ 2) * (-ξ / Elim.Dq C q))
        / (-ξ / Elim.Dq C q) + C * P / ξ ^ 2 = 0


  left_endpoint_D : ∀ Pl δ d : ℝ, Pl ≠ 0 →
    Elim.Dq ((δ + d) * (Pl - δ) / Pl ^ 2) ((Pl - δ) / Pl) = d * (Pl - δ) / Pl ^ 2


  right_endpoint_ξ : ∀ q e d C : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 → Elim.Dq C q ≠ 0 →
    q * (e / (1 - q)) / (d * q * (1 - q) / (e * Elim.Dq C q))
      = (e / (1 - q)) ^ 2 * Elim.Dq C q / d


  h_stationarity : ∀ q v d C e hr Pr : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 → Elim.Dq C q ≠ 0 →
    e = 1 - v → hr = d * q * (1 - q) / (e * Elim.Dq C q) → Pr = e / (1 - q) →
    -v ^ 2 * hr + 2 * (hr * e + d) * (1 / Pr - 1 + e * (1 - 1 / Pr ^ 2) / 2)
      = d * (v ^ 2 * Elim.Dq C q - C * q ^ 2) / (e * Elim.Dq C q)



  t_stationarity : ∀ q v d C t p e hr Pr : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 →
    Elim.Dq C q ≠ 0 → v + q ≠ 0 → t ≠ 0 → p ≠ 0 →
    e = 1 - v → hr = d * q * (1 - q) / (e * Elim.Dq C q) → Pr = e / (1 - q) →
    v ^ 2 * Elim.Dq C q = C * q ^ 2 →
    -Elim.γ d t p - v + (hr * e + d) / hr * (1 / Pr ^ 2 - 1)
      = -Elim.γ d t p + v * (v - q) / (e * (v + q))


  p_stationarity : ∀ t p δ d : ℝ, p ≠ 0 → t + d ≠ 0 → δ + d ≠ 0 →
    (t + d) / p ^ 2 - (δ + d) / (p ^ 2 * (δ + d) / (t + d)) = 0




  affine_left_closed_form : ∀ t p : ℝ, 0 < t → 0 < p →
    NF t * (aF t p + (1 / p - 1) - (1 - δF t p)) = affineML t p ∧
      2 + 2 * mF t * aF t p - NF t * (δF t p * (1 - 1 / p)) = affineGL t p


  affine_right_closed_form : ∀ t p : ℝ, 0 < t → t < 1 → (1 + t) / 2 < p →
    NF t * (aF t p + (1 / p - 1) / ((p - eF t) / cF t p) - vF t / ((p - eF t) / cF t p))
        = affineMR t p ∧
      2 + 2 * mF t * aF t p - NF t * (eF t * (1 - 1 / p)) = affineGR t p



  first_unit_equalizer : ∀ ξ P H N : ℝ, P ≠ 0 →
    N * (P - ξ * H) / P + H * (N * ξ / P) = N


  area_derivative_in_price : ∀ ξ P H N : ℝ, P ≠ 0 →
    (N / P - N * ξ * H / P ^ 2) * P ^ 2 = N * (P - ξ * H)


  seller_cdf_derivative : ∀ ξ H H' N : ℝ,
    N * H + (-(N * ξ)) * H' + (-N) * H = -(N * ξ * H')


  low_price_balance : ∀ t p : ℝ, 0 < t → 0 < p → mF t * (1 + 1 / p + 2 * aF t p) = 2


  initial_seller_atom : ∀ t p : ℝ, 0 < t → 0 < p →
    NF t * (p - cF t p) = mF t + mF t * aF t p * p


  gain_density : ∀ ξ P H N : ℝ, P ≠ 0 →
    N * (P - ξ * H) * H / P ^ 2 = N * H / P - N * ξ * H ^ 2 / P ^ 2



  realization_price_partition : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε →
    ¬ (z ≤ a ∧ b + ε ≤ z) ∧ ¬ (z ≤ a ∧ a + ε ≤ z ∧ z < b + ε) ∧
      ¬ (a < z ∧ b + ε ≤ z ∧ z < a + ε) ∧
      (z ≤ a ∨ b + ε ≤ z ∨ (a < z ∧ z < a + ε) ∨ (a + ε ≤ z ∧ z < b + ε))

  realization_middle_trace : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε → a + ε ≤ z → z < b + ε →
    a ≤ z - ε ∧ z - ε < b

  realization_tail_only : ∀ a b ε z w : ℝ, 0 ≤ a → a ≤ b → 0 < ε → b + ε ≤ z → w ≤ b → w < z


  realization_middle_rejects : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε →
    ((a < z ∧ z < a + ε) ∨ (a + ε ≤ z ∧ z < b + ε)) → z < b + ε ∧ a < z

  realization_low_mass : ∀ m η ε : ℝ, 0 ≤ m → m ≤ 1 → 0 ≤ η → 0 < ε → ε * η ≤ 1 →
    0 ≤ m * (1 - η * ε) ∧ m * (1 - η * ε) ≤ m

  realization_combined_tail : ∀ η M₁ M₂ : ℝ, 0 ≤ η → 0 ≤ M₁ → 0 ≤ M₂ → 2 - η * (M₁ + M₂) ≤ 2









  branch_C_p : ∀ t p z lam : ℝ, z ≠ 0 → p ≠ 0 → lam + (p + t) / 2 ≠ 0 →
    z ^ 2 * (lam + t) = p ^ 2 * (lam + (p + t) / 2) →
    ((z - (p + t) / 2) / 2 - (lam + (p + t) / 2) / 2) / z ^ 2
        + (lam + (p + t) / 2) * (z ^ 2 - (z - (p + t) / 2) * (2 * z)) / (z ^ 2) ^ 2
          * (z / p + z / (4 * (lam + (p + t) / 2)))
      = (lam + t) / p ^ 3 * (t + p / 2 - z + z * p / (4 * (lam + (p + t) / 2)))



  branch_C_p_gap : ∀ t p z lam : ℝ, lam + (p + t) / 2 ≠ 0 →
    t - (t + p / 2 - z + z * p / (4 * (lam + (p + t) / 2)))
      = (z - p) / 2 + z * (2 * lam + t) / (4 * (lam + (p + t) / 2))





  branch_f_C : ∀ v q e : ℝ, e ≠ 0 → v ≠ 0 → v ^ 2 - q ^ 2 ≠ 0 →
    v ^ 2 * (1 - 2 * q) + q ^ 2 ≠ 0 →
    ((v * (-1) * (e * (v + q)) - v * (v - q) * e) / (e * (v + q)) ^ 2)
        / (((v ^ 2 * (1 - q) + v ^ 2 * q * (-1)) * (v ^ 2 - q ^ 2)
            - v ^ 2 * q * (1 - q) * (-2 * q)) / (v ^ 2 - q ^ 2) ^ 2)
      = -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2))


  branch_f_C_gap : ∀ v q e : ℝ, e ≠ 0 → v ^ 2 * (1 - 2 * q) + q ^ 2 ≠ 0 →
    -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)) + 2 / e
      = 4 * v * q * (1 - v) / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2))


  branch_den : ∀ v q : ℝ, v ^ 2 * (1 - 2 * q) + q ^ 2 = (v - q) ^ 2 + 2 * v * q * (1 - v)





  branch_R_p : ∀ p lam t e fC Cp : ℝ, p ≠ 0 → e ≠ 0 →
    1 / p ^ 2 + 2 * (lam + t) / p ^ 3 + fC * Cp
      = 1 / p ^ 2 + 2 * (lam + t) * (e - t) / (e * p ^ 3) + 2 * (t * (lam + t) / p ^ 3 - Cp) / e
        + (fC + 2 / e) * Cp



  branch_small_t_expansion : ∀ t lam r : ℝ, t ≠ 0 → 7 * t / 4 + r ≠ 0 →
    -Elim.γ lam t (7 * t / 4 + r) * (7 * t / 4 + r) ^ 2 * t ^ 2
      = lam * (1 - 2 * t ^ 2) * r ^ 2 + t * (7 / 2 * lam * (1 - 2 * t ^ 2) - t) * r
        + t ^ 2 * ((33 - 98 * t ^ 2) * lam / 16 - 11 * t / 4)


  branch_Pl_ratio : ∀ lam t : ℝ,
    43 * (lam + t) - 38 * (lam + 11 * t / 8) = 5 * (lam - 37 / 100) + 37 / 4 * (1 / 5 - t)


  branch_lambda_delta : ∀ lam δ : ℝ,
    129 * lam - 74 * (lam + δ) = 55 * (lam - 37 / 100) + 74 * (11 / 40 - δ)



  branch_ordered_phase : ∀ v k lam δ : ℝ, δ ≠ 0 →
    v ^ 2 * Elim.Dq ((lam + δ) * k * (1 - k) / δ) k - (lam + δ) * k * (1 - k) / δ * k ^ 2
      = k * (1 - k) / δ * (lam * v ^ 2 - (lam + δ) * k ^ 2)



  branch_large_t : ∀ t : ℝ, t ≠ 0 → 1 + t ≠ 0 →
    largeTBound t - largeTBound (421 / 1000)
      = (t - 421 / 1000) * (1 + 3 / 8 * (t + 421 / 1000) / (t ^ 2 * (421 / 1000) ^ 2)
        + 2 / ((1 + t) * (1 + 421 / 1000)))
```

## conj:two-exact

Printed source: two_units.tex:301

```tex
\begin{conjecture}\label{conj:two-exact}
The optimal two-unit common-price welfare guarantee equals
\(r_2^*=r_{\mathrm{fam}}\).
\end{conjecture}
```

## app:two-recurrence

Printed source: two_unit_pricing_proofs.tex:341

```tex
\subsection{Finite-node evaluation}\label{app:two-recurrence}
```

[nodeMass_backward_proof](../../lean/FixedPrice/TwoUnit/Pricing/FiniteNodesProofs.lean#L29)

```lean
theorem nodeMass_backward_proof : NodeMassBackwardStatement
```

[nodeMass_isLeastSolution_proof](../../lean/FixedPrice/TwoUnit/Pricing/FiniteNodesProofs.lean#L33)

```lean
theorem nodeMass_isLeastSolution_proof : NodeMassIsLeastSolutionStatement
```

[nodeValue_convex_piecewiseAffine_proof](../../lean/FixedPrice/TwoUnit/Pricing/FiniteNodesProofs.lean#L37)

```lean
theorem nodeValue_convex_piecewiseAffine_proof : NodeValueConvexPiecewiseAffineStatement
```

[sellerPotential_hasDerivAt_between_nodes_proof](../../lean/FixedPrice/TwoUnit/Pricing/FiniteNodesProofs.lean#L49)

```lean
theorem sellerPotential_hasDerivAt_between_nodes_proof :
    SellerPotentialHasDerivAtBetweenNodesStatement
```

[sellerPotential_jump_at_node_proof](../../lean/FixedPrice/TwoUnit/Pricing/FiniteNodesProofs.lean#L54)

```lean
theorem sellerPotential_jump_at_node_proof : SellerPotentialJumpAtNodeStatement
```

[PricingScalarCertificates](../../lean/FixedPrice/TwoUnit/Pricing/Defs.lean#L231)

```lean
structure PricingScalarCertificates : Prop where



  obstacle_identity : ∀ L u d s ε θ I : ℝ, L ≠ 0 →
    L * (u - (1 - d * s / L + ε * θ / L + I / L)) = (d * s - L + L * u - I) - ε * θ



  affine_slack : ∀ a L s d₀ d₁ u₀ u₁ I₀ I₁ θ₀ θ₁ ε : ℝ,
    -(a * I₀ + (1 - a) * I₁) + L * (a * u₀ + (1 - a) * u₁) - L + (a * d₀ + (1 - a) * d₁) * s
        - ε * (a * θ₀ + (1 - a) * θ₁) =
      a * (-I₀ + L * u₀ - L + d₀ * s - ε * θ₀) + (1 - a) * (-I₁ + L * u₁ - L + d₁ * s - ε * θ₁)



  ordered_farkas : ∀ ψ₁ ψ₂ θ₁ θ₂ : ℝ, 0 ≤ ψ₁ + θ₁ → 0 ≤ ψ₂ - θ₂ → 0 ≤ θ₂ - θ₁ → 0 ≤ ψ₁ + ψ₂



  tail_repair : ∀ ΔL ΔG δ : ℝ, 0 ≤ ΔL → ΔL ≤ δ → 0 ≤ ΔG → 0 ≤ -ΔL + ΔG + δ




  kernel_contraction : ∀ b L E k : ℝ, 0 ≤ b → 1 ≤ L → L ≤ b + 1 → 0 ≤ E →
    |k| ≤ E * (L - 1) → (b + 1) * |k| ≤ E * L * b


  max_nonexpansive : ∀ E x₁ x₂ y₁ y₂ : ℝ, 0 ≤ E → |x₁ - y₁| ≤ E → |x₂ - y₂| ≤ E →
    |max 0 (max x₁ x₂) - max 0 (max y₁ y₂)| ≤ E



  constant_mass_feasible : ∀ L b d s : ℝ, 0 < d → 0 ≤ s → s ≤ b → 1 ≤ L → L ≤ b + 1 →
    0 ≤ -L + b + d * s + 1


  prefix_extension : ∀ old ψ₁ ψ₂ : ℝ, old ≤ ψ₂ → 0 ≤ ψ₁ + ψ₂ →
    old ≤ max old (-ψ₁) ∧ max old (-ψ₁) ≤ ψ₂ ∧ -ψ₁ ≤ max old (-ψ₁)



  rounded_stopLoss : ∀ r x δ s : ℝ, 0 ≤ r → r ≤ x → x < δ + r → 0 < δ → 0 ≤ s →
    0 ≤ max 0 (x - s) - max 0 (r - s) ∧ max 0 (x - s) - max 0 (r - s) ≤ δ


  rounded_gain_both : ∀ x z r s : ℝ, 0 ≤ s → s < z → z ≤ r → r ≤ x → 0 ≤ x - r


  rounded_gain_original_only : ∀ x z r s : ℝ, 0 ≤ r → r < z → z ≤ x → 0 ≤ s → s < z →
    0 ≤ x - s



  rounded_branches : ∀ x z r s : ℝ, r ≤ x →
    z ≤ s ∨ (z ≤ r ∧ s < z) ∨ (x < z ∧ s < z) ∨ (z ≤ x ∧ r < z ∧ s < z)
```

[NodeScalarCertificates](../../lean/FixedPrice/TwoUnit/Pricing/FiniteNodes.lean#L41)

```lean
structure NodeScalarCertificates : Prop where



  step_least : ∀ c next o₁ o₂ : ℝ, 0 ≤ next → next ≤ c → o₁ ≤ c → o₂ ≤ c →
    0 ≤ max next (max o₁ o₂) ∧ next ≤ max next (max o₁ o₂) ∧ o₁ ≤ max next (max o₁ o₂) ∧
      o₂ ≤ max next (max o₁ o₂) ∧ max next (max o₁ o₂) ≤ c


  step_mono : ∀ n₁ n₂ a₁ a₂ b₁ b₂ : ℝ, n₁ ≤ n₂ → a₁ ≤ a₂ → b₁ ≤ b₂ →
    max n₁ (max a₁ b₁) ≤ max n₂ (max a₂ b₂)


  summand_mono : ∀ lo up w : ℝ, 0 ≤ w → lo ≤ up → lo * w ≤ up * w


  max_convexity : ∀ x₀ x₁ x₂ y₀ y₁ y₂ a : ℝ, 0 ≤ a → a ≤ 1 →
    max (a * x₀ + (1 - a) * y₀) (max (a * x₁ + (1 - a) * y₁) (a * x₂ + (1 - a) * y₂)) ≤
      a * max x₀ (max x₁ x₂) + (1 - a) * max y₀ (max y₁ y₂)
```

## prop:finite

Printed source: paper.tex:1386

```tex
\begin{proposition}[finite-tail error]\label{prop:finite}
Let \(d=\tau(C_*)\), and let \(r_\eta\) be the optimal fixed-price welfare ratio of \eqref{eq:43} at \(C_*\). With
\[
L_{\mathrm{err}}(d)=\frac3d+\frac3{d^2}+\frac2{d^3},
\]
one has
\begin{equation}
0\le r_\eta-\beta_*
\le\eta\left[\beta_*L_{\mathrm{err}}(d)+\frac1d\right].
\label{eq:B1}
\end{equation}
\end{proposition}
```

[proposition_finiteTail](../../lean/FixedPrice/TheoremA.lean#L99)

```lean
theorem proposition_finiteTail {C η : ℝ} (hC : C ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hroot : optimalValue C = 1 + initialState C) (hη : η ∈ Ioc (0 : ℝ) 1) :
    let P
```

[objective_liftControl_sub_le](../../lean/FixedPrice/Perturbation.lean#L153)

```lean
theorem objective_liftControl_sub_le {d η : ℝ} (hd : 0 < d) (hη : η ∈ Icc (0 : ℝ) 1)
    {h : ℝ → ℝ} (hmeas : AEStronglyMeasurable h (volume.restrict (Icc 0 1)))
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1) :
    |objective d (liftControl η h) - objective d h| ≤ η * perturbConst d
```

## app:nonconcavity

Printed source: paper.tex:1436

```tex
\subsection{Nonconcavity in the original control}\label{app:nonconcavity}
```

## lem:2fam-realization

Printed source: two_unit_family.tex:41

```tex
\begin{lemma}[Realization by limiting instances]\label{lem:2fam-realization}
Every member of $\mathfrak F$ is the limit of strictly positive,
finite-mean ordered two-unit instances with independent buyer and seller
vectors, whose optimal common-price welfare ratios converge to
$R_{\mathrm f}$. Their seller welfare and efficient gains converge to
$M_{\mathrm f}$ and $G_{\mathrm f}$, and their best price gains converge
to $2$.
\end{lemma}
```

[lem_2fam_realization](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L68)

```lean
theorem lem_2fam_realization (hI : FamilyIdentities) : RealizationStatement
```

[FamilyIdentities](../../lean/FixedPrice/TwoUnit/Family/Certificates.lean#L263)

```lean
structure FamilyIdentities : Prop where



  comparison_second_form : ∀ (β : ℝ) (θ : Params) (T Q : ℝ), θ.Admissible → 0 < β →
    (β * (2 + 2 * θ.m * θ.a - θ.N * Real.log θ.p - θ.N * Q)
        - (1 - β) * (θ.N * (θ.a + T - θ.ξ₀)) - 2) / (β * θ.N)
      = Kconst β θ - (Q + dOf β * T)



  ratio_comparison : ∀ β M G N : ℝ, β ≠ 0 → N ≠ 0 → M + G ≠ 0 →
    (β * G - (1 - β) * M - 2) / (β * N) = (M + G) / N * (1 - (M + 2) / (M + G) / β)



  ratio_minimum_signs : ∀ β N O K R : ℝ, 0 < β → 0 < N → 0 < O → β * N * K = O * (β - R) →
    (β ≤ R → K ≤ 0) ∧ (K = 0 ↔ R = β)



  buyer_mean : ∀ t p : ℝ, 0 < t → 0 < p → 2 * aF t p + 1 / p - 1 = 1 / t - 1

  p_one_ratio : ∀ t : ℝ, 0 < t →
    (1 + 3 * t ^ 2) / (1 + t) ^ 2 = 3 / 4 + (3 * t - 1) ^ 2 / (4 * (1 + t) ^ 2)



  left_variation : ∀ t p d H : ℝ, 0 < t → 0 < p →
    (t / p ^ 2 - 1 / p - d / (2 * p ^ 2))
        - (-(cF t p * H ^ 2 + d) / (2 * p ^ 2) - 2 * cF t p * H / p ^ 2 * (1 - H / 2))
      = -(cF t p * (H - 2) ^ 2 / (2 * p ^ 2))


  right_variation : ∀ ξ₀ H d : ℝ, d - ((ξ₀ * H ^ 2 + d) - 2 * ξ₀ * H ^ 2) = ξ₀ * H ^ 2



  envelope_p : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.t → 0 < θ.p → 0 < Pl →
    (θ.t / θ.p ^ 2 - 1 / θ.p - d / (2 * θ.p ^ 2))
        - ((envelopeCoeffs d θ Pl Pr).Ec / 2 + (envelopeCoeffs d θ Pl Pr).Eδ / 2)
      = statP d θ Pl / 2


  envelope_t : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.t → 0 < θ.p → 0 < θ.ξ₀ → 0 < θ.v →
      0 < Pl → 0 < Pr →
    (-1 / θ.p + d / (2 * θ.t ^ 2) - d) + d * (-1 / (2 * θ.h))
        - ((envelopeCoeffs d θ Pl Pr).Ec * (-1 / 2) + (envelopeCoeffs d θ Pl Pr).Eδ / 2
            + (envelopeCoeffs d θ Pl Pr).Eξ₀ * (-1 / (2 * θ.h))
            + (envelopeCoeffs d θ Pl Pr).Ee / 2)
      = statT d θ Pl Pr


  envelope_h : ∀ (d : ℝ) (θ : Params) (Pl Pr : ℝ), 0 < θ.ξ₀ → 0 < θ.v → 0 < Pr →
    d * (-θ.ξ₀ / θ.h)
        - ((envelopeCoeffs d θ Pl Pr).Eξ₀ * (-θ.ξ₀ / θ.h) + (envelopeCoeffs d θ Pl Pr).Eh)
      = statH d θ Pr





  quadrature_Q_sum : ∀ p δ e h Pl Pr C Y : ℝ, 0 < p → 0 < Pl → 0 < Pr → h ≠ 0 →
    (Real.log (Pl / p) + δ * (1 / Pl - 1 / p))
        + ((Pl - δ) / Pl - h * ((Pr - e) / h) / Pr + Real.log (Pr / Pl) - C * Y)
        + (-Real.log Pr + e * (1 - 1 / Pr))
      = -Real.log p - C * Y - δ / p + e



  omega_derivative : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
    H / P + ξ * (-C * P / ξ ^ 2) / P - ξ * H * H / P ^ 2
      = -((ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2)


  gradient_integrand : ∀ ξ P H C : ℝ, ξ ≠ 0 → P ≠ 0 →
    ξ * H ^ 2 / P ^ 2 = (ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) / P ^ 2 + H / P - C / ξ



  euler_first_integral : ∀ ξ P H C : ℝ, ξ ≠ 0 →
    (H ^ 2 - C * P ^ 2 / ξ ^ 2) + (-H + 2 * C * P / ξ) * H + (2 * ξ * H - P) * (-C * P / ξ ^ 2) = 0


  euler_from_first_integral : ∀ ξ P H C : ℝ, ξ ≠ 0 →
    P * H + ξ * (P * (-C * P / ξ ^ 2) - H ^ 2) + (ξ * H ^ 2 - P * H + C * P ^ 2 / ξ) = 0


  left_contact_density : ∀ ξ δ d : ℝ, ξ + δ ≠ 0 →
    1 / (ξ + δ) + ξ * (0 / (ξ + δ) - 1 / (ξ + δ) ^ 2) + d / (ξ + δ) ^ 2 = (δ + d) / (ξ + δ) ^ 2


  right_contact_density : ∀ ξ h e d : ℝ, h * ξ + e ≠ 0 →
    h / (h * ξ + e) + ξ * (0 / (h * ξ + e) - h ^ 2 / (h * ξ + e) ^ 2) + d / (h * ξ + e) ^ 2
      = (h * e + d) / (h * ξ + e) ^ 2

  gap_density : ∀ ξ P zp rp r d : ℝ, P ≠ 0 →
    ξ * ((zp + rp) ^ 2 - zp ^ 2) + d / P ^ 2 * (Real.exp (-2 * r) - 1)
      = ξ * rp ^ 2 + d / P ^ 2 * (Real.exp (-2 * r) - 1 + 2 * r) + 2 * ξ * zp * rp
        - 2 * d / P ^ 2 * r



  quadratic_complete_square : ∀ u C : ℝ, Elim.Dq C u = (u - 1 / 2) ^ 2 + C - 1 / 4


  reconstructed_logP_q : ∀ q ξ C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    ((-ξ / Elim.Dq C q) / ξ - (2 * q - 1) / Elim.Dq C q) / 2 = -(q / Elim.Dq C q)

  reconstructed_P_xi : ∀ q ξ P C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    (-q * P / Elim.Dq C q) / (-ξ / Elim.Dq C q) = q * P / ξ


  reconstructed_P_xixi : ∀ q ξ P C : ℝ, ξ ≠ 0 → Elim.Dq C q ≠ 0 →
    (P / ξ + q / ξ * (-q * P / Elim.Dq C q) + (-q * P / ξ ^ 2) * (-ξ / Elim.Dq C q))
        / (-ξ / Elim.Dq C q) + C * P / ξ ^ 2 = 0


  left_endpoint_D : ∀ Pl δ d : ℝ, Pl ≠ 0 →
    Elim.Dq ((δ + d) * (Pl - δ) / Pl ^ 2) ((Pl - δ) / Pl) = d * (Pl - δ) / Pl ^ 2


  right_endpoint_ξ : ∀ q e d C : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 → Elim.Dq C q ≠ 0 →
    q * (e / (1 - q)) / (d * q * (1 - q) / (e * Elim.Dq C q))
      = (e / (1 - q)) ^ 2 * Elim.Dq C q / d


  h_stationarity : ∀ q v d C e hr Pr : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 → Elim.Dq C q ≠ 0 →
    e = 1 - v → hr = d * q * (1 - q) / (e * Elim.Dq C q) → Pr = e / (1 - q) →
    -v ^ 2 * hr + 2 * (hr * e + d) * (1 / Pr - 1 + e * (1 - 1 / Pr ^ 2) / 2)
      = d * (v ^ 2 * Elim.Dq C q - C * q ^ 2) / (e * Elim.Dq C q)



  t_stationarity : ∀ q v d C t p e hr Pr : ℝ, q ≠ 0 → q ≠ 1 → e ≠ 0 → d ≠ 0 →
    Elim.Dq C q ≠ 0 → v + q ≠ 0 → t ≠ 0 → p ≠ 0 →
    e = 1 - v → hr = d * q * (1 - q) / (e * Elim.Dq C q) → Pr = e / (1 - q) →
    v ^ 2 * Elim.Dq C q = C * q ^ 2 →
    -Elim.γ d t p - v + (hr * e + d) / hr * (1 / Pr ^ 2 - 1)
      = -Elim.γ d t p + v * (v - q) / (e * (v + q))


  p_stationarity : ∀ t p δ d : ℝ, p ≠ 0 → t + d ≠ 0 → δ + d ≠ 0 →
    (t + d) / p ^ 2 - (δ + d) / (p ^ 2 * (δ + d) / (t + d)) = 0




  affine_left_closed_form : ∀ t p : ℝ, 0 < t → 0 < p →
    NF t * (aF t p + (1 / p - 1) - (1 - δF t p)) = affineML t p ∧
      2 + 2 * mF t * aF t p - NF t * (δF t p * (1 - 1 / p)) = affineGL t p


  affine_right_closed_form : ∀ t p : ℝ, 0 < t → t < 1 → (1 + t) / 2 < p →
    NF t * (aF t p + (1 / p - 1) / ((p - eF t) / cF t p) - vF t / ((p - eF t) / cF t p))
        = affineMR t p ∧
      2 + 2 * mF t * aF t p - NF t * (eF t * (1 - 1 / p)) = affineGR t p



  first_unit_equalizer : ∀ ξ P H N : ℝ, P ≠ 0 →
    N * (P - ξ * H) / P + H * (N * ξ / P) = N


  area_derivative_in_price : ∀ ξ P H N : ℝ, P ≠ 0 →
    (N / P - N * ξ * H / P ^ 2) * P ^ 2 = N * (P - ξ * H)


  seller_cdf_derivative : ∀ ξ H H' N : ℝ,
    N * H + (-(N * ξ)) * H' + (-N) * H = -(N * ξ * H')


  low_price_balance : ∀ t p : ℝ, 0 < t → 0 < p → mF t * (1 + 1 / p + 2 * aF t p) = 2


  initial_seller_atom : ∀ t p : ℝ, 0 < t → 0 < p →
    NF t * (p - cF t p) = mF t + mF t * aF t p * p


  gain_density : ∀ ξ P H N : ℝ, P ≠ 0 →
    N * (P - ξ * H) * H / P ^ 2 = N * H / P - N * ξ * H ^ 2 / P ^ 2



  realization_price_partition : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε →
    ¬ (z ≤ a ∧ b + ε ≤ z) ∧ ¬ (z ≤ a ∧ a + ε ≤ z ∧ z < b + ε) ∧
      ¬ (a < z ∧ b + ε ≤ z ∧ z < a + ε) ∧
      (z ≤ a ∨ b + ε ≤ z ∨ (a < z ∧ z < a + ε) ∨ (a + ε ≤ z ∧ z < b + ε))

  realization_middle_trace : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε → a + ε ≤ z → z < b + ε →
    a ≤ z - ε ∧ z - ε < b

  realization_tail_only : ∀ a b ε z w : ℝ, 0 ≤ a → a ≤ b → 0 < ε → b + ε ≤ z → w ≤ b → w < z


  realization_middle_rejects : ∀ a b ε z : ℝ, 0 ≤ a → a ≤ b → 0 < ε →
    ((a < z ∧ z < a + ε) ∨ (a + ε ≤ z ∧ z < b + ε)) → z < b + ε ∧ a < z

  realization_low_mass : ∀ m η ε : ℝ, 0 ≤ m → m ≤ 1 → 0 ≤ η → 0 < ε → ε * η ≤ 1 →
    0 ≤ m * (1 - η * ε) ∧ m * (1 - η * ε) ≤ m

  realization_combined_tail : ∀ η M₁ M₂ : ℝ, 0 ≤ η → 0 ≤ M₁ → 0 ≤ M₂ → 2 - η * (M₁ + M₂) ≤ 2









  branch_C_p : ∀ t p z lam : ℝ, z ≠ 0 → p ≠ 0 → lam + (p + t) / 2 ≠ 0 →
    z ^ 2 * (lam + t) = p ^ 2 * (lam + (p + t) / 2) →
    ((z - (p + t) / 2) / 2 - (lam + (p + t) / 2) / 2) / z ^ 2
        + (lam + (p + t) / 2) * (z ^ 2 - (z - (p + t) / 2) * (2 * z)) / (z ^ 2) ^ 2
          * (z / p + z / (4 * (lam + (p + t) / 2)))
      = (lam + t) / p ^ 3 * (t + p / 2 - z + z * p / (4 * (lam + (p + t) / 2)))



  branch_C_p_gap : ∀ t p z lam : ℝ, lam + (p + t) / 2 ≠ 0 →
    t - (t + p / 2 - z + z * p / (4 * (lam + (p + t) / 2)))
      = (z - p) / 2 + z * (2 * lam + t) / (4 * (lam + (p + t) / 2))





  branch_f_C : ∀ v q e : ℝ, e ≠ 0 → v ≠ 0 → v ^ 2 - q ^ 2 ≠ 0 →
    v ^ 2 * (1 - 2 * q) + q ^ 2 ≠ 0 →
    ((v * (-1) * (e * (v + q)) - v * (v - q) * e) / (e * (v + q)) ^ 2)
        / (((v ^ 2 * (1 - q) + v ^ 2 * q * (-1)) * (v ^ 2 - q ^ 2)
            - v ^ 2 * q * (1 - q) * (-2 * q)) / (v ^ 2 - q ^ 2) ^ 2)
      = -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2))


  branch_f_C_gap : ∀ v q e : ℝ, e ≠ 0 → v ^ 2 * (1 - 2 * q) + q ^ 2 ≠ 0 →
    -2 * (v - q) ^ 2 / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2)) + 2 / e
      = 4 * v * q * (1 - v) / (e * (v ^ 2 * (1 - 2 * q) + q ^ 2))


  branch_den : ∀ v q : ℝ, v ^ 2 * (1 - 2 * q) + q ^ 2 = (v - q) ^ 2 + 2 * v * q * (1 - v)





  branch_R_p : ∀ p lam t e fC Cp : ℝ, p ≠ 0 → e ≠ 0 →
    1 / p ^ 2 + 2 * (lam + t) / p ^ 3 + fC * Cp
      = 1 / p ^ 2 + 2 * (lam + t) * (e - t) / (e * p ^ 3) + 2 * (t * (lam + t) / p ^ 3 - Cp) / e
        + (fC + 2 / e) * Cp



  branch_small_t_expansion : ∀ t lam r : ℝ, t ≠ 0 → 7 * t / 4 + r ≠ 0 →
    -Elim.γ lam t (7 * t / 4 + r) * (7 * t / 4 + r) ^ 2 * t ^ 2
      = lam * (1 - 2 * t ^ 2) * r ^ 2 + t * (7 / 2 * lam * (1 - 2 * t ^ 2) - t) * r
        + t ^ 2 * ((33 - 98 * t ^ 2) * lam / 16 - 11 * t / 4)


  branch_Pl_ratio : ∀ lam t : ℝ,
    43 * (lam + t) - 38 * (lam + 11 * t / 8) = 5 * (lam - 37 / 100) + 37 / 4 * (1 / 5 - t)


  branch_lambda_delta : ∀ lam δ : ℝ,
    129 * lam - 74 * (lam + δ) = 55 * (lam - 37 / 100) + 74 * (11 / 40 - δ)



  branch_ordered_phase : ∀ v k lam δ : ℝ, δ ≠ 0 →
    v ^ 2 * Elim.Dq ((lam + δ) * k * (1 - k) / δ) k - (lam + δ) * k * (1 - k) / δ * k ^ 2
      = k * (1 - k) / δ * (lam * v ^ 2 - (lam + δ) * k ^ 2)



  branch_large_t : ∀ t : ℝ, t ≠ 0 → 1 + t ≠ 0 →
    largeTBound t - largeTBound (421 / 1000)
      = (t - 421 / 1000) * (1 + 3 / 8 * (t + 421 / 1000) / (t ^ 2 * (421 / 1000) ^ 2)
        + 2 / ((1 + t) * (1 + 421 / 1000)))
```

## lem:2fam-compact

Printed source: two_unit_family.tex:127

```tex
\begin{lemma}[Compactness below three quarters]\label{lem:2fam-compact}
Let $0<\beta_{\mathrm f}\le3/4$. Every curve with
$R_{\mathrm f}<\beta_{\mathrm f}$ satisfies
$1/32<m_{\mathrm f}<3/4$, $\xi_0<600$, and $p_{\mathrm f}<1$.
If $K_{\mathrm f}$ takes a positive value, its positive supremum is
attained in this parameter region.
\end{lemma}
```

[lem_2fam_compact](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L32)

```lean
theorem lem_2fam_compact (hN : FamilyNumerics) (hI : FamilyIdentities) : CompactStatement
```

## lem:2fam-shape

Printed source: two_unit_family.tex:184

```tex
\begin{lemma}[Three-arc energy minimizer]\label{lem:2fam-shape}
At every feasible fixed $(t_{\mathrm f},p_{\mathrm f},\xi_0)$, the energy
$E_{\mathrm f}$ has a unique minimizer in \eqref{eq:2fam-class}.
It is entirely affine, or consists of an initial affine contact, one
strictly concave free interval, and a final affine contact.
Either contact may have zero length. On the free interval there is
a constant $C_{\mathrm f}>0$ such that
\begin{equation}
 \mathcal P''+\frac{C_{\mathrm f}}{\xi^2}\mathcal P=0,
 \qquad
 d_{\mathrm f}
  =\xi\mathcal P'^2-\mathcal P\mathcal P'
          +\frac{C_{\mathrm f}\mathcal P^2}{\xi}.
 \label{eq:2fam-euler}
\end{equation}
If $c_{\mathrm f}=0$, every non-affine minimizer has a positive initial
contact interval.
\end{lemma}
```

[shape_holds](../../lean/FixedPrice/TwoUnit/Family/Shape.lean#L112)

```lean
theorem shape_holds : ShapeStatement
```

## lem:2fam-boundary

Printed source: two_unit_family.tex:291

```tex
\begin{lemma}[Interior outer parameters]\label{lem:2fam-boundary}
Suppose $\beta_{\mathrm f}\in[18227/25000,729081/10^6]$.
At a positive global maximum of $K_{\mathrm f}$, or at a global
minimum of $R_{\mathrm f}$ whose value is $\beta_{\mathrm f}$, one has
$t_{\mathrm f}<p_{\mathrm f}<1$ and both affine contacts have positive length.
The derivatives of $K_{\mathrm f}$ with respect to
$(t_{\mathrm f},p_{\mathrm f},h_{\mathrm f})$ vanish there.
\end{lemma}
```

[lem_2fam_boundary](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L41)

```lean
theorem lem_2fam_boundary (hN : FamilyNumerics) (hI : FamilyIdentities) : BoundaryStatement
```

## lem:2fam-domain

Printed source: two_unit_family.tex:466

```tex
\begin{lemma}[Stationary domain and monotonicity]\label{lem:2fam-domain}
For $37/100\le d_{\mathrm f}\le3/8$, every physical stationary
point satisfies $1/5<t_{\mathrm f}<421/1000$.
On the algebraic branch, $\partial_{p_{\mathrm f}}\mathcal A_{\mathrm f}>0$.
\end{lemma}
```

[lem_2fam_domain](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L47)

```lean
theorem lem_2fam_domain (hN : FamilyNumerics) (hI : FamilyIdentities) : DomainStatement
```

## lem:2fam-cover

Printed source: two_unit_family.tex:519

```tex
\begin{lemma}[Validated stationary branch]\label{lem:2fam-cover}
For every $\beta_{\mathrm f}\in[18227/25000,729081/10^6]$, the system
\eqref{eq:2fam-algebraic}--\eqref{eq:2fam-connection} has exactly one
physical stationary point. At $\beta_{\mathrm f}=18227/25000$ it satisfies
$\beta_{\mathrm f}G_{\mathrm f}-(1-\beta_{\mathrm f})M_{\mathrm f}-2<0$.
\end{lemma}
```

[lem_2fam_cover](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L59)

```lean
theorem lem_2fam_cover (hN : FamilyNumerics) (hI : FamilyIdentities) : CoverStatement
```

[cover_atMostOne](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L51)

```lean
theorem cover_atMostOne (hN : FamilyNumerics) (hI : FamilyIdentities) :
    CoverAtMostOneStatement
```

## lem:2fam-witness

Printed source: two_unit_family.tex:617

```tex
\begin{lemma}[A rational comparison curve]\label{lem:2fam-witness}
The class \(\mathfrak F\) contains a rational concave polygon
with \(R_{\mathrm f}<729081/10^6\).
\end{lemma}
```

[lem_2fam_witness](../../lean/FixedPrice/TwoUnit/Family/Final.lean#L64)

```lean
theorem lem_2fam_witness (hN : FamilyNumerics) : WitnessStatement
```

[FamilyNumerics](../../lean/FixedPrice/TwoUnit/Family/Certificates.lean#L125)

```lean
structure FamilyNumerics : Prop where











  small_mass_endpoint : smallMassBound (1 / 32) < -2694 / 10000









  affine_left : ∀ t p : ℝ, 0 < t → t < 1 → t ≤ p → p < 1 →
    73 / 100 * (affineML t p + affineGL t p) ≤ affineML t p + 2



  affine_right : ∀ t p : ℝ, 0 < t → t < 1 → (1 + t) / 2 < p → p < 1 →
    73 / 100 * (affineMR t p + affineGR t p) ≤ affineMR t p + 2













  branch_positive_constants :
    0 < (37 / 100 : ℝ) * (1 - 2 * (1 / 5) ^ 2) ∧
    0 < (7 / 2 : ℝ) * (37 / 100) * (1 - 2 * (1 / 5) ^ 2) - 1 / 5 ∧
    0 < ((33 : ℝ) - 98 * (1 / 5) ^ 2) * (37 / 100) / 16 - 11 * (1 / 5) / 4 ∧
    0 < (256 / 225 : ℝ) - 43 / 38 ∧
    0 < (3 / 10 : ℝ) - 59 / 224 ∧
    0 < (74 / 129 : ℝ) - 9 / 16 ∧
    0 < largeTBound (421 / 1000)












  cover_C : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∀ t p : ℝ, 1 / 5 ≤ t → t ≤ 421 / 1000 →
    t < p → p ≤ 1 → Elim.algResidual (dOf β) t p = 0 → Elim.Pl (dOf β) t p ≤ 1 →
    Elim.qR (dOf β) t p ≤ Elim.qL (dOf β) t p → 1 / 4 < Elim.C (dOf β) t p





  cover_unique : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∀ t p t' p' : ℝ,
    CoverRoot (dOf β) t p → CoverRoot (dOf β) t' p' → t = t' ∧ p = p'






  cover_exists : CoverMonotonicity → ∀ β ∈ Icc βlo βhi, ∃ t p : ℝ, t ∈ rootStripT ∧
    p ∈ rootStripP ∧ CoverRoot (dOf β) t p





  physical_box : ∀ β ∈ Icc βlo βhi, ∀ t ∈ rootStripT, ∀ p ∈ rootStripP,
    PhysicalMargins (dOf β) t p






  lower_endpoint_sign : CoverMonotonicity → ∀ t p : ℝ, CoverRoot (dOf βlo) t p →
    Elim.comparisonJ t p βlo < 0





  polygon_witness : ∃ D : PolygonData, D.Valid ∧ D.segmentRatio < 729081 / 10 ^ 6
```

## prop:2fam-separate-responses

Printed source: two_unit_family.tex:804

```tex
\begin{proposition}[Separate global responses at the reference]
\label{prop:2fam-separate-responses}
Let $(Z^*,Y^*)$ be the minimizing body pair from Proposition~\ref{prop:2fam-optimum}, and set $\beta_{\mathrm f}=r_{\mathrm{fam}}$.
For the normalized welfare quantities in \eqref{eq:2fam-limiting-welfare}, the
probability $\pi_{\mathrm f}$ defined by \eqref{eq:2fam-price-density} satisfies
\begin{align*}
 \mathcal W_{\mathrm f,\pi_{\mathrm f}}(Z^*,Y)
     &\ge\beta_{\mathrm f}\mathcal O_{\mathrm f}(Z^*,Y)
       &&\text{for every finite-mean }0\le Y_1\le Y_2,\\
 \mathcal W_{\mathrm f,\pi_{\mathrm f}}(Z,Y^*)
     &\ge\beta_{\mathrm f}\mathcal O_{\mathrm f}(Z,Y^*)
       &&\text{for every finite-mean }Z_1\ge Z_2\ge0.
\end{align*}
For every $z\ge0$,
\begin{equation}
 \Upsilon_{2,\mathrm f}(z)+\inf_{w\ge z}\Upsilon_{1,\mathrm f}(w)\ge0,
 \qquad
 \Upsilon_{2,\mathrm f}(z)+\inf_{w\ge z}\Upsilon_{1,\mathrm f}(w)=0
       \quad\Longleftrightarrow\quad z=a_{\mathrm f}.
 \label{eq:2fam-second-gap}
\end{equation}
Each welfare inequality fixes the entire opposite reference side and
keeps the escaping buyer first moments equal to one.
\end{proposition}
```

## app:two-finite

Printed source: two_unit_computation.tex:2

```tex
\section{The two-unit instance}\label{app:two-finite}
```

## Historical manifest wording

These differences are source observations, not rejected theorems:

- P_energy (lem:energy): Stored historical TeX wording differs; no semantic verdict.
- P_representation (lem:representation): Stored historical TeX wording differs; no semantic verdict.
- T_calibration (thm:calibration): Stored historical TeX wording differs; no semantic verdict.
- T_frontier (thm:frontier): Stored historical TeX wording differs; no semantic verdict.
- T_two_pricing (thm:two-pricing): Stored historical TeX wording differs; no semantic verdict.
