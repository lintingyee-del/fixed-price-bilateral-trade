import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Explicit definitions from paper.tex, equations (3), (4), (6), and (31).
All integrals use Lebesgue measure. No economic environment is imported. -/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace FixedPrice

def denominator (C y : ℝ) : ℝ := 1 - y + C * y ^ 2

def endParameter (C : ℝ) : ℝ := (1 - 2 * C) / (C * (1 - C))

def primitive (C y : ℝ) : ℝ := ∫ r in 0..y, (denominator C r)⁻¹

def initialState (C : ℝ) : ℝ :=
  C ^ 2 / (1 - 2 * C) * Real.exp (-(primitive C (endParameter C)) / 2)

def optimalValue (C : ℝ) : ℝ := C * (2 + primitive C (endParameter C))

def state (d : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ := d + ∫ u in 0..t, h u

def secondMoment (h : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in 0..t, h u ^ 2

def objective (d : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, h t / state d h t + (d ^ 2 - secondMoment h t) / state d h t ^ 2

def middleState (d C y : ℝ) : ℝ :=
  d * Real.sqrt (denominator C y) * Real.exp (primitive C y / 2)

def maximizingControl (d C t : ℝ) : ℝ :=
  if t ≤ C then 0
  else if t ≤ C * (1 + endParameter C) then
    let y := t / C - 1
    y * middleState d C y / denominator C y
  else 1

def logEnergy (d R : ℝ) (ell : ℝ → ℝ) : ℝ :=
  -Real.log d - ell 0 +
    ∫ a in 0..R, d ^ 2 - Real.exp (-2 * ell a) - a * (deriv ell a) ^ 2

def gapIntegrand (ell v Q : ℝ → ℝ) (a : ℝ) : ℝ :=
  a * (deriv v a) ^ 2 + Real.exp (-2 * ell a) *
    (Real.exp (-2 * v a) - 1 + 2 * v a) - 2 * Q a * v a

end FixedPrice
