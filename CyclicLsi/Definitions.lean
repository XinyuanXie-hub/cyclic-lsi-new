import Mathlib.Analysis.Fourier.ZMod

/-!
# Public definitions used in theorem statements

This file collects the project-defined notation that appears in the first-level
paper-facing theorem statements.

Mathlib/Lean provides the ambient objects and operations:
`ℕ`, `ℝ`, `ℂ`, `Fin`, `ZMod`, `NeZero`, `Real.log`, `Real.sqrt`,
`Complex.normSq`, finite sums `∑`, absolute value, arithmetic, and order.

Project definitions introduced here:

* `avg f = (∑ x, f x) / |α|`, the uniform average `π(f)`.
* `fourierCoeff u k = n⁻¹ * ZMod.dft u k`, the normalized Fourier coefficient
  `\hat u(k)` on `ZMod n`.
* `zmodWordLength k = |k|_cyc`, the word-length multiplier
  `ψ_n(k) = min(k, n-k)` expressed using Mathlib's `ZMod.valMinAbs`.
-/

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Uniform average over a finite type, corresponding to the paper's `π(f)`. -/
def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

/-- Normalized Fourier coefficient on `ZMod n`, corresponding to `\hat u(k)`. -/
def fourierCoeff {n : ℕ} [NeZero n] (u : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  (n : ℂ)⁻¹ * ZMod.dft u k

/-- Word-length multiplier on `ZMod n`, corresponding to `ψ_n(k) = min(k,n-k)`. -/
def zmodWordLength {n : ℕ} (k : ZMod n) : ℝ :=
  (k.valMinAbs.natAbs : ℝ)

end

end CyclicLsi
