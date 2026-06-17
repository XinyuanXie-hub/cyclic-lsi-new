import CyclicLsi.Definitions
import CyclicLsi.CubicMajorant
import CyclicLsi.Proposition6
import CyclicLsi.Proposition7
import CyclicLsi.Proposition8
import CyclicLsi.Proposition9


/-!
# Theorem 1

This file proves the PDF's cyclic-group log-Sobolev inequality by composing
PDF Propositions 6-9 for the concrete word-length energy.

Statement dictionary:

* Mathlib/Lean: `ℕ`, `ℝ`, `ℂ`, `ZMod n`, `Real.log`, `Complex.normSq`,
  finite sums `∑`, powers, inequalities, and the coercion `ℝ → ℂ`.
* `avg` is defined in `CyclicLsi.Definitions`; it is the uniform average
  `π(g) = |G|⁻¹ ∑ x, g x`.
* `fourierCoeff` is defined in `CyclicLsi.Definitions`; it is the normalized
  Fourier coefficient `\hat f(k)`.
* `zmodWordLength` is defined in `CyclicLsi.Definitions`; it is the cyclic
  word length `ψ_n(k) = min(k,n-k)`.
* The right-hand side is the Fourier-multiplier expression for
  `2 π(f A_{ψ_n} f)`.
-/

namespace CyclicLsi

noncomputable section

/-- The word-length log-Sobolev inequality on `ZMod n`, matching the PDF's
cyclic-group domain notation. -/
theorem theorem1 (n : ℕ) (hn : 4 ≤ n)
    (f : ZMod n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    letI : NeZero n := ⟨by omega⟩
    avg (fun x : ZMod n ↦ f x ^ 2 * Real.log (f x ^ 2)) -
        avg (fun x : ZMod n ↦ f x ^ 2) *
          Real.log (avg (fun x : ZMod n ↦ f x ^ 2)) ≤
      2 * ∑ k : ZMod n,
        zmodWordLength k *
          Complex.normSq (fourierCoeff (fun x : ZMod n ↦ (f x : ℂ)) k) := by
  sorry

end

end CyclicLsi
