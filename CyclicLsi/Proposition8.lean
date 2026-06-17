import CyclicLsi.Definitions

/-!
# Proposition 8: odd third-moment estimate

This public file contains only PDF Proposition 8. The odd resonance, Fourier,
and block-estimate lemmas should be supplied in `CyclicLsi.Support`.

Statement dictionary:

* Mathlib/Lean: `ℕ`, `ℝ`, `ℂ`, `ZMod n`, `Real.sqrt`,
  `Complex.normSq`, finite sums `∑`, absolute value, powers, arithmetic, and
  inequalities.
* `avg` is defined in `CyclicLsi.Definitions`; it is the uniform average
  `π(g) = |G|⁻¹ ∑ x, g x`.
* `fourierCoeff` is defined in `CyclicLsi.Definitions`; it is the normalized
  Fourier coefficient `\hat u(k)`.
* `zmodWordLength` is defined in `CyclicLsi.Definitions`; it is the cyclic
  word length `ψ_n(k) = min(k,n-k)`.
* The Fourier sum in the square root is the word-length energy
  `π(u A_{ψ_n} u)`.
-/

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Proposition 8, in the native odd cyclic-group `ZMod` form. -/
theorem proposition8 (m : ℕ) (hm : 2 ≤ m)
    (u : ZMod (2 * m + 1) → ℝ) (hu : avg u = 0) :
    |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)| ≤
      3 * avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 2) *
        Real.sqrt
          ((∑ k : ZMod (2 * m + 1),
              zmodWordLength k *
                Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) k)) -
            avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 2)) := by
  sorry

end

end CyclicLsi
