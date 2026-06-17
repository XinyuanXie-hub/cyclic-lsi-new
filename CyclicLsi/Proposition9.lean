import CyclicLsi.Definitions

/-!
# Proposition 9: even third-moment estimate

This public file contains only PDF Proposition 9. The even resonance, Fourier,
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

/-- Proposition 9, in the native even cyclic-group `ZMod` form. -/
theorem proposition9 (m : ℕ) (hm : 2 ≤ m) :
    letI : NeZero (2 * m) := ⟨by omega⟩
    ∀ u : ZMod (2 * m) → ℝ,
      avg u = 0 →
        |avg (fun x : ZMod (2 * m) ↦ u x ^ 3)| ≤
          3 * avg (fun x : ZMod (2 * m) ↦ u x ^ 2) *
            Real.sqrt
              ((∑ k : ZMod (2 * m),
                  zmodWordLength k *
                    Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) k)) -
                avg (fun x : ZMod (2 * m) ↦ u x ^ 2)) := by
  sorry

end

end CyclicLsi
