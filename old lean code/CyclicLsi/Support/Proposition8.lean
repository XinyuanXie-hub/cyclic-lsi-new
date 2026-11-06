module
import CyclicLsi.Definitions
public import CyclicLsi.Support.Proposition78.OddCase.Proof


/-!
# Proposition 10: odd third-moment estimate

This file proves Proposition 10 for the proof of Theorem 1. The odd resonance, Fourier,
and block-estimate lemmas are in `CyclicLsi.Support.Proposition78`.

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

public noncomputable section

/-- Proposition 10, in the native odd cyclic-group `ZMod` form. -/
theorem proposition8 (m : ℕ) (hm : 2 ≤ m)
    (u : ZMod (2 * m + 1) → ℝ) (hu : avg u = 0) :
    |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)| ≤
      3 * avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 2) *
        Real.sqrt
          ((∑ k : ZMod (2 * m + 1),
              zmodWordLength k *
                Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) k)) -
            avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 2)) := by
  let : NeZero (2 * m + 1) := ⟨by omega⟩
  have hu_mean : MeanZero u := hu
  let a : Fin m → ℝ := oddFourierAmp m u
  have hres :
      |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)| ≤
        oddBoundaryB0 a + oddWeightedB1 a := by
    calc
      |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)|
          ≤ ∑ d : OddResonanceDomain m,
              oddTripleNormWeight u (oddResonanceTriple d) := by
            simpa [oddTripleNormWeight] using
              odd_abs_avg_cube_le_resonance_domain_sum (m := m) (u := u) hu_mean
      _ = oddBoundaryB0 a + oddWeightedB1 a := by
            simpa [a] using odd_resonance_domain_sum_eq_boundary_add_weighted hm u
  have hodd :
      |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)| ≤
        3 * blockSsq a * √(blockQsq a) := by
    exact odd_third_moment_from_weighted_blocks a
      hres
      (odd_boundaryB0_le hm (a := a) (ha := fun j ↦ oddFourierAmp_nonneg u j))
      (odd_weightedB1_le (a := a))
  have hS : blockSsq a = Ssq u := by
    calc
      blockSsq a =
          zmodFourierSsq (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) := by
            simpa [a] using odd_blockSsq_fourierAmp_eq_zmodFourierSsq (m := m) hu_mean
      _ = Ssq u := zmodFourierSsq_eq_Ssq_real u
  have hQ : blockQsq a = zmodWordEnergyReal u - Ssq u := by
    simpa [a] using odd_blockQsq_fourierAmp_eq_zmodWordEnergyReal_sub_Ssq (m := m) hu_mean
  simpa [hS, hQ, Ssq, zmodWordEnergyReal, zmodFourierEnergy] using hodd

end

end CyclicLsi
