module

public import CyclicLsi.Definitions
public import CyclicLsi.Support.Proposition78.EvenCase.Proof


/-!
# Proposition 9: even third-moment estimate

This public file contains only PDF Proposition 9. The even resonance, Fourier,
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

@[expose] public section

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
  letI : NeZero (2 * m) := ⟨by omega⟩
  intro u hu
  have hu_mean : MeanZero u := hu
  let a : Fin m → ℝ := evenFourierAmp (m := m) u
  have hmoment :
      |avg (fun x : ZMod (2 * m) ↦ u x ^ 3)| ≤
        √(blockQsq a) * √(evenWeightedSum a) := by
    calc
      |avg (fun x : ZMod (2 * m) ↦ u x ^ 3)|
          ≤ ∑ d : EvenResonanceDomain m,
              evenTripleNormWeight u (evenResonanceTriple d) := by
            simpa [evenTripleNormWeight] using
              even_abs_avg_cube_le_resonance_domain_sum (m := m) hm (u := u) hu_mean
      _ ≤ √(blockQsq a) * √(evenWeightedSum a) := by
            simpa [a] using even_resonance_domain_sum_le_cauchy hm u
  have heven :
      |avg (fun x : ZMod (2 * m) ↦ u x ^ 3)| ≤
        3 * blockSsq a * √(blockQsq a) := by
    exact even_third_moment_from_weighted_blocks hm a hmoment
  have hS : blockSsq a = Ssq u := by
    calc
      blockSsq a =
          zmodFourierSsq (fun x : ZMod (2 * m) ↦ (u x : ℂ)) := by
            simpa [a] using even_blockSsq_fourierAmp_eq_zmodFourierSsq (m := m) hu_mean
      _ = Ssq u := zmodFourierSsq_eq_Ssq_real u
  have hQ : blockQsq a = zmodWordEnergyReal u - Ssq u := by
    simpa [a] using even_blockQsq_fourierAmp_eq_zmodWordEnergyReal_sub_Ssq (m := m) hu_mean
  simpa [hS, hQ, Ssq, zmodWordEnergyReal, zmodFourierEnergy] using heven

end

end CyclicLsi
