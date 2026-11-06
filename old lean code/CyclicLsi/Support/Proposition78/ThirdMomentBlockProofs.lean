module
public import CyclicLsi.Support.Proposition78.BlockBounds
public import CyclicLsi.Support.Proposition78.ThirdMomentBlocks



/-!
# Abstract block proofs for the odd and even third-moment estimates

This file combines the block-combinatorial `W` estimates with the final scalar
inequalities.  The remaining bridge to the numbered propositions is the Fourier
resonance step: for each real mean-zero `u`, construct the amplitude vector
`a` and prove the displayed resonance/Cauchy hypotheses below for
`moment = Avg(u^3)`.
-/

namespace CyclicLsi

public noncomputable section

/-- Nonnegativity of the zero-based square sum. -/
theorem blockSsq_nonneg {m : ℕ} (a : Fin m → ℝ) :
    0 ≤ blockSsq a := by
  unfold blockSsq
  positivity

/-- Nonnegativity of the zero-based surplus square sum. -/
theorem blockQsq_nonneg {m : ℕ} (a : Fin m → ℝ) :
    0 ≤ blockQsq a := by
  unfold blockQsq
  positivity

theorem sqrt_oddWeightedSum_le {m : ℕ} (a : Fin m → ℝ) :
    √(oddWeightedSum a) ≤ √(11 : ℝ) * blockSsq a := by
  calc
    √(oddWeightedSum a) ≤ √(11 * blockSsq a ^ 2) :=
      Real.sqrt_le_sqrt (oddWeightedSum_le a)
    _ = √(11 : ℝ) * blockSsq a := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (11 : ℝ)),
        Real.sqrt_sq (blockSsq_nonneg a)]

theorem sqrt_evenWeightedSum_le {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℝ) :
    √(evenWeightedSum a) ≤ 3 * blockSsq a := by
  calc
    √(evenWeightedSum a) ≤ √(9 * blockSsq a ^ 2) :=
      Real.sqrt_le_sqrt (evenWeightedSum_le hm a)
    _ = 3 * blockSsq a := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
      rw [show (3 : ℝ) ^ 2 * blockSsq a ^ 2 = (3 * blockSsq a) ^ 2 by ring]
      rw [Real.sqrt_sq (mul_nonneg (by norm_num) (blockSsq_nonneg a))]

/-- Odd block proof after the Fourier resonance and boundary estimates have
been supplied.
-/
theorem odd_third_moment_from_weighted_blocks {m : ℕ} (a : Fin m → ℝ)
    {moment B0 B1 : ℝ}
    (hmoment : |moment| ≤ B0 + B1)
    (hB0 : B0 ≤ (1 / (2 * √(2 : ℝ))) * blockSsq a * √(blockQsq a))
    (hB1 :
      B1 ≤ √((1 : ℝ) / 2) * √(blockQsq a) * √(oddWeightedSum a)) :
    |moment| ≤ 3 * blockSsq a * √(blockQsq a) := by
  have hB1_final :
      B1 ≤ √((11 : ℝ) / 2) * blockSsq a * √(blockQsq a) := by
    have hconst :
        √((1 : ℝ) / 2) * √(11 : ℝ) = √((11 : ℝ) / 2) := by
      rw [← Real.sqrt_mul (by norm_num : 0 ≤ (1 : ℝ) / 2)]
      congr 1
      norm_num
    have hfactor_nonneg : 0 ≤ √((1 : ℝ) / 2) * √(blockQsq a) := by
      positivity
    calc
      B1 ≤ √((1 : ℝ) / 2) * √(blockQsq a) * √(oddWeightedSum a) := hB1
      _ ≤ √((1 : ℝ) / 2) * √(blockQsq a) * (√(11 : ℝ) * blockSsq a) := by
        exact mul_le_mul_of_nonneg_left (sqrt_oddWeightedSum_le a) hfactor_nonneg
      _ = √((11 : ℝ) / 2) * blockSsq a * √(blockQsq a) := by
        rw [← hconst]
        ring
  exact odd_third_moment_from_block_bounds
    (S := blockSsq a) (Q := √(blockQsq a))
    (blockSsq_nonneg a) (Real.sqrt_nonneg _)
    hmoment hB0 hB1_final

/-- Even block proof after the Fourier resonance/Cauchy estimate has been
supplied.
-/
theorem even_third_moment_from_weighted_blocks {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℝ)
    {moment : ℝ}
    (hmoment : |moment| ≤ √(blockQsq a) * √(evenWeightedSum a)) :
    |moment| ≤ 3 * blockSsq a * √(blockQsq a) := by
  calc
    |moment| ≤ √(blockQsq a) * √(evenWeightedSum a) := hmoment
    _ ≤ √(blockQsq a) * (3 * blockSsq a) := by
      exact mul_le_mul_of_nonneg_left (sqrt_evenWeightedSum_le hm a) (Real.sqrt_nonneg _)
    _ = 3 * blockSsq a * √(blockQsq a) := by
      ring

end

end CyclicLsi

