module
public import CyclicLsi.Support.Basic



/-!
# Final block inequalities for the third-moment estimates

This file proves the closing real-variable inequalities used at the end of
the odd and even third-moment estimates.  The Fourier resonance counting
and the definitions of the block quantities are separate from these final
estimates.
-/

namespace CyclicLsi

public noncomputable section

/-- The numerical constant in the odd estimate is strictly below `3`. -/
theorem odd_block_constant_lt_three :
    √((11 : ℝ) / 2) + 1 / (2 * √(2 : ℝ)) < 3 := by
  have hsqrt11 : √((11 : ℝ) / 2) < (5 / 2 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5 / 2)]
    norm_num
  have hsqrt2_ge_one : (1 : ℝ) ≤ √(2 : ℝ) := by
    rw [← Real.one_le_sqrt]
    norm_num
  have hsqrt2_pos : 0 < √(2 : ℝ) := by positivity
  have hfrac : 1 / (2 * √(2 : ℝ)) ≤ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * √(2 : ℝ)) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  linarith

/-- Final step of the odd block estimate.

In the paper, `B0` is the boundary contribution and `B1` is the weighted
Cauchy-Schwarz contribution.  Once those two bounds are proved, their sum is
bounded by `3 * S * Q`.
-/
theorem odd_third_moment_from_block_bounds {moment S Q B0 B1 : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hmoment : |moment| ≤ B0 + B1)
    (hB0 : B0 ≤ (1 / (2 * √(2 : ℝ))) * S * Q)
    (hB1 : B1 ≤ √((11 : ℝ) / 2) * S * Q) :
    |moment| ≤ 3 * S * Q := by
  let c0 : ℝ := 1 / (2 * √(2 : ℝ))
  let c1 : ℝ := √((11 : ℝ) / 2)
  have hconst : c0 + c1 ≤ 3 := by
    dsimp [c0, c1]
    linarith [odd_block_constant_lt_three.le]
  have hSQ : 0 ≤ S * Q := mul_nonneg hS hQ
  calc
    |moment| ≤ B0 + B1 := hmoment
    _ ≤ c0 * S * Q + c1 * S * Q := add_le_add hB0 hB1
    _ = (c0 + c1) * (S * Q) := by ring
    _ ≤ 3 * (S * Q) := mul_le_mul_of_nonneg_right hconst hSQ
    _ = 3 * S * Q := by ring

end

end CyclicLsi
