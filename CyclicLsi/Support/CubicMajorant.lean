import CyclicLsi.Support.CubicMajorant.Lemmas


/-!
# Cubic majorant (Lemma 7 in v4)

This file proves the pointwise Frank--Ivanisvili cubic majorant used by Theorem 1.
The derivative and monotonicity lemmas are in `CyclicLsi.Support.CubicMajorant.Lemmas`.

Statement dictionary:

* All symbols in the theorem statement are from Mathlib/Lean: `ℝ`,
  `Real.log`, powers, arithmetic, and inequalities.
* No project-defined notation appears in this theorem statement.
-/

namespace CyclicLsi

noncomputable section

/-- The pointwise cubic majorant used in the entropy reduction. -/
theorem pointwiseCubicMajorant (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.log (t ^ 2) ≤
      (2 / 3 : ℝ) * ((t - 1) ^ 2 * (t + 2)) + (t ^ 2 - 1) := by
  have hgap := cubicMajorantGap_nonneg ht
  unfold cubicMajorantGap at hgap
  linarith

end

end CyclicLsi
