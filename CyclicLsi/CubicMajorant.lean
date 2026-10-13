module

public import CyclicLsi.Support.CubicMajorant


/-!
# Cubic majorant

This public file contains only the pointwise Frank--Ivanisvili cubic majorant.
The derivative and monotonicity lemmas are in `CyclicLsi.Support.CubicMajorant`.

Statement dictionary:

* All symbols in the theorem statement are from Mathlib/Lean: `ℝ`,
  `Real.log`, powers, arithmetic, and inequalities.
* No project-defined notation appears in this theorem statement.
-/

@[expose] public section

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
