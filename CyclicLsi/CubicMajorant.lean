import CyclicLsi.Definitions

/-!
# Cubic majorant

This public file contains only the pointwise Frank--Ivanisvili cubic majorant.
The proof should be supplied by support lemmas in `CyclicLsi.Support`.

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
  sorry

end

end CyclicLsi
