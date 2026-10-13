module

public import CyclicLsi.Proposition8



/-!
# Transported odd third-moment endpoint

This support file packages PDF Proposition 8 into the `Fin`-indexed theorem
shape used by the final finite proof chain.
-/

@[expose] public section

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Proposition 8 transported to `Fin` and unfolded in the theorem type used
by the main finite theorem. -/
theorem proposition8_finWordEnergy (m : ℕ) (hm : 2 ≤ m)
    (u : Fin (2 * m + 1) → ℝ) (hu : MeanZero u) :
  |avg (fun x : Fin (2 * m + 1) ↦ u x ^ 3)| ≤
      3 * Ssq u * Real.sqrt (Qsq (finWordEnergy (2 * m + 1)) u) := by
  haveI : NeZero (2 * m + 1) := ⟨by omega⟩
  have h :=
    thirdMomentEstimateFor_of_zmod
      (n := 2 * m + 1) (energyZ := zmodWordEnergyReal) (proposition8 m hm) u hu
  simpa [Qsq, finWordEnergy_of_ne] using h

end

end CyclicLsi
