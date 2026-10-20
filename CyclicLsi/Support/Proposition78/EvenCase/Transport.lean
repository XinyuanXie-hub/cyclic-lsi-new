import CyclicLsi.Support.Proposition9



/-!
# Transported even third-moment endpoint

This support file packages Proposition 11 into the `Fin`-indexed theorem
shape used by the final finite proof chain.
-/

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Proposition 11 transported to `Fin` and unfolded in the theorem type used
by the main finite theorem. -/
theorem proposition9_finWordEnergy (m : ℕ) (hm : 2 ≤ m)
    (u : Fin (2 * m) → ℝ) (hu : MeanZero u) :
  |avg (fun x : Fin (2 * m) ↦ u x ^ 3)| ≤
      3 * Ssq u * Real.sqrt (Qsq (finWordEnergy (2 * m)) u) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have h :=
    thirdMomentEstimateFor_of_zmod
      (n := 2 * m) (energyZ := zmodWordEnergyReal) (proposition9 m hm) u hu
  simpa [Qsq, finWordEnergy_of_ne] using h

end

end CyclicLsi
