module

public import CyclicLsi.Support.Basic


/-!
# Formal theorem dependency chain

This support file records the formalized chain
`Proposition 8 / Proposition 9 -> Proposition 7 -> Proposition 6 -> Theorem 1`.
-/

@[expose] public section

namespace CyclicLsi

noncomputable section

/-- The internal theorem-composition lemma used by the public proof of Theorem 1. -/
theorem theorem1_from_propositions6_7_8_9 {energy : EnergyFamily}
    (h6 : ∀ n : ℕ, 4 ≤ n -> CubicCriterionFor n (energy n) ->
      ∀ f : Fin n -> ℝ, Nonnegative f ->
        ent (fun x => f x ^ 2) ≤ 2 * energy n f)
    (h7 : ∀ n : ℕ, 4 ≤ n ->
      ThirdMomentEstimateFor n (energy n) -> CubicCriterionFor n (energy n))
    (h8 : ∀ m : ℕ, 2 ≤ m ->
      ThirdMomentEstimateFor (2 * m + 1) (energy (2 * m + 1)))
    (h9 : ∀ m : ℕ, 2 ≤ m ->
      ThirdMomentEstimateFor (2 * m) (energy (2 * m))) :
    ∀ n : ℕ, 4 ≤ n ->
      ∀ f : Fin n -> ℝ, Nonnegative f ->
        ent (fun x => f x ^ 2) ≤ 2 * energy n f := by
  intro n hn
  have hthird : ThirdMomentEstimateFor n (energy n) := by
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · subst n
      exact h9 m (by omega)
    · subst n
      exact h8 m (by omega)
  exact h6 n hn (h7 n hn hthird)

end

end CyclicLsi
