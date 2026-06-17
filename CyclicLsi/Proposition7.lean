import CyclicLsi.Definitions


/-!
# Proposition 7: cubic criterion from the third-moment estimate

This public file contains only PDF Proposition 7. Centering and algebraic
expansion lemmas should be supplied in `CyclicLsi.Support`.

Statement dictionary:

* Mathlib/Lean: `ℕ`, `ℝ`, `Fin n`, `Real.sqrt`, absolute value, powers,
  arithmetic, and inequalities.
* `avg` is defined in `CyclicLsi.Definitions`; it is the uniform average
  `π(g) = |G|⁻¹ ∑ i, g i`.
* The parameter `energy` represents the abstract Dirichlet form `E`.
* The assumption `hthird` is the paper's mean-zero third-moment estimate
  `|π(u^3)| ≤ 3 π(u^2) sqrt(E(u) - π(u^2))`.
* The conclusion is the normalized cubic criterion
  `E(x) ≥ (1/3) π((x - 1)^2 (x + 2))`.
-/

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Proposition 7: the mean-zero third-moment estimate implies the normalized
cubic criterion. -/
theorem proposition7 {n : ℕ} (hn : n ≠ 0)
    {energy : (Fin n → ℝ) → ℝ}
    (henergy_centered :
      ∀ x : Fin n → ℝ, energy x = energy (fun i ↦ x i - avg x))
    (hqsq_nonneg :
      ∀ u : Fin n → ℝ, avg u = 0 →
        0 ≤ energy u - avg (fun i ↦ u i ^ 2))
    (hthird :
      ∀ u : Fin n → ℝ,
        avg u = 0 →
          |avg (fun i ↦ u i ^ 3)| ≤
            3 * avg (fun i ↦ u i ^ 2) *
              Real.sqrt (energy u - avg (fun i ↦ u i ^ 2))) :
    ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → avg (fun i ↦ x i ^ 2) = 1 →
      (1 / 3 : ℝ) * avg (fun i ↦ (x i - 1) ^ 2 * (x i + 2)) ≤ energy x := by
  sorry

end

end CyclicLsi
