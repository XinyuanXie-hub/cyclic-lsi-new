import CyclicLsi.Definitions


/-!
# Proposition 6: entropy from the normalized cubic criterion

This public file contains only PDF Proposition 6. Supporting normalization and
entropy-scaling lemmas should be supplied in `CyclicLsi.Support`.

Statement dictionary:

* Mathlib/Lean: `ℕ`, `ℝ`, `Fin n`, `Real.log`, powers, arithmetic, and
  inequalities.
* `avg` is defined in `CyclicLsi.Definitions`; it is the uniform average
  `π(g) = |G|⁻¹ ∑ i, g i`.
* The parameter `energy` represents the abstract Dirichlet form `E`.
* The assumption `hmajor` is the pointwise cubic majorant from the paper.
* The assumption `hcubic` is the normalized cubic criterion
  `E(x) ≥ (1/3) π((x - 1)^2 (x + 2))`.
-/

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Proposition 6: the normalized cubic criterion implies the log-Sobolev
inequality. -/
theorem proposition6
    {n : ℕ} (hn : 0 < n) {energy : (Fin n → ℝ) → ℝ}
    (hmajor :
      ∀ t : ℝ, 0 ≤ t →
        t ^ 2 * Real.log (t ^ 2) ≤
          (2 / 3 : ℝ) * ((t - 1) ^ 2 * (t + 2)) + (t ^ 2 - 1))
    (hhom :
      ∀ (c : ℝ) (f : Fin n → ℝ),
        energy (fun x ↦ c * f x) = c ^ 2 * energy f)
    (hcubic :
      ∀ x : Fin n → ℝ,
        (∀ i, 0 ≤ x i) → avg (fun i ↦ x i ^ 2) = 1 →
          (1 / 3 : ℝ) * avg (fun i ↦ (x i - 1) ^ 2 * (x i + 2)) ≤ energy x) :
    ∀ f : Fin n → ℝ, (∀ i, 0 ≤ f i) →
      avg (fun i ↦ f i ^ 2 * Real.log (f i ^ 2)) -
          avg (fun i ↦ f i ^ 2) * Real.log (avg (fun i ↦ f i ^ 2)) ≤
        2 * energy f := by
  sorry

end

end CyclicLsi
