module

public import CyclicLsi.Definitions
public import CyclicLsi.Support.Proposition7

/-!
# Proposition 7: cubic criterion from the third-moment estimate

This public file contains only PDF Proposition 7. Centering and algebraic
expansion lemmas are in `CyclicLsi.Support.Proposition7`.

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

@[expose] public section

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
  intro x hx_nonneg hx_norm
  change (1 / 3 : ℝ) * cubicExpression x ≤ energy x
  let a : ℝ := avg x
  let u : Fin n → ℝ := centered x
  have hu_mean : MeanZero u := centered_meanZero_fin hn x
  have hu_sq : Ssq u = 1 - a ^ 2 := by
    dsimp [u, a]
    rw [Ssq_centered_eq hn, hx_norm]
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact avg_nonneg hx_nonneg
  have hS_nonneg : 0 ≤ Ssq u := by
    unfold Ssq
    exact avg_nonneg fun i ↦ sq_nonneg (u i)
  have ha_le_one : a ≤ 1 := by
    have : a ^ 2 ≤ 1 := by nlinarith [hS_nonneg, hu_sq]
    nlinarith [ha_nonneg, this]
  have hQ_nonneg : 0 ≤ Qsq energy u := by
    simpa [MeanZero, Qsq, Ssq] using hqsq_nonneg u hu_mean
  have hthird_abs :
      |avg (fun i ↦ u i ^ 3)| ≤ 3 * Ssq u * Real.sqrt (Qsq energy u) := by
    simpa [MeanZero, Ssq, Qsq] using hthird u hu_mean
  have hthird_signed :
      avg (fun i ↦ u i ^ 3) ≤ 3 * Ssq u * Real.sqrt (Qsq energy u) := by
    exact (le_abs_self _).trans hthird_abs
  have hamgm :
      3 * Ssq u * Real.sqrt (Qsq energy u) ≤
        (3 / 4 : ℝ) * (Ssq u) ^ 2 + 3 * Qsq energy u := by
    have hsqrt_sq : (Real.sqrt (Qsq energy u)) ^ 2 = Qsq energy u :=
      Real.sq_sqrt hQ_nonneg
    have hsq : 0 ≤ (Ssq u / 2 - Real.sqrt (Qsq energy u)) ^ 2 := sq_nonneg _
    nlinarith [hsq, hsqrt_sq]
  have htail :
      (3 / 4 : ℝ) * (Ssq u) ^ 2 + 3 * Qsq energy u ≤
        (1 - a) ^ 2 * (1 + 2 * a) + 3 * Qsq energy u := by
    have hfactor :
        (1 - a) ^ 2 * (1 + 2 * a) - (3 / 4 : ℝ) * (1 - a ^ 2) ^ 2 =
          (1 / 4 : ℝ) * (1 - a) ^ 3 * (1 + 3 * a) := by
      ring
    have hnonneg :
        0 ≤ (1 / 4 : ℝ) * (1 - a) ^ 3 * (1 + 3 * a) := by
      have h1ma : 0 ≤ 1 - a := by linarith
      have h1p3a : 0 ≤ 1 + 3 * a := by nlinarith
      exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h1ma 3)) h1p3a
    nlinarith [hfactor, hnonneg, hu_sq]
  have hu_cubic_bound :
      avg (fun i ↦ u i ^ 3) ≤ (1 - a) ^ 2 * (1 + 2 * a) + 3 * Qsq energy u :=
    hthird_signed.trans (hamgm.trans htail)
  have hcubic_expansion :
      cubicExpression x = 2 - 2 * a ^ 3 + avg (fun i ↦ u i ^ 3) := by
    dsimp [a, u]
    exact cubicExpression_centered_expansion hn x hx_norm
  have henergy_centered : energy x = energy u := by
    change energy x = energy (fun i ↦ x i - avg x)
    exact henergy_centered x
  have hcriterion :
      cubicExpression x ≤ 3 * energy x := by
    rw [hcubic_expansion, henergy_centered]
    have hQdef : Qsq energy u = energy u - Ssq u := rfl
    nlinarith [hu_cubic_bound, hu_sq, hQdef]
  nlinarith

end

end CyclicLsi
