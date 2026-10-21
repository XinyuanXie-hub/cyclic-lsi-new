module
import CyclicLsi.Definitions
public import CyclicLsi.Support.Proposition6.Lemmas



/-!
# Proposition 8: entropy from the normalized cubic criterion

This file proves Proposition 8 for the proof of Theorem 1. Supporting normalization
and entropy-scaling lemmas are in `CyclicLsi.Support.Proposition6.Lemmas`.

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

public noncomputable section

/-- Proposition 8: the normalized cubic criterion implies the log-Sobolev
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
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro f hf_nonneg
  change ent (fun x ↦ f x ^ 2) ≤ 2 * energy f
  let s : ℝ := avg (fun x ↦ f x ^ 2)
  have hs_def : s = avg (fun x ↦ f x ^ 2) := rfl
  have hs_nonneg : 0 ≤ s := by
    rw [hs_def]
    exact avg_sq_nonneg f
  rcases hs_nonneg.eq_or_lt with hs_zero | hs_pos
  · have hf_avg_zero : avg (fun x ↦ f x ^ 2) = 0 := by
      rw [← hs_def, hs_zero]
    have hf_zero : f = fun _ ↦ 0 :=
      eq_zero_of_avg_sq_eq_zero (f := f) hf_avg_zero
    rw [hf_zero]
    simp [ent_zero, energy_zero_of_quadraticHomogeneous hhom]
  · let x : Fin n → ℝ := fun i ↦ (√s)⁻¹ * f i
    have hx_nonneg : Nonnegative x := by
      exact nonnegative_smul_of_nonnegative (inv_nonneg.mpr (Real.sqrt_nonneg s)) hf_nonneg
    have hx_norm : avg (fun i ↦ x i ^ 2) = 1 := by
      simpa [x] using normalized_smul (f := f) (s := s) hs_def hs_pos
    have hent_x : ent (fun i ↦ x i ^ 2) ≤ (2 / 3 : ℝ) * cubicExpression x :=
      ent_le_two_thirds_cubic_of_normalized hmajor hx_nonneg hx_norm
    have hcubic_x : (1 / 3 : ℝ) * cubicExpression x ≤ energy x :=
      by simpa [cubicExpression] using hcubic x hx_nonneg hx_norm
    have htwo_cubic : (2 / 3 : ℝ) * cubicExpression x ≤ 2 * energy x := by
      linarith
    have hent_energy_x : ent (fun i ↦ x i ^ 2) ≤ 2 * energy x :=
      hent_x.trans htwo_cubic
    have hs_sqrt_sq : (√s) ^ 2 = s := Real.sq_sqrt hs_pos.le
    have hs_ne : s ≠ 0 := hs_pos.ne'
    have hsqrt_ne : √s ≠ 0 := (Real.sqrt_ne_zero hs_pos.le).mpr hs_ne
    have henergy_x : s * energy x = energy f := by
      have hhom_x := hhom (√s) x
      have hscale : (fun i ↦ √s * x i) = f := by
        funext i
        dsimp [x]
        calc
          √s * ((√s)⁻¹ * f i) = (√s * (√s)⁻¹) * f i := by ring
          _ = f i := by rw [mul_inv_cancel₀ hsqrt_ne, one_mul]
      calc
        s * energy x = (√s) ^ 2 * energy x := by rw [hs_sqrt_sq]
        _ = energy (fun i ↦ √s * x i) := (hhom_x).symm
        _ = energy f := by rw [hscale]
    calc
      ent (fun i ↦ f i ^ 2)
          = s * ent (fun i ↦ x i ^ 2) := by
            simpa [x] using ent_smul_sq (f := f) (s := s) hs_def hs_pos
      _ ≤ s * (2 * energy x) := mul_le_mul_of_nonneg_left hent_energy_x hs_pos.le
      _ = 2 * energy f := by linarith

end

end CyclicLsi
