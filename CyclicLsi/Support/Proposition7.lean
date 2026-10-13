module

public import CyclicLsi.Support.Basic



/-!
# Proposition 7: cubic criterion from the third-moment estimate

This file formalizes the algebraic reduction from a mean-zero third moment
estimate to the cubic criterion.  The proof states explicitly the two energy
facts used in the paper:

* adding constants does not change the Dirichlet energy;
* the surplus `Q^2 = E(u) - S^2` is nonnegative for mean-zero `u`.
-/

@[expose] public section

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Center a function by subtracting its uniform average. -/
def centered {α : Type*} [Fintype α] (x : α → ℝ) : α → ℝ :=
  fun i ↦ x i - avg x

theorem centered_meanZero_fin {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ) :
    MeanZero (centered x) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  unfold MeanZero centered
  rw [avg_sub, avg_const]
  ring

theorem Ssq_centered_eq {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ) :
    Ssq (centered x) = avg (fun i ↦ x i ^ 2) - avg x ^ 2 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  unfold Ssq centered
  have hpoint :
      ∀ i : Fin n,
        (x i - avg x) ^ 2 = x i ^ 2 + (-2 * avg x) * x i + avg x ^ 2 := by
    intro i
    ring
  calc
    avg (fun i ↦ (x i - avg x) ^ 2)
        = avg (fun i ↦ x i ^ 2 + (-2 * avg x) * x i + avg x ^ 2) :=
          avg_congr hpoint
    _ = avg (fun i ↦ x i ^ 2) - avg x ^ 2 := by
      rw [avg_add, avg_add, avg_const_mul, avg_const]
      ring

theorem cubicExpression_centered_expansion {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ)
    (hnorm : avg (fun i ↦ x i ^ 2) = 1) :
    cubicExpression x = 2 - 2 * avg x ^ 3 + avg (fun i ↦ centered x i ^ 3) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  let a : ℝ := avg x
  let u : Fin n → ℝ := centered x
  have hu_avg : avg u = 0 := centered_meanZero_fin hn x
  have hu_sq : avg (fun i ↦ u i ^ 2) = 1 - a ^ 2 := by
    dsimp [u, a]
    simpa [Ssq] using Ssq_centered_eq hn x |>.trans (by rw [hnorm])
  have hx_eq : ∀ i : Fin n, x i = a + u i := by
    intro i
    dsimp [a, u, centered]
    ring
  have hpoly₁ :
      ∀ i : Fin n, (x i - 1) ^ 2 * (x i + 2) = x i ^ 3 - 3 * x i + 2 := by
    intro i
    ring
  have hpoly₂ :
      ∀ i : Fin n,
        x i ^ 3 = a ^ 3 + (3 * a ^ 2) * u i + (3 * a) * u i ^ 2 + u i ^ 3 := by
    intro i
    rw [hx_eq i]
    ring
  unfold cubicExpression
  calc
    avg (fun i ↦ (x i - 1) ^ 2 * (x i + 2))
        = avg (fun i ↦ x i ^ 3 - 3 * x i + 2) := avg_congr hpoly₁
    _ = avg (fun i ↦
          (a ^ 3 + (3 * a ^ 2) * u i + (3 * a) * u i ^ 2 + u i ^ 3)
            - 3 * x i + 2) := by
          apply avg_congr
          intro i
          rw [hpoly₂ i]
    _ = 2 - 2 * a ^ 3 + avg (fun i ↦ u i ^ 3) := by
      rw [avg_add, avg_sub, avg_add, avg_add, avg_add]
      rw [avg_const, avg_const_mul, hu_avg, avg_const_mul, hu_sq]
      have hxavg : avg x = a := rfl
      rw [avg_const_mul, hxavg, avg_const]
      ring

end

end CyclicLsi
