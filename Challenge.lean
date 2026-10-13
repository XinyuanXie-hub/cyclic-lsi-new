module

public import Mathlib.Analysis.Fourier.ZMod

/-!
# Log-Sobolev inequality on finite cyclic groups

This independent statement records the inequality in Theorem 1 of Xinyuan
Xie and Haonan Zhang, *Sharp log-Sobolev inequalities on finite cyclic groups*,
arXiv:2606.02847v2. It imports only Mathlib, not the proof development.

For `n ≥ 4` and a nonnegative real function `f` on `ZMod n`,
`Ent_π(f²) ≤ 2 ∑ k, ψₙ(k) |f̂(k)|²`, where `π` is uniform probability,
`ψₙ(k) = min(k, n-k)`, and `f̂` is the normalized discrete Fourier transform.
At zero the convention is `0 * log 0 = 0`, as in Lean's `Real.log`.

Only this inequality is compared. Optimality of the constant, complex-valued
functions, hypercontractivity, and the circle theorem are outside this claim.
The deliberate `sorry` below is permitted in the Challenge, never in the
corresponding proved declaration in `CyclicLsi.MainTheorem`.
-/

@[expose] public section

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Uniform probability average; on `ZMod n` its denominator is `n`. -/
def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

/-- Normalized Fourier coefficient, with Mathlib's negative-exponent convention. -/
def fourierCoeff {n : ℕ} [NeZero n] (u : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  (n : ℂ)⁻¹ * ZMod.dft u k

/-- Cyclic word length: the absolute value of a least-absolute integer representative. -/
def zmodWordLength {n : ℕ} (k : ZMod n) : ℝ :=
  (k.valMinAbs.natAbs : ℝ)

/-- The word-length log-Sobolev inequality for nonnegative real functions, `n ≥ 4`. -/
theorem theorem1 (n : ℕ) (hn : 4 ≤ n)
    (f : ZMod n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 3) hn)⟩
    avg (fun x : ZMod n ↦ f x ^ 2 * Real.log (f x ^ 2)) -
        avg (fun x : ZMod n ↦ f x ^ 2) *
          Real.log (avg (fun x : ZMod n ↦ f x ^ 2)) ≤
      2 * ∑ k : ZMod n,
        zmodWordLength k *
          Complex.normSq (fourierCoeff (fun x : ZMod n ↦ (f x : ℂ)) k) := by
  sorry

end

end CyclicLsi
