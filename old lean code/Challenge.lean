module
public import Mathlib.Analysis.Fourier.ZMod

/-!
# Log-Sobolev inequality on finite cyclic groups

Comparator statement for Theorem 1 (inequality only) in Xinyuan Xie and
Haonan Zhang, *Sharp log-Sobolev inequalities and quartic stability on finite
cyclic groups*, arXiv:2606.02847v4.

The proof is in `Solution`; `sorry` here marks the Comparator target.
-/

public section

namespace CyclicLsi

/-- Uniform average. -/
noncomputable def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

/-- Fourier coefficient with normalization `1/n` and exponent `-2πikx/n`. -/
noncomputable def fourierCoeff {n : ℕ} [NeZero n] (u : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  (n : ℂ)⁻¹ * ZMod.dft u k

/-- Cyclic word length `min(k, n-k)`. -/
def zmodWordLength {n : ℕ} (k : ZMod n) : ℝ :=
  (k.valMinAbs.natAbs : ℝ)

/-- Theorem 1, excluding sharpness. -/
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

end CyclicLsi
