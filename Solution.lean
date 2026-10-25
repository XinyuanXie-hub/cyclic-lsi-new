module
public import CyclicLsi.Definitions
import CyclicLsi

/-!
# Solution: Theorem 1

This file proves the inequality in Theorem 1 of arXiv:2606.02847v4 using
Lemma 7 and Propositions 8–11. The Lean names `proposition6`–`proposition9`
retain the numbering from v2.

The shared definitions live in `CyclicLsi.Definitions` so the supporting proofs
can import them without depending on this solution module. `Challenge.lean`
states the same definitions independently for Comparator.

Statement dictionary:

* Mathlib/Lean: `ℕ`, `ℝ`, `ℂ`, `ZMod n`, `Real.log`, `Complex.normSq`,
  finite sums `∑`, powers, inequalities, and the coercion `ℝ → ℂ`.
* `avg` is defined in `CyclicLsi.Definitions`; it is the uniform average
  `π(g) = |G|⁻¹ ∑ x, g x`.
* `fourierCoeff` is defined in `CyclicLsi.Definitions`; it is the normalized
  Fourier coefficient `\hat f(k)`.
* `zmodWordLength` is defined in `CyclicLsi.Definitions`; it is the cyclic
  word length `ψ_n(k) = min(k,n-k)`.
* The right-hand side is the Fourier-multiplier expression for
  `2 π(f A_{ψ_n} f)`.
-/

namespace CyclicLsi

/-- Theorem 1 of arXiv:2606.02847v4, excluding sharpness. -/
public theorem theorem1 (n : ℕ) (hn : 4 ≤ n)
    (f : ZMod n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 3) hn)⟩
    avg (fun x : ZMod n ↦ f x ^ 2 * Real.log (f x ^ 2)) -
        avg (fun x : ZMod n ↦ f x ^ 2) *
          Real.log (avg (fun x : ZMod n ↦ f x ^ 2)) ≤
      2 * ∑ k : ZMod n,
        zmodWordLength k *
          Complex.normSq (fourierCoeff (fun x : ZMod n ↦ (f x : ℂ)) k) := by
  let : NeZero n := ⟨by omega⟩
  have hfin :
      ∀ n : ℕ, 4 ≤ n →
        ∀ f : Fin n → ℝ, Nonnegative f →
          ent (fun x ↦ f x ^ 2) ≤ 2 * finWordEnergy n f :=
    theorem1_from_propositions6_7_8_9
      (by
        intro n hn hcubic f hf
        exact proposition6
          (n := n) (by omega) pointwiseCubicMajorant
          (finWordEnergy_quadraticHomogeneous_ge4 hn) hcubic f hf)
      (by
        intro n hn hthird x hx_nonneg hx_norm
        exact proposition7
          (n := n) (by omega) (finWordEnergy_centered_ge4 hn)
          (finWordEnergy_qsq_nonneg_ge4 hn)
          hthird x hx_nonneg hx_norm)
      proposition8_finWordEnergy
      proposition9_finWordEnergy
  let e : ZMod n ≃ Fin n := (finZModEquiv n).symm
  let ffin : Fin n → ℝ := pullEquiv e f
  have hffin_nonneg : Nonnegative ffin := by
    intro i
    exact hf (e.symm i)
  have hmain := hfin n hn ffin hffin_nonneg
  have hent :
      ent (fun i : Fin n ↦ ffin i ^ 2) =
        ent (fun x : ZMod n ↦ f x ^ 2) := by
    unfold ent
    have hlog :
        avg (fun i : Fin n ↦ ffin i ^ 2 * Real.log (ffin i ^ 2)) =
          avg (fun x : ZMod n ↦ f x ^ 2 * Real.log (f x ^ 2)) := by
      simpa only [ffin, pullEquiv] using!
        avg_pullEquiv e (fun x : ZMod n ↦ f x ^ 2 * Real.log (f x ^ 2))
    have hsquare :
        avg (fun i : Fin n ↦ ffin i ^ 2) =
          avg (fun x : ZMod n ↦ f x ^ 2) := by
      simpa only [ffin, pullEquiv] using!
        avg_pullEquiv e (fun x : ZMod n ↦ f x ^ 2)
    rw [hlog, hsquare]
  have henergy : finWordEnergy n ffin = zmodWordEnergyReal f := by
    rw [finWordEnergy_of_ne]
    congr 1
    funext z
    simp [ffin, finToZModFun, pullEquiv, e]
  rw [hent, henergy] at hmain
  simpa [ent, zmodWordEnergyReal, zmodFourierEnergy] using hmain

end CyclicLsi

-- Reader checks: the full statement and its transitive axiom dependencies.
#check @CyclicLsi.theorem1
#print axioms CyclicLsi.theorem1
