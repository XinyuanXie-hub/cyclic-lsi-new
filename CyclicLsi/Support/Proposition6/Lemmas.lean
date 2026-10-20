import CyclicLsi.Support.Basic



/-!
# Proposition 8: entropy from the normalized cubic criterion

This file contains normalization and entropy-scaling lemmas supporting
Proposition 8 in `CyclicLsi.Support.Proposition6`.
-/

namespace CyclicLsi

open scoped BigOperators

noncomputable section

/-- Quadratic homogeneity of an energy functional. -/
def QuadraticHomogeneous {α : Type*} (energy : (α → ℝ) → ℝ) : Prop :=
  ∀ (c : ℝ) (f : α → ℝ), energy (fun x ↦ c * f x) = c ^ 2 * energy f

lemma avg_sq_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun x ↦ (c * f x) ^ 2) = c ^ 2 * avg (fun x ↦ f x ^ 2) := by
  calc
    avg (fun x ↦ (c * f x) ^ 2)
        = avg (fun x ↦ c ^ 2 * f x ^ 2) := by
          congr
          ext x
          ring
    _ = c ^ 2 * avg (fun x ↦ f x ^ 2) := avg_const_mul (c ^ 2) _

lemma avg_sq_nonneg {α : Type*} [Fintype α] (f : α → ℝ) :
    0 ≤ avg (fun x ↦ f x ^ 2) :=
  avg_nonneg fun x ↦ sq_nonneg (f x)

/-- If the average square is zero on a nonempty finite type, the function is zero. -/
lemma eq_zero_of_avg_sq_eq_zero {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} (hf : avg (fun x ↦ f x ^ 2) = 0) :
    f = fun _ ↦ 0 := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum_div : (∑ x, f x ^ 2) / (Fintype.card α : ℝ) = 0 := by
    simpa [avg] using hf
  have hsum : (∑ x, f x ^ 2) = 0 := by
    exact (div_eq_zero_iff.mp hsum_div).resolve_right hcard
  funext x
  have hx_sq : f x ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ ↦ sq_nonneg (f y))).mp hsum x (Finset.mem_univ x)
  exact sq_eq_zero_iff.mp hx_sq

lemma ent_zero {α : Type*} [Fintype α] :
    ent (fun _ : α ↦ 0) = 0 := by
  simp [ent, avg]

lemma energy_zero_of_quadraticHomogeneous {α : Type*}
    {energy : (α → ℝ) → ℝ} (hhom : QuadraticHomogeneous energy) :
    energy (fun _ : α ↦ 0) = 0 := by
  simpa using hhom 0 (fun _ : α ↦ 0)

/-- Averaging the pointwise cubic majorant gives the normalized entropy bound. -/
theorem ent_le_two_thirds_cubic_of_normalized {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ}
    (hmajor :
      ∀ t : ℝ, 0 ≤ t →
        t ^ 2 * Real.log (t ^ 2) ≤
          (2 / 3 : ℝ) * ((t - 1) ^ 2 * (t + 2)) + (t ^ 2 - 1))
    (hf_nonneg : Nonnegative f) (hf_norm : avg (fun x ↦ f x ^ 2) = 1) :
    ent (fun x ↦ f x ^ 2) ≤ (2 / 3 : ℝ) * cubicExpression f := by
  let lhs : α → ℝ := fun x ↦ f x ^ 2 * Real.log (f x ^ 2)
  let cubicTerm : α → ℝ := fun x ↦ (f x - 1) ^ 2 * (f x + 2)
  have hpoint : ∀ x, lhs x ≤ (2 / 3 : ℝ) * cubicTerm x + (f x ^ 2 - 1) := by
    intro x
    simpa [lhs, cubicTerm] using hmajor (f x) (hf_nonneg x)
  have havg_point : avg lhs ≤ avg (fun x ↦ (2 / 3 : ℝ) * cubicTerm x + (f x ^ 2 - 1)) :=
    avg_mono hpoint
  have htail : avg (fun x ↦ f x ^ 2 - 1) = 0 := by
    rw [avg_sub, hf_norm, avg_const]
    norm_num
  have hrhs :
      avg (fun x ↦ (2 / 3 : ℝ) * cubicTerm x + (f x ^ 2 - 1))
        = (2 / 3 : ℝ) * cubicExpression f := by
    rw [avg_add, avg_const_mul, htail]
    simp [cubicExpression, cubicTerm]
  have hent : ent (fun x ↦ f x ^ 2) = avg lhs := by
    simp [ent, lhs, hf_norm]
  exact hent.trans_le (havg_point.trans_eq hrhs)

lemma normalized_smul {α : Type*} [Fintype α] {f : α → ℝ}
    {s : ℝ} (hs : s = avg (fun x ↦ f x ^ 2)) (hs_pos : 0 < s) :
    avg (fun x ↦ ((√s)⁻¹ * f x) ^ 2) = 1 := by
  rw [avg_sq_smul]
  have hs_sqrt_sq : (√s) ^ 2 = s := Real.sq_sqrt hs_pos.le
  have hs_ne : s ≠ 0 := hs_pos.ne'
  calc
    (√s)⁻¹ ^ 2 * avg (fun x ↦ f x ^ 2)
        = (√s)⁻¹ ^ 2 * s := by rw [hs]
    _ = s⁻¹ * s := by rw [inv_pow, hs_sqrt_sq]
    _ = 1 := inv_mul_cancel₀ hs_ne

lemma nonnegative_smul_of_nonnegative {α : Type*} {c : ℝ} {f : α → ℝ}
    (hc : 0 ≤ c) (hf : Nonnegative f) :
    Nonnegative (fun x ↦ c * f x) := by
  intro x
  exact mul_nonneg hc (hf x)

lemma ent_smul_sq {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {s : ℝ} (hs : s = avg (fun x ↦ f x ^ 2)) (hs_pos : 0 < s) :
    ent (fun x ↦ f x ^ 2)
      = s * ent (fun x ↦ ((√s)⁻¹ * f x) ^ 2) := by
  let g : α → ℝ := fun x ↦ ((√s)⁻¹ * f x) ^ 2
  have hs_sqrt_sq : (√s) ^ 2 = s := Real.sq_sqrt hs_pos.le
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hsqrt_ne : √s ≠ 0 := by
    exact (Real.sqrt_ne_zero hs_pos.le).mpr hs_ne
  have hf_as_scaled : (fun x ↦ f x ^ 2) = fun x ↦ s * g x := by
    funext x
    change f x ^ 2 = s * (((√s)⁻¹ * f x) ^ 2)
    have hs_inv : s * (√s)⁻¹ ^ 2 = 1 := by
      rw [inv_pow, hs_sqrt_sq]
      exact mul_inv_cancel₀ hs_ne
    calc
      f x ^ 2 = 1 * f x ^ 2 := by ring
      _ = (s * (√s)⁻¹ ^ 2) * f x ^ 2 := by rw [hs_inv]
      _ = s * (((√s)⁻¹ * f x) ^ 2) := by ring
  have hg_norm : avg g = 1 := by
    simpa [g] using normalized_smul (f := f) (s := s) hs hs_pos
  have hlog_point :
      ∀ x, s * g x * Real.log (s * g x) =
        s * (g x * Real.log (g x)) + (s * Real.log s) * g x := by
    intro x
    by_cases hgx : g x = 0
    · simp [hgx]
    · have hs_mul_ne : s * g x ≠ 0 := mul_ne_zero hs_ne hgx
      rw [Real.log_mul hs_ne hgx]
      ring
  have havg_smul : avg (fun x ↦ s * g x) = s := by
    rw [avg_const_mul, hg_norm, mul_one]
  have havg_log :
      avg (fun x ↦ s * g x * Real.log (s * g x))
        = s * avg (fun x ↦ g x * Real.log (g x)) + s * Real.log s := by
    calc
      avg (fun x ↦ s * g x * Real.log (s * g x))
          = avg (fun x ↦ s * (g x * Real.log (g x)) + (s * Real.log s) * g x) := by
            congr
            ext x
            exact hlog_point x
      _ = avg (fun x ↦ s * (g x * Real.log (g x)))
            + avg (fun x ↦ (s * Real.log s) * g x) := avg_add _ _
      _ = s * avg (fun x ↦ g x * Real.log (g x)) + s * Real.log s := by
            rw [avg_const_mul, avg_const_mul, hg_norm, mul_one]
  calc
    ent (fun x ↦ f x ^ 2)
        = ent (fun x ↦ s * g x) := by rw [hf_as_scaled]
    _ = avg (fun x ↦ s * (g x * Real.log (g x))) := by
      simp only [ent]
      rw [havg_log, havg_smul, avg_const_mul]
      ring_nf
    _ = s * avg (fun x ↦ g x * Real.log (g x)) := by
      rw [avg_const_mul]
    _ = s * ent g := by
      simp [ent, hg_norm]

end

end CyclicLsi
