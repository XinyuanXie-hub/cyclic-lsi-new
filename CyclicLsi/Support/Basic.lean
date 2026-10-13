module

public import CyclicLsi.Definitions



/-!
# Shared finite-probability notation

This support file contains elementary lemmas and proof-only abbreviations built
on the public notation from `CyclicLsi.Definitions`.
-/

@[expose] public section

namespace CyclicLsi

open scoped BigOperators

noncomputable section

theorem avg_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    avg f ≤ avg g := by
  unfold avg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ ↦ h x) (by positivity)

theorem avg_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ avg f := by
  unfold avg
  exact div_nonneg (Finset.sum_nonneg fun x _ ↦ hf x) (by positivity)

theorem avg_congr {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ x, f x = g x) :
    avg f = avg g := by
  unfold avg
  congr 1
  exact Finset.sum_congr rfl fun x _ ↦ h x

@[simp]
theorem avg_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    avg (fun x ↦ f x + g x) = avg f + avg g := by
  simp [avg, Finset.sum_add_distrib, add_div]

@[simp]
theorem avg_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    avg (fun x ↦ f x - g x) = avg f - avg g := by
  unfold avg
  rw [Finset.sum_sub_distrib]
  ring

@[simp]
theorem avg_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun x ↦ c * f x) = c * avg f := by
  simp only [avg]
  rw [← Finset.mul_sum]
  ring_nf

@[simp]
theorem avg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    avg (fun _ : α ↦ c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [Fintype.card_ne_zero]

/-- Entropy with respect to the uniform probability measure. -/
def ent {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  avg (fun x ↦ f x * Real.log (f x)) - avg f * Real.log (avg f)

/-- Pointwise nonnegativity for real-valued functions. -/
def Nonnegative {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, 0 ≤ f x

/-- Mean-zero condition with respect to the uniform average. -/
def MeanZero {α : Type*} [Fintype α] (f : α → ℝ) : Prop :=
  avg f = 0

/-- The energy functional for each cyclic group size. -/
abbrev EnergyFamily : Type :=
  (n : ℕ) → (Fin n → ℝ) → ℝ

/-- The cubic expression appearing in PDF Proposition 6. -/
def cubicExpression {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  avg (fun x ↦ (f x - 1) ^ 2 * (f x + 2))

/-- The cubic criterion used in PDF Proposition 6. -/
def CubicCriterionFor (n : ℕ) (energy : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    Nonnegative x → avg (fun i ↦ x i ^ 2) = 1 →
      (1 / 3 : ℝ) * cubicExpression x ≤ energy x

/-- Variance-like quantity `S^2 = Avg(u^2)` from PDF Proposition 7. -/
def Ssq {α : Type*} [Fintype α] (u : α → ℝ) : ℝ :=
  avg (fun x ↦ u x ^ 2)

/-- Surplus energy `Q^2 = energy(u) - S^2` from PDF Proposition 7. -/
def Qsq {n : ℕ} (energy : (Fin n → ℝ) → ℝ) (u : Fin n → ℝ) : ℝ :=
  energy u - Ssq u

/-- The third moment bound used in PDF Proposition 7. -/
def ThirdMomentEstimateFor (n : ℕ) (energy : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ u : Fin n → ℝ,
    MeanZero u → |avg (fun x ↦ u x ^ 3)| ≤ 3 * Ssq u * Real.sqrt (Qsq energy u)

end

end CyclicLsi
