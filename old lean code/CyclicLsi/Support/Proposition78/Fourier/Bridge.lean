module
public import CyclicLsi.Support.Basic



/-!
# Fourier identities for the third-moment estimates

The third-moment support files are indexed by conjugate frequency blocks.  This
file starts the bridge from functions on a cyclic group to Mathlib's discrete
Fourier transform on `ZMod n`.
-/

namespace CyclicLsi

open scoped BigOperators
open ZMod

@[expose] public noncomputable section

/-- Uniform complex average on `ZMod n`. -/
def zmodAvg {n : ℕ} [NeZero n] (f : ZMod n → ℂ) : ℂ :=
  (∑ x : ZMod n, f x) / (n : ℂ)

/-- Fourier-side word-length energy on `ZMod n`.

This is the concrete energy used by the paper:
`∑ ψ_n(k) |hat u(k)|^2`.
-/
def zmodFourierEnergy {n : ℕ} [NeZero n] (u : ZMod n → ℂ) : ℝ :=
  ∑ k : ZMod n, zmodWordLength k * Complex.normSq (fourierCoeff u k)

/-- The square norm of Fourier coefficients on `ZMod n`. -/
def zmodFourierSsq {n : ℕ} [NeZero n] (u : ZMod n → ℂ) : ℝ :=
  ∑ k : ZMod n, Complex.normSq (fourierCoeff u k)

/-- Fourier-side surplus energy. -/
def zmodFourierQsq {n : ℕ} [NeZero n] (u : ZMod n → ℂ) : ℝ :=
  zmodFourierEnergy u - zmodFourierSsq u

theorem zmodWordLength_neg {n : ℕ} (k : ZMod n) :
    zmodWordLength (-k) = zmodWordLength k := by
  unfold zmodWordLength
  rw [ZMod.natAbs_valMinAbs_neg]

theorem odd_zmodWordLength_pos_freq {m : ℕ} (j : Fin m) :
    zmodWordLength ((j.val + 1 : ℕ) : ZMod (2 * m + 1)) = (j.val + 1 : ℝ) := by
  have : NeZero (2 * m + 1) := ⟨by omega⟩
  have hhalf : j.val + 1 ≤ (2 * m + 1) / 2 := by omega
  unfold zmodWordLength
  rw [ZMod.valMinAbs_natCast_of_le_half hhalf]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_natAbs, Int.cast_abs, Int.cast_add,
    Int.cast_natCast, Int.cast_one, abs_eq_self, ge_iff_le]
  positivity

theorem even_zmodWordLength_middle {m : ℕ} :
    zmodWordLength ((m : ℕ) : ZMod (2 * m)) = (m : ℝ) := by
  have hhalf : m ≤ (2 * m) / 2 := by omega
  unfold zmodWordLength
  rw [ZMod.valMinAbs_natCast_of_le_half hhalf]
  simp

theorem fourierCoeff_zero {n : ℕ} [NeZero n] (u : ZMod n → ℂ) :
    fourierCoeff u 0 = zmodAvg u := by
  simp [fourierCoeff, zmodAvg, ZMod.dft_apply_zero, div_eq_mul_inv, mul_comm]

/-- Fourier inversion in normalized-coefficient form. -/
theorem fourier_expansion {n : ℕ} [NeZero n] (u : ZMod n → ℂ) (x : ZMod n) :
    u x = ∑ k : ZMod n, fourierCoeff u k * ZMod.stdAddChar (k * x) := by
  calc
    u x = (ZMod.dft.symm (ZMod.dft u)) x := by simp
    _ = (n : ℂ)⁻¹ • ∑ k : ZMod n, ZMod.stdAddChar (k * x) • ZMod.dft u k :=
      ZMod.invDFT_apply (ZMod.dft u) x
    _ = ∑ k : ZMod n, fourierCoeff u k * ZMod.stdAddChar (k * x) := by
      simp [fourierCoeff, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Fourier coefficients of real-valued functions satisfy conjugate symmetry. -/
theorem fourierCoeff_real_neg {n : ℕ} [NeZero n] (u : ZMod n → ℝ) (k : ZMod n) :
    fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) (-k) =
      star (fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k) := by
  have hchar (a : ZMod n) :
      star (ZMod.stdAddChar (-a)) = ZMod.stdAddChar a := by
    have h := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := n)) a
    rw [h]
    simp
  have hsum :
      (∑ x : ZMod n, ZMod.stdAddChar (-(x * -k)) * (u x : ℂ)) =
        star (∑ x : ZMod n, ZMod.stdAddChar (-(x * k)) * (u x : ℂ)) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro x _
    calc
      ZMod.stdAddChar (-(x * -k)) * (u x : ℂ)
          = ZMod.stdAddChar (x * k) * (u x : ℂ) := by
            congr 2
            ring
      _ = star (ZMod.stdAddChar (-(x * k)) * (u x : ℂ)) := by
            rw [star_mul, hchar (x * k)]
            simp [mul_comm]
  unfold fourierCoeff
  simp only [ZMod.dft_apply, smul_eq_mul]
  rw [hsum]
  simp [star_mul]
  ring

/-- Raw orthogonality for the standard additive character on `ZMod n`. -/
theorem sum_stdAddChar_mul {n : ℕ} [NeZero n] (k : ZMod n) :
    (∑ x : ZMod n, ZMod.stdAddChar (k * x)) =
      if k = 0 then (n : ℂ) else 0 := by
  simpa [mul_comm] using
    (AddChar.sum_mulShift (R := ZMod n) (R' := ℂ)
      (ψ := ZMod.stdAddChar (N := n)) k (ZMod.isPrimitive_stdAddChar n))

/-- Normalized orthogonality for the standard additive character on `ZMod n`. -/
theorem zmodAvg_stdAddChar_mul {n : ℕ} [NeZero n] (k : ZMod n) :
    zmodAvg (fun x : ZMod n ↦ ZMod.stdAddChar (k * x)) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [zmodAvg, hk, NeZero.ne (n : ℂ)]
  · simp [zmodAvg, sum_stdAddChar_mul, hk]

/-- Cubic character orthogonality: only zero-frequency cubic resonances survive averaging. -/
theorem zmodAvg_stdAddChar_triple {n : ℕ} [NeZero n] (k l r : ZMod n) :
    zmodAvg (fun x : ZMod n ↦
      ZMod.stdAddChar (k * x) * ZMod.stdAddChar (l * x) * ZMod.stdAddChar (r * x)) =
      if k + l + r = 0 then 1 else 0 := by
  have hpoint :
      (fun x : ZMod n ↦
        ZMod.stdAddChar (k * x) * ZMod.stdAddChar (l * x) * ZMod.stdAddChar (r * x)) =
        fun x : ZMod n ↦ ZMod.stdAddChar ((k + l + r) * x) := by
    funext x
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hpoint]
  exact zmodAvg_stdAddChar_mul (k + l + r)

theorem zmodAvg_const_mul {n : ℕ} [NeZero n] (c : ℂ) (f : ZMod n → ℂ) :
    zmodAvg (fun x : ZMod n ↦ c * f x) = c * zmodAvg f := by
  unfold zmodAvg
  change (∑ x : ZMod n, c * f x) / (n : ℂ) =
    c * ((∑ x : ZMod n, f x) / (n : ℂ))
  rw [← Finset.mul_sum]
  ring

theorem zmodAvg_sum3 {n : ℕ} [NeZero n] {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ZMod n → ℂ) :
    zmodAvg (fun x : ZMod n ↦ ∑ a : α, ∑ b : β, ∑ c : γ, F a b c x) =
      ∑ a : α, ∑ b : β, ∑ c : γ, zmodAvg (fun x : ZMod n ↦ F a b c x) := by
  unfold zmodAvg
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  congr with a
  rw [Finset.sum_comm]
  congr with b
  rw [Finset.sum_comm]

theorem zmodAvg_sum {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]
    (f : ι → ZMod n → ℂ) :
    zmodAvg (fun x ↦ ∑ i, f i x) = ∑ i, zmodAvg (f i) := by
  unfold zmodAvg
  rw [Finset.sum_comm]
  simp [Finset.sum_div]

theorem zmodAvg_char_conj_mul {n : ℕ} [NeZero n] (k l : ZMod n) :
    zmodAvg (fun x : ZMod n ↦
      star (ZMod.stdAddChar (k * x)) * ZMod.stdAddChar (l * x)) =
      if l - k = 0 then 1 else 0 := by
  have hpoint :
      (fun x : ZMod n ↦
        star (ZMod.stdAddChar (k * x)) * ZMod.stdAddChar (l * x)) =
        fun x : ZMod n ↦ ZMod.stdAddChar ((l - k) * x) := by
    funext x
    have hconj :=
      (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := n)) (k * x)).symm
    change (starRingEnd ℂ) (ZMod.stdAddChar (k * x)) * ZMod.stdAddChar (l * x) =
      ZMod.stdAddChar ((l - k) * x)
    rw [hconj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hpoint]
  exact zmodAvg_stdAddChar_mul (l - k)

/-- Parseval identity for the normalized Fourier coefficients. -/
theorem parseval_inner {n : ℕ} [NeZero n] (u v : ZMod n → ℂ) :
    zmodAvg (fun x : ZMod n ↦ star (u x) * v x) =
      ∑ k : ZMod n, star (fourierCoeff u k) * fourierCoeff v k := by
  have hpoint :
      (fun x : ZMod n ↦ star (u x) * v x) =
      fun x : ZMod n ↦
        ∑ k : ZMod n, ∑ l : ZMod n,
          (star (fourierCoeff u k) * fourierCoeff v l) *
            (star (ZMod.stdAddChar (k * x)) * ZMod.stdAddChar (l * x)) := by
    funext x
    rw [fourier_expansion u x, fourier_expansion v x]
    simp_rw [star_sum, star_mul]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hpoint]
  rw [zmodAvg_sum]
  congr with k
  rw [zmodAvg_sum]
  calc
    (∑ l : ZMod n,
        zmodAvg fun x ↦
          (star (fourierCoeff u k) * fourierCoeff v l) *
            (star (ZMod.stdAddChar (k * x)) * ZMod.stdAddChar (l * x)))
        = ∑ l : ZMod n,
            (star (fourierCoeff u k) * fourierCoeff v l) *
              (if l - k = 0 then (1 : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [zmodAvg_const_mul, zmodAvg_char_conj_mul]
    _ = star (fourierCoeff u k) * fourierCoeff v k := by
          simp [sub_eq_zero]

/-- Parseval identity in squared-modulus form, still as a complex equality. -/
theorem parseval_normSq_complex {n : ℕ} [NeZero n] (u : ZMod n → ℂ) :
    zmodAvg (fun x : ZMod n ↦ (Complex.normSq (u x) : ℂ)) =
      ∑ k : ZMod n, (Complex.normSq (fourierCoeff u k) : ℂ) := by
  simpa [Complex.normSq_eq_conj_mul_self] using parseval_inner u u

/-- Parseval identity in real squared-modulus form. -/
theorem parseval_normSq_real {n : ℕ} [NeZero n] (u : ZMod n → ℂ) :
    (∑ x : ZMod n, Complex.normSq (u x)) / (n : ℝ) =
      ∑ k : ZMod n, Complex.normSq (fourierCoeff u k) := by
  apply Complex.ofReal_injective
  simpa [zmodAvg, Complex.ofReal_sum, Complex.ofReal_div] using
    parseval_normSq_complex u

/-- Parseval for real-valued functions on `ZMod n`. -/
theorem parseval_real_sq {n : ℕ} [NeZero n] (u : ZMod n → ℝ) :
    (∑ x : ZMod n, u x ^ 2) / (n : ℝ) =
      ∑ k : ZMod n,
        Complex.normSq (fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k) := by
  simpa [Complex.normSq_ofReal, pow_two] using
    parseval_normSq_real (fun x : ZMod n ↦ (u x : ℂ))

theorem norm_fourierCoeff_neg_real {n : ℕ} [NeZero n]
    (u : ZMod n → ℝ) (k : ZMod n) :
    ‖fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) (-k)‖ =
      ‖fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k‖ := by
  rw [fourierCoeff_real_neg]
  simp

theorem normSq_fourierCoeff_neg_real {n : ℕ} [NeZero n]
    (u : ZMod n → ℝ) (k : ZMod n) :
    Complex.normSq (fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) (-k)) =
      Complex.normSq (fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k) := by
  rw [fourierCoeff_real_neg]
  simp [Complex.normSq_conj]

theorem sqrt_two_norm_sq (z : ℂ) :
    (Real.sqrt 2 * ‖z‖) ^ 2 = 2 * Complex.normSq z := by
  rw [Complex.normSq_eq_norm_sq]
  rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

theorem cube_sum_expand {α : Type*} [Fintype α] (a : α → ℂ) :
    (∑ k : α, a k) ^ 3 =
      ∑ k : α, ∑ l : α, ∑ r : α, a k * a l * a r := by
  have hpow (z : ℂ) : z ^ 3 = z * z * z := by ring
  rw [hpow]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  simp [mul_comm, mul_left_comm]

theorem zmodAvg_coeff_stdAddChar_triple {n : ℕ} [NeZero n]
    (a b c : ℂ) (k l r : ZMod n) :
    zmodAvg (fun x : ZMod n ↦
      (a * ZMod.stdAddChar (k * x)) *
      (b * ZMod.stdAddChar (l * x)) *
      (c * ZMod.stdAddChar (r * x))) =
    a * b * c * (if k + l + r = 0 then (1 : ℂ) else 0) := by
  have hpoint :
      (fun x : ZMod n ↦
        (a * ZMod.stdAddChar (k * x)) *
        (b * ZMod.stdAddChar (l * x)) *
        (c * ZMod.stdAddChar (r * x))) =
      fun x : ZMod n ↦
        (a * b * c) *
          (ZMod.stdAddChar (k * x) *
           ZMod.stdAddChar (l * x) *
           ZMod.stdAddChar (r * x)) := by
    funext x
    ring
  rw [hpoint, zmodAvg_const_mul, zmodAvg_stdAddChar_triple]

theorem zmodAvg_cube_eq_resonant_sum {n : ℕ} [NeZero n] (u : ZMod n → ℂ) :
    zmodAvg (fun x : ZMod n ↦ u x ^ 3) =
      ∑ k : ZMod n, ∑ l : ZMod n, ∑ r : ZMod n,
        fourierCoeff u k * fourierCoeff u l * fourierCoeff u r *
          (if k + l + r = 0 then (1 : ℂ) else 0) := by
  have hpoint :
      (fun x : ZMod n ↦ u x ^ 3) =
      fun x : ZMod n ↦
        ∑ k : ZMod n, ∑ l : ZMod n, ∑ r : ZMod n,
          (fourierCoeff u k * ZMod.stdAddChar (k * x)) *
          (fourierCoeff u l * ZMod.stdAddChar (l * x)) *
          (fourierCoeff u r * ZMod.stdAddChar (r * x)) := by
    funext x
    rw [fourier_expansion u x]
    exact cube_sum_expand
      (fun k : ZMod n ↦ fourierCoeff u k * ZMod.stdAddChar (k * x))
  rw [hpoint, zmodAvg_sum3]
  congr with k
  congr with l
  congr with r
  rw [zmodAvg_coeff_stdAddChar_triple]

/-- Real-valued average on `ZMod n`. -/
def zmodAvgR {n : ℕ} [NeZero n] (f : ZMod n → ℝ) : ℝ :=
  (∑ x : ZMod n, f x) / (n : ℝ)

theorem zmodAvgR_cast {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    ((zmodAvgR f : ℝ) : ℂ) =
      zmodAvg (fun x : ZMod n ↦ (f x : ℂ)) := by
  simp [zmodAvgR, zmodAvg, Complex.ofReal_sum, Complex.ofReal_div]

theorem zmodAvgR_eq_avg {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    zmodAvgR f = avg f := by
  simp [zmodAvgR, avg, ZMod.card]

theorem fourierCoeff_zero_of_meanZero {n : ℕ} [NeZero n]
    {u : ZMod n → ℝ} (hu : MeanZero u) :
    fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) 0 = 0 := by
  rw [fourierCoeff_zero]
  rw [← zmodAvgR_cast]
  rw [zmodAvgR_eq_avg]
  exact_mod_cast hu

theorem abs_zmodAvgR_eq_norm_zmodAvgC {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    |zmodAvgR f| = ‖zmodAvg (fun x : ZMod n ↦ (f x : ℂ))‖ := by
  rw [← zmodAvgR_cast f]
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem abs_avg_cube_le_resonant_norm_sum {n : ℕ} [NeZero n] (u : ZMod n → ℝ) :
    |avg (fun x : ZMod n ↦ u x ^ 3)| ≤
      ∑ k : ZMod n, ∑ l : ZMod n, ∑ r : ZMod n,
        if k + l + r = 0 then
          ‖fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k‖ *
            ‖fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) l‖ *
            ‖fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) r‖
        else
          0 := by
  let c : ZMod n → ℂ := fun k ↦ fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k
  have hcube :
      zmodAvg (fun x : ZMod n ↦ ((u x : ℂ) ^ 3)) =
        ∑ k : ZMod n, ∑ l : ZMod n, ∑ r : ZMod n,
          c k * c l * c r * (if k + l + r = 0 then (1 : ℂ) else 0) := by
    simpa [c] using
      zmodAvg_cube_eq_resonant_sum (fun x : ZMod n ↦ (u x : ℂ))
  calc
    |avg (fun x : ZMod n ↦ u x ^ 3)|
        = ‖zmodAvg (fun x : ZMod n ↦ ((u x : ℂ) ^ 3))‖ := by
          rw [← zmodAvgR_eq_avg (fun x : ZMod n ↦ u x ^ 3)]
          rw [abs_zmodAvgR_eq_norm_zmodAvgC]
          congr with x
          norm_num [Complex.ofReal_pow]
    _ = ‖∑ k : ZMod n, ∑ l : ZMod n, ∑ r : ZMod n,
          c k * c l * c r * (if k + l + r = 0 then (1 : ℂ) else 0)‖ := by
          rw [hcube]
    _ ≤ ∑ k : ZMod n, ‖∑ l : ZMod n, ∑ r : ZMod n,
          c k * c l * c r * (if k + l + r = 0 then (1 : ℂ) else 0)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ k : ZMod n, ∑ l : ZMod n,
          ‖∑ r : ZMod n,
            c k * c l * c r * (if k + l + r = 0 then (1 : ℂ) else 0)‖ := by
          exact Finset.sum_le_sum fun k _ ↦ norm_sum_le _ _
    _ ≤ ∑ k : ZMod n, ∑ l : ZMod n, ∑ r : ZMod n,
          ‖c k * c l * c r * (if k + l + r = 0 then (1 : ℂ) else 0)‖ := by
          exact Finset.sum_le_sum fun k _ ↦
            Finset.sum_le_sum fun l _ ↦ norm_sum_le _ _
    _ = ∑ k : ZMod n, ∑ l : ZMod n, ∑ r : ZMod n,
        if k + l + r = 0 then ‖c k‖ * ‖c l‖ * ‖c r‖ else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          apply Finset.sum_congr rfl
          intro r _
          by_cases h : k + l + r = 0
          · simp [h, mul_assoc]
          · simp [h]
    _ = ∑ k : ZMod n, ∑ l : ZMod n, ∑ r : ZMod n,
        if k + l + r = 0 then
          ‖fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k‖ *
            ‖fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) l‖ *
            ‖fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) r‖
        else
          0 := by
          rfl

end

end CyclicLsi
