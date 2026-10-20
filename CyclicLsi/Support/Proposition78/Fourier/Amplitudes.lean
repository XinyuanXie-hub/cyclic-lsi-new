import CyclicLsi.Support.Proposition78.Fourier.Transport
import CyclicLsi.Support.Proposition78.BlockBounds
import CyclicLsi.Support.Proposition78.EvenCase.Resonance



/-!
# Fourier amplitudes for the odd and even third-moment estimates

This file introduces the real nonnegative amplitude vectors used by the block
estimates and records the Parseval bridge from physical square averages to
Fourier square sums.
-/

namespace CyclicLsi

open scoped BigOperators

noncomputable section

abbrev realFourierCoeff {n : ℕ} [NeZero n]
    (u : ZMod n → ℝ) (k : ZMod n) : ℂ :=
  fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k

def oddFourierAmp (m : ℕ) (u : ZMod (2 * m + 1) → ℝ) : Fin m → ℝ :=
  fun j ↦
    letI : NeZero (2 * m + 1) := ⟨by omega⟩
    Real.sqrt 2 * ‖realFourierCoeff u ((j.val + 1 : ℕ) : ZMod (2 * m + 1))‖

def evenFourierAmp {m : ℕ} [NeZero (2 * m)]
    (u : ZMod (2 * m) → ℝ) : Fin m → ℝ :=
  fun j ↦
    if j.val + 1 = m then
      ‖realFourierCoeff u ((j.val + 1 : ℕ) : ZMod (2 * m))‖
    else
      Real.sqrt 2 * ‖realFourierCoeff u ((j.val + 1 : ℕ) : ZMod (2 * m))‖

def blockEnergy {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, (j.val + 1 : ℝ) * a j ^ 2

theorem blockQsq_eq_blockEnergy_sub_blockSsq {m : ℕ} (a : Fin m → ℝ) :
    blockQsq a = blockEnergy a - blockSsq a := by
  unfold blockQsq blockEnergy blockSsq
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem zmodFourierSsq_eq_Ssq_real {n : ℕ} [NeZero n] (u : ZMod n → ℝ) :
    zmodFourierSsq (fun x : ZMod n ↦ (u x : ℂ)) = Ssq u := by
  unfold zmodFourierSsq Ssq avg
  rw [← parseval_real_sq u]
  simp [ZMod.card]

def finCastZModEquiv (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun i := (i.val : ZMod n)
  invFun k := ⟨k.val, ZMod.val_lt k⟩
  left_inv := by
    intro i
    apply Fin.ext
    simp [ZMod.val_natCast_of_lt i.isLt]
  right_inv := by
    intro k
    exact ZMod.natCast_zmod_val k

inductive OddFullFreq (m : ℕ) where
  | zero : OddFullFreq m
  | pos : Fin m → OddFullFreq m
  | neg : Fin m → OddFullFreq m
  deriving DecidableEq, Fintype, Repr

def oddFullFreqToFin {m : ℕ} : OddFullFreq m → Fin (2 * m + 1)
  | OddFullFreq.zero => ⟨0, by omega⟩
  | OddFullFreq.pos j => ⟨j.val + 1, by omega⟩
  | OddFullFreq.neg j => ⟨2 * m - j.val, by omega⟩

def oddFullFreqOfFin {m : ℕ} (k : Fin (2 * m + 1)) : OddFullFreq m :=
  if h0 : k.val = 0 then
    OddFullFreq.zero
  else if hle : k.val ≤ m then
    OddFullFreq.pos ⟨k.val - 1, by omega⟩
  else
    OddFullFreq.neg ⟨2 * m - k.val, by omega⟩

theorem oddFullFreq_left_inv {m : ℕ} :
    Function.LeftInverse (oddFullFreqOfFin (m := m)) (oddFullFreqToFin (m := m)) := by
  intro f
  cases f with
  | zero => simp [oddFullFreqOfFin, oddFullFreqToFin]
  | pos j =>
      have hj : j.val < m := j.isLt
      have hle : j.val + 1 ≤ m := by omega
      simp [oddFullFreqOfFin, oddFullFreqToFin, hle]
  | neg j =>
      have hj : j.val < m := j.isLt
      have h0 : 2 * m - j.val ≠ 0 := by omega
      have hnle : ¬2 * m - j.val ≤ m := by omega
      simp [oddFullFreqOfFin, oddFullFreqToFin, h0, hnle]
      congr
      omega

theorem oddFullFreq_right_inv {m : ℕ} :
    Function.RightInverse (oddFullFreqOfFin (m := m)) (oddFullFreqToFin (m := m)) := by
  intro k
  apply Fin.ext
  unfold oddFullFreqOfFin
  split_ifs with h0 hle
  · exact h0.symm
  · simp only [oddFullFreqToFin]
    have hklt : k.val < 2 * m + 1 := k.isLt
    omega
  · simp only [oddFullFreqToFin]
    have hklt : k.val < 2 * m + 1 := k.isLt
    omega

def oddFullFreqEquivFin (m : ℕ) : OddFullFreq m ≃ Fin (2 * m + 1) where
  toFun := oddFullFreqToFin
  invFun := oddFullFreqOfFin
  left_inv := oddFullFreq_left_inv
  right_inv := oddFullFreq_right_inv

def oddFullFreqEquivZMod (m : ℕ) : OddFullFreq m ≃ ZMod (2 * m + 1) := by
  haveI : NeZero (2 * m + 1) := ⟨by omega⟩
  exact (oddFullFreqEquivFin m).trans (finCastZModEquiv (2 * m + 1))

def oddFullFreqZ {m : ℕ} (f : OddFullFreq m) : ZMod (2 * m + 1) :=
  oddFullFreqEquivZMod m f

theorem oddFullFreqZ_zero {m : ℕ} :
    oddFullFreqZ (OddFullFreq.zero (m := m)) = 0 := by
  simp [oddFullFreqZ, oddFullFreqEquivZMod, oddFullFreqEquivFin, oddFullFreqToFin,
    finCastZModEquiv]

theorem oddFullFreqZ_pos {m : ℕ} (j : Fin m) :
    oddFullFreqZ (OddFullFreq.pos j) =
      ((j.val + 1 : ℕ) : ZMod (2 * m + 1)) := by
  simp [oddFullFreqZ, oddFullFreqEquivZMod, oddFullFreqEquivFin, oddFullFreqToFin,
    finCastZModEquiv]

theorem oddFullFreqZ_neg {m : ℕ} (j : Fin m) :
    oddFullFreqZ (OddFullFreq.neg j) =
      -((j.val + 1 : ℕ) : ZMod (2 * m + 1)) := by
  have hsum : (2 * m - j.val) + (j.val + 1) = 2 * m + 1 := by
    have hj : j.val < m := j.isLt
    omega
  apply eq_neg_iff_add_eq_zero.mpr
  rw [oddFullFreqZ]
  rw [show (oddFullFreqEquivZMod m) (OddFullFreq.neg j) =
      ((2 * m - j.val : ℕ) : ZMod (2 * m + 1)) by rfl]
  rw [← Nat.cast_add]
  rw [hsum]
  simp

theorem sum_zmod_oddFullFreq {m : ℕ} {β : Type*} [AddCommMonoid β]
    (F : ZMod (2 * m + 1) → β) :
    ∑ k : ZMod (2 * m + 1), F k = ∑ f : OddFullFreq m, F (oddFullFreqZ f) := by
  have h := Fintype.sum_equiv (e := oddFullFreqEquivZMod m)
    (f := fun f : OddFullFreq m ↦ F (oddFullFreqZ f)) (g := F) (by intro f; rfl)
  exact h.symm

def oddFullFreqCasesEquiv (m : ℕ) : OddFullFreq m ≃ Unit ⊕ Fin m ⊕ Fin m where
  toFun
    | OddFullFreq.zero => Sum.inl ()
    | OddFullFreq.pos j => Sum.inr (Sum.inl j)
    | OddFullFreq.neg j => Sum.inr (Sum.inr j)
  invFun
    | Sum.inl _ => OddFullFreq.zero
    | Sum.inr (Sum.inl j) => OddFullFreq.pos j
    | Sum.inr (Sum.inr j) => OddFullFreq.neg j
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl u =>
        cases u
        rfl
    | inr y =>
        cases y <;> rfl

theorem oddFullFreq_sum_expand {m : ℕ} {β : Type*} [AddCommMonoid β]
    (F : ZMod (2 * m + 1) → β) :
    (∑ f : OddFullFreq m, F (oddFullFreqZ f)) =
      F 0 + ∑ j : Fin m,
        (F (((j.val + 1 : ℕ) : ZMod (2 * m + 1))) +
          F (-((j.val + 1 : ℕ) : ZMod (2 * m + 1)))) := by
  calc
    (∑ f : OddFullFreq m, F (oddFullFreqZ f))
        = ∑ y : Unit ⊕ Fin m ⊕ Fin m,
            F (oddFullFreqZ ((oddFullFreqCasesEquiv m).symm y)) := by
            exact Fintype.sum_equiv (oddFullFreqCasesEquiv m)
              (fun f : OddFullFreq m ↦ F (oddFullFreqZ f))
              (fun y : Unit ⊕ Fin m ⊕ Fin m ↦
                F (oddFullFreqZ ((oddFullFreqCasesEquiv m).symm y)))
              (by intro f; simp)
    _ = F 0 + ∑ j : Fin m,
        (F (((j.val + 1 : ℕ) : ZMod (2 * m + 1))) +
          F (-((j.val + 1 : ℕ) : ZMod (2 * m + 1)))) := by
        simp [oddFullFreqCasesEquiv, oddFullFreqZ_zero, oddFullFreqZ_pos, oddFullFreqZ_neg,
          Finset.sum_add_distrib]

theorem odd_blockSsq_fourierAmp_eq_zmodFourierSsq
    {m : ℕ} {u : ZMod (2 * m + 1) → ℝ} (hu : MeanZero u) :
    blockSsq (oddFourierAmp m u) =
      zmodFourierSsq (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) := by
  haveI : NeZero (2 * m + 1) := ⟨by omega⟩
  unfold zmodFourierSsq blockSsq oddFourierAmp realFourierCoeff
  rw [sum_zmod_oddFullFreq]
  rw [oddFullFreq_sum_expand (m := m) (β := ℝ)
    (fun k ↦ Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) k))]
  have hzero :
      Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) 0) = 0 := by
    rw [fourierCoeff_zero_of_meanZero hu]
    simp
  rw [hzero]
  simp only [zero_add]
  apply Eq.symm
  calc
    (∑ j : Fin m,
        (Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ))
          (((j.val + 1 : ℕ) : ZMod (2 * m + 1)))) +
          Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ))
            (-(((j.val + 1 : ℕ) : ZMod (2 * m + 1)))))))
        = ∑ j : Fin m,
            2 * Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ))
              (((j.val + 1 : ℕ) : ZMod (2 * m + 1)))) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [normSq_fourierCoeff_neg_real]
          ring
      _ = ∑ j : Fin m,
            (Real.sqrt 2 * ‖fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ))
              (((j.val + 1 : ℕ) : ZMod (2 * m + 1)))‖) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [sqrt_two_norm_sq]

theorem odd_blockEnergy_fourierAmp_eq_zmodFourierEnergy
    {m : ℕ} {u : ZMod (2 * m + 1) → ℝ} (hu : MeanZero u) :
    blockEnergy (oddFourierAmp m u) =
      zmodFourierEnergy (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) := by
  haveI : NeZero (2 * m + 1) := ⟨by omega⟩
  unfold zmodFourierEnergy blockEnergy oddFourierAmp realFourierCoeff
  rw [sum_zmod_oddFullFreq]
  rw [oddFullFreq_sum_expand (m := m) (β := ℝ)
    (fun k ↦ zmodWordLength k *
      Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) k))]
  have hzero :
      zmodWordLength (0 : ZMod (2 * m + 1)) *
        Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) 0) = 0 := by
    rw [fourierCoeff_zero_of_meanZero hu]
    simp
  rw [hzero]
  simp only [zero_add]
  apply Eq.symm
  calc
    (∑ j : Fin m,
        (zmodWordLength (((j.val + 1 : ℕ) : ZMod (2 * m + 1))) *
            Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ))
              (((j.val + 1 : ℕ) : ZMod (2 * m + 1)))) +
          zmodWordLength (-(((j.val + 1 : ℕ) : ZMod (2 * m + 1)))) *
            Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ))
              (-(((j.val + 1 : ℕ) : ZMod (2 * m + 1)))))))
        = ∑ j : Fin m,
            (j.val + 1 : ℝ) *
              (2 * Complex.normSq (fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ))
                (((j.val + 1 : ℕ) : ZMod (2 * m + 1))))) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [zmodWordLength_neg]
          rw [odd_zmodWordLength_pos_freq]
          rw [normSq_fourierCoeff_neg_real]
          ring
      _ = ∑ j : Fin m,
            (j.val + 1 : ℝ) *
              (Real.sqrt 2 * ‖fourierCoeff (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ))
                (((j.val + 1 : ℕ) : ZMod (2 * m + 1)))‖) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [sqrt_two_norm_sq]

theorem odd_blockQsq_fourierAmp_eq_zmodFourierQsq
    {m : ℕ} {u : ZMod (2 * m + 1) → ℝ} (hu : MeanZero u) :
    blockQsq (oddFourierAmp m u) =
      zmodFourierQsq (fun x : ZMod (2 * m + 1) ↦ (u x : ℂ)) := by
  rw [blockQsq_eq_blockEnergy_sub_blockSsq, zmodFourierQsq]
  rw [odd_blockEnergy_fourierAmp_eq_zmodFourierEnergy hu]
  rw [odd_blockSsq_fourierAmp_eq_zmodFourierSsq hu]

inductive EvenFullFreq (m : ℕ) where
  | zero : EvenFullFreq m
  | pos : Fin (m - 1) → EvenFullFreq m
  | neg : Fin (m - 1) → EvenFullFreq m
  | mid : EvenFullFreq m
  deriving DecidableEq, Fintype, Repr

def evenFullFreqToFin (m : ℕ) [NeZero (2 * m)] : EvenFullFreq m → Fin (2 * m)
  | EvenFullFreq.zero => ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 * m))⟩
  | EvenFullFreq.pos j => ⟨j.val + 1, by
      have hne : 2 * m ≠ 0 := NeZero.ne (2 * m)
      have hj : j.val < m - 1 := j.isLt
      omega⟩
  | EvenFullFreq.neg j => ⟨2 * m - j.val - 1, by
      have hne : 2 * m ≠ 0 := NeZero.ne (2 * m)
      have hj : j.val < m - 1 := j.isLt
      omega⟩
  | EvenFullFreq.mid => ⟨m, by
      have hne : 2 * m ≠ 0 := NeZero.ne (2 * m)
      omega⟩

def evenFullFreqOfFin (m : ℕ) [NeZero (2 * m)] (k : Fin (2 * m)) : EvenFullFreq m :=
  if h0 : k.val = 0 then
    EvenFullFreq.zero
  else if hmid : k.val = m then
    EvenFullFreq.mid
  else if hlt : k.val < m then
    EvenFullFreq.pos ⟨k.val - 1, by omega⟩
  else
    EvenFullFreq.neg ⟨2 * m - k.val - 1, by
      have hklt : k.val < 2 * m := k.isLt
      omega⟩

theorem evenFullFreq_left_inv {m : ℕ} [NeZero (2 * m)] :
    Function.LeftInverse (evenFullFreqOfFin m) (evenFullFreqToFin m) := by
  intro f
  cases f with
  | zero => simp [evenFullFreqOfFin, evenFullFreqToFin]
  | pos j =>
      have hne : 2 * m ≠ 0 := NeZero.ne (2 * m)
      have hj : j.val < m - 1 := j.isLt
      have hmid : j.val + 1 ≠ m := by omega
      have hlt : j.val + 1 < m := by omega
      simp [evenFullFreqOfFin, evenFullFreqToFin, hmid, hlt]
  | neg j =>
      have hne : 2 * m ≠ 0 := NeZero.ne (2 * m)
      have hj : j.val < m - 1 := j.isLt
      have h0 : 2 * m - j.val - 1 ≠ 0 := by omega
      have hmid : 2 * m - j.val - 1 ≠ m := by omega
      have hnlt : ¬2 * m - j.val - 1 < m := by omega
      simp [evenFullFreqOfFin, evenFullFreqToFin, h0, hmid, hnlt]
      congr
      omega
  | mid =>
      have hne : 2 * m ≠ 0 := NeZero.ne (2 * m)
      have hm0 : m ≠ 0 := by omega
      simp [evenFullFreqOfFin, evenFullFreqToFin, hm0]

theorem evenFullFreq_right_inv {m : ℕ} [NeZero (2 * m)] :
    Function.RightInverse (evenFullFreqOfFin m) (evenFullFreqToFin m) := by
  intro k
  apply Fin.ext
  unfold evenFullFreqOfFin
  split_ifs with h0 hmid hlt
  · exact h0.symm
  · exact hmid.symm
  · simp only [evenFullFreqToFin]
    have hklt : k.val < 2 * m := k.isLt
    omega
  · simp only [evenFullFreqToFin]
    have hklt : k.val < 2 * m := k.isLt
    omega

def evenFullFreqEquivFin (m : ℕ) [NeZero (2 * m)] : EvenFullFreq m ≃ Fin (2 * m) where
  toFun := evenFullFreqToFin m
  invFun := evenFullFreqOfFin m
  left_inv := evenFullFreq_left_inv
  right_inv := evenFullFreq_right_inv

def evenFullFreqEquivZMod (m : ℕ) [NeZero (2 * m)] : EvenFullFreq m ≃ ZMod (2 * m) :=
  (evenFullFreqEquivFin m).trans (finCastZModEquiv (2 * m))

def evenFullFreqZ {m : ℕ} [NeZero (2 * m)] (f : EvenFullFreq m) : ZMod (2 * m) :=
  evenFullFreqEquivZMod m f

def evenFreqToFull {m : ℕ} : EvenFreq m → EvenFullFreq m
  | EvenFreq.pos j => EvenFullFreq.pos j
  | EvenFreq.neg j => EvenFullFreq.neg j
  | EvenFreq.mid => EvenFullFreq.mid

def evenFullFreqNonzeroEquiv (m : ℕ) : EvenFullFreq m ≃ Unit ⊕ EvenFreq m where
  toFun
    | EvenFullFreq.zero => Sum.inl ()
    | EvenFullFreq.pos j => Sum.inr (EvenFreq.pos j)
    | EvenFullFreq.neg j => Sum.inr (EvenFreq.neg j)
    | EvenFullFreq.mid => Sum.inr EvenFreq.mid
  invFun
    | Sum.inl _ => EvenFullFreq.zero
    | Sum.inr f => evenFreqToFull f
  left_inv := by
    intro f
    cases f <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl u =>
        cases u
        rfl
    | inr f =>
        cases f <;> rfl

theorem evenFullFreq_sum_nonzero {m : ℕ} {β : Type*} [AddCommMonoid β]
    (F : EvenFullFreq m → β) (h0 : F EvenFullFreq.zero = 0) :
    (∑ f : EvenFullFreq m, F f) =
      ∑ f : EvenFreq m, F (evenFreqToFull f) := by
  calc
    (∑ f : EvenFullFreq m, F f)
        = ∑ x : Unit ⊕ EvenFreq m, F ((evenFullFreqNonzeroEquiv m).symm x) := by
            exact Fintype.sum_equiv (evenFullFreqNonzeroEquiv m) F
              (fun x : Unit ⊕ EvenFreq m ↦ F ((evenFullFreqNonzeroEquiv m).symm x))
              (by intro f; simp)
    _ = ∑ f : EvenFreq m, F (evenFreqToFull f) := by
          simp [evenFullFreqNonzeroEquiv, h0]

theorem evenFullFreq_triple_sum_nonzero {m : ℕ} {β : Type*} [AddCommMonoid β]
    (F : EvenFullFreq m → EvenFullFreq m → EvenFullFreq m → β)
    (h₁ : ∀ b c, F EvenFullFreq.zero b c = 0)
    (h₂ : ∀ a c, F a EvenFullFreq.zero c = 0)
    (h₃ : ∀ a b, F a b EvenFullFreq.zero = 0) :
    (∑ a : EvenFullFreq m, ∑ b : EvenFullFreq m, ∑ c : EvenFullFreq m, F a b c) =
      ∑ t : EvenTriple m,
        F (evenFreqToFull t.1) (evenFreqToFull t.2.1) (evenFreqToFull t.2.2) := by
  classical
  calc
    (∑ a : EvenFullFreq m, ∑ b : EvenFullFreq m, ∑ c : EvenFullFreq m, F a b c)
        = ∑ a : EvenFreq m, ∑ b : EvenFullFreq m, ∑ c : EvenFullFreq m,
            F (evenFreqToFull a) b c := by
            rw [evenFullFreq_sum_nonzero]
            simp [h₁]
    _ = ∑ a : EvenFreq m, ∑ b : EvenFreq m, ∑ c : EvenFullFreq m,
            F (evenFreqToFull a) (evenFreqToFull b) c := by
            congr with a
            rw [evenFullFreq_sum_nonzero]
            simp [h₂]
    _ = ∑ a : EvenFreq m, ∑ b : EvenFreq m, ∑ c : EvenFreq m,
            F (evenFreqToFull a) (evenFreqToFull b) (evenFreqToFull c) := by
            congr with a
            congr with b
            rw [evenFullFreq_sum_nonzero]
            simp [h₃]
    _ = ∑ t : EvenTriple m,
        F (evenFreqToFull t.1) (evenFreqToFull t.2.1) (evenFreqToFull t.2.2) := by
          rw [Fintype.sum_prod_type]
          congr with a
          rw [Fintype.sum_prod_type]

theorem evenFullFreqZ_zero {m : ℕ} [NeZero (2 * m)] :
    evenFullFreqZ (EvenFullFreq.zero (m := m)) = 0 := by
  simp [evenFullFreqZ, evenFullFreqEquivZMod, evenFullFreqEquivFin, evenFullFreqToFin,
    finCastZModEquiv]

theorem evenFullFreqZ_pos {m : ℕ} [NeZero (2 * m)] (j : Fin (m - 1)) :
    evenFullFreqZ (EvenFullFreq.pos j) =
      ((j.val + 1 : ℕ) : ZMod (2 * m)) := by
  rfl

theorem evenFullFreqZ_mid {m : ℕ} [NeZero (2 * m)] :
    evenFullFreqZ (EvenFullFreq.mid (m := m)) =
      ((m : ℕ) : ZMod (2 * m)) := by
  rfl

theorem evenFullFreqZ_neg {m : ℕ} [NeZero (2 * m)] (j : Fin (m - 1)) :
    evenFullFreqZ (EvenFullFreq.neg j) =
      -((j.val + 1 : ℕ) : ZMod (2 * m)) := by
  have hsum : (2 * m - j.val - 1) + (j.val + 1) = 2 * m := by
    have hne : 2 * m ≠ 0 := NeZero.ne (2 * m)
    have hj : j.val < m - 1 := j.isLt
    omega
  apply eq_neg_iff_add_eq_zero.mpr
  rw [evenFullFreqZ]
  rw [show (evenFullFreqEquivZMod m) (EvenFullFreq.neg j) =
      ((2 * m - j.val - 1 : ℕ) : ZMod (2 * m)) by rfl]
  rw [← Nat.cast_add]
  rw [hsum]
  simp

theorem evenFullFreqZ_toFull {m : ℕ} [NeZero (2 * m)] (f : EvenFreq m) :
    evenFullFreqZ (evenFreqToFull f) = evenFreqZ f := by
  cases f with
  | pos j => simp [evenFreqToFull, evenFullFreqZ_pos, evenFreqZ]
  | neg j => simp [evenFreqToFull, evenFullFreqZ_neg, evenFreqZ]
  | mid => simp [evenFreqToFull, evenFullFreqZ_mid, evenFreqZ]

theorem sum_zmod_evenFullFreq {m : ℕ} [NeZero (2 * m)] {β : Type*} [AddCommMonoid β]
    (F : ZMod (2 * m) → β) :
    ∑ k : ZMod (2 * m), F k = ∑ f : EvenFullFreq m, F (evenFullFreqZ f) := by
  have h := Fintype.sum_equiv (e := evenFullFreqEquivZMod m)
    (f := fun f : EvenFullFreq m ↦ F (evenFullFreqZ f)) (g := F) (by intro f; rfl)
  exact h.symm

def evenFullFreqCasesEquiv (m : ℕ) :
    EvenFullFreq m ≃ (Unit ⊕ Fin (m - 1) ⊕ Fin (m - 1)) ⊕ Unit where
  toFun
    | EvenFullFreq.zero => Sum.inl (Sum.inl ())
    | EvenFullFreq.pos j => Sum.inl (Sum.inr (Sum.inl j))
    | EvenFullFreq.neg j => Sum.inl (Sum.inr (Sum.inr j))
    | EvenFullFreq.mid => Sum.inr ()
  invFun
    | Sum.inl (Sum.inl _) => EvenFullFreq.zero
    | Sum.inl (Sum.inr (Sum.inl j)) => EvenFullFreq.pos j
    | Sum.inl (Sum.inr (Sum.inr j)) => EvenFullFreq.neg j
    | Sum.inr _ => EvenFullFreq.mid
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl y =>
        cases y with
        | inl u =>
            cases u
            rfl
        | inr z =>
            cases z <;> rfl
    | inr u =>
        cases u
        rfl

theorem evenFullFreq_sum_expand {m : ℕ} [NeZero (2 * m)] {β : Type*} [AddCommMonoid β]
    (F : ZMod (2 * m) → β) :
    (∑ f : EvenFullFreq m, F (evenFullFreqZ f)) =
      F 0 + F (((m : ℕ) : ZMod (2 * m))) +
        ∑ j : Fin (m - 1),
          (F (((j.val + 1 : ℕ) : ZMod (2 * m))) +
            F (-((j.val + 1 : ℕ) : ZMod (2 * m)))) := by
  calc
    (∑ f : EvenFullFreq m, F (evenFullFreqZ f))
        = ∑ y : (Unit ⊕ Fin (m - 1) ⊕ Fin (m - 1)) ⊕ Unit,
            F (evenFullFreqZ ((evenFullFreqCasesEquiv m).symm y)) := by
            exact Fintype.sum_equiv (evenFullFreqCasesEquiv m)
              (fun f : EvenFullFreq m ↦ F (evenFullFreqZ f))
              (fun y : (Unit ⊕ Fin (m - 1) ⊕ Fin (m - 1)) ⊕ Unit ↦
                F (evenFullFreqZ ((evenFullFreqCasesEquiv m).symm y)))
              (by intro f; simp)
    _ = F 0 + F (((m : ℕ) : ZMod (2 * m))) +
        ∑ j : Fin (m - 1),
          (F (((j.val + 1 : ℕ) : ZMod (2 * m))) +
            F (-((j.val + 1 : ℕ) : ZMod (2 * m)))) := by
        simp [evenFullFreqCasesEquiv, evenFullFreqZ_zero, evenFullFreqZ_pos,
          evenFullFreqZ_neg, evenFullFreqZ_mid, Finset.sum_add_distrib, add_comm, add_assoc]

def finInitLastEquiv (m : ℕ) [NeZero m] : Fin m ≃ Fin (m - 1) ⊕ Unit where
  toFun j :=
    if h : j.val = m - 1 then Sum.inr () else Sum.inl ⟨j.val, by
      have hm : m ≠ 0 := NeZero.ne m
      omega⟩
  invFun
    | Sum.inl j => ⟨j.val, by
        have hm : m ≠ 0 := NeZero.ne m
        omega⟩
    | Sum.inr _ => ⟨m - 1, by
        have hm : m ≠ 0 := NeZero.ne m
        omega⟩
  left_inv := by
    intro j
    apply Fin.ext
    dsimp
    split_ifs with h
    · simp [h]
    · rfl
  right_inv := by
    intro x
    cases x with
    | inl j =>
        dsimp
        have hj : j.val < m - 1 := j.isLt
        have hne : j.val ≠ m - 1 := by omega
        simp [hne]
    | inr u =>
        cases u
        simp

theorem sum_fin_eq_init_add_last {m : ℕ} [NeZero m] {β : Type*} [AddCommMonoid β]
    (F : Fin m → β) :
    ∑ j : Fin m, F j =
      (∑ j : Fin (m - 1), F ⟨j.val, by omega⟩) +
        F ⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ := by
  calc
    ∑ j : Fin m, F j
        = ∑ x : Fin (m - 1) ⊕ Unit, F ((finInitLastEquiv m).symm x) := by
            exact Fintype.sum_equiv (finInitLastEquiv m)
              F (fun x : Fin (m - 1) ⊕ Unit ↦ F ((finInitLastEquiv m).symm x))
              (by intro j; simp)
    _ = (∑ j : Fin (m - 1), F ⟨j.val, by omega⟩) +
        F ⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ := by
        simp [finInitLastEquiv]

theorem even_blockSsq_fourierAmp_eq_zmodFourierSsq
    {m : ℕ} [NeZero (2 * m)] {u : ZMod (2 * m) → ℝ} (hu : MeanZero u) :
    blockSsq (evenFourierAmp (m := m) u) =
      zmodFourierSsq (fun x : ZMod (2 * m) ↦ (u x : ℂ)) := by
  haveI : NeZero m := ⟨by
    intro hm
    exact (NeZero.ne (2 * m)) (by omega)⟩
  unfold zmodFourierSsq
  rw [sum_zmod_evenFullFreq]
  rw [evenFullFreq_sum_expand (m := m) (β := ℝ)
    (fun k ↦ Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) k))]
  have hzero :
      Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) 0) = 0 := by
    rw [fourierCoeff_zero_of_meanZero hu]
    simp
  rw [hzero]
  simp only [zero_add]
  unfold blockSsq evenFourierAmp realFourierCoeff
  rw [sum_fin_eq_init_add_last]
  simp only
  apply Eq.symm
  calc
    (Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) ↑m) +
        ∑ j : Fin (m - 1),
          (Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
            (((j.val + 1 : ℕ) : ZMod (2 * m)))) +
            Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
              (-(((j.val + 1 : ℕ) : ZMod (2 * m)))))))
        = Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) ↑m) +
          ∑ j : Fin (m - 1),
            2 * Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
              (((j.val + 1 : ℕ) : ZMod (2 * m)))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [normSq_fourierCoeff_neg_real]
          ring
      _ = (∑ j : Fin (m - 1),
            (Real.sqrt 2 * ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
              (((j.val + 1 : ℕ) : ZMod (2 * m)))‖) ^ 2) +
          ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) ↑m‖ ^ 2 := by
          rw [add_comm]
          congr 1
          · apply Finset.sum_congr rfl
            intro j _
            rw [sqrt_two_norm_sq]
          · rw [Complex.normSq_eq_norm_sq]
      _ = (∑ j : Fin (m - 1),
            (if (⟨j.val, by omega⟩ : Fin m).val + 1 = m then
              ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                (((⟨j.val, by omega⟩ : Fin m).val + 1 : ℕ) : ZMod (2 * m))‖
            else
              Real.sqrt 2 * ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                (((⟨j.val, by omega⟩ : Fin m).val + 1 : ℕ) : ZMod (2 * m))‖) ^ 2) +
          (if (⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ : Fin m).val + 1 = m then
              ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                ((((⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ : Fin m).val + 1 : ℕ) :
                  ZMod (2 * m)))‖
            else
              Real.sqrt 2 * ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                ((((⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ : Fin m).val + 1 : ℕ) :
                  ZMod (2 * m)))‖) ^ 2 := by
          congr 1
          · apply Finset.sum_congr rfl
            intro j _
            have hne : ¬j.val + 1 = m := by
              have hj : j.val < m - 1 := j.isLt
              omega
            simp [hne]
          · have hlast : (m - 1) + 1 = m := by
              have hm : m ≠ 0 := NeZero.ne m
              omega
            simp [hlast]

theorem even_blockEnergy_fourierAmp_eq_zmodFourierEnergy
    {m : ℕ} [NeZero (2 * m)] {u : ZMod (2 * m) → ℝ} (hu : MeanZero u) :
    blockEnergy (evenFourierAmp (m := m) u) =
      zmodFourierEnergy (fun x : ZMod (2 * m) ↦ (u x : ℂ)) := by
  haveI : NeZero m := ⟨by
    intro hm
    exact (NeZero.ne (2 * m)) (by omega)⟩
  unfold zmodFourierEnergy
  rw [sum_zmod_evenFullFreq]
  rw [evenFullFreq_sum_expand (m := m) (β := ℝ)
    (fun k ↦ zmodWordLength k *
      Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) k))]
  have hzero :
      zmodWordLength (0 : ZMod (2 * m)) *
        Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) 0) = 0 := by
    rw [fourierCoeff_zero_of_meanZero hu]
    simp
  rw [hzero]
  simp only [zero_add]
  unfold blockEnergy evenFourierAmp realFourierCoeff
  rw [sum_fin_eq_init_add_last]
  simp only
  apply Eq.symm
  calc
    (zmodWordLength (↑m : ZMod (2 * m)) *
        Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) ↑m) +
        ∑ j : Fin (m - 1),
          (zmodWordLength (((j.val + 1 : ℕ) : ZMod (2 * m))) *
              Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                (((j.val + 1 : ℕ) : ZMod (2 * m)))) +
            zmodWordLength (-(((j.val + 1 : ℕ) : ZMod (2 * m)))) *
              Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                (-(((j.val + 1 : ℕ) : ZMod (2 * m)))))))
        = (m : ℝ) * Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) ↑m) +
          ∑ j : Fin (m - 1),
            (j.val + 1 : ℝ) *
              (2 * Complex.normSq (fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                (((j.val + 1 : ℕ) : ZMod (2 * m))))) := by
          congr 1
          · rw [even_zmodWordLength_middle]
          · apply Finset.sum_congr rfl
            intro j _
            rw [zmodWordLength_neg]
            have hlen :
                zmodWordLength (((j.val + 1 : ℕ) : ZMod (2 * m))) = (j.val + 1 : ℝ) := by
              have hhalf : j.val + 1 ≤ (2 * m) / 2 := by
                have hne : 2 * m ≠ 0 := NeZero.ne (2 * m)
                have hj : j.val < m - 1 := j.isLt
                omega
              unfold zmodWordLength
              rw [ZMod.valMinAbs_natCast_of_le_half hhalf]
              simp only [Nat.cast_add, Nat.cast_one, Nat.cast_natAbs, Int.cast_abs, Int.cast_add,
                Int.cast_natCast, Int.cast_one, abs_eq_self, ge_iff_le]
              positivity
            rw [hlen]
            rw [normSq_fourierCoeff_neg_real]
            ring
      _ = (∑ j : Fin (m - 1),
            (j.val + 1 : ℝ) *
              (Real.sqrt 2 * ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                (((j.val + 1 : ℕ) : ZMod (2 * m)))‖) ^ 2) +
          (m : ℝ) * ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ)) ↑m‖ ^ 2 := by
          rw [add_comm]
          congr 1
          · apply Finset.sum_congr rfl
            intro j _
            rw [sqrt_two_norm_sq]
          · rw [Complex.normSq_eq_norm_sq]
      _ = (∑ j : Fin (m - 1),
            ((⟨j.val, by omega⟩ : Fin m).val + 1 : ℝ) *
            (if (⟨j.val, by omega⟩ : Fin m).val + 1 = m then
              ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                (((⟨j.val, by omega⟩ : Fin m).val + 1 : ℕ) : ZMod (2 * m))‖
            else
              Real.sqrt 2 * ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                (((⟨j.val, by omega⟩ : Fin m).val + 1 : ℕ) : ZMod (2 * m))‖) ^ 2) +
          ((⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ : Fin m).val + 1 : ℝ) *
          (if (⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ : Fin m).val + 1 = m then
              ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                ((((⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ : Fin m).val + 1 : ℕ) :
                  ZMod (2 * m)))‖
            else
              Real.sqrt 2 * ‖fourierCoeff (fun x : ZMod (2 * m) ↦ (u x : ℂ))
                ((((⟨m - 1, by have hm : m ≠ 0 := NeZero.ne m; omega⟩ : Fin m).val + 1 : ℕ) :
                  ZMod (2 * m)))‖) ^ 2 := by
          congr 1
          · apply Finset.sum_congr rfl
            intro j _
            have hne : ¬j.val + 1 = m := by
              have hj : j.val < m - 1 := j.isLt
              omega
            simp [hne]
          · have hlast : (m - 1) + 1 = m := by
              have hm : m ≠ 0 := NeZero.ne m
              omega
            rw [hlast]
            simp only [↓reduceIte]
            have hreal : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
              exact_mod_cast hlast.symm
            rw [hreal]

theorem even_blockQsq_fourierAmp_eq_zmodFourierQsq
    {m : ℕ} [NeZero (2 * m)] {u : ZMod (2 * m) → ℝ} (hu : MeanZero u) :
    blockQsq (evenFourierAmp (m := m) u) =
      zmodFourierQsq (fun x : ZMod (2 * m) ↦ (u x : ℂ)) := by
  rw [blockQsq_eq_blockEnergy_sub_blockSsq, zmodFourierQsq]
  rw [even_blockEnergy_fourierAmp_eq_zmodFourierEnergy hu]
  rw [even_blockSsq_fourierAmp_eq_zmodFourierSsq hu]

end

end CyclicLsi

