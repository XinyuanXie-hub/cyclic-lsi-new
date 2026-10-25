module
import Mathlib.Algebra.Order.Chebyshev
public import CyclicLsi.Support.Basic



/-!
# Block combinatorics for the odd and even third-moment estimates

This file contains the finite-dimensional Cauchy--Schwarz estimates used in
the block proofs of the odd and even third-moment estimates.

The Fourier-resonance bridge supplies the block sums `L`, `R`, `U`, and `V`.
The lemmas here prove the sharp numerical estimates applied to each block.
-/

namespace CyclicLsi

@[expose] public noncomputable section

open scoped BigOperators

/-- Cauchy--Schwarz for a finite type, in the form used for one resonance block. -/
theorem sum_sq_le_card_mul_sum_sq_univ {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
  simpa using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f))

/-- The odd-block pointwise estimate.

In the odd proof, a block with weight `r = k - 1` has
`L^2 ≤ r U` and `R^2 ≤ (r + 1) V`.  Since `r ≥ 1`, the latter gives
`R^2 ≤ 2 r V`, and the cross term is absorbed by
`0 ≤ (2L - 3R)^2`.
-/
theorem odd_pointwise_block_bound {r L R U V : ℝ}
    (hr : 1 ≤ r) (hV : 0 ≤ V)
    (hL : L ^ 2 ≤ r * U) (hR : R ^ 2 ≤ (r + 1) * V) :
    (3 * L + R) ^ 2 / r ≤ 11 * (U + V) := by
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hR' : R ^ 2 ≤ 2 * r * V := by
    have hcoef : r + 1 ≤ 2 * r := by linarith
    calc
      R ^ 2 ≤ (r + 1) * V := hR
      _ ≤ (2 * r) * V := mul_le_mul_of_nonneg_right hcoef hV
      _ = 2 * r * V := by ring
  have hcross : 0 ≤ (2 * L - 3 * R) ^ 2 := sq_nonneg _
  rw [div_le_iff₀ hr_pos]
  nlinarith

/-- The even ordinary/wrap-around block pointwise estimate.

For the even proof away from the middle frequency, both `L` and `R` have
the same number of ordered terms, so `L^2 ≤ r U` and `R^2 ≤ r V`.  The
factor `1 / 2` in the definition of `W` gives the constant `5`.
-/
theorem even_pointwise_block_bound {r L R U V : ℝ}
    (hr : 0 < r) (hL : L ^ 2 ≤ r * U) (hR : R ^ 2 ≤ r * V) :
    (3 * L + R) ^ 2 / (2 * r) ≤ 5 * (U + V) := by
  have hden : 0 < 2 * r := by positivity
  have hcross : 0 ≤ (L - 3 * R) ^ 2 := sq_nonneg _
  rw [div_le_iff₀ hden]
  nlinarith

/-- The middle-frequency Cauchy--Schwarz estimate in the even proof. -/
theorem even_middle_block_bound {r L U : ℝ}
    (hr : 0 < r) (hL : L ^ 2 ≤ r * U) :
    9 * L ^ 2 / r ≤ 9 * U := by
  rw [div_le_iff₀ hr]
  nlinarith

/-- A reusable Cauchy--Schwarz estimate for an explicitly indexed block. -/
theorem indexed_block_sq_le {N : ℕ} (b : Fin N → ℝ) :
    (∑ i : Fin N, b i) ^ 2 ≤ (N : ℝ) * ∑ i : Fin N, b i ^ 2 := by
  simpa [Fintype.card_fin] using sum_sq_le_card_mul_sum_sq_univ b

theorem sum_comp_le_univ_sum_of_injective {α β : Type*} [Fintype α] [Fintype β]
    {f : α → β} (hf : Function.Injective f) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b) :
    (∑ x : α, w (f x)) ≤ ∑ y : β, w y := by
  classical
  have himage :
      ∑ y ∈ (Finset.univ.image f), w y = ∑ x : α, w (f x) :=
    Finset.sum_image (s := Finset.univ) (g := f) (f := w)
      (fun x _ y _ hxy ↦ hf hxy)
  calc
    (∑ x : α, w (f x))
        = ∑ y ∈ (Finset.univ.image f), w y := himage.symm
    _ ≤ ∑ y : β, w y := by
          exact Finset.sum_le_univ_sum_of_nonneg fun y ↦ hw y

/-- The square-sum `S^2 = ∑ a_j^2` for zero-based Fourier block amplitudes. -/
def blockSsq {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, a j ^ 2

/-- The surplus `Q^2 = ∑ j a_j^2`, where `j` is zero-based. -/
def blockQsq {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, (j.val : ℝ) * a j ^ 2

theorem blockSsq_sq_eq_pair_sum {m : ℕ} (a : Fin m → ℝ) :
    blockSsq a ^ 2 = ∑ p : Fin m × Fin m, a p.1 ^ 2 * a p.2 ^ 2 := by
  unfold blockSsq
  rw [sq, Finset.sum_mul_sum]
  exact (Fintype.sum_prod_type' fun i j ↦ a i ^ 2 * a j ^ 2).symm

/-- Odd case: ordinary resonance block.

For zero-based block index `r = k - 1`, this is the paper's
`L_k = ∑_{i+j=k} a_i a_j`.  It has exactly `r` ordered terms.
-/
def oddL {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  ∑ t : Fin r.val,
    a ⟨t.val, by omega⟩ * a ⟨r.val - 1 - t.val, by omega⟩

/-- The corresponding square block for `oddL`. -/
def oddU {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  ∑ t : Fin r.val,
    (a ⟨t.val, by omega⟩ ^ 2) * (a ⟨r.val - 1 - t.val, by omega⟩ ^ 2)

/-- Odd case: wrap-around resonance block.

For zero-based block index `r = k - 1`, this is the paper's
`R_k = ∑_{i+j=n-k} a_i a_j`.  It has exactly `r + 1` ordered terms.
-/
def oddR {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  ∑ t : Fin (r.val + 1),
    a ⟨m - r.val - 1 + t.val, by omega⟩ *
      a ⟨m - 1 - t.val, by omega⟩

/-- The corresponding square block for `oddR`. -/
def oddV {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  ∑ t : Fin (r.val + 1),
    (a ⟨m - r.val - 1 + t.val, by omega⟩ ^ 2) *
      (a ⟨m - 1 - t.val, by omega⟩ ^ 2)

theorem oddL_sq_le {m : ℕ} (a : Fin m → ℝ) (r : Fin m) :
    oddL a r ^ 2 ≤ (r.val : ℝ) * oddU a r := by
  simpa [oddL, oddU, mul_pow] using
    indexed_block_sq_le
      (N := r.val)
      (fun t : Fin r.val =>
        a ⟨t.val, by omega⟩ * a ⟨r.val - 1 - t.val, by omega⟩)

theorem oddR_sq_le {m : ℕ} (a : Fin m → ℝ) (r : Fin m) :
    oddR a r ^ 2 ≤ ((r.val : ℝ) + 1) * oddV a r := by
  simpa [oddR, oddV, mul_pow, Nat.cast_add, Nat.cast_one] using
    indexed_block_sq_le
      (N := r.val + 1)
      (fun t : Fin (r.val + 1) =>
        a ⟨m - r.val - 1 + t.val, by omega⟩ *
          a ⟨m - 1 - t.val, by omega⟩)

/-- The ordered pair represented by an odd ordinary-resonance square term. -/
def oddUPair {m : ℕ} (p : Sigma fun r : Fin m ↦ Fin r.val) : Fin m × Fin m :=
  (⟨p.2.val, by omega⟩, ⟨p.1.val - 1 - p.2.val, by omega⟩)

theorem oddUPair_injective {m : ℕ} :
    Function.Injective (oddUPair (m := m)) := by
  intro p q hpq
  cases p with
  | mk r t =>
    cases q with
    | mk s u =>
      have ht : t.val = u.val := by
        exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
      have hsnd : r.val - 1 - t.val = s.val - 1 - u.val := by
        exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
      have hr : r.val = s.val := by omega
      have hrs : r = s := Fin.ext hr
      subst s
      have htu : t = u := Fin.ext ht
      subst u
      rfl

/-- The ordered pair represented by an odd wrap-around square term, excluding
the boundary block `r = 0`.
-/
def oddVPair {m : ℕ}
    (p : Sigma fun r : {r : Fin m // r.val ≠ 0} ↦ Fin (r.val.val + 1)) :
    Fin m × Fin m :=
  (⟨m - p.1.val.val - 1 + p.2.val, by
      have hr : p.1.val.val ≠ 0 := p.1.property
      omega⟩,
    ⟨m - 1 - p.2.val, by
      have hr : p.1.val.val ≠ 0 := p.1.property
      omega⟩)

theorem oddVPair_injective {m : ℕ} :
    Function.Injective (oddVPair (m := m)) := by
  intro p q hpq
  cases p with
  | mk r t =>
    cases q with
    | mk s u =>
      have hfst :
          m - r.val.val - 1 + t.val = m - s.val.val - 1 + u.val := by
        exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
      have hsnd : m - 1 - t.val = m - 1 - u.val := by
        exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
      have ht : t.val = u.val := by
        have hrt : t.val < r.val.val + 1 := t.isLt
        have hsu : u.val < s.val.val + 1 := u.isLt
        have hrnz : r.val.val ≠ 0 := r.property
        have hsnz : s.val.val ≠ 0 := s.property
        have hrlt : r.val.val < m := r.val.isLt
        have hslt : s.val.val < m := s.val.isLt
        omega
      have hrval : r.val.val = s.val.val := by
        have hrt : t.val < r.val.val + 1 := t.isLt
        have hsu : u.val < s.val.val + 1 := u.isLt
        have hrnz : r.val.val ≠ 0 := r.property
        have hsnz : s.val.val ≠ 0 := s.property
        have hrlt : r.val.val < m := r.val.isLt
        have hslt : s.val.val < m := s.val.isLt
        omega
      have hrs : r = s := Subtype.ext (Fin.ext hrval)
      subst s
      have htu : t = u := Fin.ext ht
      subst u
      rfl

abbrev OddUDomain (m : ℕ) : Type :=
  Sigma fun r : Fin m ↦ Fin r.val

abbrev OddVDomain (m : ℕ) : Type :=
  Sigma fun r : {r : Fin m // r.val ≠ 0} ↦ Fin (r.val.val + 1)

def pairWeight {m : ℕ} (a : Fin m → ℝ) (p : Fin m × Fin m) : ℝ :=
  a p.1 ^ 2 * a p.2 ^ 2

/-- The combined odd square-block map into all ordered pairs. -/
def oddSquarePair {m : ℕ} :
    OddUDomain m ⊕ OddVDomain m → Fin m × Fin m :=
  Sum.elim oddUPair oddVPair

theorem oddSquarePair_injective {m : ℕ} :
    Function.Injective (oddSquarePair (m := m)) := by
  intro p q hpq
  cases p with
  | inl pu =>
    cases q with
    | inl qu =>
      have h : pu = qu := oddUPair_injective hpq
      subst qu
      rfl
    | inr qv =>
      exfalso
      cases pu with
      | mk r t =>
        cases qv with
        | mk s u =>
          have hfst :
              t.val = m - s.val.val - 1 + u.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
          have hsnd :
              r.val - 1 - t.val = m - 1 - u.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
          have htlt : t.val < r.val := t.isLt
          have hrlt : r.val < m := r.isLt
          have hsnz : s.val.val ≠ 0 := s.property
          have hslt : s.val.val < m := s.val.isLt
          have hult : u.val < s.val.val + 1 := u.isLt
          omega
  | inr pv =>
    cases q with
    | inl qu =>
      exfalso
      cases pv with
      | mk r t =>
        cases qu with
        | mk s u =>
          have hfst :
              m - r.val.val - 1 + t.val = u.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
          have hsnd :
              m - 1 - t.val = s.val - 1 - u.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
          have htnz : r.val.val ≠ 0 := r.property
          have hrlt : r.val.val < m := r.val.isLt
          have htlt : t.val < r.val.val + 1 := t.isLt
          have hult : u.val < s.val := u.isLt
          have hslt : s.val < m := s.isLt
          omega
    | inr qv =>
      have h : pv = qv := oddVPair_injective hpq
      subst qv
      rfl

/-- Even case: ordinary resonance block away from the middle frequency. -/
def evenL {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  ∑ t : Fin r.val,
    a ⟨t.val, by omega⟩ * a ⟨r.val - 1 - t.val, by omega⟩

/-- The corresponding square block for `evenL`. -/
def evenU {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  ∑ t : Fin r.val,
    (a ⟨t.val, by omega⟩ ^ 2) * (a ⟨r.val - 1 - t.val, by omega⟩ ^ 2)

/-- Even case: wrap-around resonance block away from the middle frequency.

Only the first `m - 1` amplitudes participate; the middle frequency is treated
separately.  This indexed form is intended for `1 ≤ r ≤ m - 2`.
-/
def evenR {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  ∑ t : Fin r.val,
    a ⟨m - r.val - 1 + t.val, by omega⟩ *
      a ⟨m - 2 - t.val, by omega⟩

/-- The corresponding square block for `evenR`. -/
def evenV {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  ∑ t : Fin r.val,
    (a ⟨m - r.val - 1 + t.val, by omega⟩ ^ 2) *
      (a ⟨m - 2 - t.val, by omega⟩ ^ 2)

/-- Even case: the middle-frequency resonance block. -/
def evenLm {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ t : Fin (m - 1),
    a ⟨t.val, by omega⟩ * a ⟨m - 2 - t.val, by omega⟩

/-- The corresponding square block for `evenLm`. -/
def evenUm {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ t : Fin (m - 1),
    (a ⟨t.val, by omega⟩ ^ 2) * (a ⟨m - 2 - t.val, by omega⟩ ^ 2)

theorem evenL_sq_le {m : ℕ} (a : Fin m → ℝ) (r : Fin m) :
    evenL a r ^ 2 ≤ (r.val : ℝ) * evenU a r := by
  simpa [evenL, evenU, mul_pow] using
    indexed_block_sq_le
      (N := r.val)
      (fun t : Fin r.val =>
        a ⟨t.val, by omega⟩ * a ⟨r.val - 1 - t.val, by omega⟩)

theorem evenR_sq_le {m : ℕ} (a : Fin m → ℝ) (r : Fin m) :
    evenR a r ^ 2 ≤ (r.val : ℝ) * evenV a r := by
  simpa [evenR, evenV, mul_pow] using
    indexed_block_sq_le
      (N := r.val)
      (fun t : Fin r.val =>
        a ⟨m - r.val - 1 + t.val, by omega⟩ *
          a ⟨m - 2 - t.val, by omega⟩)

theorem evenLm_sq_le {m : ℕ} (a : Fin m → ℝ) :
    evenLm a ^ 2 ≤ ((m - 1 : ℕ) : ℝ) * evenUm a := by
  simpa [evenLm, evenUm, mul_pow] using
    indexed_block_sq_le
      (N := m - 1)
      (fun t : Fin (m - 1) =>
        a ⟨t.val, by omega⟩ * a ⟨m - 2 - t.val, by omega⟩)

abbrev EvenOrdinaryIndex (m : ℕ) : Type :=
  {r : Fin m // r.val ≠ 0 ∧ r.val ≠ m - 1}

abbrev EvenUDomain (m : ℕ) : Type :=
  Sigma fun r : EvenOrdinaryIndex m ↦ Fin r.val.val

abbrev EvenVDomain (m : ℕ) : Type :=
  Sigma fun r : EvenOrdinaryIndex m ↦ Fin r.val.val

abbrev EvenMDomain (m : ℕ) : Type :=
  Fin (m - 1)

/-- The ordered pair represented by an even ordinary low-sum square term. -/
def evenUPair {m : ℕ} (p : EvenUDomain m) : Fin m × Fin m :=
  (⟨p.2.val, by omega⟩, ⟨p.1.val.val - 1 - p.2.val, by omega⟩)

/-- The ordered pair represented by an even wrap-around square term. -/
def evenVPair {m : ℕ} (p : EvenVDomain m) : Fin m × Fin m :=
  (⟨m - p.1.val.val - 1 + p.2.val, by
      have hr0 : p.1.val.val ≠ 0 := p.1.property.1
      have hrlast : p.1.val.val ≠ m - 1 := p.1.property.2
      omega⟩,
    ⟨m - 2 - p.2.val, by
      have hr0 : p.1.val.val ≠ 0 := p.1.property.1
      have hrlast : p.1.val.val ≠ m - 1 := p.1.property.2
      omega⟩)

/-- The ordered pair represented by the even middle-frequency square term. -/
def evenMPair {m : ℕ} (t : EvenMDomain m) : Fin m × Fin m :=
  (⟨t.val, by omega⟩, ⟨m - 2 - t.val, by omega⟩)

theorem evenUPair_injective {m : ℕ} :
    Function.Injective (evenUPair (m := m)) := by
  intro p q hpq
  cases p with
  | mk r t =>
    cases q with
    | mk s u =>
      have ht : t.val = u.val := by
        exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
      have hsnd : r.val.val - 1 - t.val = s.val.val - 1 - u.val := by
        exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
      have hr : r.val.val = s.val.val := by omega
      have hrs : r = s := Subtype.ext (Fin.ext hr)
      subst s
      have htu : t = u := Fin.ext ht
      subst u
      rfl

theorem evenVPair_injective {m : ℕ} :
    Function.Injective (evenVPair (m := m)) := by
  intro p q hpq
  cases p with
  | mk r t =>
    cases q with
    | mk s u =>
      have hfst :
          m - r.val.val - 1 + t.val = m - s.val.val - 1 + u.val := by
        exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
      have hsnd : m - 2 - t.val = m - 2 - u.val := by
        exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
      have ht : t.val = u.val := by
        have hrt : t.val < r.val.val := t.isLt
        have hsu : u.val < s.val.val := u.isLt
        have hr0 : r.val.val ≠ 0 := r.property.1
        have hs0 : s.val.val ≠ 0 := s.property.1
        have hrlast : r.val.val ≠ m - 1 := r.property.2
        have hslast : s.val.val ≠ m - 1 := s.property.2
        have hrlt : r.val.val < m := r.val.isLt
        have hslt : s.val.val < m := s.val.isLt
        omega
      have hrval : r.val.val = s.val.val := by
        have hrt : t.val < r.val.val := t.isLt
        have hsu : u.val < s.val.val := u.isLt
        have hr0 : r.val.val ≠ 0 := r.property.1
        have hs0 : s.val.val ≠ 0 := s.property.1
        have hrlast : r.val.val ≠ m - 1 := r.property.2
        have hslast : s.val.val ≠ m - 1 := s.property.2
        have hrlt : r.val.val < m := r.val.isLt
        have hslt : s.val.val < m := s.val.isLt
        omega
      have hrs : r = s := Subtype.ext (Fin.ext hrval)
      subst s
      have htu : t = u := Fin.ext ht
      subst u
      rfl

theorem evenMPair_injective {m : ℕ} :
    Function.Injective (evenMPair (m := m)) := by
  intro t u htu
  exact Fin.ext (congrArg (fun z : Fin m × Fin m ↦ z.1.val) htu)

/-- The combined even square-block map into all ordered pairs. -/
def evenSquarePair {m : ℕ} :
    (EvenUDomain m ⊕ EvenVDomain m) ⊕ EvenMDomain m → Fin m × Fin m :=
  Sum.elim (Sum.elim evenUPair evenVPair) evenMPair

theorem evenSquarePair_injective {m : ℕ} :
    Function.Injective (evenSquarePair (m := m)) := by
  intro p q hpq
  cases p with
  | inl puv =>
    cases puv with
    | inl pu =>
      cases q with
      | inl quv =>
        cases quv with
        | inl qu =>
          have h : pu = qu := evenUPair_injective hpq
          subst qu
          rfl
        | inr qv =>
          exfalso
          cases pu with
          | mk r t =>
            cases qv with
            | mk s u =>
              have hfst :
                  t.val = m - s.val.val - 1 + u.val := by
                exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
              have hsnd :
                  r.val.val - 1 - t.val = m - 2 - u.val := by
                exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
              have htlt : t.val < r.val.val := t.isLt
              have hr0 : r.val.val ≠ 0 := r.property.1
              have hrlast : r.val.val ≠ m - 1 := r.property.2
              have hrlt : r.val.val < m := r.val.isLt
              have hult : u.val < s.val.val := u.isLt
              have hs0 : s.val.val ≠ 0 := s.property.1
              have hslast : s.val.val ≠ m - 1 := s.property.2
              have hslt : s.val.val < m := s.val.isLt
              omega
      | inr qm =>
        exfalso
        cases pu with
        | mk r t =>
          have hfst : t.val = qm.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
          have hsnd : r.val.val - 1 - t.val = m - 2 - qm.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
          have htlt : t.val < r.val.val := t.isLt
          have hr0 : r.val.val ≠ 0 := r.property.1
          have hrlast : r.val.val ≠ m - 1 := r.property.2
          have hrlt : r.val.val < m := r.val.isLt
          have hqmlt : qm.val < m - 1 := qm.isLt
          omega
    | inr pv =>
      cases q with
      | inl quv =>
        cases quv with
        | inl qu =>
          exfalso
          cases pv with
          | mk r t =>
            cases qu with
            | mk s u =>
              have hfst :
                  m - r.val.val - 1 + t.val = u.val := by
                exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
              have hsnd :
                  m - 2 - t.val = s.val.val - 1 - u.val := by
                exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
              have htlt : t.val < r.val.val := t.isLt
              have hr0 : r.val.val ≠ 0 := r.property.1
              have hrlast : r.val.val ≠ m - 1 := r.property.2
              have hrlt : r.val.val < m := r.val.isLt
              have hult : u.val < s.val.val := u.isLt
              have hs0 : s.val.val ≠ 0 := s.property.1
              have hslast : s.val.val ≠ m - 1 := s.property.2
              have hslt : s.val.val < m := s.val.isLt
              omega
        | inr qv =>
          have h : pv = qv := evenVPair_injective hpq
          subst qv
          rfl
      | inr qm =>
        exfalso
        cases pv with
        | mk r t =>
          have hfst : m - r.val.val - 1 + t.val = qm.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
          have hsnd : m - 2 - t.val = m - 2 - qm.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
          have htlt : t.val < r.val.val := t.isLt
          have hr0 : r.val.val ≠ 0 := r.property.1
          have hrlast : r.val.val ≠ m - 1 := r.property.2
          have hrlt : r.val.val < m := r.val.isLt
          have hqmlt : qm.val < m - 1 := qm.isLt
          omega
  | inr pm =>
    cases q with
    | inl quv =>
      cases quv with
      | inl qu =>
        exfalso
        cases qu with
        | mk r t =>
          have hfst : pm.val = t.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
          have hsnd : m - 2 - pm.val = r.val.val - 1 - t.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
          have htlt : t.val < r.val.val := t.isLt
          have hr0 : r.val.val ≠ 0 := r.property.1
          have hrlast : r.val.val ≠ m - 1 := r.property.2
          have hrlt : r.val.val < m := r.val.isLt
          have hpmlt : pm.val < m - 1 := pm.isLt
          omega
      | inr qv =>
        exfalso
        cases qv with
        | mk r t =>
          have hfst : pm.val = m - r.val.val - 1 + t.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.1.val) hpq
          have hsnd : m - 2 - pm.val = m - 2 - t.val := by
            exact congrArg (fun z : Fin m × Fin m ↦ z.2.val) hpq
          have htlt : t.val < r.val.val := t.isLt
          have hr0 : r.val.val ≠ 0 := r.property.1
          have hrlast : r.val.val ≠ m - 1 := r.property.2
          have hrlt : r.val.val < m := r.val.isLt
          have hpmlt : pm.val < m - 1 := pm.isLt
          omega
    | inr qm =>
      have h : pm = qm := evenMPair_injective hpq
      subst qm
      rfl

/-- Odd weighted contribution for a single non-boundary block.

The boundary block `r = 0` is handled separately in the paper, so it is
recorded as zero here.
-/
def oddWeightedTerm {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  if r.val = 0 then
    0
  else
    (3 * oddL a r + oddR a r) ^ 2 / (r.val : ℝ)

/-- Odd square contribution used in the coverage estimate. -/
def oddSquareTerm {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  if r.val = 0 then
    0
  else
    oddU a r + oddV a r

/-- The odd proof's weighted Cauchy sum. -/
def oddWeightedSum {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ r : Fin m, oddWeightedTerm a r

/-- The odd proof's squared-block coverage sum. -/
def oddSquareSum {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ r : Fin m, oddSquareTerm a r

theorem oddWeightedTerm_le {m : ℕ} (a : Fin m → ℝ) (r : Fin m) :
    oddWeightedTerm a r ≤ 11 * oddSquareTerm a r := by
  by_cases h0 : r.val = 0
  · simp [oddWeightedTerm, oddSquareTerm, h0]
  · have hr_nat : 1 ≤ r.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
    have hr : (1 : ℝ) ≤ (r.val : ℝ) := by exact_mod_cast hr_nat
    have hV : 0 ≤ oddV a r := by
      unfold oddV
      positivity
    simpa [oddWeightedTerm, oddSquareTerm, h0, mul_add] using
      odd_pointwise_block_bound
        (r := (r.val : ℝ))
        (L := oddL a r)
        (R := oddR a r)
        (U := oddU a r)
        (V := oddV a r)
        hr hV (oddL_sq_le a r) (oddR_sq_le a r)

/-- The summed odd Cauchy estimate, conditional only on the block-coverage
estimate `oddSquareSum ≤ S^4`.
-/
theorem oddWeightedSum_le_of_coverage {m : ℕ} (a : Fin m → ℝ)
    (hcover : oddSquareSum a ≤ blockSsq a ^ 2) :
    oddWeightedSum a ≤ 11 * blockSsq a ^ 2 := by
  calc
    oddWeightedSum a
        ≤ ∑ r : Fin m, 11 * oddSquareTerm a r := by
          unfold oddWeightedSum
          exact Finset.sum_le_sum fun r _ ↦ oddWeightedTerm_le a r
    _ = 11 * oddSquareSum a := by
          simp [oddSquareSum, Finset.mul_sum]
    _ ≤ 11 * blockSsq a ^ 2 := by
          exact mul_le_mul_of_nonneg_left hcover (by norm_num)

theorem oddSquareSum_eq_pair_sum {m : ℕ} (a : Fin m → ℝ) :
    oddSquareSum a =
      ∑ p : OddUDomain m ⊕ OddVDomain m, pairWeight a (oddSquarePair p) := by
  classical
  have hleft :
      oddSquareSum a =
        (∑ r : Fin m, oddU a r) +
          ∑ r : {r : Fin m // r.val ≠ 0}, oddV a r.val := by
    unfold oddSquareSum oddSquareTerm
    have hsplit :
        (∑ r : Fin m, if r.val = 0 then 0 else oddU a r + oddV a r) =
          (∑ r : Fin m, oddU a r) +
            ∑ r : Fin m, if r.val = 0 then 0 else oddV a r := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      by_cases h0 : r.val = 0
      · have hU0 : oddU a r = 0 := by
          unfold oddU
          have : IsEmpty (Fin r.val) := by
            rw [h0]
            infer_instance
          exact Fintype.sum_empty _
        simp [h0, hU0]
      · simp [h0]
    have hsub :
        (∑ r : Fin m, if r.val = 0 then 0 else oddV a r) =
          ∑ r : {r : Fin m // r.val ≠ 0}, oddV a r.val := by
      let p : Fin m → Prop := fun r ↦ r.val ≠ 0
      have hif :
          (∑ r : Fin m, if r.val = 0 then 0 else oddV a r) =
            ∑ r : Fin m, if p r then oddV a r else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases h0 : r.val = 0 <;> simp [p, h0]
      have hfilter :
          (∑ r ∈ (Finset.univ.filter p), oddV a r) =
            ∑ r : Fin m, if p r then oddV a r else 0 := by
        simpa [p] using
          (Finset.sum_filter (s := (Finset.univ : Finset (Fin m))) (p := p)
            (f := fun r ↦ oddV a r))
      have hsubtype :
          (∑ r ∈ (Finset.univ.filter p), oddV a r) =
            ∑ r : {r : Fin m // p r}, oddV a r.val := by
        exact Finset.sum_subtype (s := Finset.univ.filter p)
          (h := by intro r; simp [p]) (f := fun r ↦ oddV a r)
      rw [hif, ← hfilter, hsubtype]
    rw [hsplit, hsub]
  have hU :
      (∑ p : OddUDomain m, pairWeight a (oddSquarePair (Sum.inl p))) =
        ∑ r : Fin m, oddU a r := by
    simpa [OddUDomain, oddU, pairWeight, oddSquarePair, oddUPair, mul_pow] using
      (Fintype.sum_sigma'
        (f := fun (r : Fin m) (t : Fin r.val) ↦
          pairWeight a (oddSquarePair (Sum.inl (Sigma.mk r t)))))
  have hV :
      (∑ p : OddVDomain m, pairWeight a (oddSquarePair (Sum.inr p))) =
        ∑ r : {r : Fin m // r.val ≠ 0}, oddV a r.val := by
    simpa [OddVDomain, oddV, pairWeight, oddSquarePair, oddVPair, mul_pow] using
      (Fintype.sum_sigma'
        (f := fun (r : {r : Fin m // r.val ≠ 0}) (t : Fin (r.val.val + 1)) ↦
          pairWeight a (oddSquarePair (Sum.inr (Sigma.mk r t)))))
  rw [hleft, Fintype.sum_sum_type, hU, hV]

theorem oddSquareSum_le_blockSsq_sq {m : ℕ} (a : Fin m → ℝ) :
    oddSquareSum a ≤ blockSsq a ^ 2 := by
  rw [oddSquareSum_eq_pair_sum, blockSsq_sq_eq_pair_sum]
  exact
    sum_comp_le_univ_sum_of_injective
      (f := oddSquarePair (m := m))
      oddSquarePair_injective
      (pairWeight a)
      (by
        intro p
        unfold pairWeight
        positivity)

/-- The unconditional odd summed Cauchy estimate. -/
theorem oddWeightedSum_le {m : ℕ} (a : Fin m → ℝ) :
    oddWeightedSum a ≤ 11 * blockSsq a ^ 2 :=
  oddWeightedSum_le_of_coverage a (oddSquareSum_le_blockSsq_sq a)

/-- Even weighted contribution for a single ordinary/wrap-around block.

The ordinary blocks are `1 ≤ r ≤ m - 2`; all other indices are recorded as
zero.  The middle-frequency block is stored separately.
-/
def evenWeightedOrdinaryTerm {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  if r.val = 0 ∨ r.val = m - 1 then
    0
  else
    (3 * evenL a r + evenR a r) ^ 2 / (2 * (r.val : ℝ))

/-- Even ordinary squared-block contribution. -/
def evenSquareOrdinaryTerm {m : ℕ} (a : Fin m → ℝ) (r : Fin m) : ℝ :=
  if r.val = 0 ∨ r.val = m - 1 then
    0
  else
    evenU a r + evenV a r

/-- The ordinary part of the even proof's weighted Cauchy sum. -/
def evenWeightedOrdinarySum {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ r : Fin m, evenWeightedOrdinaryTerm a r

/-- The ordinary part of the even proof's squared-block coverage sum. -/
def evenSquareOrdinarySum {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  ∑ r : Fin m, evenSquareOrdinaryTerm a r

/-- The complete even proof's weighted Cauchy sum, including the middle block. -/
def evenWeightedSum {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  evenWeightedOrdinarySum a + 9 * evenLm a ^ 2 / ((m - 1 : ℕ) : ℝ)

/-- The complete even proof's squared-block coverage sum. -/
def evenSquareSum {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  evenSquareOrdinarySum a + evenUm a

theorem evenWeightedOrdinaryTerm_le {m : ℕ} (a : Fin m → ℝ) (r : Fin m) :
    evenWeightedOrdinaryTerm a r ≤ 5 * evenSquareOrdinaryTerm a r := by
  by_cases hbad : r.val = 0 ∨ r.val = m - 1
  · simp [evenWeightedOrdinaryTerm, evenSquareOrdinaryTerm, hbad]
  · have h0 : r.val ≠ 0 := by
      intro h
      exact hbad (Or.inl h)
    have hr_nat : 0 < r.val := Nat.pos_of_ne_zero h0
    have hr : 0 < (r.val : ℝ) := by exact_mod_cast hr_nat
    simpa [evenWeightedOrdinaryTerm, evenSquareOrdinaryTerm, hbad, mul_add] using
      even_pointwise_block_bound
        (r := (r.val : ℝ))
        (L := evenL a r)
        (R := evenR a r)
        (U := evenU a r)
        (V := evenV a r)
        hr (evenL_sq_le a r) (evenR_sq_le a r)

/-- The summed even Cauchy estimate, conditional only on the block-coverage
estimate `evenSquareSum ≤ S^4`.
-/
theorem evenWeightedSum_le_of_coverage {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℝ)
    (hcover : evenSquareSum a ≤ blockSsq a ^ 2) :
    evenWeightedSum a ≤ 9 * blockSsq a ^ 2 := by
  have hm_pos : 0 < ((m - 1 : ℕ) : ℝ) := by
    have : 0 < m - 1 := by omega
    exact_mod_cast this
  have hmiddle : 9 * evenLm a ^ 2 / ((m - 1 : ℕ) : ℝ) ≤ 9 * evenUm a :=
    even_middle_block_bound (r := ((m - 1 : ℕ) : ℝ)) (L := evenLm a) (U := evenUm a)
      hm_pos (evenLm_sq_le a)
  have hord :
      evenWeightedOrdinarySum a ≤ 5 * evenSquareOrdinarySum a := by
    calc
      evenWeightedOrdinarySum a
          ≤ ∑ r : Fin m, 5 * evenSquareOrdinaryTerm a r := by
            unfold evenWeightedOrdinarySum
            exact Finset.sum_le_sum fun r _ ↦ evenWeightedOrdinaryTerm_le a r
      _ = 5 * evenSquareOrdinarySum a := by
            simp [evenSquareOrdinarySum, Finset.mul_sum]
  have hmiddle_nonneg : 0 ≤ evenUm a := by
    unfold evenUm
    positivity
  have hord_nonneg : 0 ≤ evenSquareOrdinarySum a := by
    unfold evenSquareOrdinarySum evenSquareOrdinaryTerm evenU evenV
    positivity
  calc
    evenWeightedSum a
        ≤ 5 * evenSquareOrdinarySum a + 9 * evenUm a := by
          unfold evenWeightedSum
          exact add_le_add hord hmiddle
    _ ≤ 9 * (evenSquareOrdinarySum a + evenUm a) := by
          nlinarith
    _ = 9 * evenSquareSum a := by
          unfold evenSquareSum
          ring
    _ ≤ 9 * blockSsq a ^ 2 := by
          exact mul_le_mul_of_nonneg_left hcover (by norm_num)

theorem evenSquareSum_eq_pair_sum {m : ℕ} (a : Fin m → ℝ) :
    evenSquareSum a =
      ∑ p : (EvenUDomain m ⊕ EvenVDomain m) ⊕ EvenMDomain m,
        pairWeight a (evenSquarePair p) := by
  classical
  let p : Fin m → Prop := fun r ↦ r.val ≠ 0 ∧ r.val ≠ m - 1
  have hord :
      evenSquareOrdinarySum a =
        (∑ r : EvenOrdinaryIndex m, evenU a r.val) +
          ∑ r : EvenOrdinaryIndex m, evenV a r.val := by
    unfold evenSquareOrdinarySum evenSquareOrdinaryTerm
    have hsplit :
        (∑ r : Fin m,
            if r.val = 0 ∨ r.val = m - 1 then 0 else evenU a r + evenV a r) =
          (∑ r : Fin m, if p r then evenU a r else 0) +
            ∑ r : Fin m, if p r then evenV a r else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hp : p r
      · have hbad : ¬ (r.val = 0 ∨ r.val = m - 1) := by
          dsimp [p] at hp
          exact fun h ↦ h.elim hp.1 hp.2
        simp [p, hp]
      · have hbad : r.val = 0 ∨ r.val = m - 1 := by
          dsimp [p] at hp
          omega
        simp [p, hp, hbad]
    have hsubU :
        (∑ r : Fin m, if p r then evenU a r else 0) =
          ∑ r : EvenOrdinaryIndex m, evenU a r.val := by
      have hfilter :
          (∑ r ∈ (Finset.univ.filter p), evenU a r) =
            ∑ r : Fin m, if p r then evenU a r else 0 := by
        simpa using
          (Finset.sum_filter (s := (Finset.univ : Finset (Fin m))) (p := p)
            (f := fun r ↦ evenU a r))
      have hsubtype :
          (∑ r ∈ (Finset.univ.filter p), evenU a r) =
            ∑ r : EvenOrdinaryIndex m, evenU a r.val := by
        exact Finset.sum_subtype (s := Finset.univ.filter p)
          (h := by intro r; simp [p]) (f := fun r ↦ evenU a r)
      rw [← hfilter, hsubtype]
    have hsubV :
        (∑ r : Fin m, if p r then evenV a r else 0) =
          ∑ r : EvenOrdinaryIndex m, evenV a r.val := by
      have hfilter :
          (∑ r ∈ (Finset.univ.filter p), evenV a r) =
            ∑ r : Fin m, if p r then evenV a r else 0 := by
        simpa using
          (Finset.sum_filter (s := (Finset.univ : Finset (Fin m))) (p := p)
            (f := fun r ↦ evenV a r))
      have hsubtype :
          (∑ r ∈ (Finset.univ.filter p), evenV a r) =
            ∑ r : EvenOrdinaryIndex m, evenV a r.val := by
        exact Finset.sum_subtype (s := Finset.univ.filter p)
          (h := by intro r; simp [p]) (f := fun r ↦ evenV a r)
      rw [← hfilter, hsubtype]
    rw [hsplit, hsubU, hsubV]
  have hU :
      (∑ x : EvenUDomain m, pairWeight a (evenSquarePair (Sum.inl (Sum.inl x)))) =
        ∑ r : EvenOrdinaryIndex m, evenU a r.val := by
    simpa [EvenUDomain, evenU, pairWeight, evenSquarePair, evenUPair, mul_pow] using
      (Fintype.sum_sigma'
        (f := fun (r : EvenOrdinaryIndex m) (t : Fin r.val.val) ↦
          pairWeight a (evenSquarePair (Sum.inl (Sum.inl (Sigma.mk r t))))))
  have hV :
      (∑ x : EvenVDomain m, pairWeight a (evenSquarePair (Sum.inl (Sum.inr x)))) =
        ∑ r : EvenOrdinaryIndex m, evenV a r.val := by
    simpa [EvenVDomain, evenV, pairWeight, evenSquarePair, evenVPair, mul_pow] using
      (Fintype.sum_sigma'
        (f := fun (r : EvenOrdinaryIndex m) (t : Fin r.val.val) ↦
          pairWeight a (evenSquarePair (Sum.inl (Sum.inr (Sigma.mk r t))))))
  have hM :
      (∑ x : EvenMDomain m, pairWeight a (evenSquarePair (Sum.inr x))) =
        evenUm a := by
    simp [EvenMDomain, evenUm, pairWeight, evenSquarePair, evenMPair]
  unfold evenSquareSum
  rw [hord, Fintype.sum_sum_type, Fintype.sum_sum_type, hU, hV, hM]

theorem evenSquareSum_le_blockSsq_sq {m : ℕ} (a : Fin m → ℝ) :
    evenSquareSum a ≤ blockSsq a ^ 2 := by
  rw [evenSquareSum_eq_pair_sum, blockSsq_sq_eq_pair_sum]
  exact
    sum_comp_le_univ_sum_of_injective
      (f := evenSquarePair (m := m))
      evenSquarePair_injective
      (pairWeight a)
      (by
        intro p
        unfold pairWeight
        positivity)

/-- The unconditional even summed Cauchy estimate. -/
theorem evenWeightedSum_le {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℝ) :
    evenWeightedSum a ≤ 9 * blockSsq a ^ 2 :=
  evenWeightedSum_le_of_coverage hm a (evenSquareSum_le_blockSsq_sq a)

end

end CyclicLsi
