module

public import CyclicLsi.Support.Proposition78.Fourier.ResonanceBounds


/-!
# Proposition 8: odd third-moment estimate

This file proves the odd cyclic-group third-moment estimate for the concrete
word-length Fourier energy.
-/

@[expose] public section

namespace CyclicLsi

open scoped BigOperators

noncomputable section

theorem oddFourierAmp_nonneg {m : ℕ} (u : ZMod (2 * m + 1) → ℝ) (j : Fin m) :
    0 ≤ oddFourierAmp m u j := by
  unfold oddFourierAmp
  positivity

def oddBoundaryB0 {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  if hm : 0 < m then
    √((1 : ℝ) / 2) * a ⟨0, hm⟩ * oddR a ⟨0, hm⟩
  else
    0

def oddWeightedB1 {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  √((1 : ℝ) / 2) *
    ∑ r : {r : Fin m // r.val ≠ 0},
      a r.val * (3 * oddL a r.val + oddR a r.val)

theorem oddL_zero {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) :
    oddL a ⟨0, hm⟩ = 0 := by
  unfold oddL
  exact Fintype.sum_empty _

theorem oddR_zero_eq_last_sq {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) :
    oddR a ⟨0, hm⟩ = a ⟨m - 1, by omega⟩ ^ 2 := by
  unfold oddR
  simp [pow_two]

theorem sum_fin_eq_zero_add_ne_zero {m : ℕ} [NeZero m]
    {β : Type*} [AddCommMonoid β] (F : Fin m → β) :
    ∑ r : Fin m, F r =
      F ⟨0, by exact Nat.pos_of_ne_zero (NeZero.ne m)⟩ +
        ∑ r : {r : Fin m // r.val ≠ 0}, F r.val := by
  classical
  let p : Fin m → Prop := fun r ↦ r.val ≠ 0
  have hsplit :
      (∑ r : Fin m, F r) =
        (∑ r : Fin m, if r.val = 0 then F r else 0) +
          ∑ r : Fin m, if p r then F r else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h0 : r.val = 0
    · have hr : r = ⟨0, by exact Nat.pos_of_ne_zero (NeZero.ne m)⟩ := Fin.ext h0
      simp [p, hr]
    · have hrne : r ≠ 0 := by
        intro hr
        exact h0 (congrArg Fin.val hr)
      simp [p, h0, hrne]
  have hzero :
      (∑ r : Fin m, if r.val = 0 then F r else 0) =
        F ⟨0, by exact Nat.pos_of_ne_zero (NeZero.ne m)⟩ := by
    rw [Finset.sum_eq_single (⟨0, by exact Nat.pos_of_ne_zero (NeZero.ne m)⟩ : Fin m)]
    · simp
    · intro r _ hr
      have hval : r.val ≠ 0 := by
        intro hz
        apply hr
        exact Fin.ext hz
      simp [hval]
    · intro hnot
      simp at hnot
  have hsub :
      (∑ r : Fin m, if p r then F r else 0) =
        ∑ r : {r : Fin m // p r}, F r.val := by
    have hfilter :
        (∑ r ∈ (Finset.univ.filter p), F r) =
          ∑ r : Fin m, if p r then F r else 0 := by
      simpa [p] using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin m))) (p := p) (f := F))
    have hsubtype :
        (∑ r ∈ (Finset.univ.filter p), F r) =
          ∑ r : {r : Fin m // p r}, F r.val := by
      exact Finset.sum_subtype (s := Finset.univ.filter p)
        (h := by intro r; simp [p]) (f := F)
    rw [← hfilter, hsubtype]
  rw [hsplit, hzero, hsub]

theorem fin_last_sq_le_blockQsq {m : ℕ} (hm : 2 ≤ m) {a : Fin m → ℝ} :
    a ⟨m - 1, by omega⟩ ^ 2 ≤ blockQsq a := by
  let last : Fin m := ⟨m - 1, by omega⟩
  have hlast_mem : last ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ last
  have hlast_weight : (last.val : ℝ) * a last ^ 2 ≥ a last ^ 2 := by
    have hweight : (1 : ℝ) ≤ (last.val : ℝ) := by
      dsimp [last]
      exact_mod_cast (by omega : 1 ≤ m - 1)
    simpa using mul_le_mul_of_nonneg_right hweight (sq_nonneg (a last))
  unfold blockQsq
  exact hlast_weight.trans
    (Finset.single_le_sum (f := fun j : Fin m ↦ (j.val : ℝ) * a j ^ 2)
      (fun j _ ↦ by positivity) hlast_mem)

theorem fin_last_le_sqrt_blockQsq {m : ℕ} (hm : 2 ≤ m) {a : Fin m → ℝ} :
    a ⟨m - 1, by omega⟩ ≤ √(blockQsq a) := by
  apply Real.le_sqrt_of_sq_le
  exact fin_last_sq_le_blockQsq hm

theorem two_mul_first_mul_last_le_blockSsq {m : ℕ} (hm : 2 ≤ m)
    {a : Fin m → ℝ} :
    2 * a ⟨0, by omega⟩ * a ⟨m - 1, by omega⟩ ≤ blockSsq a := by
  let first : Fin m := ⟨0, by omega⟩
  let last : Fin m := ⟨m - 1, by omega⟩
  have hne : first ≠ last := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [first, last] at hval
    omega
  have hsubset :
      ({first, last} : Finset (Fin m)) ⊆ Finset.univ := by
    intro j hj
    simp
  have hsmall :
      (∑ j ∈ ({first, last} : Finset (Fin m)), a j ^ 2) ≤ blockSsq a := by
    unfold blockSsq
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro j _ _; positivity)
  have htwo :
      2 * a first * a last ≤ a first ^ 2 + a last ^ 2 := by
    have hsq : 0 ≤ (a first - a last) ^ 2 := sq_nonneg _
    nlinarith
  have hpair :
      (∑ j ∈ ({first, last} : Finset (Fin m)), a j ^ 2) =
        a first ^ 2 + a last ^ 2 := by
    simp [first, last, hne]
  nlinarith

theorem odd_boundaryB0_le {m : ℕ} (hm : 2 ≤ m)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) :
    oddBoundaryB0 a ≤
      (1 / (2 * √(2 : ℝ))) * blockSsq a * √(blockQsq a) := by
  have hmpos : 0 < m := by omega
  let first : Fin m := ⟨0, hmpos⟩
  let last : Fin m := ⟨m - 1, by omega⟩
  have hR : oddR a first = a last ^ 2 := by
    simpa [first, last] using oddR_zero_eq_last_sq hmpos a
  have hS : 2 * a first * a last ≤ blockSsq a := by
    simpa [first, last] using two_mul_first_mul_last_le_blockSsq hm
  have hlast : a last ≤ √(blockQsq a) := by
    simpa [last] using fin_last_le_sqrt_blockQsq hm
  have hnonneg : 0 ≤ a last := ha last
  have hprod :
      a first * a last ^ 2 ≤ (1 / 2) * blockSsq a * √(blockQsq a) := by
    have hmul :
        (2 * a first * a last) * a last ≤ blockSsq a * √(blockQsq a) :=
      mul_le_mul hS hlast (ha last) (by
        unfold blockSsq
        positivity)
    nlinarith
  unfold oddBoundaryB0
  simp only [hmpos, dite_true]
  change √((1 : ℝ) / 2) * a first * oddR a first ≤
    (1 / (2 * √(2 : ℝ))) * blockSsq a * √(blockQsq a)
  rw [hR]
  have hsqrt_half :
      √((1 : ℝ) / 2) = 1 / √(2 : ℝ) := by
    have hsqrt2_pos : 0 < √(2 : ℝ) := by positivity
    rw [eq_div_iff hsqrt2_pos.ne']
    exact sqrt_half_mul_sqrt_two
  calc
    √((1 : ℝ) / 2) * a first * a last ^ 2
        = √((1 : ℝ) / 2) * (a first * a last ^ 2) := by ring
    _ ≤ √((1 : ℝ) / 2) *
        ((1 / 2) * blockSsq a * √(blockQsq a)) := by
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (1 / (2 * √(2 : ℝ))) * blockSsq a * √(blockQsq a) := by
          rw [hsqrt_half]
          ring

theorem odd_weightedB1_le {m : ℕ} {a : Fin m → ℝ} :
    oddWeightedB1 a ≤
      √((1 : ℝ) / 2) * √(blockQsq a) * √(oddWeightedSum a) := by
  classical
  by_cases hm0 : m = 0
  · subst m
    simp [oddWeightedB1, blockQsq, oddWeightedSum]
  haveI : NeZero m := ⟨hm0⟩
  let F : Fin m → ℝ := fun r ↦ √(r.val : ℝ) * a r
  let G : Fin m → ℝ := fun r ↦
    if h : r.val = 0 then
      0
    else
      (3 * oddL a r + oddR a r) / √(r.val : ℝ)
  have hFG :
      ∑ r : Fin m, F r * G r =
        ∑ r : {r : Fin m // r.val ≠ 0},
          a r.val * (3 * oddL a r.val + oddR a r.val) := by
    rw [sum_fin_eq_zero_add_ne_zero (F := fun r : Fin m ↦ F r * G r)]
    let z : Fin m := ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩
    change F z * G z + (∑ r : {r : Fin m // r.val ≠ 0}, F r.val * G r.val) =
      ∑ r : {r : Fin m // r.val ≠ 0},
        a r.val * (3 * oddL a r.val + oddR a r.val)
    have hzero : F z * G z = 0 := by
      simp [F, G, z]
    rw [hzero, zero_add]
    apply Finset.sum_congr rfl
    intro r _
    have hrpos : 0 < (r.val.val : ℝ) := by
      have : 0 < r.val.val := Nat.pos_of_ne_zero r.property
      exact_mod_cast this
    dsimp [F, G]
    rw [if_neg r.property]
    field_simp [(Real.sqrt_pos.2 hrpos).ne']
  have hFsq :
      ∑ r : Fin m, F r ^ 2 = blockQsq a := by
    unfold blockQsq
    apply Finset.sum_congr rfl
    intro r _
    simp [F, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (r.val : ℝ))]
  have hGsq :
      ∑ r : Fin m, G r ^ 2 = oddWeightedSum a := by
    unfold oddWeightedSum oddWeightedTerm
    apply Finset.sum_congr rfl
    intro r _
    by_cases h0 : r.val = 0
    · simp [G, h0]
    · have hrpos : 0 < (r.val : ℝ) := by
        have : 0 < r.val := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      dsimp [G]
      rw [if_neg h0, if_neg h0]
      change ((3 * oddL a r + oddR a r) / √(r.val : ℝ)) ^ 2 =
        (3 * oddL a r + oddR a r) ^ 2 / (r.val : ℝ)
      rw [div_pow, Real.sq_sqrt hrpos.le]
  have hcauchy :
      ∑ r : Fin m, F r * G r ≤ √(blockQsq a) * √(oddWeightedSum a) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m)) F G
    simpa [hFsq, hGsq] using h
  unfold oddWeightedB1
  have hmul :=
    mul_le_mul_of_nonneg_left (by simpa [hFG] using hcauchy)
      (Real.sqrt_nonneg ((1 : ℝ) / 2))
  simpa [mul_assoc] using hmul

def oddTripleNormWeight {m : ℕ} (u : ZMod (2 * m + 1) → ℝ)
    (t : OddTriple m) : ℝ :=
  ‖realFourierCoeff u (oddSignedFreq t.1)‖ *
    ‖realFourierCoeff u (oddSignedFreq t.2.1)‖ *
    ‖realFourierCoeff u (oddSignedFreq t.2.2)‖

theorem two_mul_sqrt_half_cube :
    2 * (√((1 : ℝ) / 2) ^ 3) = √((1 : ℝ) / 2) := by
  have hsq : (√((1 : ℝ) / 2)) ^ 2 = (1 : ℝ) / 2 :=
    Real.sq_sqrt (by norm_num : 0 ≤ (1 : ℝ) / 2)
  nlinarith [Real.sqrt_nonneg ((1 : ℝ) / 2)]

theorem sum_oddOrientation {β : Type*} [AddCommMonoid β]
    (F : OddOrientation → β) :
    ∑ o : OddOrientation, F o = F OddOrientation.base + F OddOrientation.conj := by
  rw [show (Finset.univ : Finset OddOrientation) =
      {OddOrientation.base, OddOrientation.conj} by
    ext o
    cases o <;> simp]
  simp

@[simp]
theorem card_oddSlot : Fintype.card OddSlot = 3 := by
  decide

def oddOrdCoreWeight {m : ℕ} (a : Fin m → ℝ) (c : OddOrdCore m) : ℝ :=
  a c.1 * (a ⟨c.2.val, by omega⟩ * a ⟨c.1.val - 1 - c.2.val, by omega⟩)

def oddWrapCoreWeight {m : ℕ} (a : Fin m → ℝ) (c : OddWrapCore m) : ℝ :=
  a c.1 *
    (a ⟨m - c.1.val + c.2.val - 1, by omega⟩ *
      a ⟨m - c.2.val - 1, by omega⟩)

theorem oddOrdCoreWeight_sum_eq {m : ℕ} (a : Fin m → ℝ) :
    (∑ c : OddOrdCore m, oddOrdCoreWeight a c) =
      ∑ r : Fin m, a r * oddL a r := by
  simpa [OddOrdCore, oddOrdCoreWeight, oddL, Finset.mul_sum, mul_assoc] using
    (Fintype.sum_sigma'
      (f := fun (r : Fin m) (t : Fin r.val) ↦
        a r * (a ⟨t.val, by omega⟩ * a ⟨r.val - 1 - t.val, by omega⟩)))

theorem oddWrapCoreWeight_sum_eq {m : ℕ} (a : Fin m → ℝ) :
    (∑ c : OddWrapCore m, oddWrapCoreWeight a c) =
      ∑ r : Fin m, a r * oddR a r := by
  unfold OddWrapCore oddWrapCoreWeight oddR
  calc
    (∑ c : Sigma fun r : Fin m ↦ Fin (r.val + 1),
        a c.fst *
          (a ⟨m - c.fst.val + c.snd.val - 1, by omega⟩ *
            a ⟨m - c.snd.val - 1, by omega⟩))
        = ∑ r : Fin m, ∑ t : Fin (r.val + 1),
            a r *
              (a ⟨m - r.val + t.val - 1, by omega⟩ *
                a ⟨m - t.val - 1, by omega⟩) :=
          Fintype.sum_sigma'
            (f := fun (r : Fin m) (t : Fin (r.val + 1)) ↦
              a r *
                (a ⟨m - r.val + t.val - 1, by omega⟩ *
                  a ⟨m - t.val - 1, by omega⟩))
    _ = ∑ r : Fin m, a r *
          ∑ t : Fin (r.val + 1),
            a ⟨m - r.val - 1 + t.val, by omega⟩ *
              a ⟨m - 1 - t.val, by omega⟩ := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          congr 2
          · apply congrArg a
            have hidx :
                m - r.val + t.val - 1 = m - r.val - 1 + t.val := by
              have ht : t.val < r.val + 1 := t.isLt
              omega
            exact Fin.ext hidx
          · apply congrArg a
            have hidx : m - t.val - 1 = m - 1 - t.val := by
              have ht : t.val < r.val + 1 := t.isLt
              have hr : r.val < m := r.isLt
              omega
            exact Fin.ext hidx

theorem odd_ord_resonance_sum_eq {m : ℕ} (u : ZMod (2 * m + 1) → ℝ) :
    (∑ d : OddOrdDomain m, oddTripleNormWeight u (oddOrdTriple d)) =
      3 * √((1 : ℝ) / 2) *
        ∑ r : Fin m, oddFourierAmp m u r * oddL (oddFourierAmp m u) r := by
  classical
  let a : Fin m → ℝ := oddFourierAmp m u
  let q : ℝ := √((1 : ℝ) / 2)
  have hprod (t : OddTriple m) :
      oddTripleNormWeight u t = q ^ 3 * (a t.1.2 * a t.2.1.2 * a t.2.2.2) := by
    unfold oddTripleNormWeight q a
    rw [norm_oddSignedFreq_eq_sqrt_half_mul_amp,
      norm_oddSignedFreq_eq_sqrt_half_mul_amp,
      norm_oddSignedFreq_eq_sqrt_half_mul_amp]
    ring
  unfold OddOrdDomain
  calc
    (∑ d : OddOrientation × OddSlot × OddOrdCore m,
        oddTripleNormWeight u (oddOrdTriple d))
        = ∑ y : OddSlot × OddOrdCore m,
            2 * q ^ 3 * oddOrdCoreWeight a y.2 := by
          rw [Fintype.sum_prod_type_right]
          apply Finset.sum_congr rfl
          intro y _
          cases y with
          | mk slot c =>
            cases c with
            | mk r t =>
              rw [sum_oddOrientation]
              cases slot <;>
                simp [oddOrdTriple, oddOrientTriple, oddFlipTriple, oddFlipFreq,
                  oddOrdCoreTriple, oddPlaceOrd, oddOrdCoreWeight, hprod, q, a] <;>
                ring_nf
    _ = 3 * q * ∑ c : OddOrdCore m, oddOrdCoreWeight a c := by
          rw [Fintype.sum_prod_type_right]
          calc
            (∑ y : OddOrdCore m, ∑ x : OddSlot,
                2 * q ^ 3 * oddOrdCoreWeight a (x, y).2)
                = ∑ y : OddOrdCore m, 3 * q * oddOrdCoreWeight a y := by
                    apply Finset.sum_congr rfl
                    intro c _
                    have hq : 2 * q ^ 3 = q := by
                      simpa [q] using two_mul_sqrt_half_cube
                    simp [hq]
                    ring
            _ = 3 * q * ∑ c : OddOrdCore m, oddOrdCoreWeight a c := by
                  rw [Finset.mul_sum]
    _ = 3 * √((1 : ℝ) / 2) *
        ∑ r : Fin m, oddFourierAmp m u r * oddL (oddFourierAmp m u) r := by
          rw [oddOrdCoreWeight_sum_eq]

theorem odd_wrap_resonance_sum_eq {m : ℕ} (u : ZMod (2 * m + 1) → ℝ) :
    (∑ d : OddWrapDomain m, oddTripleNormWeight u (oddWrapTriple d)) =
      √((1 : ℝ) / 2) *
        ∑ r : Fin m, oddFourierAmp m u r * oddR (oddFourierAmp m u) r := by
  classical
  let a : Fin m → ℝ := oddFourierAmp m u
  let q : ℝ := √((1 : ℝ) / 2)
  have hprod (t : OddTriple m) :
      oddTripleNormWeight u t = q ^ 3 * (a t.1.2 * a t.2.1.2 * a t.2.2.2) := by
    unfold oddTripleNormWeight q a
    rw [norm_oddSignedFreq_eq_sqrt_half_mul_amp,
      norm_oddSignedFreq_eq_sqrt_half_mul_amp,
      norm_oddSignedFreq_eq_sqrt_half_mul_amp]
    ring
  unfold OddWrapDomain
  calc
    (∑ d : OddOrientation × OddWrapCore m,
        oddTripleNormWeight u (oddWrapTriple d))
        = ∑ c : OddWrapCore m, 2 * q ^ 3 * oddWrapCoreWeight a c := by
          rw [Fintype.sum_prod_type_right]
          apply Finset.sum_congr rfl
          intro c _
          cases c with
          | mk r t =>
            rw [sum_oddOrientation]
            simp [oddWrapTriple, oddOrientTriple, oddFlipTriple, oddFlipFreq,
              oddWrapCoreTriple, oddWrapCoreWeight, hprod, q, a]
            ring_nf
    _ = q * ∑ c : OddWrapCore m, oddWrapCoreWeight a c := by
          calc
            (∑ c : OddWrapCore m, 2 * q ^ 3 * oddWrapCoreWeight a c)
                = ∑ c : OddWrapCore m, q * oddWrapCoreWeight a c := by
                    apply Finset.sum_congr rfl
                    intro c _
                    have hq : 2 * q ^ 3 = q := by
                      simpa [q] using two_mul_sqrt_half_cube
                    rw [hq]
            _ = q * ∑ c : OddWrapCore m, oddWrapCoreWeight a c := by
                  rw [Finset.mul_sum]
    _ = √((1 : ℝ) / 2) *
        ∑ r : Fin m, oddFourierAmp m u r * oddR (oddFourierAmp m u) r := by
          rw [oddWrapCoreWeight_sum_eq]

theorem odd_resonance_domain_sum_eq_boundary_add_weighted {m : ℕ} (hm : 2 ≤ m)
    (u : ZMod (2 * m + 1) → ℝ) :
    (∑ d : OddResonanceDomain m, oddTripleNormWeight u (oddResonanceTriple d)) =
      oddBoundaryB0 (oddFourierAmp m u) + oddWeightedB1 (oddFourierAmp m u) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  let a : Fin m → ℝ := oddFourierAmp m u
  have hmpos : 0 < m := by omega
  calc
    (∑ d : OddResonanceDomain m, oddTripleNormWeight u (oddResonanceTriple d))
        = (∑ d : OddOrdDomain m, oddTripleNormWeight u (oddOrdTriple d)) +
            ∑ d : OddWrapDomain m, oddTripleNormWeight u (oddWrapTriple d) := by
          simp [OddResonanceDomain, oddResonanceTriple, Fintype.sum_sum_type]
    _ = 3 * √((1 : ℝ) / 2) * (∑ r : Fin m, a r * oddL a r) +
          √((1 : ℝ) / 2) * (∑ r : Fin m, a r * oddR a r) := by
          simp [a, odd_ord_resonance_sum_eq, odd_wrap_resonance_sum_eq]
    _ = oddBoundaryB0 a + oddWeightedB1 a := by
          rw [sum_fin_eq_zero_add_ne_zero (F := fun r : Fin m ↦ a r * oddL a r)]
          rw [sum_fin_eq_zero_add_ne_zero (F := fun r : Fin m ↦ a r * oddR a r)]
          have hL0 : oddL a (0 : Fin m) = 0 := by
            simpa using oddL_zero (Nat.pos_of_ne_zero (NeZero.ne m)) a
          unfold oddBoundaryB0 oddWeightedB1
          simp [hmpos, hL0, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            add_comm, add_left_comm]
          ring_nf

theorem odd_blockQsq_fourierAmp_eq_zmodWordEnergyReal_sub_Ssq {m : ℕ}
    {u : ZMod (2 * m + 1) → ℝ} (hu : MeanZero u) :
    blockQsq (oddFourierAmp m u) = zmodWordEnergyReal u - Ssq u := by
  haveI : NeZero (2 * m + 1) := ⟨by omega⟩
  rw [odd_blockQsq_fourierAmp_eq_zmodFourierQsq hu]
  unfold zmodFourierQsq zmodWordEnergyReal
  rw [zmodFourierSsq_eq_Ssq_real]

end

end CyclicLsi
