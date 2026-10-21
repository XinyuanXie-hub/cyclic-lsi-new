module
public import CyclicLsi.Support.Proposition78.Fourier.Bridge



/-!
# Odd cyclic-group resonance indexing

This file starts the Fourier-resonance enumeration for the odd third-moment
estimate.  The indices are zero-based: `j : Fin m` represents paper frequency
`j + 1`.
-/

namespace CyclicLsi

open scoped BigOperators

@[expose] public noncomputable section

abbrev OddN (m : ℕ) : ℕ :=
  2 * m + 1

inductive OddSign where
  | pos
  | neg
  deriving DecidableEq, Fintype, Repr

inductive OddOrientation where
  | base
  | conj
  deriving DecidableEq, Fintype, Repr

inductive OddSlot where
  | fst
  | snd
  | thd
  deriving DecidableEq, Fintype, Repr

abbrev OddSignedFreq (m : ℕ) : Type :=
  OddSign × Fin m

abbrev OddTriple (m : ℕ) : Type :=
  OddSignedFreq m × OddSignedFreq m × OddSignedFreq m

abbrev OddOrdCore (m : ℕ) : Type :=
  Sigma fun r : Fin m ↦ Fin r.val

abbrev OddWrapCore (m : ℕ) : Type :=
  Sigma fun r : Fin m ↦ Fin (r.val + 1)

abbrev OddOrdDomain (m : ℕ) : Type :=
  OddOrientation × OddSlot × OddOrdCore m

abbrev OddWrapDomain (m : ℕ) : Type :=
  OddOrientation × OddWrapCore m

abbrev OddResonanceDomain (m : ℕ) : Type :=
  OddOrdDomain m ⊕ OddWrapDomain m

def oddPosFreq (m : ℕ) (j : Fin m) : ZMod (OddN m) :=
  (j.val + 1 : ℕ)

def oddSignedFreq {m : ℕ} (f : OddSignedFreq m) : ZMod (OddN m) :=
  match f.1 with
  | OddSign.pos => oddPosFreq m f.2
  | OddSign.neg => -oddPosFreq m f.2

def oddTripleSum {m : ℕ} (t : OddTriple m) : ZMod (OddN m) :=
  oddSignedFreq t.1 + oddSignedFreq t.2.1 + oddSignedFreq t.2.2

def oddFlipFreq {m : ℕ} (f : OddSignedFreq m) : OddSignedFreq m :=
  match f.1 with
  | OddSign.pos => (OddSign.neg, f.2)
  | OddSign.neg => (OddSign.pos, f.2)

def oddFlipTriple {m : ℕ} (t : OddTriple m) : OddTriple m :=
  (oddFlipFreq t.1, oddFlipFreq t.2.1, oddFlipFreq t.2.2)

def oddOrientTriple {m : ℕ} : OddOrientation → OddTriple m → OddTriple m
  | OddOrientation.base, t => t
  | OddOrientation.conj, t => oddFlipTriple t

def oddPlaceOrd {m : ℕ} (slot : OddSlot) (i j k : Fin m) : OddTriple m :=
  match slot with
  | OddSlot.fst => ((OddSign.neg, k), (OddSign.pos, i), (OddSign.pos, j))
  | OddSlot.snd => ((OddSign.pos, i), (OddSign.neg, k), (OddSign.pos, j))
  | OddSlot.thd => ((OddSign.pos, i), (OddSign.pos, j), (OddSign.neg, k))

def oddOrdCoreTriple {m : ℕ} (slot : OddSlot) (c : OddOrdCore m) : OddTriple m :=
  let r := c.1
  let t := c.2
  let i : Fin m := ⟨t.val, by omega⟩
  let j : Fin m := ⟨r.val - 1 - t.val, by omega⟩
  oddPlaceOrd slot i j r

def oddWrapCoreTriple {m : ℕ} (c : OddWrapCore m) : OddTriple m :=
  let r := c.1
  let t := c.2
  let i : Fin m := ⟨m - r.val + t.val - 1, by omega⟩
  let j : Fin m := ⟨m - t.val - 1, by omega⟩
  ((OddSign.pos, i), (OddSign.pos, j), (OddSign.pos, r))

def oddOrdTriple {m : ℕ} (d : OddOrdDomain m) : OddTriple m :=
  oddOrientTriple d.1 (oddOrdCoreTriple d.2.1 d.2.2)

def oddWrapTriple {m : ℕ} (d : OddWrapDomain m) : OddTriple m :=
  oddOrientTriple d.1 (oddWrapCoreTriple d.2)

def oddResonanceTriple {m : ℕ} : OddResonanceDomain m → OddTriple m :=
  Sum.elim oddOrdTriple oddWrapTriple

theorem oddSignedFreq_flip {m : ℕ} (f : OddSignedFreq m) :
    oddSignedFreq (oddFlipFreq f) = -oddSignedFreq f := by
  cases f with
  | mk s j =>
    cases s <;> simp [oddFlipFreq, oddSignedFreq]

theorem oddTripleSum_flip {m : ℕ} (t : OddTriple m) :
    oddTripleSum (oddFlipTriple t) = -oddTripleSum t := by
  simp [oddTripleSum, oddFlipTriple, oddSignedFreq_flip]
  abel

theorem odd_natCast_eq_of_lt_oddN {m a b : ℕ}
    (ha : a < OddN m) (hb : b < OddN m)
    (h : (a : ZMod (OddN m)) = (b : ZMod (OddN m))) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

theorem odd_pair_sum_eq_of_natCast_eq {m a b c : ℕ}
    (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m)
    (h : ((a + b : ℕ) : ZMod (OddN m)) = (c : ZMod (OddN m))) :
    a + b = c := by
  apply odd_natCast_eq_of_lt_oddN (m := m)
  · unfold OddN
    omega
  · unfold OddN
    omega
  · exact h

theorem odd_eq_oddN_of_pos_le_three_mul_of_dvd {m s : ℕ}
    (hspos : 0 < s) (hsle : s ≤ 3 * m) (hdvd : OddN m ∣ s) :
    s = OddN m := by
  rcases hdvd with ⟨q, rfl⟩
  have hqpos : 0 < q := by
    by_contra hq
    have : q = 0 := by omega
    subst q
    simp at hspos
  have hqle : q ≤ 1 := by
    by_contra hq
    have hq2 : 2 ≤ q := by omega
    have : 2 * OddN m ≤ q * OddN m := Nat.mul_le_mul_right _ hq2
    unfold OddN at this hsle
    nlinarith
  have hq : q = 1 := by omega
  subst q
  simp

theorem odd_triple_sum_eq_oddN_of_natCast_eq_zero {m a b c : ℕ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c)
    (ha : a ≤ m) (hb : b ≤ m) (hc : c ≤ m)
    (h : ((a + b + c : ℕ) : ZMod (OddN m)) = 0) :
    a + b + c = OddN m := by
  have hdvd : OddN m ∣ a + b + c :=
    (ZMod.natCast_eq_zero_iff (a + b + c) (OddN m)).mp h
  apply odd_eq_oddN_of_pos_le_three_mul_of_dvd
  · omega
  · omega
  · exact hdvd

theorem oddPlaceOrd_nat_sum_eq_of_sum_zero {m : ℕ}
    (slot : OddSlot) (i j k : Fin m)
    (h : oddTripleSum (oddPlaceOrd slot i j k) = 0) :
    (i.val + 1) + (j.val + 1) = k.val + 1 := by
  have hi : i.val + 1 ≤ m := by omega
  have hj : j.val + 1 ≤ m := by omega
  have hk : k.val + 1 ≤ m := by omega
  apply odd_pair_sum_eq_of_natCast_eq (m := m) hi hj hk
  cases slot <;>
    simp [oddTripleSum, oddPlaceOrd, oddSignedFreq, oddPosFreq] at h <;>
    rw [← sub_eq_zero] <;>
    simp only [Nat.cast_add, Nat.cast_one] <;>
    abel_nf at h ⊢ <;>
    exact h

theorem oddAllPos_nat_sum_eq_oddN_of_sum_zero {m : ℕ} (i j k : Fin m)
    (h : oddTripleSum ((OddSign.pos, i), (OddSign.pos, j), (OddSign.pos, k)) = 0) :
    (i.val + 1) + (j.val + 1) + (k.val + 1) = OddN m := by
  apply odd_triple_sum_eq_oddN_of_natCast_eq_zero
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · simp [oddTripleSum, oddSignedFreq, oddPosFreq] at h
    simp only [Nat.cast_add, Nat.cast_one]
    abel_nf at h ⊢
    exact h

theorem oddTripleSum_flip_eq_zero {m : ℕ} {t : OddTriple m}
    (h : oddTripleSum t = 0) :
    oddTripleSum (oddFlipTriple t) = 0 := by
  rw [oddTripleSum_flip, h, neg_zero]

theorem oddOrdCoreTriple_eq_placeOrd_of_sum {m : ℕ} (slot : OddSlot) (i j k : Fin m)
    (hijk : (i.val + 1) + (j.val + 1) = k.val + 1) :
    oddOrdCoreTriple slot ⟨k, ⟨i.val, by omega⟩⟩ = oddPlaceOrd slot i j k := by
  have hjval : k.val - 1 - i.val = j.val := by omega
  cases slot <;>
    dsimp [oddOrdCoreTriple, oddPlaceOrd] <;>
    congr

theorem oddWrapCoreTriple_eq_allPos_of_sum {m : ℕ} (i j k : Fin m)
    (hijk : (i.val + 1) + (j.val + 1) + (k.val + 1) = OddN m) :
    oddWrapCoreTriple ⟨k, ⟨m - j.val - 1, by
      unfold OddN at hijk
      omega⟩⟩ =
      ((OddSign.pos, i), (OddSign.pos, j), (OddSign.pos, k)) := by
  have hi : m - k.val + (m - j.val - 1) - 1 = i.val := by
    unfold OddN at hijk
    omega
  have hj : m - (m - j.val - 1) - 1 = j.val := by
    unfold OddN at hijk
    omega
  dsimp [oddWrapCoreTriple]
  apply Prod.ext
  · exact Prod.ext rfl (Fin.ext hi)
  · apply Prod.ext
    · exact Prod.ext rfl (Fin.ext hj)
    · rfl

theorem oddResonanceTriple_exists_of_sum_zero {m : ℕ} (t : OddTriple m)
    (ht : oddTripleSum t = 0) :
    ∃ d : OddResonanceDomain m, oddResonanceTriple d = t := by
  rcases t with ⟨⟨s₁, a⟩, ⟨⟨s₂, b⟩, ⟨s₃, c⟩⟩⟩
  cases s₁ <;> cases s₂ <;> cases s₃
  · have hsum := oddAllPos_nat_sum_eq_oddN_of_sum_zero a b c ht
    refine ⟨Sum.inr (OddOrientation.base, ⟨c, ⟨m - b.val - 1, by
      unfold OddN at hsum
      omega⟩⟩), ?_⟩
    simpa [oddResonanceTriple, oddWrapTriple, oddOrientTriple]
      using oddWrapCoreTriple_eq_allPos_of_sum a b c hsum
  · have hplace : oddTripleSum (oddPlaceOrd OddSlot.thd a b c) = 0 := by
      simpa [oddPlaceOrd] using ht
    have hsum := oddPlaceOrd_nat_sum_eq_of_sum_zero OddSlot.thd a b c hplace
    refine ⟨Sum.inl (OddOrientation.base, OddSlot.thd, ⟨c, ⟨a.val, by omega⟩⟩), ?_⟩
    simpa [oddResonanceTriple, oddOrdTriple, oddOrientTriple, oddPlaceOrd]
      using oddOrdCoreTriple_eq_placeOrd_of_sum OddSlot.thd a b c hsum
  · have hplace : oddTripleSum (oddPlaceOrd OddSlot.snd a c b) = 0 := by
      simpa [oddPlaceOrd] using ht
    have hsum := oddPlaceOrd_nat_sum_eq_of_sum_zero OddSlot.snd a c b hplace
    refine ⟨Sum.inl (OddOrientation.base, OddSlot.snd, ⟨b, ⟨a.val, by omega⟩⟩), ?_⟩
    simpa [oddResonanceTriple, oddOrdTriple, oddOrientTriple, oddPlaceOrd]
      using oddOrdCoreTriple_eq_placeOrd_of_sum OddSlot.snd a c b hsum
  · have hflip : oddTripleSum (oddPlaceOrd OddSlot.fst b c a) = 0 := by
      simpa [oddPlaceOrd, oddFlipTriple, oddFlipFreq] using
        (oddTripleSum_flip_eq_zero
          (t := ((OddSign.pos, a), (OddSign.neg, b), (OddSign.neg, c))) ht)
    have hsum := oddPlaceOrd_nat_sum_eq_of_sum_zero OddSlot.fst b c a hflip
    refine ⟨Sum.inl (OddOrientation.conj, OddSlot.fst, ⟨a, ⟨b.val, by omega⟩⟩), ?_⟩
    have hcore := oddOrdCoreTriple_eq_placeOrd_of_sum OddSlot.fst b c a hsum
    dsimp [oddResonanceTriple, oddOrdTriple, oddOrientTriple]
    rw [hcore]
    rfl
  · have hplace : oddTripleSum (oddPlaceOrd OddSlot.fst b c a) = 0 := by
      simpa [oddPlaceOrd] using ht
    have hsum := oddPlaceOrd_nat_sum_eq_of_sum_zero OddSlot.fst b c a hplace
    refine ⟨Sum.inl (OddOrientation.base, OddSlot.fst, ⟨a, ⟨b.val, by omega⟩⟩), ?_⟩
    simpa [oddResonanceTriple, oddOrdTriple, oddOrientTriple, oddPlaceOrd]
      using oddOrdCoreTriple_eq_placeOrd_of_sum OddSlot.fst b c a hsum
  · have hflip : oddTripleSum (oddPlaceOrd OddSlot.snd a c b) = 0 := by
      simpa [oddPlaceOrd, oddFlipTriple, oddFlipFreq] using
        (oddTripleSum_flip_eq_zero
          (t := ((OddSign.neg, a), (OddSign.pos, b), (OddSign.neg, c))) ht)
    have hsum := oddPlaceOrd_nat_sum_eq_of_sum_zero OddSlot.snd a c b hflip
    refine ⟨Sum.inl (OddOrientation.conj, OddSlot.snd, ⟨b, ⟨a.val, by omega⟩⟩), ?_⟩
    have hcore := oddOrdCoreTriple_eq_placeOrd_of_sum OddSlot.snd a c b hsum
    dsimp [oddResonanceTriple, oddOrdTriple, oddOrientTriple]
    rw [hcore]
    rfl
  · have hflip : oddTripleSum (oddPlaceOrd OddSlot.thd a b c) = 0 := by
      simpa [oddPlaceOrd, oddFlipTriple, oddFlipFreq] using
        (oddTripleSum_flip_eq_zero
          (t := ((OddSign.neg, a), (OddSign.neg, b), (OddSign.pos, c))) ht)
    have hsum := oddPlaceOrd_nat_sum_eq_of_sum_zero OddSlot.thd a b c hflip
    refine ⟨Sum.inl (OddOrientation.conj, OddSlot.thd, ⟨c, ⟨a.val, by omega⟩⟩), ?_⟩
    have hcore := oddOrdCoreTriple_eq_placeOrd_of_sum OddSlot.thd a b c hsum
    dsimp [oddResonanceTriple, oddOrdTriple, oddOrientTriple]
    rw [hcore]
    rfl
  · have hflip : oddTripleSum ((OddSign.pos, a), (OddSign.pos, b), (OddSign.pos, c)) = 0 := by
      simpa [oddFlipTriple, oddFlipFreq] using
        (oddTripleSum_flip_eq_zero
          (t := ((OddSign.neg, a), (OddSign.neg, b), (OddSign.neg, c))) ht)
    have hsum := oddAllPos_nat_sum_eq_oddN_of_sum_zero a b c hflip
    refine ⟨Sum.inr (OddOrientation.conj, ⟨c, ⟨m - b.val - 1, by
      unfold OddN at hsum
      omega⟩⟩), ?_⟩
    have hcore := oddWrapCoreTriple_eq_allPos_of_sum a b c hsum
    dsimp [oddResonanceTriple, oddWrapTriple, oddOrientTriple]
    rw [hcore]
    rfl

end

end CyclicLsi
