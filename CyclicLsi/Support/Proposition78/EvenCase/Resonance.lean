module
public import CyclicLsi.Support.Proposition78.BlockBounds



/-!
# Even cyclic-group resonance indexing

This file records the explicit zero-resonance families used in the even
third-moment estimate.  The indices are zero-based: `j : Fin (m - 1)`
represents the non-middle frequency `j + 1`, while `EvenFreq.mid` represents
the self-conjugate frequency `m` in `ZMod (2 * m)`.
-/

namespace CyclicLsi

open scoped BigOperators

@[expose] public noncomputable section

inductive EvenFreq (m : ℕ) where
  | pos : Fin (m - 1) → EvenFreq m
  | neg : Fin (m - 1) → EvenFreq m
  | mid : EvenFreq m
  deriving DecidableEq, Fintype, Repr

inductive EvenOrientation where
  | base
  | conj
  deriving DecidableEq, Repr

instance : Fintype EvenOrientation where
  elems := {.base, .conj}
  complete := by intro x; cases x <;> simp

inductive EvenSlot where
  | fst
  | snd
  | thd
  deriving DecidableEq, Repr

instance : Fintype EvenSlot where
  elems := {.fst, .snd, .thd}
  complete := by intro x; cases x <;> simp

abbrev EvenTriple (m : ℕ) : Type :=
  EvenFreq m × EvenFreq m × EvenFreq m

def evenFreqZ {m : ℕ} : EvenFreq m → ZMod (2 * m)
  | EvenFreq.pos j => ((j.val + 1 : ℕ) : ZMod (2 * m))
  | EvenFreq.neg j => -((j.val + 1 : ℕ) : ZMod (2 * m))
  | EvenFreq.mid => ((m : ℕ) : ZMod (2 * m))

def evenTripleSum {m : ℕ} (t : EvenTriple m) : ZMod (2 * m) :=
  evenFreqZ t.1 + evenFreqZ t.2.1 + evenFreqZ t.2.2

def evenFlipFreq {m : ℕ} : EvenFreq m → EvenFreq m
  | EvenFreq.pos j => EvenFreq.neg j
  | EvenFreq.neg j => EvenFreq.pos j
  | EvenFreq.mid => EvenFreq.mid

def evenFlipTriple {m : ℕ} (t : EvenTriple m) : EvenTriple m :=
  (evenFlipFreq t.1, evenFlipFreq t.2.1, evenFlipFreq t.2.2)

def evenOrientTriple {m : ℕ} : EvenOrientation → EvenTriple m → EvenTriple m
  | EvenOrientation.base, t => t
  | EvenOrientation.conj, t => evenFlipTriple t

def evenPlaceOrd {m : ℕ} (slot : EvenSlot) (i j k : Fin (m - 1)) :
    EvenTriple m :=
  match slot with
  | EvenSlot.fst => (EvenFreq.neg k, EvenFreq.pos i, EvenFreq.pos j)
  | EvenSlot.snd => (EvenFreq.pos i, EvenFreq.neg k, EvenFreq.pos j)
  | EvenSlot.thd => (EvenFreq.pos i, EvenFreq.pos j, EvenFreq.neg k)

def evenPlaceMiddle {m : ℕ} (slot : EvenSlot) (i j : Fin (m - 1)) :
    EvenTriple m :=
  match slot with
  | EvenSlot.fst => (EvenFreq.mid, EvenFreq.pos i, EvenFreq.pos j)
  | EvenSlot.snd => (EvenFreq.pos i, EvenFreq.mid, EvenFreq.pos j)
  | EvenSlot.thd => (EvenFreq.pos i, EvenFreq.pos j, EvenFreq.mid)

def evenOrdCoreTriple {m : ℕ} (slot : EvenSlot) (p : EvenUDomain m) :
    EvenTriple m :=
  let r := p.1.val
  let t := p.2
  let i : Fin (m - 1) := ⟨t.val, by
    have hr0 : r.val ≠ 0 := p.1.property.1
    have hrlast : r.val ≠ m - 1 := p.1.property.2
    have hrlt : r.val < m := r.isLt
    have ht : t.val < r.val := t.isLt
    omega⟩
  let j : Fin (m - 1) := ⟨r.val - 1 - t.val, by
    have hr0 : r.val ≠ 0 := p.1.property.1
    have hrlast : r.val ≠ m - 1 := p.1.property.2
    have hrlt : r.val < m := r.isLt
    have ht : t.val < r.val := t.isLt
    omega⟩
  let k : Fin (m - 1) := ⟨r.val, by
    have hrlast : r.val ≠ m - 1 := p.1.property.2
    have hrlt : r.val < m := r.isLt
    omega⟩
  evenPlaceOrd slot i j k

def evenWrapCoreTriple {m : ℕ} (p : EvenVDomain m) : EvenTriple m :=
  let r := p.1.val
  let t := p.2
  let i : Fin (m - 1) := ⟨m - r.val - 1 + t.val, by
    have hr0 : r.val ≠ 0 := p.1.property.1
    have hrlast : r.val ≠ m - 1 := p.1.property.2
    have hrlt : r.val < m := r.isLt
    have ht : t.val < r.val := t.isLt
    omega⟩
  let j : Fin (m - 1) := ⟨m - 2 - t.val, by
    have hr0 : r.val ≠ 0 := p.1.property.1
    have hrlast : r.val ≠ m - 1 := p.1.property.2
    have hrlt : r.val < m := r.isLt
    have ht : t.val < r.val := t.isLt
    omega⟩
  let k : Fin (m - 1) := ⟨r.val, by
    have hrlast : r.val ≠ m - 1 := p.1.property.2
    have hrlt : r.val < m := r.isLt
    omega⟩
  (EvenFreq.pos i, EvenFreq.pos j, EvenFreq.pos k)

def evenMiddleCoreTriple {m : ℕ} (slot : EvenSlot) (t : EvenMDomain m) :
    EvenTriple m :=
  let i : Fin (m - 1) := t
  let j : Fin (m - 1) := ⟨m - 2 - t.val, by
    have ht : t.val < m - 1 := t.isLt
    omega⟩
  evenPlaceMiddle slot i j

abbrev EvenOrdDomain (m : ℕ) : Type :=
  EvenOrientation × EvenSlot × EvenUDomain m

abbrev EvenWrapResDomain (m : ℕ) : Type :=
  EvenOrientation × EvenVDomain m

abbrev EvenMiddleResDomain (m : ℕ) : Type :=
  EvenOrientation × EvenSlot × EvenMDomain m

abbrev EvenResonanceDomain (m : ℕ) : Type :=
  (EvenOrdDomain m ⊕ EvenWrapResDomain m) ⊕ EvenMiddleResDomain m

def evenOrdTriple {m : ℕ} (d : EvenOrdDomain m) : EvenTriple m :=
  evenOrientTriple d.1 (evenOrdCoreTriple d.2.1 d.2.2)

def evenWrapTriple {m : ℕ} (d : EvenWrapResDomain m) : EvenTriple m :=
  evenOrientTriple d.1 (evenWrapCoreTriple d.2)

def evenMiddleTriple {m : ℕ} (d : EvenMiddleResDomain m) : EvenTriple m :=
  evenOrientTriple d.1 (evenMiddleCoreTriple d.2.1 d.2.2)

def evenResonanceTriple {m : ℕ} : EvenResonanceDomain m → EvenTriple m :=
  Sum.elim (Sum.elim evenOrdTriple evenWrapTriple) evenMiddleTriple

theorem even_mid_neg {m : ℕ} :
    ((m : ℕ) : ZMod (2 * m)) = -((m : ℕ) : ZMod (2 * m)) := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← Nat.cast_add]
  have h : m + m = 2 * m := by omega
  rw [h]
  simp

theorem evenFreqZ_flip {m : ℕ} (f : EvenFreq m) :
    evenFreqZ (evenFlipFreq f) = -evenFreqZ f := by
  cases f with
  | pos j => simp [evenFlipFreq, evenFreqZ]
  | neg j => simp [evenFlipFreq, evenFreqZ]
  | mid => simpa [evenFlipFreq, evenFreqZ] using even_mid_neg (m := m)

theorem evenTripleSum_flip {m : ℕ} (t : EvenTriple m) :
    evenTripleSum (evenFlipTriple t) = -evenTripleSum t := by
  simp [evenTripleSum, evenFlipTriple, evenFreqZ_flip]
  abel

theorem even_natCast_eq_of_lt_two_mul {m a b : ℕ}
    (ha : a < 2 * m) (hb : b < 2 * m)
    (h : (a : ZMod (2 * m)) = (b : ZMod (2 * m))) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

theorem even_pair_sum_eq_of_natCast_eq {m a b c : ℕ}
    (hm : 2 ≤ m) (ha : a ≤ m - 1) (hb : b ≤ m - 1) (hc : c ≤ m - 1)
    (h : ((a + b : ℕ) : ZMod (2 * m)) = (c : ZMod (2 * m))) :
    a + b = c := by
  apply even_natCast_eq_of_lt_two_mul (m := m)
  · omega
  · omega
  · exact h

theorem even_eq_two_mul_of_pos_lt_four_mul_of_dvd {m s : ℕ}
    (hspos : 0 < s) (hslt : s < 4 * m) (hdvd : 2 * m ∣ s) :
    s = 2 * m := by
  rcases hdvd with ⟨q, rfl⟩
  have hqpos : 0 < q := by
    by_contra hq
    have : q = 0 := by omega
    subst q
    simp at hspos
  have hq_lt_two : q < 2 := by
    by_contra hq
    have hq2 : 2 ≤ q := by omega
    have : 2 * (2 * m) ≤ q * (2 * m) := Nat.mul_le_mul_right _ hq2
    nlinarith
  have hq : q = 1 := by omega
  subst q
  simp

theorem even_triple_sum_eq_two_mul_of_natCast_eq_zero {m a b c : ℕ}
    (hm : 2 ≤ m)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c)
    (ha : a ≤ m - 1) (hb : b ≤ m - 1) (hc : c ≤ m - 1)
    (h : ((a + b + c : ℕ) : ZMod (2 * m)) = 0) :
    a + b + c = 2 * m := by
  have hdvd : 2 * m ∣ a + b + c :=
    (ZMod.natCast_eq_zero_iff (a + b + c) (2 * m)).mp h
  apply even_eq_two_mul_of_pos_lt_four_mul_of_dvd (m := m)
  · omega
  · omega
  · exact hdvd

theorem even_middle_pair_sum_eq_of_natCast_eq_zero {m a b : ℕ}
    (hm : 2 ≤ m)
    (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a ≤ m - 1) (hb : b ≤ m - 1)
    (h : ((a + b + m : ℕ) : ZMod (2 * m)) = 0) :
    a + b = m := by
  have hsum : a + b + m = 2 * m := by
    have hdvd : 2 * m ∣ a + b + m :=
      (ZMod.natCast_eq_zero_iff (a + b + m) (2 * m)).mp h
    apply even_eq_two_mul_of_pos_lt_four_mul_of_dvd (m := m)
    · omega
    · omega
    · exact hdvd
  omega

theorem evenPlaceOrd_nat_sum_eq_of_sum_zero {m : ℕ} (hm : 2 ≤ m)
    (slot : EvenSlot) (i j k : Fin (m - 1))
    (h : evenTripleSum (evenPlaceOrd slot i j k) = 0) :
    (i.val + 1) + (j.val + 1) = k.val + 1 := by
  have hi : i.val + 1 ≤ m - 1 := by omega
  have hj : j.val + 1 ≤ m - 1 := by omega
  have hk : k.val + 1 ≤ m - 1 := by omega
  apply even_pair_sum_eq_of_natCast_eq (m := m) hm hi hj hk
  cases slot <;>
    simp [evenTripleSum, evenPlaceOrd, evenFreqZ] at h <;>
    rw [← sub_eq_zero] <;>
    simp only [Nat.cast_add, Nat.cast_one] <;>
    abel_nf at h ⊢ <;>
    exact h

theorem evenAllPos_nat_sum_eq_two_mul_of_sum_zero {m : ℕ} (hm : 2 ≤ m)
    (i j k : Fin (m - 1))
    (h : evenTripleSum (EvenFreq.pos i, EvenFreq.pos j, EvenFreq.pos k) = 0) :
    (i.val + 1) + (j.val + 1) + (k.val + 1) = 2 * m := by
  apply even_triple_sum_eq_two_mul_of_natCast_eq_zero (m := m) hm
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · simp [evenTripleSum, evenFreqZ] at h
    simp only [Nat.cast_add, Nat.cast_one]
    abel_nf at h ⊢
    exact h

theorem evenMiddle_nat_sum_eq_of_sum_zero {m : ℕ} (hm : 2 ≤ m)
    (slot : EvenSlot) (i j : Fin (m - 1))
    (h : evenTripleSum (evenPlaceMiddle slot i j) = 0) :
    (i.val + 1) + (j.val + 1) = m := by
  apply even_middle_pair_sum_eq_of_natCast_eq_zero (m := m) hm
  · omega
  · omega
  · omega
  · omega
  · cases slot <;>
      simp [evenTripleSum, evenPlaceMiddle, evenFreqZ] at h <;>
      simp only [Nat.cast_add, Nat.cast_one] <;>
      abel_nf at h ⊢ <;>
      exact h

theorem evenTripleSum_flip_eq_zero {m : ℕ} {t : EvenTriple m}
    (h : evenTripleSum t = 0) :
    evenTripleSum (evenFlipTriple t) = 0 := by
  rw [evenTripleSum_flip, h, neg_zero]

theorem evenOrdCoreTriple_exists_placeOrd_of_sum {m : ℕ} (slot : EvenSlot)
    (i j k : Fin (m - 1))
    (hijk : (i.val + 1) + (j.val + 1) = k.val + 1) :
    ∃ p : EvenUDomain m, evenOrdCoreTriple slot p = evenPlaceOrd slot i j k := by
  have hsum : i.val + j.val + 1 = k.val := by omega
  let r : EvenOrdinaryIndex m := ⟨⟨k.val, by
    have hk : k.val < m - 1 := k.isLt
    omega⟩, by
      have hk : k.val < m - 1 := k.isLt
      constructor
      · exact Nat.ne_of_gt (by
          change 0 < k.val
          omega)
      · exact ne_of_lt hk⟩
  let t : Fin r.val.val := ⟨i.val, by
    change i.val < k.val
    omega⟩
  refine ⟨⟨r, t⟩, ?_⟩
  have hjval : k.val - 1 - i.val = j.val := by omega
  cases slot <;>
    dsimp [evenOrdCoreTriple, evenPlaceOrd] <;>
    congr

theorem evenWrapCoreTriple_exists_allPos_of_sum {m : ℕ} (hm : 2 ≤ m)
    (i j k : Fin (m - 1))
    (hijk : (i.val + 1) + (j.val + 1) + (k.val + 1) = 2 * m) :
    ∃ p : EvenVDomain m, evenWrapCoreTriple p =
      (EvenFreq.pos i, EvenFreq.pos j, EvenFreq.pos k) := by
  have hsum : i.val + j.val + k.val + 3 = 2 * m := by omega
  let r : EvenOrdinaryIndex m := ⟨⟨k.val, by
    have hk : k.val < m - 1 := k.isLt
    omega⟩, by
      have hk : k.val < m - 1 := k.isLt
      constructor
      · exact Nat.ne_of_gt (by
          change 0 < k.val
          omega)
      · exact ne_of_lt hk⟩
  let t : Fin r.val.val := ⟨m - j.val - 2, by
    change m - j.val - 2 < k.val
    omega⟩
  refine ⟨⟨r, t⟩, ?_⟩
  dsimp [evenWrapCoreTriple]
  apply Prod.ext
  · apply congrArg EvenFreq.pos
    apply Fin.ext
    change m - k.val - 1 + (m - j.val - 2) = i.val
    omega
  · apply Prod.ext
    · apply congrArg EvenFreq.pos
      apply Fin.ext
      change m - 2 - (m - j.val - 2) = j.val
      omega
    · apply congrArg EvenFreq.pos
      apply Fin.ext
      rfl

theorem evenMiddleCoreTriple_eq_placeMiddle_of_sum {m : ℕ}
    (slot : EvenSlot) (i j : Fin (m - 1))
    (hij : (i.val + 1) + (j.val + 1) = m) :
    evenMiddleCoreTriple slot i = evenPlaceMiddle slot i j := by
  have hj : m - 2 - i.val = j.val := by omega
  cases slot <;>
    dsimp [evenMiddleCoreTriple, evenPlaceMiddle] <;>
    congr

theorem even_middle_natCast_ne_zero {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℕ) : ZMod (2 * m)) ≠ 0 := by
  intro h
  have hnat := even_natCast_eq_of_lt_two_mul (m := m) (a := m) (b := 0)
    (by omega) (by omega) (by simpa using h)
  omega

theorem even_pos_neg_mid_sum_ne_zero {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin (m - 1)) :
    evenTripleSum (EvenFreq.pos i, EvenFreq.neg j, EvenFreq.mid) ≠ 0 := by
  intro h
  have hcast :
      (((m + (i.val + 1) : ℕ) : ZMod (2 * m)) =
        ((j.val + 1 : ℕ) : ZMod (2 * m))) := by
    simp [evenTripleSum, evenFreqZ] at h
    rw [← sub_eq_zero]
    simp only [Nat.cast_add, Nat.cast_one]
    abel_nf at h ⊢
    exact h
  have hnat := even_natCast_eq_of_lt_two_mul (m := m)
    (a := m + (i.val + 1)) (b := j.val + 1)
    (by omega) (by omega) hcast
  omega

theorem even_two_mid_pos_sum_ne_zero {m : ℕ} (hm : 2 ≤ m)
    (i : Fin (m - 1)) :
    evenTripleSum (EvenFreq.mid, EvenFreq.mid, EvenFreq.pos i) ≠ 0 := by
  intro h
  have hpair : ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) = 0 := by
    rw [← Nat.cast_add]
    have hsum : m + m = 2 * m := by omega
    rw [hsum]
    simp
  have hpos : (((i.val + 1 : ℕ) : ZMod (2 * m))) = 0 := by
    change ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) +
        (((i.val + 1 : ℕ) : ZMod (2 * m))) = 0 at h
    rw [← h, hpair, zero_add]
  have hnat := even_natCast_eq_of_lt_two_mul (m := m)
    (a := i.val + 1) (b := 0) (by omega) (by omega) (by simpa using hpos)
  omega

theorem even_two_mid_neg_sum_ne_zero {m : ℕ} (hm : 2 ≤ m)
    (i : Fin (m - 1)) :
    evenTripleSum (EvenFreq.mid, EvenFreq.mid, EvenFreq.neg i) ≠ 0 := by
  intro h
  have hpair : ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) = 0 := by
    rw [← Nat.cast_add]
    have hsum : m + m = 2 * m := by omega
    rw [hsum]
    simp
  have hneg : -(((i.val + 1 : ℕ) : ZMod (2 * m))) = 0 := by
    change ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) +
        -
        (((i.val + 1 : ℕ) : ZMod (2 * m))) = 0 at h
    rw [← h, hpair, zero_add]
  have hpos : (((i.val + 1 : ℕ) : ZMod (2 * m))) = 0 := neg_eq_zero.mp hneg
  have hnat := even_natCast_eq_of_lt_two_mul (m := m)
    (a := i.val + 1) (b := 0) (by omega) (by omega) (by simpa using hpos)
  omega

theorem even_three_mid_sum_ne_zero {m : ℕ} (hm : 2 ≤ m) :
    evenTripleSum (EvenFreq.mid, EvenFreq.mid, (EvenFreq.mid : EvenFreq m)) ≠ 0 := by
  intro h
  have hpair : ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) = 0 := by
    rw [← Nat.cast_add]
    have hsum : m + m = 2 * m := by omega
    rw [hsum]
    simp
  have hmid : (((m : ℕ) : ZMod (2 * m))) = 0 := by
    change ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) +
        ((m : ℕ) : ZMod (2 * m)) = 0 at h
    rw [← h, hpair, zero_add]
  exact even_middle_natCast_ne_zero hm hmid

theorem evenResonanceTriple_exists_of_sum_zero {m : ℕ} (hm : 2 ≤ m)
    (t : EvenTriple m) (ht : evenTripleSum t = 0) :
    ∃ d : EvenResonanceDomain m, evenResonanceTriple d = t := by
  rcases t with ⟨x, y, z⟩
  cases x with
  | pos a =>
      cases y with
      | pos b =>
          cases z with
          | pos c =>
              have hsum := evenAllPos_nat_sum_eq_two_mul_of_sum_zero hm a b c ht
              rcases evenWrapCoreTriple_exists_allPos_of_sum hm a b c hsum with ⟨p, hp⟩
              refine ⟨Sum.inl (Sum.inr (EvenOrientation.base, p)), ?_⟩
              simpa [evenResonanceTriple, evenWrapTriple, evenOrientTriple] using hp
          | neg c =>
              have hplace : evenTripleSum (evenPlaceOrd EvenSlot.thd a b c) = 0 := by
                simpa [evenPlaceOrd] using ht
              have hsum := evenPlaceOrd_nat_sum_eq_of_sum_zero hm EvenSlot.thd a b c hplace
              rcases evenOrdCoreTriple_exists_placeOrd_of_sum EvenSlot.thd a b c hsum with
                ⟨p, hp⟩
              refine ⟨Sum.inl (Sum.inl (EvenOrientation.base, EvenSlot.thd, p)), ?_⟩
              simpa [evenResonanceTriple, evenOrdTriple, evenOrientTriple, evenPlaceOrd] using hp
          | mid =>
              have hplace : evenTripleSum (evenPlaceMiddle EvenSlot.thd a b) = 0 := by
                simpa [evenPlaceMiddle] using ht
              have hsum := evenMiddle_nat_sum_eq_of_sum_zero hm EvenSlot.thd a b hplace
              have hp := evenMiddleCoreTriple_eq_placeMiddle_of_sum EvenSlot.thd a b hsum
              refine ⟨Sum.inr (EvenOrientation.base, EvenSlot.thd, a), ?_⟩
              simpa [evenResonanceTriple, evenMiddleTriple, evenOrientTriple, evenPlaceMiddle]
                using hp
      | neg b =>
          cases z with
          | pos c =>
              have hplace : evenTripleSum (evenPlaceOrd EvenSlot.snd a c b) = 0 := by
                simpa [evenPlaceOrd] using ht
              have hsum := evenPlaceOrd_nat_sum_eq_of_sum_zero hm EvenSlot.snd a c b hplace
              rcases evenOrdCoreTriple_exists_placeOrd_of_sum EvenSlot.snd a c b hsum with
                ⟨p, hp⟩
              refine ⟨Sum.inl (Sum.inl (EvenOrientation.base, EvenSlot.snd, p)), ?_⟩
              simpa [evenResonanceTriple, evenOrdTriple, evenOrientTriple, evenPlaceOrd] using hp
          | neg c =>
              have hflip : evenTripleSum (evenPlaceOrd EvenSlot.fst b c a) = 0 := by
                simpa [evenPlaceOrd, evenFlipTriple, evenFlipFreq] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.pos a, EvenFreq.neg b, EvenFreq.neg c)) ht)
              have hsum := evenPlaceOrd_nat_sum_eq_of_sum_zero hm EvenSlot.fst b c a hflip
              rcases evenOrdCoreTriple_exists_placeOrd_of_sum EvenSlot.fst b c a hsum with
                ⟨p, hp⟩
              refine ⟨Sum.inl (Sum.inl (EvenOrientation.conj, EvenSlot.fst, p)), ?_⟩
              dsimp [evenResonanceTriple, evenOrdTriple, evenOrientTriple]
              rw [hp]
              rfl
          | mid =>
              exfalso
              exact even_pos_neg_mid_sum_ne_zero hm a b ht
      | mid =>
          cases z with
          | pos c =>
              have hplace : evenTripleSum (evenPlaceMiddle EvenSlot.snd a c) = 0 := by
                simpa [evenPlaceMiddle] using ht
              have hsum := evenMiddle_nat_sum_eq_of_sum_zero hm EvenSlot.snd a c hplace
              have hp := evenMiddleCoreTriple_eq_placeMiddle_of_sum EvenSlot.snd a c hsum
              refine ⟨Sum.inr (EvenOrientation.base, EvenSlot.snd, a), ?_⟩
              simpa [evenResonanceTriple, evenMiddleTriple, evenOrientTriple, evenPlaceMiddle]
                using hp
          | neg c =>
              exfalso
              exact even_pos_neg_mid_sum_ne_zero hm a c (by
                simpa [evenTripleSum, evenFreqZ, add_comm, add_left_comm, add_assoc] using ht)
          | mid =>
              exfalso
              exact even_two_mid_pos_sum_ne_zero hm a (by
                simpa [evenTripleSum, evenFreqZ, add_comm, add_left_comm, add_assoc] using ht)
  | neg a =>
      cases y with
      | pos b =>
          cases z with
          | pos c =>
              have hplace : evenTripleSum (evenPlaceOrd EvenSlot.fst b c a) = 0 := by
                simpa [evenPlaceOrd] using ht
              have hsum := evenPlaceOrd_nat_sum_eq_of_sum_zero hm EvenSlot.fst b c a hplace
              rcases evenOrdCoreTriple_exists_placeOrd_of_sum EvenSlot.fst b c a hsum with
                ⟨p, hp⟩
              refine ⟨Sum.inl (Sum.inl (EvenOrientation.base, EvenSlot.fst, p)), ?_⟩
              simpa [evenResonanceTriple, evenOrdTriple, evenOrientTriple, evenPlaceOrd] using hp
          | neg c =>
              have hflip : evenTripleSum (evenPlaceOrd EvenSlot.snd a c b) = 0 := by
                simpa [evenPlaceOrd, evenFlipTriple, evenFlipFreq] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.neg a, EvenFreq.pos b, EvenFreq.neg c)) ht)
              have hsum := evenPlaceOrd_nat_sum_eq_of_sum_zero hm EvenSlot.snd a c b hflip
              rcases evenOrdCoreTriple_exists_placeOrd_of_sum EvenSlot.snd a c b hsum with
                ⟨p, hp⟩
              refine ⟨Sum.inl (Sum.inl (EvenOrientation.conj, EvenSlot.snd, p)), ?_⟩
              dsimp [evenResonanceTriple, evenOrdTriple, evenOrientTriple]
              rw [hp]
              rfl
          | mid =>
              exfalso
              exact even_pos_neg_mid_sum_ne_zero hm a b (by
                simpa [evenFlipTriple, evenFlipFreq] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.neg a, EvenFreq.pos b, EvenFreq.mid)) ht))
      | neg b =>
          cases z with
          | pos c =>
              have hflip : evenTripleSum (evenPlaceOrd EvenSlot.thd a b c) = 0 := by
                simpa [evenPlaceOrd, evenFlipTriple, evenFlipFreq] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.neg a, EvenFreq.neg b, EvenFreq.pos c)) ht)
              have hsum := evenPlaceOrd_nat_sum_eq_of_sum_zero hm EvenSlot.thd a b c hflip
              rcases evenOrdCoreTriple_exists_placeOrd_of_sum EvenSlot.thd a b c hsum with
                ⟨p, hp⟩
              refine ⟨Sum.inl (Sum.inl (EvenOrientation.conj, EvenSlot.thd, p)), ?_⟩
              dsimp [evenResonanceTriple, evenOrdTriple, evenOrientTriple]
              rw [hp]
              rfl
          | neg c =>
              have hflip : evenTripleSum (EvenFreq.pos a, EvenFreq.pos b, EvenFreq.pos c) = 0 := by
                simpa [evenFlipTriple, evenFlipFreq] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.neg a, EvenFreq.neg b, EvenFreq.neg c)) ht)
              have hsum := evenAllPos_nat_sum_eq_two_mul_of_sum_zero hm a b c hflip
              rcases evenWrapCoreTriple_exists_allPos_of_sum hm a b c hsum with ⟨p, hp⟩
              refine ⟨Sum.inl (Sum.inr (EvenOrientation.conj, p)), ?_⟩
              dsimp [evenResonanceTriple, evenWrapTriple, evenOrientTriple]
              rw [hp]
              rfl
          | mid =>
              have hflip : evenTripleSum (evenPlaceMiddle EvenSlot.thd a b) = 0 := by
                simpa [evenPlaceMiddle, evenFlipTriple, evenFlipFreq] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.neg a, EvenFreq.neg b, EvenFreq.mid)) ht)
              have hsum := evenMiddle_nat_sum_eq_of_sum_zero hm EvenSlot.thd a b hflip
              have hp := evenMiddleCoreTriple_eq_placeMiddle_of_sum EvenSlot.thd a b hsum
              refine ⟨Sum.inr (EvenOrientation.conj, EvenSlot.thd, a), ?_⟩
              dsimp [evenResonanceTriple, evenMiddleTriple, evenOrientTriple]
              rw [hp]
              rfl
      | mid =>
          cases z with
          | pos c =>
              exfalso
              exact even_pos_neg_mid_sum_ne_zero hm a c (by
                simpa [evenFlipTriple, evenFlipFreq, evenTripleSum, evenFreqZ,
                  add_comm, add_left_comm, add_assoc] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.neg a, EvenFreq.mid, EvenFreq.pos c)) ht))
          | neg c =>
              have hflip : evenTripleSum (evenPlaceMiddle EvenSlot.snd a c) = 0 := by
                simpa [evenPlaceMiddle, evenFlipTriple, evenFlipFreq] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.neg a, EvenFreq.mid, EvenFreq.neg c)) ht)
              have hsum := evenMiddle_nat_sum_eq_of_sum_zero hm EvenSlot.snd a c hflip
              have hp := evenMiddleCoreTriple_eq_placeMiddle_of_sum EvenSlot.snd a c hsum
              refine ⟨Sum.inr (EvenOrientation.conj, EvenSlot.snd, a), ?_⟩
              dsimp [evenResonanceTriple, evenMiddleTriple, evenOrientTriple]
              rw [hp]
              rfl
          | mid =>
              exfalso
              exact even_two_mid_neg_sum_ne_zero hm a (by
                simpa [evenTripleSum, evenFreqZ, add_comm, add_left_comm, add_assoc] using ht)
  | mid =>
      cases y with
      | pos b =>
          cases z with
          | pos c =>
              have hplace : evenTripleSum (evenPlaceMiddle EvenSlot.fst b c) = 0 := by
                simpa [evenPlaceMiddle] using ht
              have hsum := evenMiddle_nat_sum_eq_of_sum_zero hm EvenSlot.fst b c hplace
              have hp := evenMiddleCoreTriple_eq_placeMiddle_of_sum EvenSlot.fst b c hsum
              refine ⟨Sum.inr (EvenOrientation.base, EvenSlot.fst, b), ?_⟩
              simpa [evenResonanceTriple, evenMiddleTriple, evenOrientTriple, evenPlaceMiddle]
                using hp
          | neg c =>
              exfalso
              exact even_pos_neg_mid_sum_ne_zero hm b c (by
                simpa [evenTripleSum, evenFreqZ, add_comm, add_left_comm, add_assoc] using ht)
          | mid =>
              exfalso
              exact even_two_mid_pos_sum_ne_zero hm b (by
                simpa [evenTripleSum, evenFreqZ, add_comm, add_left_comm, add_assoc] using ht)
      | neg b =>
          cases z with
          | pos c =>
              exfalso
              exact even_pos_neg_mid_sum_ne_zero hm b c (by
                simpa [evenFlipTriple, evenFlipFreq, evenTripleSum, evenFreqZ,
                  add_comm, add_left_comm, add_assoc] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.mid, EvenFreq.neg b, EvenFreq.pos c)) ht))
          | neg c =>
              have hflip : evenTripleSum (evenPlaceMiddle EvenSlot.fst b c) = 0 := by
                simpa [evenPlaceMiddle, evenFlipTriple, evenFlipFreq] using
                  (evenTripleSum_flip_eq_zero
                    (t := (EvenFreq.mid, EvenFreq.neg b, EvenFreq.neg c)) ht)
              have hsum := evenMiddle_nat_sum_eq_of_sum_zero hm EvenSlot.fst b c hflip
              have hp := evenMiddleCoreTriple_eq_placeMiddle_of_sum EvenSlot.fst b c hsum
              refine ⟨Sum.inr (EvenOrientation.conj, EvenSlot.fst, b), ?_⟩
              dsimp [evenResonanceTriple, evenMiddleTriple, evenOrientTriple]
              rw [hp]
              rfl
          | mid =>
              exfalso
              exact even_two_mid_neg_sum_ne_zero hm b (by
                simpa [evenTripleSum, evenFreqZ, add_comm, add_left_comm, add_assoc] using ht)
      | mid =>
          cases z with
          | pos c =>
              exfalso
              exact even_two_mid_pos_sum_ne_zero hm c ht
          | neg c =>
              exfalso
              exact even_two_mid_neg_sum_ne_zero hm c ht
          | mid =>
              exfalso
              exact even_three_mid_sum_ne_zero hm ht

end

end CyclicLsi
