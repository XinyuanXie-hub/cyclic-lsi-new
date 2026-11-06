module
public import CyclicLsi.Definitions

open scoped BigOperators
open ZMod
open Finset

@[expose] public noncomputable section
namespace CyclicLsi

/- Support/Basic -/
/-!
# Shared finite-probability notation

This support file contains elementary lemmas and proof-only abbreviations built
on the public notation from `CyclicLsi.Definitions`.
-/

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

/- Direct pinned-DFT contraction -/
lemma dft_fourierCoeff {n : ℕ} [NeZero n] (u : ZMod n → ℂ) :
    ZMod.dft (fourierCoeff u) = fun x ↦ u (-x) := by
  unfold fourierCoeff
  simp [ZMod.dft_const_mul, ZMod.dft_dft, smul_eq_mul, NeZero.ne (n : ℂ)]

lemma coefficient_adjoint {n : ℕ} [NeZero n] (u v : ZMod n → ℂ) :
    (∑ k : ZMod n, fourierCoeff u (-k) * v k) =
      (n : ℂ)⁻¹ * ∑ x : ZMod n, u x * ZMod.dft v (-x) := by
  simp only [fourierCoeff, ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

lemma fourierCoeff_real_neg {n : ℕ} [NeZero n] (u : ZMod n → ℝ) (k : ZMod n) :
    fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) (-k) =
      star (fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k) := by
  simp [fourierCoeff, ZMod.dft_apply, smul_eq_mul, star_mul, star_sum,
    AddChar.map_neg_eq_conj, mul_neg, mul_comm]

lemma parseval_real_sq {n : ℕ} [NeZero n] (u : ZMod n → ℝ) :
    (∑ x : ZMod n, u x ^ 2) / (n : ℝ) =
      ∑ k : ZMod n, Complex.normSq (fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) k) := by
  apply Complex.ofReal_injective
  simpa [dft_fourierCoeff, fourierCoeff_real_neg, Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_sum, pow_two, div_eq_mul_inv, mul_comm] using
    (coefficient_adjoint (fun x : ZMod n ↦ (u x : ℂ))
      (fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)))).symm

lemma fourierCoeff_zero_of_meanZero {n : ℕ} [NeZero n]
    {u : ZMod n → ℝ} (hu : avg u = 0) :
    fourierCoeff (fun x : ZMod n ↦ (u x : ℂ)) 0 = 0 := by
  simpa [avg, ZMod.card, fourierCoeff, ZMod.dft_apply_zero, div_eq_mul_inv, mul_comm] using
    congrArg Complex.ofReal hu

namespace Native
attribute [local instance] Classical.propDecidable

/- Derivative-free polynomial scalar certificate -/
private def directGap (t : ℝ) : ℝ :=
  2 * t ^ 3 + 3 * t ^ 2 - 6 * t + 1 - 6 * t ^ 2 * Real.log t

private def directDistance (t : ℝ) : ℝ := t * (t - 1) ^ 2

private theorem directGap_lower {t : ℝ} (ht : 0 < t) :
    -4 * directDistance t ≤ directGap t := by
  have hlog := Real.log_le_sub_one_of_pos ht
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 6 * t ^ 2)
  have hs := sq_nonneg (t - 1)
  unfold directGap directDistance
  nlinarith only [hm, hs]

private theorem directGap_square {t : ℝ} (ht : 0 < t) :
    2 * t ^ 2 * directGap t ≤ directGap (t ^ 2) := by
  have heq : directGap (t ^ 2) - 2 * t ^ 2 * directGap t =
      (t - 1) ^ 4 * (2 * t ^ 2 + 4 * t + 1) := by
    unfold directGap
    rw [Real.log_pow]
    ring
  have hrem : 0 ≤ (t - 1) ^ 4 * (2 * t ^ 2 + 4 * t + 1) := by positivity
  linarith only [heq, hrem]

private theorem directDistance_square (t : ℝ) :
    4 * t ^ 2 * directDistance t ≤ directDistance (t ^ 2) := by
  have heq : directDistance (t ^ 2) - 4 * t ^ 2 * directDistance t =
      t ^ 2 * (t - 1) ^ 4 := by
    unfold directDistance
    ring
  have hrem : 0 ≤ t ^ 2 * (t - 1) ^ 4 := by positivity
  linarith only [heq, hrem]

private theorem directGap_lower_iterate (n : ℕ) :
    ∀ t : ℝ, 0 < t → -4 * directDistance t ≤ 2 ^ n * directGap t := by
  induction n with
  | zero =>
    intro t ht
    simpa using directGap_lower ht
  | succ n ih =>
    intro t ht
    have hx : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
    have hi := ih (Real.sqrt t) hx
    have hg := directGap_square hx
    have hq := directDistance_square (Real.sqrt t)
    rw [hsq] at hg hq
    have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 4 * t)
    have hp : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) _
    have hh := mul_le_mul_of_nonneg_left hg hp
    rw [pow_succ]
    nlinarith only [hmul, hq, hh]

private theorem directGap_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ directGap t := by
  by_contra hn
  have hg : directGap t < 0 := lt_of_not_ge hn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (4 * directDistance t / -directGap t) (by norm_num : (1 : ℝ) < 2)
  have hp : 0 < -directGap t := neg_pos.mpr hg
  have hc := (div_lt_iff₀ hp).mp hn
  have hi := directGap_lower_iterate n t ht
  nlinarith only [hc, hi]

/- Scale the derivative-free polynomial gap directly. -/
private theorem scaled_pointwise_majorant
    (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (ht : 0 < t) :
    3 * t ^ 2 * (s ^ 2 * Real.log (s ^ 2) - Real.log (t ^ 2) * s ^ 2) ≤
      2 * t * s ^ 3 - 6 * t ^ 3 * s + 4 * t ^ 4 +
        3 * t ^ 2 * (s ^ 2 - t ^ 2) := by
  rcases hs.eq_or_lt with rfl | hs
  · norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_zero, zero_mul, sub_zero, zero_sub]
    nlinarith only [sq_nonneg (t ^ 2)]
  · have h := mul_nonneg (pow_nonneg ht.le 4) (directGap_nonneg (div_pos hs ht))
    have heq : t ^ 4 * directGap (s / t) =
        2 * t * s ^ 3 - 6 * t ^ 3 * s + 4 * t ^ 4 + 3 * t ^ 2 * (s ^ 2 - t ^ 2) -
          3 * t ^ 2 * (s ^ 2 * Real.log (s ^ 2) - Real.log (t ^ 2) * s ^ 2) := by
      unfold directGap
      rw [Real.log_div hs.ne' ht.ne', Real.log_pow, Real.log_pow]
      field_simp [ht.ne']
      ring
    rw [heq] at h
    exact sub_nonneg.mp h

/-- The cubic majorant is integrated at its physical scale; no normalized
signal, energy scaling or physical centering is needed. -/
theorem scaled_entropy_majorant {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t)
    (hV : avg (fun x ↦ f x ^ 2) = t ^ 2) :
    3 * t ^ 2 * ent (fun x ↦ f x ^ 2) ≤
      2 * t * avg (fun x ↦ f x ^ 3) - 6 * t ^ 3 * avg f + 4 * t ^ 4 := by
  have h := avg_mono fun x ↦ scaled_pointwise_majorant (f x) (hf x) t ht
  unfold ent
  rw [hV]
  simpa only [avg_const_mul, avg_sub, avg_add, avg_const, hV,
    sub_self, mul_zero, add_zero, mul_comm (Real.log (t ^ 2)) (t ^ 2)] using h


/- Fixed-rectangle spectral certificate -/
def cyclicLength {n : ℕ} (k : ZMod n) : ℕ := k.valMinAbs.natAbs

def cyclicSurplus {n : ℕ} (k : ZMod n) : ℝ := (cyclicLength k - 1 : ℕ)

lemma cyclicLength_pos_of_ne_zero {n : ℕ} {k : ZMod n} (hk : k ≠ 0) :
    0 < cyclicLength k := by
  exact Int.natAbs_pos.mpr ((ZMod.valMinAbs_eq_zero k).not.mpr hk)

lemma cyclicSurplus_eq_of_ne_zero {n : ℕ} {k : ZMod n} (hk : k ≠ 0) :
    cyclicSurplus k = (cyclicLength k : ℝ) - 1 := by
  simp only [cyclicSurplus, Nat.cast_sub (cyclicLength_pos_of_ne_zero hk), Nat.cast_one]

lemma resonance_val_cases {n : ℕ} [NeZero n] {k i j : ZMod n}
    (hk : k ≠ 0) (hi : i ≠ 0) (hj : j ≠ 0) (hr : k + i + j = 0) :
    k.val + i.val + j.val = n ∨ k.val + i.val + j.val = 2 * n := by
  have hsum : k + i = -j := eq_neg_iff_add_eq_zero.mpr hr
  have hval := congrArg ZMod.val hsum
  simp only [ZMod.neg_val, ite_eq_right hj] at hval
  have hjlt := ZMod.val_lt j
  by_cases h : k.val + i.val < n
  · left
    rw [ZMod.val_add_of_lt h] at hval
    omega
  · right
    rw [ZMod.val_add_of_le (Nat.le_of_not_gt h)] at hval
    omega

/- Native/CommonDefinitions -/
def spectrumS {n : ℕ} [NeZero n] (c : ZMod n → ℂ) : ℝ :=
  ∑ k, Complex.normSq (c k)

def spectrumQ {n : ℕ} [NeZero n] (c : ZMod n → ℂ) : ℝ :=
  ∑ k, cyclicSurplus k * Complex.normSq (c k)

/- Native/PairDefinitions -/
def pairCubic {n : ℕ} [NeZero n] (c : ZMod n → ℂ) : ℝ :=
  ∑ i, ∑ j, (c (-(i+j)) * c i * c j).re

namespace Rectangle

def segment {n : ℕ} [NeZero n] (m : ℕ) : Finset (ZMod n) :=
  univ.filter fun k => 0 < k.val ∧ k.val ≤ m

@[simp] lemma mem_segment {n : ℕ} [NeZero n] (m : ℕ) (k : ZMod n) :
    k ∈ segment m ↔ 0 < k.val ∧ k.val ≤ m := by
  simp [segment]

def mass {n : ℕ} [NeZero n] (a : ZMod n → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ segment m, a k ^ 2

def cubic {n : ℕ} [NeZero n] (a : ZMod n → ℝ) (p h : ℕ) : ℝ :=
  ∑ i ∈ segment p, ∑ j ∈ segment h, a i * a j * a (i + j)

def square {n : ℕ} [NeZero n] (a : ZMod n → ℝ) (p h : ℕ) : ℝ :=
  ∑ i ∈ segment p, ∑ j ∈ segment h, a (i + j) ^ 2

def total {n : ℕ} [NeZero n] (a : ZMod n → ℝ) : ℝ :=
  ∑ i, ∑ j, a (-(i + j)) * a i * a j

lemma nat_rectangle_cover {p h x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hph : p ≤ h) (hhp : h ≤ 2 * p)
    (hsum : x + y + z = p + h + 2) :
    (x ≤ p ∧ y ≤ h) ∨ (y ≤ p ∧ z ≤ h) ∨ (z ≤ p ∧ x ≤ h) := by
  omega

lemma rectangle_cover {n : ℕ} [NeZero n] (p h : ℕ)
    (hph : p ≤ h) (hhp : h ≤ 2 * p) (hsum : p + h + 2 = n)
    {k i j : ZMod n} (hk : k ≠ 0) (hi : i ≠ 0) (hj : j ≠ 0)
    (hr : k + i + j = 0) :
    ((k ∈ segment p ∧ i ∈ segment h) ∨ (i ∈ segment p ∧ j ∈ segment h) ∨
      (j ∈ segment p ∧ k ∈ segment h)) ∨
    ((-k ∈ segment p ∧ -i ∈ segment h) ∨ (-i ∈ segment p ∧ -j ∈ segment h) ∨
      (-j ∈ segment p ∧ -k ∈ segment h)) := by
  have cover (u v w : ZMod n) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
      (hs : u.val + v.val + w.val = n) :
      (u ∈ segment p ∧ v ∈ segment h) ∨ (v ∈ segment p ∧ w ∈ segment h) ∨
        (w ∈ segment p ∧ u ∈ segment h) := by
    simpa [mem_segment, ZMod.val_pos.mpr hu, ZMod.val_pos.mpr hv,
      ZMod.val_pos.mpr hw] using
      nat_rectangle_cover (ZMod.val_pos.mpr hu) (ZMod.val_pos.mpr hv)
        (ZMod.val_pos.mpr hw) hph hhp (hs.trans hsum.symm)
  rcases resonance_val_cases hk hi hj hr with hs | hs
  · exact Or.inl (cover k i j hk hi hj hs)
  · right
    apply cover (-k) (-i) (-j) (neg_ne_zero.mpr hk) (neg_ne_zero.mpr hi)
      (neg_ne_zero.mpr hj)
    simp only [ZMod.neg_val, ite_eq_right hk, ite_eq_right hi, ite_eq_right hj]
    have := ZMod.val_lt k
    have := ZMod.val_lt i
    have := ZMod.val_lt j
    omega

namespace Fusion

/-- Six resonant pair images of one rectangular pair. -/
def sixPair {n : ℕ} (r : Fin 6) (i j : ZMod n) : ZMod n × ZMod n :=
  ![(i, j), (j, -(i + j)), (-(i + j), i),
    (-i, -j), (-j, i + j), (i + j, -i)] r

lemma sixPair_product {n : ℕ} [NeZero n] (a : ZMod n → ℝ)
    (heven : ∀ k, a (-k) = a k) (r : Fin 6) (i j : ZMod n) :
    a (-((sixPair r i j).1 + (sixPair r i j).2)) *
      a (sixPair r i j).1 * a (sixPair r i j).2 = a i * a j * a (i + j) := by
  fin_cases r
  all_goals simp only [sixPair, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk]
  all_goals ring_nf
  all_goals
    simp only [sub_eq_add_neg, ← neg_add, heven, mul_comm, mul_left_comm]

lemma sixPair_covers {n : ℕ} [NeZero n] (p h : ℕ)
    (hph : p ≤ h) (hhp : h ≤ 2 * p) (hsum : p + h + 2 = n)
    (i j : ZMod n) (hk : -(i + j) ≠ 0) (hi : i ≠ 0) (hj : j ≠ 0) :
    ∃ r : Fin 6, ∃ u v : ZMod n,
      (u ∈ segment p ∧ v ∈ segment h) ∧ sixPair r u v = (i, j) := by
  rcases rectangle_cover p h hph hhp hsum hk hi hj (by abel) with
    (hc | hc | hc) | (hc | hc | hc)
  · refine ⟨1, -(i + j), i, hc, ?_⟩
    ext
    all_goals simp [sixPair]
  · exact ⟨0, i, j, hc, by simp [sixPair]⟩
  · refine ⟨2, j, -(i + j), hc, ?_⟩
    ext
    all_goals simp [sixPair]
  · refine ⟨4, -(-(i + j)), -i, hc, ?_⟩
    ext
    all_goals simp [sixPair]
  · exact ⟨3, -i, -j, hc, by simp [sixPair]⟩
  · refine ⟨5, -j, -(-(i + j)), hc, ?_⟩
    ext
    all_goals simp [sixPair]

/-- The six-image cover uses the library image-sum inequality directly. -/
theorem cover_bound_image {n : ℕ} [NeZero n] (p h : ℕ)
    (hph : p ≤ h) (hhp : h ≤ 2 * p) (hsum : p + h + 2 = n)
    (a : ZMod n → ℝ) (ha : ∀ k, 0 ≤ a k) (hzero : a 0 = 0)
    (heven : ∀ k, a (-k) = a k) : total a ≤ 6 * cubic a p h := by
  let R : Finset (Fin 6 × (ZMod n × ZMod n)) :=
    univ.product ((segment p).product (segment h))
  let φ (t : Fin 6 × (ZMod n × ZMod n)) := sixPair t.1 t.2.1 t.2.2
  let T (q : ZMod n × ZMod n) := a (-(q.1 + q.2)) * a q.1 * a q.2
  have hsupp (q : ZMod n × ZMod n) (hq : q ∉ R.image φ) : T q = 0 := by
    obtain ⟨i, j⟩ := q
    by_cases hk : -(i + j) = 0
    · simp only [T, hk, hzero, zero_mul]
    by_cases hi : i = 0
    · simp [T, hi, hzero]
    by_cases hj : j = 0
    · simp [T, hj, hzero]
    obtain ⟨r, u, v, huv, heq⟩ := sixPair_covers p h hph hhp hsum i j hk hi hj
    exact (hq (mem_image.mpr ⟨(r, u, v), by simp [R, huv.1, huv.2], heq⟩)).elim
  calc
    total a = ∑ q ∈ R.image φ, T q := by
      unfold total
      change (∑ i, ∑ j, T (i, j)) = _
      rw [← Fintype.sum_prod_type]
      exact (sum_subset (subset_univ _) (fun q _ hq => hsupp q hq)).symm
    _ ≤ ∑ t ∈ R, T (φ t) :=
      sum_image_le_of_nonneg (fun q _ => mul_nonneg (mul_nonneg (ha _) (ha _)) (ha _))
    _ = 6 * cubic a p h := by
      simp only [R]
      simp only [φ, T, sixPair_product a heven]
      simp [cubic, sum_product]


end Fusion

theorem fiber_bound {n : ℕ} [NeZero n] (p h : ℕ) (hsum : p + h + 2 = n)
    (k : ZMod n) :
    (((segment p).filter fun i => k - i ∈ segment h).card : ℝ) ≤ cyclicSurplus k := by
  let E := {i : ZMod n // i ∈ segment p ∧ k - i ∈ segment h}
  have bounds (i : E) :
      (0 < i.val.val ∧ i.val.val ≤ p) ∧
        (0 < (k - i.val).val ∧ (k - i.val).val ≤ h) := by
    simpa only [mem_segment] using i.property
  have val_sum (i : E) : k.val = i.val.val + (k - i.val).val := by
    have hi := (bounds i).1.2
    have hj := (bounds i).2.2
    simpa only [add_sub_cancel] using
      (ZMod.val_add_of_lt (show i.val.val + (k - i.val).val < n by omega))
  let f : E → Fin (k.val - 1) := fun i => ⟨i.val.val - 1, by
    have hi := (bounds i).1.1
    have hj := (bounds i).2.1
    have hv := val_sum i
    omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply ZMod.val_injective n
    have hi := (bounds i).1.1
    have hj := (bounds j).1.1
    have heq := congrArg Fin.val hij
    dsimp only [f] at heq
    omega
  let g : E → Fin (n - k.val - 1) := fun i => ⟨p - i.val.val, by
    have hi := (bounds i).1.2
    have hj := (bounds i).2.2
    have hv := val_sum i
    omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply ZMod.val_injective n
    have hi := (bounds i).1.2
    have hj := (bounds j).1.2
    have heq := congrArg Fin.val hij
    dsimp only [g] at heq
    omega
  have hcard : Fintype.card E ≤ cyclicLength k - 1 := by
    have hfcard := Fintype.card_le_of_injective f hf
    have hgcard := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin] at hfcard hgcard
    simp only [cyclicLength, ZMod.valMinAbs_natAbs_eq_min]
    omega
  have hnat : ((segment p).filter fun i => k - i ∈ segment h).card ≤
      cyclicLength k - 1 := by
    simpa [E, Fintype.card_subtype, segment, Finset.filter_filter] using hcard
  simpa only [cyclicSurplus, Nat.cast_le] using hnat

lemma mass_bound {n : ℕ} [NeZero n] (p h : ℕ) (hsum : p+h+2=n)
    (a : ZMod n → ℝ) (heven : ∀ k, a (-k)=a k) :
    mass a p + mass a h ≤ ∑ k, a k^2 := by
  have hd : Disjoint (segment p : Finset (ZMod n)) ((segment h).image fun k => -k) := by
    rw [Finset.disjoint_left]
    intro k hk hkn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hkn
    obtain ⟨hjpos, hjh⟩ := (mem_segment h j).mp hj
    obtain ⟨hkpos, hkp⟩ := (mem_segment p (-j)).mp hk
    have hj0 : j ≠ 0 := by
      intro hj0
      simp [hj0] at hjpos
    rw [ZMod.neg_val, ite_eq_right hj0] at hkp
    have hjlt := ZMod.val_lt j
    omega
  have hm : (∑ k ∈ (segment h).image (fun k : ZMod n => -k), a k^2) = mass a h := by
    rw [Finset.sum_image]
    · simp [mass, heven]
    · intro x hx y hy hxy
      exact neg_injective hxy
  rw [← hm, mass, ← Finset.sum_union hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
    intro k _ _
    positivity)

lemma square_fibers {n : ℕ} [NeZero n] (a : ZMod n → ℝ) (p h : ℕ) :
    square a p h = ∑ k, (((segment p).filter fun i => k-i ∈ segment h).card : ℝ) * a k ^ 2 := by
  unfold square
  calc
    _ = ∑ i ∈ segment p, ∑ k : ZMod n, if k-i ∈ segment h then a k ^ 2 else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_ite_mem_eq (segment h) (fun j => a (i+j)^2)]
      exact Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun j => by simp)
    _ = ∑ k : ZMod n, ∑ i ∈ segment p, if k-i ∈ segment h then a k ^ 2 else 0 := sum_comm
    _ = _ := by simp only [← sum_filter, sum_const, nsmul_eq_mul]

lemma square_bound {n : ℕ} [NeZero n] (a : ZMod n → ℝ) (p h : ℕ)
    (hcount : ∀ k : ZMod n,
      (((segment p).filter fun i => k-i ∈ segment h).card : ℝ) ≤ cyclicSurplus k) :
    square a p h ≤ ∑ k, cyclicSurplus k * a k ^ 2 := by
  rw [square_fibers]
  exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hcount k) (sq_nonneg _)

lemma rectangle_square {n : ℕ} [NeZero n] (a : ZMod n → ℝ) (p h : ℕ) (τ : ℝ) :
    2 * τ * cubic a p h ≤ τ ^ 2 * square a p h + mass a p * mass a h := by
  have hp (i j : ZMod n) :
      2 * τ * (a i * a j * a (i+j)) ≤ τ ^ 2 * a (i+j) ^ 2 + a i ^ 2 * a j ^ 2 := by
    nlinarith only [sq_nonneg (τ * a (i+j) - a i * a j)]
  unfold cubic square mass
  rw [sum_mul_sum]
  simpa only [mul_sum, sum_add_distrib] using
    (sum_le_sum fun i (_ : i ∈ segment p) =>
      sum_le_sum fun j (_ : j ∈ segment h) => hp i j)

lemma scaled_bound {n : ℕ} [NeZero n] (p h : ℕ) (hsum : p+h+2=n)
    (a : ZMod n → ℝ) (heven : ∀ k, a (-k)=a k)
    (hcover : total a ≤ 6 * cubic a p h)
    (hcount : ∀ k : ZMod n,
      (((segment p).filter fun i => k-i ∈ segment h).card : ℝ) ≤ cyclicSurplus k)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    τ * total a ≤ 3 * τ ^ 2 * (∑ k, cyclicSurplus k * a k ^ 2) +
      (3/4 : ℝ) * (∑ k, a k ^ 2) ^ 2 := by
  have hm0 : 0 ≤ mass a p + mass a h := by
    unfold mass
    positivity
  have hm := mul_self_le_mul_self hm0 (mass_bound p h hsum a heven)
  have hab : 4 * mass a p * mass a h ≤ (∑ k, a k ^ 2) ^ 2 := by
    nlinarith only [hm, sq_nonneg (mass a p - mass a h)]
  have hc := mul_le_mul_of_nonneg_left hcover hτ
  have hq := mul_le_mul_of_nonneg_left (square_bound a p h hcount) (sq_nonneg τ)
  nlinarith only [hc, hq, rectangle_square a p h τ, hab]

lemma rectangle_parameters {n : ℕ} (hn : 4 ≤ n) :
    1 ≤ n / 3 ∧ n / 3 ≤ n - n / 3 - 2 ∧
      n - n / 3 - 2 ≤ 2 * (n / 3) ∧ n / 3 + (n - n / 3 - 2) + 2 = n := by
  omega

lemma complex_bound {n : ℕ} [NeZero n] (c : ZMod n → ℂ) (t : ℝ)
    (hbound : ∀ τ : ℝ, 0 ≤ τ →
      τ * total (fun k => ‖c k‖) ≤
        3 * τ ^ 2 * (∑ k, cyclicSurplus k * ‖c k‖ ^ 2) +
          (3 / 4 : ℝ) * (∑ k, ‖c k‖ ^ 2) ^ 2) :
    t * pairCubic c ≤ 3 * t ^ 2 * spectrumQ c +
      (3 / 4 : ℝ) * spectrumS c ^ 2 := by
  have habs : |pairCubic c| ≤ total (fun k => ‖c k‖) := by
    unfold pairCubic total
    calc
      _ ≤ ∑ i, |∑ j, (c (-(i + j)) * c i * c j).re| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(c (-(i + j)) * c i * c j).re| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, ‖c (-(i + j))‖ * ‖c i‖ * ‖c j‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [norm_mul] using Complex.abs_re_le_norm (c (-(i + j)) * c i * c j)
  calc
    t * pairCubic c ≤ |t * pairCubic c| := le_abs_self _
    _ = |t| * |pairCubic c| := abs_mul _ _
    _ ≤ |t| * total (fun k => ‖c k‖) :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg t)
    _ ≤ _ := by
      simpa only [sq_abs, Complex.sq_norm, spectrumQ, spectrumS] using
        hbound |t| (abs_nonneg t)

end Rectangle

theorem pair_scaled_directed_bound {n : ℕ} [NeZero n] (hn4 : 4 ≤ n)
    (c : ZMod n → ℂ) (hc0 : c 0 = 0)
    (hsym : ∀ k, Complex.normSq (c (-k)) = Complex.normSq (c k)) (t : ℝ) :
    t * pairCubic c ≤ 3 * t ^ 2 * spectrumQ c + (3 / 4 : ℝ) * (spectrumS c) ^ 2 := by
  obtain ⟨hp, hph, hhp, hsum⟩ := Rectangle.rectangle_parameters hn4
  have heven (k : ZMod n) : ‖c (-k)‖ = ‖c k‖ := by
    simpa only [Complex.norm_def] using congrArg Real.sqrt (hsym k)
  apply Rectangle.complex_bound c t
  intro τ hτ
  exact Rectangle.scaled_bound _ _ hsum _ heven
    (Rectangle.Fusion.cover_bound_image _ _ hph hhp hsum _ (fun k => norm_nonneg _) (by simp [hc0]) heven)
    (Rectangle.fiber_bound _ _ hsum) τ hτ

/- Native/DirectDefinitions -/
def coefficientEnergy {n : ℕ} [NeZero n] (c : ZMod n → ℂ) : ℝ :=
  ∑ k, zmodWordLength k * Complex.normSq (c k)

/- Native/RealCentering -/
lemma centered_mean {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    avg (fun x => f x - avg f) = 0 := by
  simp only [avg_sub, avg_const, sub_self]

lemma centered_sq {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    avg (fun x => (f x - avg f) ^ 2) = avg (fun x => f x ^ 2) - (avg f) ^ 2 := by
  calc
    _ = avg (fun x => f x ^ 2 - (2 * avg f) * f x + (avg f) ^ 2) :=
      avg_congr fun x => by ring
    _ = _ := by
      simp only [avg_add, avg_sub, avg_const_mul, avg_const]
      ring

lemma centered_cube {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    avg (fun x => (f x - avg f) ^ 3) =
      avg (fun x => f x ^ 3) - 3 * avg f * avg (fun x => f x ^ 2) + 2 * (avg f) ^ 3 := by
  calc
    _ = avg (fun x => f x ^ 3 - (3 * avg f) * f x ^ 2 +
        (3 * (avg f) ^ 2) * f x - (avg f) ^ 3) := avg_congr fun x => by ring
    _ = _ := by
      simp only [avg_add, avg_sub, avg_const_mul, avg_const]
      ring

theorem fourier_const_nonzero {n : ℕ} [NeZero n]
    (c : ℂ) {k : ZMod n} (hk : k ≠ 0) :
    fourierCoeff (fun _ : ZMod n => c) k = 0 := by
  unfold fourierCoeff
  simp only [ZMod.dft_apply, smul_eq_mul, ← Finset.sum_mul]
  have h := AddChar.sum_eq_zero_of_ne_one
    (ZMod.isPrimitive_stdAddChar n (neg_ne_zero.mpr hk))
  simpa only [AddChar.mulShift_apply, neg_mul, mul_neg, mul_comm, mul_zero, zero_mul] using
    congrArg (fun z : ℂ => (n : ℂ)⁻¹ * (z * c)) h

theorem fourier_sub_const_nonzero {n : ℕ} [NeZero n]
    (u : ZMod n → ℝ) (c : ℝ) {k : ZMod n} (hk : k ≠ 0) :
    fourierCoeff (fun x : ZMod n => ((u x - c : ℝ) : ℂ)) k =
      fourierCoeff (fun x : ZMod n => (u x : ℂ)) k := by
  have hc := fourier_const_nonzero (n := n) (c : ℂ) hk
  have h := congrArg (fun z : ℂ => (n : ℂ)⁻¹ * z)
    (congrFun (map_sub ZMod.dft (fun x : ZMod n => (u x : ℂ))
      (fun _ : ZMod n => (c : ℂ))) k)
  simp only [fourierCoeff] at hc
  simpa only [fourierCoeff, Complex.ofReal_sub, Pi.sub_def, mul_sub, hc, sub_zero] using h


theorem coefficientEnergy_sub_const {n : ℕ} [NeZero n]
    (u : ZMod n → ℝ) (a : ℝ) :
    coefficientEnergy (fun k => fourierCoeff (fun x => ((u x - a : ℝ) : ℂ)) k) =
      coefficientEnergy (fun k => fourierCoeff (fun x => (u x : ℂ)) k) := by
  unfold coefficientEnergy
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  by_cases hk : k = 0
  · subst k
    simp [zmodWordLength]
  · rw [fourier_sub_const_nonzero u a hk]

lemma spectrumQ_meanZero {n : ℕ} [NeZero n] (c : ZMod n → ℂ) (hc0 : c 0 = 0) :
    spectrumQ c = coefficientEnergy c - spectrumS c := by
  symm
  unfold coefficientEnergy spectrumS spectrumQ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · subst k
    rw [hc0]
    simp
  · rw [cyclicSurplus_eq_of_ne_zero hk]
    change zmodWordLength k * Complex.normSq (c k) - Complex.normSq (c k) =
      ((cyclicLength k : ℝ) - 1) * Complex.normSq (c k)
    simp only [zmodWordLength, cyclicLength]
    ring

/- Direct cubic Fourier contraction -/
lemma coefficient_product {n : ℕ} [NeZero n] (u v : ZMod n → ℂ) (k : ZMod n) :
    fourierCoeff (fun x => u x * v x) (-k) =
      ∑ j : ZMod n, fourierCoeff u (-(k + j)) * fourierCoeff v j := by
  let w := fun x => ZMod.stdAddChar (x * k) * u x
  have hw (j : ZMod n) : fourierCoeff w (-j) = fourierCoeff u (-(k + j)) := by
    simp only [fourierCoeff, ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg,
      w, mul_add, AddChar.map_add_eq_mul]
    congr 1
    apply sum_congr rfl
    intro x _
    exact (mul_assoc _ _ _).symm.trans (congrArg (· * u x) (mul_comm _ _))
  have h := coefficient_adjoint w (fourierCoeff v)
  rw [dft_fourierCoeff] at h
  simp only [neg_neg, hw] at h
  calc
    _ = (n : ℂ)⁻¹ * ∑ x : ZMod n, w x * v x := by
      simp only [fourierCoeff, ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg, w, mul_assoc]
    _ = _ := h.symm

lemma coefficient_cube {n : ℕ} [NeZero n] (u : ZMod n → ℂ) :
    (∑ i : ZMod n, ∑ j : ZMod n,
      fourierCoeff u (-(i + j)) * fourierCoeff u i * fourierCoeff u j) =
      (n : ℂ)⁻¹ * ∑ x : ZMod n, u x ^ 3 := by
  calc
    _ = ∑ i : ZMod n, fourierCoeff (fun x => u x * u x) (-i) * fourierCoeff u i := by
      simp only [coefficient_product, sum_mul]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      exact mul_right_comm _ _ _
    _ = (n : ℂ)⁻¹ * ∑ x : ZMod n, (u x * u x) * ZMod.dft (fourierCoeff u) (-x) :=
      coefficient_adjoint _ _
    _ = _ := by simp only [dft_fourierCoeff, neg_neg, pow_succ, pow_zero, one_mul]


lemma pairCubic_fourier {n : ℕ} [NeZero n] (u : ZMod n → ℝ) :
    pairCubic (fun k => fourierCoeff (fun x => (u x : ℂ)) k) = avg (fun x => u x ^ 3) := by
  have h := congrArg Complex.re (coefficient_cube (fun x => (u x : ℂ)))
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.re_sum, pairCubic, avg, ZMod.card, div_eq_mul_inv, mul_comm] using h

/- Native/DirectEntropy -/
theorem direct_entropy_sos {n : ℕ} [NeZero n] (hn4 : 4 ≤ n)
    (f : ZMod n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ent (fun x => f x ^ 2) ≤
      2 * coefficientEnergy (fun k => fourierCoeff (fun x => (f x : ℂ)) k) := by
  classical
  let c := fun k => fourierCoeff (fun x => (f x : ℂ)) k
  let E := coefficientEnergy c
  let V := avg (fun x => f x ^ 2)
  let a := avg f
  change ent (fun x => f x ^ 2) ≤ 2 * E
  have hV0 : 0 ≤ V := avg_nonneg fun x => sq_nonneg (f x)
  rcases hV0.eq_or_lt with hV | hV
  · have hsum : (∑ x, f x ^ 2) = 0 := by
      exact (div_eq_zero_iff.mp hV.symm).resolve_right
        (by exact_mod_cast (Fintype.card_ne_zero (α := ZMod n)))
    have hz (x) : f x = 0 := sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (f y))).mp hsum x
        (Finset.mem_univ x))
    simp [ent, hz, E, c, coefficientEnergy, fourierCoeff, avg, ← Pi.zero_def]
  · let t := Real.sqrt V
    have ht : 0 < t := Real.sqrt_pos.mpr hV
    have ht2 : t ^ 2 = V := Real.sq_sqrt hV.le
    let u := fun x => f x - a
    let cu := fun k => fourierCoeff (fun x => (u x : ℂ)) k
    have hc0 : cu 0 = 0 := fourierCoeff_zero_of_meanZero (centered_mean f)
    have hsym (k) : Complex.normSq (cu (-k)) = Complex.normSq (cu k) := by
      dsimp [cu]
      rw [fourierCoeff_real_neg]
      simp
    have hS : spectrumS cu = V - a ^ 2 := by
      have hp : spectrumS cu = avg (fun x => u x ^ 2) := by
        simpa only [spectrumS, cu, avg, ZMod.card] using (parseval_real_sq u).symm
      exact hp.trans (centered_sq f)
    have hQ : spectrumQ cu = E - V + a ^ 2 := by
      rw [spectrumQ_meanZero cu hc0, hS,
        show coefficientEnergy cu = E from coefficientEnergy_sub_const f a]
      ring
    have hC : pairCubic cu = avg (fun x => f x ^ 3) - 3 * a * V + 2 * a ^ 3 :=
      (pairCubic_fourier u).trans (centered_cube f)
    have hy := pair_scaled_directed_bound hn4 cu hc0 hsym t
    rw [hS, hQ, hC, ht2] at hy
    have he := scaled_entropy_majorant f hf t ht ht2.symm
    have ha : 0 ≤ a := avg_nonneg hf
    have ha2 : a ^ 2 ≤ V := by
      have h : 0 ≤ spectrumS cu :=
        Finset.sum_nonneg fun k _ => Complex.normSq_nonneg (cu k)
      rw [hS] at h
      linarith only [h]
    have hat : a ≤ t := by nlinarith only [ha, ha2, ht2, ht.le]
    have hr : 0 ≤ (t - a) ^ 3 * (t + 3 * a) :=
      mul_nonneg (pow_nonneg (sub_nonneg.mpr hat) 3) (by positivity)
    apply le_of_mul_le_mul_left _ (mul_pos (by norm_num : (0 : ℝ) < 3) hV)
    rw [← ht2] at hy ⊢
    nlinarith only [hy, he, hr]

end Native

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
  change ent (fun x => f x ^ 2) ≤
    2 * Native.coefficientEnergy (fun k => fourierCoeff (fun x => (f x : ℂ)) k)
  exact Native.direct_entropy_sos hn f hf

#check @CyclicLsi.theorem1
#print axioms CyclicLsi.theorem1

end CyclicLsi
end
