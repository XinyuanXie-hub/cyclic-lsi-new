import CyclicLsi.Support.Proposition78.Fourier.Amplitudes
import CyclicLsi.Support.Proposition78.OddCase.Resonance
import CyclicLsi.Support.Proposition78.ThirdMomentBlockProofs



/-!
# Fourier resonance bounds

This file connects the Fourier cubic expansion to the odd/even resonance
enumerations.  The estimates here are the coefficient-counting bridge between
the cyclic Fourier analysis and the real block inequalities.
-/

namespace CyclicLsi

open scoped BigOperators

noncomputable section

theorem sum_if_le_sum_of_surj_on {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) [DecidablePred P]
    (f : β → α) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hcover : ∀ a, P a → ∃ b, f b = a) :
    (∑ a : α, if P a then w a else 0) ≤ ∑ b : β, w (f b) := by
  classical
  let imageSet : Finset α := Finset.univ.image f
  have hfilter_subset : (Finset.univ.filter P) ⊆ imageSet := by
    intro a ha
    have hpa : P a := by simpa using ha
    rcases hcover a hpa with ⟨b, rfl⟩
    simp [imageSet]
  have hfilter :
      (∑ a : α, if P a then w a else 0) =
        (∑ a ∈ Finset.univ.filter P, w a) := by
    simpa using
      (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := P) (f := w)).symm
  have hto_image :
      (∑ a ∈ Finset.univ.filter P, w a) ≤ (∑ a ∈ imageSet, w a) :=
    Finset.sum_le_sum_of_subset_of_nonneg hfilter_subset
      (by intro a _ _; exact hw a)
  let preExists : ∀ a : {a : α // a ∈ imageSet}, ∃ b, f b = a.val := by
    intro a
    rcases Finset.mem_image.mp a.property with ⟨b, _, hb⟩
    exact ⟨b, hb⟩
  let pre : {a : α // a ∈ imageSet} → β := fun a ↦ Classical.choose (preExists a)
  have hpre : ∀ a : {a : α // a ∈ imageSet}, f (pre a) = a.val := by
    intro a
    exact Classical.choose_spec (preExists a)
  have hpre_inj : Function.Injective pre := by
    intro a b hab
    apply Subtype.ext
    calc
      a.val = f (pre a) := (hpre a).symm
      _ = f (pre b) := by rw [hab]
      _ = b.val := hpre b
  have himage_attach :
      (∑ a ∈ imageSet, w a) = ∑ a : {a : α // a ∈ imageSet}, w a.val := by
    exact Finset.sum_subtype (s := imageSet) (h := by intro a; rfl) (f := w)
  have hpre_sum :
      (∑ a : {a : α // a ∈ imageSet}, w (f (pre a))) =
        ∑ a : {a : α // a ∈ imageSet}, w a.val := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hpre]
  have himage_le_domain :
      (∑ a ∈ imageSet, w a) ≤ ∑ b : β, w (f b) := by
    rw [himage_attach]
    rw [← hpre_sum]
    exact sum_comp_le_univ_sum_of_injective
      (f := pre) hpre_inj (fun b : β ↦ w (f b)) (fun b ↦ hw (f b))
  calc
    (∑ a : α, if P a then w a else 0)
        = ∑ a ∈ Finset.univ.filter P, w a := hfilter
    _ ≤ (∑ a ∈ imageSet, w a) := hto_image
    _ ≤ ∑ b : β, w (f b) := himage_le_domain

def oddSignedFreqToFull {m : ℕ} : OddSignedFreq m → OddFullFreq m
  | (OddSign.pos, j) => OddFullFreq.pos j
  | (OddSign.neg, j) => OddFullFreq.neg j

def oddFullFreqNonzeroEquiv (m : ℕ) : OddFullFreq m ≃ Unit ⊕ OddSignedFreq m where
  toFun
    | OddFullFreq.zero => Sum.inl ()
    | OddFullFreq.pos j => Sum.inr (OddSign.pos, j)
    | OddFullFreq.neg j => Sum.inr (OddSign.neg, j)
  invFun
    | Sum.inl _ => OddFullFreq.zero
    | Sum.inr f => oddSignedFreqToFull f
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
        cases f with
        | mk s j =>
          cases s <;> rfl

theorem oddFullFreq_sum_nonzero {m : ℕ} {β : Type*} [AddCommMonoid β]
    (F : OddFullFreq m → β) (h0 : F OddFullFreq.zero = 0) :
    (∑ f : OddFullFreq m, F f) =
      ∑ f : OddSignedFreq m, F (oddSignedFreqToFull f) := by
  calc
    (∑ f : OddFullFreq m, F f)
        = ∑ x : Unit ⊕ OddSignedFreq m, F ((oddFullFreqNonzeroEquiv m).symm x) := by
            exact Fintype.sum_equiv (oddFullFreqNonzeroEquiv m) F
              (fun x : Unit ⊕ OddSignedFreq m ↦
                F ((oddFullFreqNonzeroEquiv m).symm x))
              (by intro f; simp)
    _ = ∑ f : OddSignedFreq m, F (oddSignedFreqToFull f) := by
          simp [oddFullFreqNonzeroEquiv, h0]

theorem oddFullFreq_triple_sum_nonzero {m : ℕ} {β : Type*} [AddCommMonoid β]
    (F : OddFullFreq m → OddFullFreq m → OddFullFreq m → β)
    (h₁ : ∀ b c, F OddFullFreq.zero b c = 0)
    (h₂ : ∀ a c, F a OddFullFreq.zero c = 0)
    (h₃ : ∀ a b, F a b OddFullFreq.zero = 0) :
    (∑ a : OddFullFreq m, ∑ b : OddFullFreq m, ∑ c : OddFullFreq m, F a b c) =
      ∑ t : OddTriple m,
        F (oddSignedFreqToFull t.1)
          (oddSignedFreqToFull t.2.1)
          (oddSignedFreqToFull t.2.2) := by
  classical
  calc
    (∑ a : OddFullFreq m, ∑ b : OddFullFreq m, ∑ c : OddFullFreq m, F a b c)
        = ∑ a : OddSignedFreq m, ∑ b : OddFullFreq m, ∑ c : OddFullFreq m,
            F (oddSignedFreqToFull a) b c := by
            rw [oddFullFreq_sum_nonzero]
            simp [h₁]
    _ = ∑ a : OddSignedFreq m, ∑ b : OddSignedFreq m, ∑ c : OddFullFreq m,
            F (oddSignedFreqToFull a) (oddSignedFreqToFull b) c := by
            congr with a
            rw [oddFullFreq_sum_nonzero]
            simp [h₂]
    _ = ∑ a : OddSignedFreq m, ∑ b : OddSignedFreq m, ∑ c : OddSignedFreq m,
            F (oddSignedFreqToFull a) (oddSignedFreqToFull b) (oddSignedFreqToFull c) := by
            congr with a
            congr with b
            rw [oddFullFreq_sum_nonzero]
            simp [h₃]
    _ = ∑ t : OddTriple m,
        F (oddSignedFreqToFull t.1)
          (oddSignedFreqToFull t.2.1)
          (oddSignedFreqToFull t.2.2) := by
          calc
            (∑ a : OddSignedFreq m, ∑ b : OddSignedFreq m, ∑ c : OddSignedFreq m,
                F (oddSignedFreqToFull a) (oddSignedFreqToFull b)
                  (oddSignedFreqToFull c))
                = ∑ a : OddSignedFreq m, ∑ bc : OddSignedFreq m × OddSignedFreq m,
                    F (oddSignedFreqToFull a) (oddSignedFreqToFull bc.1)
                      (oddSignedFreqToFull bc.2) := by
                    congr with a
                    exact (Fintype.sum_prod_type'
                      (fun b c : OddSignedFreq m ↦
                        F (oddSignedFreqToFull a) (oddSignedFreqToFull b)
                          (oddSignedFreqToFull c))).symm
            _ = ∑ t : OddTriple m,
                F (oddSignedFreqToFull t.1)
                  (oddSignedFreqToFull t.2.1)
                  (oddSignedFreqToFull t.2.2) := by
                    exact (Fintype.sum_prod_type'
                      (fun a (bc : OddSignedFreq m × OddSignedFreq m) ↦
                        F (oddSignedFreqToFull a) (oddSignedFreqToFull bc.1)
                          (oddSignedFreqToFull bc.2))).symm

theorem oddFullFreqZ_toSigned {m : ℕ} (f : OddSignedFreq m) :
    oddFullFreqZ (oddSignedFreqToFull f) = oddSignedFreq f := by
  cases f with
  | mk s j =>
    cases s
    · simp [oddSignedFreqToFull, oddSignedFreq, oddPosFreq, oddFullFreqZ_pos]
    · simp [oddSignedFreqToFull, oddSignedFreq, oddPosFreq, oddFullFreqZ_neg]

theorem sqrt_half_mul_sqrt_two : √((1 : ℝ) / 2) * √(2 : ℝ) = 1 := by
  have h :
      √((1 : ℝ) / 2) * √(2 : ℝ) = √(((1 : ℝ) / 2) * 2) := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (1 : ℝ) / 2)]
  rw [h]
  norm_num

theorem norm_oddSignedFreq_eq_sqrt_half_mul_amp {m : ℕ}
    (u : ZMod (2 * m + 1) → ℝ) (f : OddSignedFreq m) :
    ‖realFourierCoeff u (oddSignedFreq f)‖ =
      √((1 : ℝ) / 2) * oddFourierAmp m u f.2 := by
  haveI : NeZero (2 * m + 1) := ⟨by omega⟩
  cases f with
  | mk s j =>
    cases s
    · simp [oddSignedFreq, oddPosFreq, oddFourierAmp]
    · rw [oddSignedFreq]
      simp only
      rw [norm_fourierCoeff_neg_real]
      simp [oddPosFreq, oddFourierAmp]

theorem odd_abs_avg_cube_le_triple_norm_sum {m : ℕ} [NeZero (2 * m + 1)]
    {u : ZMod (2 * m + 1) → ℝ} (hu : MeanZero u) :
    |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)| ≤
      ∑ t : OddTriple m,
        if oddTripleSum t = 0 then
          ‖realFourierCoeff u (oddSignedFreq t.1)‖ *
            ‖realFourierCoeff u (oddSignedFreq t.2.1)‖ *
            ‖realFourierCoeff u (oddSignedFreq t.2.2)‖
        else
          0 := by
  let c : ZMod (2 * m + 1) → ℂ := fun k ↦ realFourierCoeff u k
  have hzero : c 0 = 0 := by
    dsimp [c, realFourierCoeff]
    exact fourierCoeff_zero_of_meanZero hu
  have hmain := abs_avg_cube_le_resonant_norm_sum (n := 2 * m + 1) u
  calc
    |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)|
        ≤ ∑ k : ZMod (2 * m + 1), ∑ l : ZMod (2 * m + 1),
          ∑ r : ZMod (2 * m + 1),
          if k + l + r = 0 then ‖c k‖ * ‖c l‖ * ‖c r‖ else 0 := by
          simpa [c, realFourierCoeff] using hmain
    _ = ∑ f : OddFullFreq m, ∑ g : OddFullFreq m, ∑ h : OddFullFreq m,
          if oddFullFreqZ f + oddFullFreqZ g + oddFullFreqZ h = 0 then
            ‖c (oddFullFreqZ f)‖ * ‖c (oddFullFreqZ g)‖ * ‖c (oddFullFreqZ h)‖
          else
            0 := by
          rw [sum_zmod_oddFullFreq]
          congr with f
          rw [sum_zmod_oddFullFreq]
          congr with g
          rw [sum_zmod_oddFullFreq]
    _ = ∑ t : OddTriple m,
        if oddTripleSum t = 0 then
          ‖c (oddSignedFreq t.1)‖ *
            ‖c (oddSignedFreq t.2.1)‖ *
            ‖c (oddSignedFreq t.2.2)‖
        else
          0 := by
          rw [oddFullFreq_triple_sum_nonzero]
          · apply Finset.sum_congr rfl
            intro t _
            simp [oddFullFreqZ_toSigned, oddTripleSum]
          · intro g h
            by_cases hsum : oddFullFreqZ OddFullFreq.zero +
                oddFullFreqZ g + oddFullFreqZ h = 0
            · simp [oddFullFreqZ_zero, hzero]
            · simp [hsum]
          · intro f h
            by_cases hsum : oddFullFreqZ f +
                oddFullFreqZ OddFullFreq.zero + oddFullFreqZ h = 0
            · simp [oddFullFreqZ_zero, hzero]
            · simp [hsum]
          · intro f g
            by_cases hsum : oddFullFreqZ f +
                oddFullFreqZ g + oddFullFreqZ OddFullFreq.zero = 0
            · simp [oddFullFreqZ_zero, hzero]
            · simp [hsum]
    _ = ∑ t : OddTriple m,
        if oddTripleSum t = 0 then
          ‖realFourierCoeff u (oddSignedFreq t.1)‖ *
            ‖realFourierCoeff u (oddSignedFreq t.2.1)‖ *
            ‖realFourierCoeff u (oddSignedFreq t.2.2)‖
        else
          0 := by
          rfl

theorem odd_sum_if_resonance_le_domain {m : ℕ}
    (w : OddTriple m → ℝ) (hw : ∀ t, 0 ≤ w t) :
    (∑ t : OddTriple m, if oddTripleSum t = 0 then w t else 0) ≤
      ∑ d : OddResonanceDomain m, w (oddResonanceTriple d) := by
  exact sum_if_le_sum_of_surj_on
    (P := fun t : OddTriple m ↦ oddTripleSum t = 0)
    (f := oddResonanceTriple) w hw
    (fun t ht ↦ oddResonanceTriple_exists_of_sum_zero t ht)

theorem odd_abs_avg_cube_le_resonance_domain_sum {m : ℕ} [NeZero (2 * m + 1)]
    {u : ZMod (2 * m + 1) → ℝ} (hu : MeanZero u) :
    |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)| ≤
      ∑ d : OddResonanceDomain m,
        ‖realFourierCoeff u (oddSignedFreq (oddResonanceTriple d).1)‖ *
          ‖realFourierCoeff u (oddSignedFreq (oddResonanceTriple d).2.1)‖ *
          ‖realFourierCoeff u (oddSignedFreq (oddResonanceTriple d).2.2)‖ := by
  calc
    |avg (fun x : ZMod (2 * m + 1) ↦ u x ^ 3)|
        ≤ ∑ t : OddTriple m,
          if oddTripleSum t = 0 then
            ‖realFourierCoeff u (oddSignedFreq t.1)‖ *
              ‖realFourierCoeff u (oddSignedFreq t.2.1)‖ *
              ‖realFourierCoeff u (oddSignedFreq t.2.2)‖
          else
            0 := odd_abs_avg_cube_le_triple_norm_sum hu
    _ ≤ ∑ d : OddResonanceDomain m,
        ‖realFourierCoeff u (oddSignedFreq (oddResonanceTriple d).1)‖ *
          ‖realFourierCoeff u (oddSignedFreq (oddResonanceTriple d).2.1)‖ *
          ‖realFourierCoeff u (oddSignedFreq (oddResonanceTriple d).2.2)‖ := by
          exact odd_sum_if_resonance_le_domain
            (fun t : OddTriple m ↦
              ‖realFourierCoeff u (oddSignedFreq t.1)‖ *
                ‖realFourierCoeff u (oddSignedFreq t.2.1)‖ *
                ‖realFourierCoeff u (oddSignedFreq t.2.2)‖)
            (by
              intro t
              positivity)

theorem even_abs_avg_cube_le_triple_norm_sum {m : ℕ} [NeZero (2 * m)]
    {u : ZMod (2 * m) → ℝ} (hu : MeanZero u) :
    |avg (fun x : ZMod (2 * m) ↦ u x ^ 3)| ≤
      ∑ t : EvenTriple m,
        if evenTripleSum t = 0 then
          ‖realFourierCoeff u (evenFreqZ t.1)‖ *
            ‖realFourierCoeff u (evenFreqZ t.2.1)‖ *
            ‖realFourierCoeff u (evenFreqZ t.2.2)‖
        else
          0 := by
  let c : ZMod (2 * m) → ℂ := fun k ↦ realFourierCoeff u k
  have hzero : c 0 = 0 := by
    dsimp [c, realFourierCoeff]
    exact fourierCoeff_zero_of_meanZero hu
  have hmain := abs_avg_cube_le_resonant_norm_sum (n := 2 * m) u
  calc
    |avg (fun x : ZMod (2 * m) ↦ u x ^ 3)|
        ≤ ∑ k : ZMod (2 * m), ∑ l : ZMod (2 * m), ∑ r : ZMod (2 * m),
          if k + l + r = 0 then ‖c k‖ * ‖c l‖ * ‖c r‖ else 0 := by
          simpa [c, realFourierCoeff] using hmain
    _ = ∑ f : EvenFullFreq m, ∑ g : EvenFullFreq m, ∑ h : EvenFullFreq m,
          if evenFullFreqZ f + evenFullFreqZ g + evenFullFreqZ h = 0 then
            ‖c (evenFullFreqZ f)‖ * ‖c (evenFullFreqZ g)‖ * ‖c (evenFullFreqZ h)‖
          else
            0 := by
          rw [sum_zmod_evenFullFreq]
          congr with f
          rw [sum_zmod_evenFullFreq]
          congr with g
          rw [sum_zmod_evenFullFreq]
    _ = ∑ t : EvenTriple m,
        if evenTripleSum t = 0 then
          ‖c (evenFreqZ t.1)‖ * ‖c (evenFreqZ t.2.1)‖ * ‖c (evenFreqZ t.2.2)‖
        else
          0 := by
          rw [evenFullFreq_triple_sum_nonzero]
          · apply Finset.sum_congr rfl
            intro t _
            simp [evenFullFreqZ_toFull, evenTripleSum]
          · intro g h
            by_cases hsum : evenFullFreqZ EvenFullFreq.zero +
                evenFullFreqZ g + evenFullFreqZ h = 0
            · simp [evenFullFreqZ_zero, hzero]
            · simp [hsum]
          · intro f h
            by_cases hsum : evenFullFreqZ f +
                evenFullFreqZ EvenFullFreq.zero + evenFullFreqZ h = 0
            · simp [evenFullFreqZ_zero, hzero]
            · simp [hsum]
          · intro f g
            by_cases hsum : evenFullFreqZ f +
                evenFullFreqZ g + evenFullFreqZ EvenFullFreq.zero = 0
            · simp [evenFullFreqZ_zero, hzero]
            · simp [hsum]
    _ = ∑ t : EvenTriple m,
        if evenTripleSum t = 0 then
          ‖realFourierCoeff u (evenFreqZ t.1)‖ *
            ‖realFourierCoeff u (evenFreqZ t.2.1)‖ *
            ‖realFourierCoeff u (evenFreqZ t.2.2)‖
        else
          0 := by
          rfl

theorem even_sum_if_resonance_le_domain {m : ℕ} (hm : 2 ≤ m)
    (w : EvenTriple m → ℝ) (hw : ∀ t, 0 ≤ w t) :
    (∑ t : EvenTriple m, if evenTripleSum t = 0 then w t else 0) ≤
      ∑ d : EvenResonanceDomain m, w (evenResonanceTriple d) := by
  exact sum_if_le_sum_of_surj_on
    (P := fun t : EvenTriple m ↦ evenTripleSum t = 0)
    (f := evenResonanceTriple) w hw
    (fun t ht ↦ evenResonanceTriple_exists_of_sum_zero hm t ht)

theorem even_abs_avg_cube_le_resonance_domain_sum {m : ℕ} [NeZero (2 * m)]
    (hm : 2 ≤ m) {u : ZMod (2 * m) → ℝ} (hu : MeanZero u) :
    |avg (fun x : ZMod (2 * m) ↦ u x ^ 3)| ≤
      ∑ d : EvenResonanceDomain m,
        ‖realFourierCoeff u (evenFreqZ (evenResonanceTriple d).1)‖ *
          ‖realFourierCoeff u (evenFreqZ (evenResonanceTriple d).2.1)‖ *
          ‖realFourierCoeff u (evenFreqZ (evenResonanceTriple d).2.2)‖ := by
  calc
    |avg (fun x : ZMod (2 * m) ↦ u x ^ 3)|
        ≤ ∑ t : EvenTriple m,
          if evenTripleSum t = 0 then
            ‖realFourierCoeff u (evenFreqZ t.1)‖ *
              ‖realFourierCoeff u (evenFreqZ t.2.1)‖ *
              ‖realFourierCoeff u (evenFreqZ t.2.2)‖
          else
            0 := even_abs_avg_cube_le_triple_norm_sum hu
    _ ≤ ∑ d : EvenResonanceDomain m,
        ‖realFourierCoeff u (evenFreqZ (evenResonanceTriple d).1)‖ *
          ‖realFourierCoeff u (evenFreqZ (evenResonanceTriple d).2.1)‖ *
          ‖realFourierCoeff u (evenFreqZ (evenResonanceTriple d).2.2)‖ := by
          exact even_sum_if_resonance_le_domain hm
            (fun t : EvenTriple m ↦
              ‖realFourierCoeff u (evenFreqZ t.1)‖ *
                ‖realFourierCoeff u (evenFreqZ t.2.1)‖ *
                ‖realFourierCoeff u (evenFreqZ t.2.2)‖)
            (by
              intro t
              positivity)

end

end CyclicLsi

