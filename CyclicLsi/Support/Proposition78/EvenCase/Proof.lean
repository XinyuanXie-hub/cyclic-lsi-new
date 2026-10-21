module
public import CyclicLsi.Support.Proposition78.Fourier.ResonanceBounds


/-!
# Proposition 11: even third-moment estimate

This file proves the even cyclic-group third-moment estimate for the concrete
word-length Fourier energy.
-/

namespace CyclicLsi

open scoped BigOperators

@[expose] public noncomputable section

theorem norm_evenFreq_pos_eq_sqrt_half_mul_amp {m : ℕ} [NeZero (2 * m)]
    (hm : 2 ≤ m) (u : ZMod (2 * m) → ℝ) (j : Fin (m - 1)) :
    ‖realFourierCoeff u (evenFreqZ (EvenFreq.pos j))‖ =
      √((1 : ℝ) / 2) * evenFourierAmp (m := m) u ⟨j.val, by omega⟩ := by
  have hne : ¬j.val + 1 = m := by
    have hj : j.val < m - 1 := j.isLt
    omega
  simp [evenFreqZ, evenFourierAmp, hne]

theorem norm_evenFreq_neg_eq_sqrt_half_mul_amp {m : ℕ} [NeZero (2 * m)]
    (hm : 2 ≤ m) (u : ZMod (2 * m) → ℝ) (j : Fin (m - 1)) :
    ‖realFourierCoeff u (evenFreqZ (EvenFreq.neg j))‖ =
      √((1 : ℝ) / 2) * evenFourierAmp (m := m) u ⟨j.val, by omega⟩ := by
  have hne : ¬j.val + 1 = m := by
    have hj : j.val < m - 1 := j.isLt
    omega
  rw [evenFreqZ]
  rw [norm_fourierCoeff_neg_real]
  simp [evenFourierAmp, hne]

theorem norm_evenFreq_mid_eq_amp {m : ℕ} [NeZero (2 * m)]
    (hm : 2 ≤ m) (u : ZMod (2 * m) → ℝ) :
    ‖realFourierCoeff u (evenFreqZ (EvenFreq.mid : EvenFreq m))‖ =
      evenFourierAmp (m := m) u ⟨m - 1, by omega⟩ := by
  have hlast : (m - 1) + 1 = m := by omega
  simp [evenFreqZ, evenFourierAmp, hlast]

def finZeroOrdinaryLastEquiv (m : ℕ) (hm : 2 ≤ m) :
    Fin m ≃ Unit ⊕ (EvenOrdinaryIndex m ⊕ Unit) where
  toFun j :=
    if h0 : j.val = 0 then
      Sum.inl ()
    else if hlast : j.val = m - 1 then
      Sum.inr (Sum.inr ())
    else
      Sum.inr (Sum.inl ⟨j, h0, hlast⟩)
  invFun
    | Sum.inl _ => ⟨0, by omega⟩
    | Sum.inr (Sum.inl r) => r.val
    | Sum.inr (Sum.inr _) => ⟨m - 1, by omega⟩
  left_inv := by
    intro j
    dsimp
    split_ifs with h0 hlast
    · exact Fin.ext h0.symm
    · exact Fin.ext hlast.symm
    · rfl
  right_inv := by
    intro x
    cases x with
    | inl u =>
        cases u
        simp
    | inr y =>
        cases y with
        | inl r =>
            dsimp
            have h0 : r.val.val ≠ 0 := r.property.1
            have hlast : r.val.val ≠ m - 1 := r.property.2
            simp [h0, hlast]
        | inr u =>
            cases u
            dsimp
            have h0 : m - 1 ≠ 0 := by omega
            simp [h0]

theorem sum_fin_eq_zero_add_ordinary_add_last {m : ℕ} (hm : 2 ≤ m)
    {β : Type*} [AddCommMonoid β] (F : Fin m → β) :
    ∑ r : Fin m, F r =
      F ⟨0, by omega⟩ +
        (∑ r : EvenOrdinaryIndex m, F r.val) +
          F ⟨m - 1, by omega⟩ := by
  calc
    ∑ r : Fin m, F r =
        ∑ x : Unit ⊕ (EvenOrdinaryIndex m ⊕ Unit),
          F ((finZeroOrdinaryLastEquiv m hm).symm x) := by
        exact Fintype.sum_equiv (finZeroOrdinaryLastEquiv m hm)
          F
          (fun x : Unit ⊕ (EvenOrdinaryIndex m ⊕ Unit) ↦
            F ((finZeroOrdinaryLastEquiv m hm).symm x))
          (by intro r; simp)
    _ = F ⟨0, by omega⟩ +
        (∑ r : EvenOrdinaryIndex m, F r.val) +
          F ⟨m - 1, by omega⟩ := by
        simp [finZeroOrdinaryLastEquiv, add_assoc]

theorem blockQsq_eq_even_ordinary_add_last {m : ℕ} (hm : 2 ≤ m)
    (a : Fin m → ℝ) :
    blockQsq a =
      (∑ r : EvenOrdinaryIndex m, (r.val.val : ℝ) * a r.val ^ 2) +
        ((m - 1 : ℕ) : ℝ) * a ⟨m - 1, by omega⟩ ^ 2 := by
  unfold blockQsq
  rw [sum_fin_eq_zero_add_ordinary_add_last hm]
  simp

theorem evenWeightedOrdinarySum_eq_subtype {m : ℕ} (hm : 2 ≤ m)
    (a : Fin m → ℝ) :
    evenWeightedOrdinarySum a =
      ∑ r : EvenOrdinaryIndex m,
        (3 * evenL a r.val + evenR a r.val) ^ 2 /
          (2 * (r.val.val : ℝ)) := by
  unfold evenWeightedOrdinarySum evenWeightedOrdinaryTerm
  rw [sum_fin_eq_zero_add_ordinary_add_last hm]
  have hzero :
      (if (0 : ℕ) = 0 ∨ (0 : ℕ) = m - 1 then 0
        else (3 * evenL a ⟨0, by omega⟩ + evenR a ⟨0, by omega⟩) ^ 2 /
          (2 * ((0 : ℕ) : ℝ))) = 0 := by
    simp
  have hlast :
      (if (m - 1 : ℕ) = 0 ∨ (m - 1 : ℕ) = m - 1 then 0
        else (3 * evenL a ⟨m - 1, by omega⟩ + evenR a ⟨m - 1, by omega⟩) ^ 2 /
          (2 * (((m - 1 : ℕ) : ℝ)))) = 0 := by
    simp
  rw [hzero, hlast, zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro r _
  have hbad : ¬ (r.val.val = 0 ∨ r.val.val = m - 1) := by
    exact fun h ↦ h.elim r.property.1 r.property.2
  simp [hbad]

def evenCauchyMoment {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℝ) : ℝ :=
  √((1 : ℝ) / 2) *
      ∑ r : EvenOrdinaryIndex m,
        a r.val * (3 * evenL a r.val + evenR a r.val) +
    3 * a ⟨m - 1, by omega⟩ * evenLm a

theorem even_cauchy_moment_le {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℝ) :
    evenCauchyMoment hm a ≤ √(blockQsq a) * √(evenWeightedSum a) := by
  classical
  let q : ℝ := √((1 : ℝ) / 2)
  let last : Fin m := ⟨m - 1, by omega⟩
  let F : EvenOrdinaryIndex m ⊕ Unit → ℝ := fun x =>
    match x with
    | Sum.inl r => √(r.val.val : ℝ) * a r.val
    | Sum.inr _ => √((m - 1 : ℕ) : ℝ) * a last
  let G : EvenOrdinaryIndex m ⊕ Unit → ℝ := fun x =>
    match x with
    | Sum.inl r =>
        q * (3 * evenL a r.val + evenR a r.val) / √(r.val.val : ℝ)
    | Sum.inr _ => 3 * evenLm a / √((m - 1 : ℕ) : ℝ)
  have hprod :
      ∑ x : EvenOrdinaryIndex m ⊕ Unit, F x * G x = evenCauchyMoment hm a := by
    have hq_prod (r : EvenOrdinaryIndex m) :
        F (Sum.inl r) * G (Sum.inl r) =
          q * (a r.val * (3 * evenL a r.val + evenR a r.val)) := by
      have hrpos : 0 < (r.val.val : ℝ) := by
        have : 0 < r.val.val := Nat.pos_of_ne_zero r.property.1
        exact_mod_cast this
      dsimp [F, G]
      field_simp [(Real.sqrt_pos.2 hrpos).ne']
    have hlast_prod :
        F (Sum.inr ()) * G (Sum.inr ()) =
          3 * a last * evenLm a := by
      have hmpos : 0 < ((m - 1 : ℕ) : ℝ) := by
        have : 0 < m - 1 := by omega
        exact_mod_cast this
      dsimp [F, G]
      field_simp [(Real.sqrt_pos.2 hmpos).ne']
    simp [Fintype.sum_sum_type, hq_prod, hlast_prod, evenCauchyMoment, q, last,
      Finset.mul_sum, mul_assoc]
  have hFsq :
      ∑ x : EvenOrdinaryIndex m ⊕ Unit, F x ^ 2 = blockQsq a := by
    calc
      ∑ x : EvenOrdinaryIndex m ⊕ Unit, F x ^ 2 =
          (∑ r : EvenOrdinaryIndex m, (r.val.val : ℝ) * a r.val ^ 2) +
            ((m - 1 : ℕ) : ℝ) * a last ^ 2 := by
          calc
            ∑ x : EvenOrdinaryIndex m ⊕ Unit, F x ^ 2 =
                (∑ r : EvenOrdinaryIndex m, (√(r.val.val : ℝ) * a r.val) ^ 2) +
                  (√((m - 1 : ℕ) : ℝ) * a last) ^ 2 := by
                simp [Fintype.sum_sum_type, F]
            _ = (∑ r : EvenOrdinaryIndex m, (r.val.val : ℝ) * a r.val ^ 2) +
                  ((m - 1 : ℕ) : ℝ) * a last ^ 2 := by
                congr 1
                · apply Finset.sum_congr rfl
                  intro r _
                  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (r.val.val : ℝ))]
                · rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ((m - 1 : ℕ) : ℝ))]
      _ = blockQsq a := (blockQsq_eq_even_ordinary_add_last hm a).symm
  have hGsq :
      ∑ x : EvenOrdinaryIndex m ⊕ Unit, G x ^ 2 = evenWeightedSum a := by
    have hq2 : q ^ 2 = (1 : ℝ) / 2 := by
      simp [q]
    have hord (r : EvenOrdinaryIndex m) :
        G (Sum.inl r) ^ 2 =
          (3 * evenL a r.val + evenR a r.val) ^ 2 /
            (2 * (r.val.val : ℝ)) := by
      have hrpos : 0 < (r.val.val : ℝ) := by
        have : 0 < r.val.val := Nat.pos_of_ne_zero r.property.1
        exact_mod_cast this
      dsimp [G]
      rw [div_pow, mul_pow, hq2, Real.sq_sqrt hrpos.le]
      field_simp [(by positivity : (2 : ℝ) ≠ 0), hrpos.ne']
    have hmid :
        G (Sum.inr ()) ^ 2 =
          9 * evenLm a ^ 2 / ((m - 1 : ℕ) : ℝ) := by
      have hmpos : 0 < ((m - 1 : ℕ) : ℝ) := by
        have : 0 < m - 1 := by omega
        exact_mod_cast this
      dsimp [G]
      rw [div_pow, Real.sq_sqrt hmpos.le]
      ring
    calc
      ∑ x : EvenOrdinaryIndex m ⊕ Unit, G x ^ 2 =
          (∑ r : EvenOrdinaryIndex m,
            (3 * evenL a r.val + evenR a r.val) ^ 2 /
              (2 * (r.val.val : ℝ))) +
            9 * evenLm a ^ 2 / ((m - 1 : ℕ) : ℝ) := by
          simp [Fintype.sum_sum_type, hord, hmid]
      _ = evenWeightedSum a := by
          rw [evenWeightedSum, evenWeightedOrdinarySum_eq_subtype hm]
  have hcauchy :=
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (EvenOrdinaryIndex m ⊕ Unit)) F G
  calc
    evenCauchyMoment hm a = ∑ x : EvenOrdinaryIndex m ⊕ Unit, F x * G x := hprod.symm
    _ ≤ √(blockQsq a) * √(evenWeightedSum a) := by
      simpa [hFsq, hGsq] using hcauchy

def evenTripleNormWeight {m : ℕ} [NeZero (2 * m)]
    (u : ZMod (2 * m) → ℝ) (t : EvenTriple m) : ℝ :=
  ‖realFourierCoeff u (evenFreqZ t.1)‖ *
    ‖realFourierCoeff u (evenFreqZ t.2.1)‖ *
    ‖realFourierCoeff u (evenFreqZ t.2.2)‖

theorem two_mul_sqrt_half_cube_even :
    2 * (√((1 : ℝ) / 2) ^ 3) = √((1 : ℝ) / 2) := by
  have hsq : (√((1 : ℝ) / 2)) ^ 2 = (1 : ℝ) / 2 :=
    Real.sq_sqrt (by norm_num : 0 ≤ (1 : ℝ) / 2)
  nlinarith [Real.sqrt_nonneg ((1 : ℝ) / 2)]

theorem sum_evenOrientation {β : Type*} [AddCommMonoid β]
    (F : EvenOrientation → β) :
    ∑ o : EvenOrientation, F o = F EvenOrientation.base + F EvenOrientation.conj := by
  rw [show (Finset.univ : Finset EvenOrientation) =
      {EvenOrientation.base, EvenOrientation.conj} by
    ext o
    cases o <;> simp]
  simp

@[simp]
theorem card_evenSlot : Fintype.card EvenSlot = 3 := by
  decide

def evenOrdCoreWeight {m : ℕ} (a : Fin m → ℝ) (c : EvenUDomain m) : ℝ :=
  a c.1.val *
    (a ⟨c.2.val, by omega⟩ *
      a ⟨c.1.val.val - 1 - c.2.val, by omega⟩)

def evenWrapCoreWeight {m : ℕ} (a : Fin m → ℝ) (c : EvenVDomain m) : ℝ :=
  a c.1.val *
    (a ⟨m - c.1.val.val - 1 + c.2.val, by
        have hr0 : c.1.val.val ≠ 0 := c.1.property.1
        have hrlast : c.1.val.val ≠ m - 1 := c.1.property.2
        omega⟩ *
      a ⟨m - 2 - c.2.val, by
        have hr0 : c.1.val.val ≠ 0 := c.1.property.1
        have hrlast : c.1.val.val ≠ m - 1 := c.1.property.2
        omega⟩)

def evenMiddleCoreWeight {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℝ)
    (t : EvenMDomain m) : ℝ :=
  a ⟨m - 1, by omega⟩ *
    (a ⟨t.val, by omega⟩ * a ⟨m - 2 - t.val, by omega⟩)

theorem evenOrdCoreWeight_sum_eq {m : ℕ} (a : Fin m → ℝ) :
    (∑ c : EvenUDomain m, evenOrdCoreWeight a c) =
      ∑ r : EvenOrdinaryIndex m, a r.val * evenL a r.val := by
  simpa [EvenUDomain, evenOrdCoreWeight, evenL, Finset.mul_sum, mul_assoc] using
    (Fintype.sum_sigma'
      (f := fun (r : EvenOrdinaryIndex m) (t : Fin r.val.val) ↦
        a r.val *
          (a ⟨t.val, by omega⟩ *
            a ⟨r.val.val - 1 - t.val, by omega⟩)))

theorem evenWrapCoreWeight_sum_eq {m : ℕ} (a : Fin m → ℝ) :
    (∑ c : EvenVDomain m, evenWrapCoreWeight a c) =
      ∑ r : EvenOrdinaryIndex m, a r.val * evenR a r.val := by
  simpa [EvenVDomain, evenWrapCoreWeight, evenR, Finset.mul_sum, mul_assoc] using
    (Fintype.sum_sigma'
      (f := fun (r : EvenOrdinaryIndex m) (t : Fin r.val.val) ↦
        a r.val *
          (a ⟨m - r.val.val - 1 + t.val, by
              have hr0 : r.val.val ≠ 0 := r.property.1
              have hrlast : r.val.val ≠ m - 1 := r.property.2
              omega⟩ *
            a ⟨m - 2 - t.val, by
              have hr0 : r.val.val ≠ 0 := r.property.1
              have hrlast : r.val.val ≠ m - 1 := r.property.2
              omega⟩)))

theorem evenMiddleCoreWeight_sum_eq {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℝ) :
    (∑ t : EvenMDomain m, evenMiddleCoreWeight hm a t) =
      a ⟨m - 1, by omega⟩ * evenLm a := by
  simp [EvenMDomain, evenMiddleCoreWeight, evenLm, Finset.mul_sum]

theorem even_ord_resonance_sum_eq {m : ℕ} [NeZero (2 * m)] (hm : 2 ≤ m)
    (u : ZMod (2 * m) → ℝ) :
    (∑ d : EvenOrdDomain m, evenTripleNormWeight u (evenOrdTriple d)) =
      3 * √((1 : ℝ) / 2) *
        ∑ r : EvenOrdinaryIndex m,
          evenFourierAmp (m := m) u r.val * evenL (evenFourierAmp (m := m) u) r.val := by
  classical
  let a : Fin m → ℝ := evenFourierAmp (m := m) u
  let q : ℝ := √((1 : ℝ) / 2)
  unfold EvenOrdDomain
  calc
    (∑ d : EvenOrientation × EvenSlot × EvenUDomain m,
        evenTripleNormWeight u (evenOrdTriple d))
        = ∑ y : EvenSlot × EvenUDomain m,
            2 * q ^ 3 * evenOrdCoreWeight a y.2 := by
          rw [Fintype.sum_prod_type_right]
          apply Finset.sum_congr rfl
          intro y _
          cases y with
          | mk slot c =>
            cases c with
            | mk r t =>
              rw [sum_evenOrientation]
              cases slot <;>
                simp [evenOrdTriple, evenOrientTriple, evenFlipTriple, evenFlipFreq,
                  evenOrdCoreTriple, evenPlaceOrd, evenOrdCoreWeight, evenTripleNormWeight,
                  norm_evenFreq_pos_eq_sqrt_half_mul_amp (m := m) hm u,
                  norm_evenFreq_neg_eq_sqrt_half_mul_amp (m := m) hm u, q, a] <;>
                ring_nf
    _ = 3 * q * ∑ c : EvenUDomain m, evenOrdCoreWeight a c := by
          rw [Fintype.sum_prod_type_right]
          calc
            (∑ y : EvenUDomain m, ∑ x : EvenSlot,
                2 * q ^ 3 * evenOrdCoreWeight a (x, y).2)
                = ∑ y : EvenUDomain m, 3 * q * evenOrdCoreWeight a y := by
                    apply Finset.sum_congr rfl
                    intro c _
                    have hq : 2 * q ^ 3 = q := by
                      simpa [q] using two_mul_sqrt_half_cube_even
                    simp [hq]
                    ring
            _ = 3 * q * ∑ c : EvenUDomain m, evenOrdCoreWeight a c := by
                  rw [Finset.mul_sum]
    _ = 3 * √((1 : ℝ) / 2) *
        ∑ r : EvenOrdinaryIndex m,
          evenFourierAmp (m := m) u r.val * evenL (evenFourierAmp (m := m) u) r.val := by
          rw [evenOrdCoreWeight_sum_eq]

theorem even_wrap_resonance_sum_eq {m : ℕ} [NeZero (2 * m)] (hm : 2 ≤ m)
    (u : ZMod (2 * m) → ℝ) :
    (∑ d : EvenWrapResDomain m, evenTripleNormWeight u (evenWrapTriple d)) =
      √((1 : ℝ) / 2) *
        ∑ r : EvenOrdinaryIndex m,
          evenFourierAmp (m := m) u r.val * evenR (evenFourierAmp (m := m) u) r.val := by
  classical
  let a : Fin m → ℝ := evenFourierAmp (m := m) u
  let q : ℝ := √((1 : ℝ) / 2)
  unfold EvenWrapResDomain
  calc
    (∑ d : EvenOrientation × EvenVDomain m,
        evenTripleNormWeight u (evenWrapTriple d))
        = ∑ c : EvenVDomain m, 2 * q ^ 3 * evenWrapCoreWeight a c := by
          rw [Fintype.sum_prod_type_right]
          apply Finset.sum_congr rfl
          intro c _
          cases c with
          | mk r t =>
            rw [sum_evenOrientation]
            simp [evenWrapTriple, evenOrientTriple, evenFlipTriple, evenFlipFreq,
              evenWrapCoreTriple, evenWrapCoreWeight, evenTripleNormWeight,
              norm_evenFreq_pos_eq_sqrt_half_mul_amp (m := m) hm u,
              norm_evenFreq_neg_eq_sqrt_half_mul_amp (m := m) hm u, q, a]
            ring_nf
    _ = q * ∑ c : EvenVDomain m, evenWrapCoreWeight a c := by
          calc
            (∑ c : EvenVDomain m, 2 * q ^ 3 * evenWrapCoreWeight a c)
                = ∑ c : EvenVDomain m, q * evenWrapCoreWeight a c := by
                    apply Finset.sum_congr rfl
                    intro c _
                    have hq : 2 * q ^ 3 = q := by
                      simpa [q] using two_mul_sqrt_half_cube_even
                    rw [hq]
            _ = q * ∑ c : EvenVDomain m, evenWrapCoreWeight a c := by
                  rw [Finset.mul_sum]
    _ = √((1 : ℝ) / 2) *
        ∑ r : EvenOrdinaryIndex m,
          evenFourierAmp (m := m) u r.val * evenR (evenFourierAmp (m := m) u) r.val := by
          rw [evenWrapCoreWeight_sum_eq]

theorem even_middle_resonance_sum_eq {m : ℕ} [NeZero (2 * m)] (hm : 2 ≤ m)
    (u : ZMod (2 * m) → ℝ) :
    (∑ d : EvenMiddleResDomain m, evenTripleNormWeight u (evenMiddleTriple d)) =
      3 * evenFourierAmp (m := m) u ⟨m - 1, by omega⟩ *
        evenLm (evenFourierAmp (m := m) u) := by
  classical
  let a : Fin m → ℝ := evenFourierAmp (m := m) u
  unfold EvenMiddleResDomain
  calc
    (∑ d : EvenOrientation × EvenSlot × EvenMDomain m,
        evenTripleNormWeight u (evenMiddleTriple d))
        = ∑ y : EvenSlot × EvenMDomain m, evenMiddleCoreWeight hm a y.2 := by
          rw [Fintype.sum_prod_type_right]
          apply Finset.sum_congr rfl
          intro y _
          cases y with
          | mk slot t =>
            rw [sum_evenOrientation]
            cases slot
            · simp only [evenMiddleTriple, evenOrientTriple, evenFlipTriple, evenFlipFreq,
                evenMiddleCoreTriple, evenPlaceMiddle, evenMiddleCoreWeight,
                evenTripleNormWeight,
                norm_evenFreq_pos_eq_sqrt_half_mul_amp (m := m) hm u,
                norm_evenFreq_neg_eq_sqrt_half_mul_amp (m := m) hm u,
                norm_evenFreq_mid_eq_amp (m := m) hm u, a]
              ring_nf
              simp [mul_comm, mul_assoc]
            · simp only [evenMiddleTriple, evenOrientTriple, evenFlipTriple, evenFlipFreq,
                evenMiddleCoreTriple, evenPlaceMiddle, evenMiddleCoreWeight,
                evenTripleNormWeight,
                norm_evenFreq_pos_eq_sqrt_half_mul_amp (m := m) hm u,
                norm_evenFreq_neg_eq_sqrt_half_mul_amp (m := m) hm u,
                norm_evenFreq_mid_eq_amp (m := m) hm u, a]
              ring_nf
              simp [mul_comm, mul_left_comm, mul_assoc]
            · simp only [evenMiddleTriple, evenOrientTriple, evenFlipTriple, evenFlipFreq,
                evenMiddleCoreTriple, evenPlaceMiddle, evenMiddleCoreWeight,
                evenTripleNormWeight,
                norm_evenFreq_pos_eq_sqrt_half_mul_amp (m := m) hm u,
                norm_evenFreq_neg_eq_sqrt_half_mul_amp (m := m) hm u,
                norm_evenFreq_mid_eq_amp (m := m) hm u, a]
              ring_nf
              simp [mul_comm, mul_left_comm, mul_assoc]
    _ = 3 * ∑ t : EvenMDomain m, evenMiddleCoreWeight hm a t := by
          rw [Fintype.sum_prod_type_right]
          calc
            (∑ y : EvenMDomain m, ∑ x : EvenSlot, evenMiddleCoreWeight hm a (x, y).2)
                = ∑ y : EvenMDomain m, 3 * evenMiddleCoreWeight hm a y := by
                    apply Finset.sum_congr rfl
                    intro t _
                    rw [show (Finset.univ : Finset EvenSlot) =
                        {EvenSlot.fst, EvenSlot.snd, EvenSlot.thd} by
                      ext slot
                      cases slot <;> simp]
                    simp
            _ = 3 * ∑ t : EvenMDomain m, evenMiddleCoreWeight hm a t := by
                  rw [Finset.mul_sum]
    _ = 3 * evenFourierAmp (m := m) u ⟨m - 1, by omega⟩ *
        evenLm (evenFourierAmp (m := m) u) := by
          rw [evenMiddleCoreWeight_sum_eq hm]
          ring

theorem even_resonance_domain_sum_eq_cauchy_moment {m : ℕ} [NeZero (2 * m)]
    (hm : 2 ≤ m) (u : ZMod (2 * m) → ℝ) :
    (∑ d : EvenResonanceDomain m, evenTripleNormWeight u (evenResonanceTriple d)) =
      evenCauchyMoment hm (evenFourierAmp (m := m) u) := by
  classical
  let a : Fin m → ℝ := evenFourierAmp (m := m) u
  calc
    (∑ d : EvenResonanceDomain m, evenTripleNormWeight u (evenResonanceTriple d))
        = ((∑ d : EvenOrdDomain m, evenTripleNormWeight u (evenOrdTriple d)) +
            ∑ d : EvenWrapResDomain m, evenTripleNormWeight u (evenWrapTriple d)) +
            ∑ d : EvenMiddleResDomain m, evenTripleNormWeight u (evenMiddleTriple d) := by
          simp [EvenResonanceDomain, evenResonanceTriple, Fintype.sum_sum_type]
    _ = (3 * √((1 : ℝ) / 2) *
          ∑ r : EvenOrdinaryIndex m, a r.val * evenL a r.val +
            √((1 : ℝ) / 2) *
              ∑ r : EvenOrdinaryIndex m, a r.val * evenR a r.val) +
          3 * a ⟨m - 1, by omega⟩ * evenLm a := by
          simp [a, even_ord_resonance_sum_eq hm, even_wrap_resonance_sum_eq hm,
            even_middle_resonance_sum_eq hm]
    _ = evenCauchyMoment hm a := by
          unfold evenCauchyMoment
          simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_comm]
          ring_nf

theorem even_resonance_domain_sum_le_cauchy {m : ℕ} [NeZero (2 * m)]
    (hm : 2 ≤ m) (u : ZMod (2 * m) → ℝ) :
    (∑ d : EvenResonanceDomain m, evenTripleNormWeight u (evenResonanceTriple d)) ≤
      √(blockQsq (evenFourierAmp (m := m) u)) *
        √(evenWeightedSum (evenFourierAmp (m := m) u)) := by
  rw [even_resonance_domain_sum_eq_cauchy_moment hm u]
  exact even_cauchy_moment_le hm (evenFourierAmp (m := m) u)

theorem even_blockQsq_fourierAmp_eq_zmodWordEnergyReal_sub_Ssq {m : ℕ}
    [NeZero (2 * m)] {u : ZMod (2 * m) → ℝ} (hu : MeanZero u) :
    blockQsq (evenFourierAmp (m := m) u) = zmodWordEnergyReal u - Ssq u := by
  rw [even_blockQsq_fourierAmp_eq_zmodFourierQsq hu]
  unfold zmodFourierQsq zmodWordEnergyReal
  rw [zmodFourierSsq_eq_Ssq_real]

end

end CyclicLsi
