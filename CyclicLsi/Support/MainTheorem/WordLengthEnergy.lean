import CyclicLsi.Support.Proposition6.Lemmas
import CyclicLsi.Support.Proposition7.Lemmas
import CyclicLsi.Support.Proposition78.OddCase.Proof
import CyclicLsi.Support.Proposition78.EvenCase.Proof


/-!
# Concrete word-length energy facts

This file closes the concrete facts about the Fourier word-length energy that
the paper uses implicitly in Propositions 5 and 6: quadratic homogeneity,
invariance under centering, and nonnegativity of the surplus `Qsq`.
-/

namespace CyclicLsi

noncomputable section

open scoped BigOperators

lemma fourierCoeff_real_smul {n : ℕ} [NeZero n]
    (c : ℝ) (u : ZMod n → ℝ) (k : ZMod n) :
    fourierCoeff (fun x : ZMod n => ((c * u x : ℝ) : ℂ)) k =
      (c : ℂ) * fourierCoeff (fun x : ZMod n => (u x : ℂ)) k := by
  unfold fourierCoeff
  have hcast : (fun x : ZMod n => ((c * u x : ℝ) : ℂ)) =
      fun x : ZMod n => (c : ℂ) * (u x : ℂ) := by
    funext x
    norm_num
  rw [hcast, ZMod.dft_const_mul]
  ring

lemma zmodWordEnergyReal_smul {n : ℕ} [NeZero n]
    (c : ℝ) (u : ZMod n → ℝ) :
    zmodWordEnergyReal (fun x => c * u x) = c ^ 2 * zmodWordEnergyReal u := by
  unfold zmodWordEnergyReal zmodFourierEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [fourierCoeff_real_smul]
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem finWordEnergy_quadraticHomogeneous_ge4 {n : ℕ} (hn : 4 ≤ n) :
    QuadraticHomogeneous (finWordEnergy n) := by
  intro c u
  haveI : NeZero n := ⟨by omega⟩
  rw [finWordEnergy_of_ne, finWordEnergy_of_ne]
  change zmodWordEnergyReal (finToZModFun (fun x : Fin n => c * u x)) =
    c ^ 2 * zmodWordEnergyReal (finToZModFun u)
  have hfun : finToZModFun (fun x : Fin n => c * u x) =
      fun z => c * finToZModFun u z := by
    rfl
  rw [hfun, zmodWordEnergyReal_smul]

lemma fourierCoeff_const_ne_zero {n : ℕ} [NeZero n]
    (c : ℂ) {k : ZMod n} (hk : k ≠ 0) :
    fourierCoeff (fun _ : ZMod n => c) k = 0 := by
  unfold fourierCoeff
  simp only [ZMod.dft_apply, smul_eq_mul]
  rw [← Finset.sum_mul]
  have hsum : (∑ x : ZMod n, ZMod.stdAddChar (-(x * k))) = 0 := by
    have h := sum_stdAddChar_mul (-k)
    simpa [hk, mul_comm, neg_mul] using h
  rw [hsum]
  ring

lemma fourierCoeff_sub_const_ne_zero {n : ℕ} [NeZero n]
    (u : ZMod n → ℝ) (c : ℝ) {k : ZMod n} (hk : k ≠ 0) :
    fourierCoeff (fun x : ZMod n => ((u x - c : ℝ) : ℂ)) k =
      fourierCoeff (fun x : ZMod n => (u x : ℂ)) k := by
  unfold fourierCoeff
  have hcast : (fun x : ZMod n => ((u x - c : ℝ) : ℂ)) =
      fun x : ZMod n => (u x : ℂ) - (c : ℂ) := by
    funext x
    norm_num
  rw [hcast]
  have hdft : ZMod.dft (fun x : ZMod n => (u x : ℂ) - (c : ℂ)) k =
      ZMod.dft (fun x : ZMod n => (u x : ℂ)) k -
        ZMod.dft (fun _ : ZMod n => (c : ℂ)) k := by
    exact congrFun
      (map_sub ZMod.dft (fun x : ZMod n => (u x : ℂ)) (fun _ : ZMod n => (c : ℂ))) k
  rw [hdft]
  have hc := fourierCoeff_const_ne_zero (n := n) (c := (c : ℂ)) hk
  unfold fourierCoeff at hc
  rw [mul_sub, hc, sub_zero]

lemma zmodWordEnergyReal_sub_const {n : ℕ} [NeZero n]
    (u : ZMod n → ℝ) (c : ℝ) :
    zmodWordEnergyReal (fun x => u x - c) = zmodWordEnergyReal u := by
  unfold zmodWordEnergyReal zmodFourierEnergy
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · subst hk
    simp [zmodWordLength]
  · rw [fourierCoeff_sub_const_ne_zero (u := u) (c := c) hk]

theorem finWordEnergy_centered_ge4 {n : ℕ} (hn : 4 ≤ n) (x : Fin n → ℝ) :
    finWordEnergy n x = finWordEnergy n (centered x) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [finWordEnergy_of_ne, finWordEnergy_of_ne]
  change zmodWordEnergyReal (finToZModFun x) =
    zmodWordEnergyReal (finToZModFun (centered x))
  have hcenter : finToZModFun (centered x) =
      fun z : ZMod n => finToZModFun x z - avg x := by
    rfl
  rw [hcenter, zmodWordEnergyReal_sub_const]

theorem finWordEnergy_qsq_nonneg_ge4 {n : ℕ} (hn : 4 ≤ n)
    (u : Fin n → ℝ) (hu : MeanZero u) :
    0 ≤ Qsq (finWordEnergy n) u := by
  rcases Nat.even_or_odd' n with ⟨m, h | h⟩
  · subst h
    have hm : 2 ≤ m := by omega
    haveI : NeZero (2 * m) := ⟨by omega⟩
    let uz : ZMod (2 * m) → ℝ := finToZModFun u
    have hmean : MeanZero uz := by
      dsimp [uz, finToZModFun]
      exact MeanZero_pullEquiv (finZModEquiv (2 * m)) hu
    have hQz : 0 ≤ zmodWordEnergyReal uz - Ssq uz := by
      let a : Fin m → ℝ := evenFourierAmp (m := m) uz
      have hEq : blockQsq a = zmodWordEnergyReal uz - Ssq uz := by
        simpa [a] using even_blockQsq_fourierAmp_eq_zmodWordEnergyReal_sub_Ssq
          (m := m) (u := uz) hmean
      have hNon : 0 ≤ blockQsq a := blockQsq_nonneg a
      linarith
    have hS : Ssq uz = Ssq u := by
      dsimp [uz, finToZModFun]
      exact Ssq_pullEquiv (finZModEquiv (2 * m)) u
    simpa [Qsq, finWordEnergy_of_ne, uz, hS] using hQz
  · subst h
    have hm : 2 ≤ m := by omega
    haveI : NeZero (2 * m + 1) := ⟨by omega⟩
    let uz : ZMod (2 * m + 1) → ℝ := finToZModFun u
    have hmean : MeanZero uz := by
      dsimp [uz, finToZModFun]
      exact MeanZero_pullEquiv (finZModEquiv (2 * m + 1)) hu
    have hQz : 0 ≤ zmodWordEnergyReal uz - Ssq uz := by
      let a : Fin m → ℝ := oddFourierAmp m uz
      have hEq : blockQsq a = zmodWordEnergyReal uz - Ssq uz := by
        simpa [a] using odd_blockQsq_fourierAmp_eq_zmodWordEnergyReal_sub_Ssq
          (m := m) (u := uz) hmean
      have hNon : 0 ≤ blockQsq a := blockQsq_nonneg a
      linarith
    have hS : Ssq uz = Ssq u := by
      dsimp [uz, finToZModFun]
      exact Ssq_pullEquiv (finZModEquiv (2 * m + 1)) u
    simpa [Qsq, finWordEnergy_of_ne, uz, hS] using hQz

end

end CyclicLsi
