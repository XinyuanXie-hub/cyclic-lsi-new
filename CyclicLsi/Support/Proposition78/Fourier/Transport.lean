import CyclicLsi.Support.Proposition78.Fourier.Bridge



/-!
# Transport between `Fin n` and `ZMod n`

The paper is naturally Fourier-analytic on `ZMod n`, while the existing
numbered statements in `MainTheorem.lean` are stated for functions on `Fin n`.
This file provides the finite-equivalence bridge.
-/

namespace CyclicLsi

noncomputable section

open scoped BigOperators

def pullEquiv {α β : Type*} (e : α ≃ β) (u : α → ℝ) : β → ℝ :=
  fun b ↦ u (e.symm b)

abbrev finZModEquiv (n : ℕ) [NeZero n] : Fin n ≃ ZMod n :=
  (ZMod.finEquiv n).toEquiv

def finToZModFun {n : ℕ} [NeZero n] (u : Fin n → ℝ) : ZMod n → ℝ :=
  pullEquiv (finZModEquiv n) u

theorem avg_pullEquiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (u : α → ℝ) :
    avg (pullEquiv e u) = avg u := by
  unfold avg pullEquiv
  rw [Fintype.sum_equiv e.symm]
  · rw [Fintype.card_congr e]
  · intro x
    rfl

theorem Ssq_pullEquiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (u : α → ℝ) :
    Ssq (pullEquiv e u) = Ssq u := by
  unfold Ssq
  rw [show avg (fun b : β ↦ pullEquiv e u b ^ 2) =
      avg (pullEquiv e (fun a : α ↦ u a ^ 2)) by rfl]
  exact avg_pullEquiv e (fun a : α ↦ u a ^ 2)

theorem MeanZero_pullEquiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {u : α → ℝ} (hu : MeanZero u) :
    MeanZero (pullEquiv e u) := by
  unfold MeanZero at hu ⊢
  rw [avg_pullEquiv]
  exact hu

def zmodWordEnergyReal {n : ℕ} [NeZero n] (u : ZMod n → ℝ) : ℝ :=
  zmodFourierEnergy (fun x : ZMod n ↦ (u x : ℂ))

def finWordEnergy : EnergyFamily :=
  fun n u =>
    if h : n = 0 then
      0
    else
      letI : NeZero n := ⟨h⟩
      zmodWordEnergyReal (finToZModFun u)

theorem finWordEnergy_of_ne {n : ℕ} [NeZero n] (u : Fin n → ℝ) :
    finWordEnergy n u = zmodWordEnergyReal (finToZModFun u) := by
  unfold finWordEnergy
  split_ifs with h
  · exact False.elim ((NeZero.ne n) h)
  · rfl

theorem thirdMomentEstimateFor_of_zmod {n : ℕ} [NeZero n]
    {energyZ : (ZMod n → ℝ) → ℝ}
    (hz : ∀ u : ZMod n → ℝ,
      MeanZero u →
        |avg (fun x ↦ u x ^ 3)| ≤
          3 * Ssq u * Real.sqrt (energyZ u - Ssq u)) :
    ThirdMomentEstimateFor n (fun u ↦ energyZ (finToZModFun u)) := by
  intro u hu
  let e : Fin n ≃ ZMod n := finZModEquiv n
  let uz : ZMod n → ℝ := finToZModFun u
  have hmean : MeanZero uz := by
    dsimp [uz, finToZModFun]
    exact MeanZero_pullEquiv e hu
  have hcube :
      avg (fun x : ZMod n ↦ uz x ^ 3) =
        avg (fun x : Fin n ↦ u x ^ 3) := by
    change avg (pullEquiv (finZModEquiv n) (fun a : Fin n ↦ u a ^ 3)) = _
    exact avg_pullEquiv (finZModEquiv n) (fun a : Fin n ↦ u a ^ 3)
  have hS : Ssq uz = Ssq u := by
    dsimp [uz, finToZModFun]
    exact Ssq_pullEquiv e u
  have hz_u := hz uz hmean
  rw [hcube, hS] at hz_u
  exact hz_u

end

end CyclicLsi
