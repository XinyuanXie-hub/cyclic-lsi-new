module
public import CyclicLsi.Support.Basic

/-!
# Cubic majorant

This file contains derivative and monotonicity lemmas supporting the pointwise
Frank--Ivanisvili cubic majorant in `CyclicLsi.Support.CubicMajorant`.
-/

namespace CyclicLsi

@[expose] public noncomputable section

/-- Difference between the cubic majorant and the entropy term. -/
def cubicMajorantGap (t : ℝ) : ℝ :=
  (2 / 3 : ℝ) * ((t - 1) ^ 2 * (t + 2)) + (t ^ 2 - 1) -
    t ^ 2 * Real.log (t ^ 2)

/-- Derivative sign driver for the cubic majorant gap. -/
def cubicMajorantSlope (t : ℝ) : ℝ :=
  t ^ 2 - 1 - 2 * t * Real.log t

lemma hasDerivAt_cubicMajorantGap {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cubicMajorantGap (2 * cubicMajorantSlope x) x := by
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hpoly :
      HasDerivAt
        (fun t : ℝ =>
          (2 / 3 : ℝ) * ((t - 1) ^ 2 * (t + 2)) + (t ^ 2 - 1))
        (2 * x ^ 2 + 2 * x - 2) x := by
    have h :=
      (((((hasDerivAt_id x).sub_const 1).pow 2).mul
          ((hasDerivAt_id x).add_const 2)).const_mul (2 / 3)).add
        (((hasDerivAt_id x).pow 2).sub_const 1)
    convert h using 1 <;> first | rfl | (dsimp; ring)
  have hlogsq : HasDerivAt (fun t : ℝ => Real.log (t ^ 2)) (2 / x) x := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      simpa using! (hasDerivAt_id x).pow 2
    have h := hpow.log hx2
    convert h using 1
    field_simp [hx]
  have hmul :
      HasDerivAt (fun t : ℝ => t ^ 2 * Real.log (t ^ 2))
        (2 * x * Real.log (x ^ 2) + x ^ 2 * (2 / x)) x := by
    exact
      ((by simpa using! (hasDerivAt_id x).pow 2) :
          HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x).mul hlogsq
  unfold cubicMajorantGap cubicMajorantSlope
  convert hpoly.sub hmul using 1
  rw [Real.log_pow]
  field_simp [hx]
  ring_nf

lemma deriv_cubicMajorantGap {x : ℝ} (hx : x ≠ 0) :
    deriv cubicMajorantGap x = 2 * cubicMajorantSlope x :=
  (hasDerivAt_cubicMajorantGap hx).deriv

lemma hasDerivAt_cubicMajorantSlope {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cubicMajorantSlope (2 * (x - 1 - Real.log x)) x := by
  unfold cubicMajorantSlope
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx
  have hmul : HasDerivAt (fun t : ℝ => 2 * t * Real.log t)
      (2 * Real.log x + 2 * x * x⁻¹) x := by
    have h := (((hasDerivAt_id x).const_mul 2).mul hlog)
    convert h using 1 <;> first | rfl | simp
  have hpoly : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).sub_const 1
  convert hpoly.sub hmul using 1
  field_simp [hx]
  ring

lemma deriv_cubicMajorantSlope {x : ℝ} (hx : x ≠ 0) :
    deriv cubicMajorantSlope x = 2 * (x - 1 - Real.log x) :=
  (hasDerivAt_cubicMajorantSlope hx).deriv

lemma cubicMajorantSlope_monotoneOn_pos :
    MonotoneOn cubicMajorantSlope (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn cubicMajorantSlope (Set.Ioi (0 : ℝ)) :=
    HasDerivAt.continuousOn fun x hx =>
      hasDerivAt_cubicMajorantSlope (by exact (ne_of_gt hx))
  have hdiff : DifferentiableOn ℝ cubicMajorantSlope (interior (Set.Ioi (0 : ℝ))) := by
    intro x hx
    have hxpos : 0 < x := by simpa [interior_Ioi] using hx
    exact (hasDerivAt_cubicMajorantSlope hxpos.ne').differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ)) hcont hdiff ?_
  intro x hx
  have hxpos : 0 < x := by simpa [interior_Ioi] using hx
  rw [deriv_cubicMajorantSlope hxpos.ne']
  have hlog := Real.log_le_sub_one_of_pos hxpos
  nlinarith

lemma cubicMajorantSlope_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ cubicMajorantSlope x := by
  have hmono := cubicMajorantSlope_monotoneOn_pos
  have h :=
    hmono (by norm_num : (1 : ℝ) ∈ Set.Ioi (0 : ℝ))
      (by exact lt_of_lt_of_le zero_lt_one hx) hx
  simpa [cubicMajorantSlope] using h

lemma cubicMajorantSlope_nonpos_of_le_one {x : ℝ} (hxpos : 0 < x) (hx : x ≤ 1) :
    cubicMajorantSlope x ≤ 0 := by
  have hmono := cubicMajorantSlope_monotoneOn_pos
  have h :=
    hmono (by exact hxpos) (by norm_num : (1 : ℝ) ∈ Set.Ioi (0 : ℝ)) hx
  simpa [cubicMajorantSlope] using h

lemma cubicMajorantGap_monotoneOn_one :
    MonotoneOn cubicMajorantGap (Set.Ici (1 : ℝ)) := by
  have hcont : ContinuousOn cubicMajorantGap (Set.Ici (1 : ℝ)) :=
    HasDerivAt.continuousOn fun x hx =>
      hasDerivAt_cubicMajorantGap (by exact (ne_of_gt (zero_lt_one.trans_le hx)))
  have hdiff : DifferentiableOn ℝ cubicMajorantGap (interior (Set.Ici (1 : ℝ))) := by
    intro x hx
    have hxpos : 0 < x := by
      have hx1 : 1 < x := by simpa [interior_Ici] using hx
      exact zero_lt_one.trans hx1
    exact (hasDerivAt_cubicMajorantGap hxpos.ne').differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Ici (1 : ℝ)) hcont hdiff ?_
  intro x hx
  have hx1 : 1 < x := by simpa [interior_Ici] using hx
  rw [deriv_cubicMajorantGap (by exact (zero_lt_one.trans hx1).ne')]
  exact mul_nonneg (by norm_num) (cubicMajorantSlope_nonneg_of_one_le hx1.le)

lemma cubicMajorantGap_antitoneOn_zero_one :
    AntitoneOn cubicMajorantGap (Set.Ioc (0 : ℝ) 1) := by
  have hcont : ContinuousOn cubicMajorantGap (Set.Ioc (0 : ℝ) 1) :=
    HasDerivAt.continuousOn fun x hx =>
      hasDerivAt_cubicMajorantGap (by exact (ne_of_gt hx.1))
  have hdiff : DifferentiableOn ℝ cubicMajorantGap (interior (Set.Ioc (0 : ℝ) 1)) := by
    intro x hx
    have hxioo : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioc] using hx
    exact (hasDerivAt_cubicMajorantGap hxioo.1.ne').differentiableAt.differentiableWithinAt
  refine antitoneOn_of_deriv_nonpos (convex_Ioc (0 : ℝ) 1) hcont hdiff ?_
  intro x hx
  have hxioo : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ioc] using hx
  rw [deriv_cubicMajorantGap hxioo.1.ne']
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    (cubicMajorantSlope_nonpos_of_le_one hxioo.1 hxioo.2.le)

lemma cubicMajorantGap_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ cubicMajorantGap t := by
  rcases ht.eq_or_lt with rfl | htpos
  · norm_num [cubicMajorantGap]
  · by_cases ht_le_one : t ≤ 1
    · have hanti := cubicMajorantGap_antitoneOn_zero_one
      have h :=
        hanti (by exact ⟨htpos, ht_le_one⟩)
          (by exact ⟨zero_lt_one, le_rfl⟩) ht_le_one
      have hgap1 : cubicMajorantGap 1 = 0 := by norm_num [cubicMajorantGap]
      linarith
    · have ht_one : 1 ≤ t := by linarith
      have hmono := cubicMajorantGap_monotoneOn_one
      have h1mem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := by
        exact (show (1 : ℝ) ≤ 1 from le_rfl)
      have htmem : t ∈ Set.Ici (1 : ℝ) := ht_one
      have h := hmono h1mem htmem ht_one
      have hgap1 : cubicMajorantGap 1 = 0 := by norm_num [cubicMajorantGap]
      linarith

end

end CyclicLsi
