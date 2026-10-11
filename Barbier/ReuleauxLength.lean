import Barbier.Reuleaux
import Barbier.ArclenFinite

noncomputable section

namespace Barbier

open Real MeasureTheory intervalIntegral Set eVariationOn ENNReal Complex

/-! ### Helper: HasDerivAt for cos(θ - c) -/

private lemma hasDerivAt_cos_sub' (c θ₀ : ℝ) :
    HasDerivAt (fun θ => Real.cos (θ - c)) (-Real.sin (θ₀ - c)) θ₀ := by
  have h1 : HasDerivAt (fun θ => θ - c) 1 θ₀ :=
    ((hasDerivAt_id θ₀).sub (hasDerivAt_const θ₀ c)).congr_deriv (by ring)
  have h2 := (Real.hasDerivAt_cos (θ₀ - c)).comp θ₀ h1
  simp only [Function.comp_def, mul_one] at h2
  exact h2

-- Helper: exp(-iα) = cos α - sin α * I  (for real α)
private lemma exp_neg_mul_I (α : ℝ) :
    Complex.exp (-(↑α * I)) = ↑(Real.cos α) - ↑(Real.sin α) * I := by
  rw [show -(↑α * I : ℂ) = ↑(-α) * I by push_cast; ring, Complex.exp_mul_I]
  push_cast; simp [Complex.cos_neg, Complex.sin_neg]; ring

/-! ### Continuity of curve (reuleaux w) -/

private lemma continuous_curve_reuleaux {w : ℝ} (hw : 0 < w) :
    Continuous (curve (reuleaux w)) := by
  have hsmooth : ContDiff ℝ 1 (reuleaux w) := (reuleaux_constWidth hw).smooth
  show Continuous (fun θ => ((reuleaux w θ : ℂ) + ((deriv (reuleaux w) θ : ℝ) : ℂ) * I) *
      Complex.exp ((θ : ℂ) * I))
  apply Continuous.mul
  · apply Continuous.add
    · exact Complex.ofRealCLM.continuous.comp hsmooth.continuous
    · exact (Complex.ofRealCLM.continuous.comp hsmooth.continuous_deriv_one).mul continuous_const
  · exact (Complex.ofRealCLM.continuous.comp continuous_id |>.mul continuous_const).cexp

/-! ### Corner pieces: curve is constant -/

private lemma corner_eqOn_Ioo (w : ℝ) (k : ℤ) :
    EqOn (curve (reuleaux w))
      (fun _ => ↑(w / Real.sqrt 3) * exp (↑((k : ℝ) * (2 * π / 3)) * I))
      (Set.Ioo (-(π / 6) + (k : ℝ) * (2 * π / 3)) (π / 6 + (k : ℝ) * (2 * π / 3))) := by
  intro θ ⟨hlo, hhi⟩
  have hmod : toIcoMod reuleaux_period_pos (-(π / 6)) θ = θ - (k : ℝ) * (2 * π / 3) := by
    rw [toIcoMod_eq_iff]
    exact ⟨⟨by linarith, by linarith [Real.pi_pos]⟩, k,
           by simp only [zsmul_eq_mul]; push_cast; ring⟩
  have hval : reuleaux w θ = (w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * π / 3)) := by
    simp only [reuleaux, reuleauxPiece, hmod]; rw [if_pos]; linarith
  have hev : reuleaux w =ᶠ[nhds θ]
      (fun θ' => (w / Real.sqrt 3) * Real.cos (θ' - (k : ℝ) * (2 * π / 3))) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hlo hhi) fun θ' ⟨hlo', hhi'⟩ => by
      have hmod' : toIcoMod reuleaux_period_pos (-(π / 6)) θ' = θ' - (k : ℝ) * (2 * π / 3) := by
        rw [toIcoMod_eq_iff]
        exact ⟨⟨by linarith, by linarith [Real.pi_pos]⟩, k,
               by simp only [zsmul_eq_mul]; push_cast; ring⟩
      simp only [reuleaux, reuleauxPiece, hmod']; rw [if_pos]; linarith
  have hder : deriv (reuleaux w) θ = -(w / Real.sqrt 3) * Real.sin (θ - (k : ℝ) * (2 * π / 3)) := by
    rw [hev.deriv_eq]
    have hd := (hasDerivAt_cos_sub' ((k : ℝ) * (2 * π / 3)) θ).const_mul (w / Real.sqrt 3)
    rw [hd.deriv]; ring
  simp only [curve, hval, hder]
  set α := θ - (k : ℝ) * (2 * π / 3)
  set β := (k : ℝ) * (2 * π / 3)
  have hθ : θ = α + β := by simp [α, β]
  have hkey : (Complex.cos ↑α - Complex.sin ↑α * I) * Complex.exp (I * ↑θ) =
      Complex.exp (I * ↑β) := by
    rw [show Complex.cos ↑α - Complex.sin ↑α * I = Complex.exp (-(↑α * I)) from by
      rw [exp_neg_mul_I]; push_cast; ring]
    rw [← Complex.exp_add]
    congr 1
    push_cast [hθ]; ring
  push_cast
  ring_nf
  rw [show ↑w * (↑(Real.sqrt 3))⁻¹ * Complex.cos ↑α * Complex.exp (I * ↑θ) -
      ↑w * (↑(Real.sqrt 3))⁻¹ * Complex.sin ↑α * I * Complex.exp (I * ↑θ) =
      ↑w * (↑(Real.sqrt 3))⁻¹ * ((Complex.cos ↑α - Complex.sin ↑α * I) * Complex.exp (I * ↑θ)) by ring]
  rw [hkey]

private lemma corner_eqOn_Icc {w : ℝ} (hw : 0 < w) (k : ℤ) :
    EqOn (curve (reuleaux w))
      (fun _ => ↑(w / Real.sqrt 3) * exp (↑((k : ℝ) * (2 * π / 3)) * I))
      (Set.Icc (-(π / 6) + (k : ℝ) * (2 * π / 3)) (π / 6 + (k : ℝ) * (2 * π / 3))) :=
  (corner_eqOn_Ioo w k).of_subset_closure
    (continuous_curve_reuleaux hw).continuousOn continuousOn_const
    Ioo_subset_Icc_self
    (by rw [closure_Ioo (by linarith [Real.pi_pos] : -(π / 6) + (k : ℝ) * (2 * π / 3) ≠
        π / 6 + (k : ℝ) * (2 * π / 3))])

/-! ### eVariationOn on corner pieces is zero -/

private lemma eVariationOn_corner_zero {w : ℝ} (hw : 0 < w) (k : ℤ) :
    eVariationOn (curve (reuleaux w))
      (Set.Icc (-(π / 6) + (k : ℝ) * (2 * π / 3)) (π / 6 + (k : ℝ) * (2 * π / 3))) = 0 := by
  rw [eVariationOn.congr (corner_eqOn_Icc hw k)]
  apply eVariationOn.constant_on
  rw [(Set.nonempty_Icc.mpr (by linarith [Real.pi_pos] :
      -(π / 6) + (k : ℝ) * (2 * π / 3) ≤ π / 6 + (k : ℝ) * (2 * π / 3))).image_const]
  exact Set.subsingleton_singleton

/-! ### Arc pieces -/

private lemma arc_toIcoMod {k : ℤ} {θ : ℝ}
    (hlo : π / 6 + (k : ℝ) * (2 * π / 3) < θ) (hhi : θ < π / 2 + (k : ℝ) * (2 * π / 3)) :
    toIcoMod reuleaux_period_pos (-(π / 6)) θ = θ - (k : ℝ) * (2 * π / 3) := by
  rw [toIcoMod_eq_iff]
  exact ⟨⟨by linarith, by linarith [Real.pi_pos]⟩, k, by simp only [zsmul_eq_mul]; push_cast; ring⟩

private lemma reuleaux_arc_val {k : ℤ} {θ : ℝ}
    (hlo : π / 6 + (k : ℝ) * (2 * π / 3) < θ) (hhi : θ < π / 2 + (k : ℝ) * (2 * π / 3))
    (w : ℝ) :
    reuleaux w θ = w - (w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * π / 3) - π / 3) := by
  simp only [reuleaux, reuleauxPiece, arc_toIcoMod hlo hhi]
  rw [if_neg (by linarith)]

-- curve(reuleaux w)(θ) = w*exp(iθ) - (w/√3)*exp(i*(k*2π/3 + π/3)) on arc piece
private lemma arc_eqOn_Ioo {w : ℝ} (hw : 0 < w) (k : ℤ) :
    EqOn (curve (reuleaux w))
      (fun θ => ↑w * exp (↑θ * I) - ↑(w / Real.sqrt 3) * exp (↑((k : ℝ) * (2 * π / 3) + π / 3) * I))
      (Set.Ioo (π / 6 + (k : ℝ) * (2 * π / 3)) (π / 2 + (k : ℝ) * (2 * π / 3))) := by
  intro θ ⟨hlo, hhi⟩
  have hev : reuleaux w =ᶠ[nhds θ]
      (fun θ' => w - (w / Real.sqrt 3) * Real.cos (θ' - (k : ℝ) * (2 * π / 3) - π / 3)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hlo hhi) fun θ' ⟨hlo', hhi'⟩ =>
      reuleaux_arc_val hlo' hhi' w
  have hval := reuleaux_arc_val hlo hhi w
  have hderiv : deriv (reuleaux w) θ =
      (w / Real.sqrt 3) * Real.sin (θ - (k : ℝ) * (2 * π / 3) - π / 3) := by
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun θ' => Real.cos (θ' - (k : ℝ) * (2 * π / 3) - π / 3))
        (-Real.sin (θ - (k : ℝ) * (2 * π / 3) - π / 3)) θ := by
      have h := (hasDerivAt_cos_sub' ((k : ℝ) * (2 * π / 3) + π / 3) θ)
      simp only [show ∀ x : ℝ, x - ((k : ℝ) * (2 * π / 3) + π / 3) =
          x - (k : ℝ) * (2 * π / 3) - π / 3 from fun x => by ring] at h
      exact h
    have hd := ((hasDerivAt_const θ w).sub (h1.const_mul (w / Real.sqrt 3)))
    refine hd.congr_deriv ?_ |>.deriv
    ring
  simp only [curve, hval, hderiv]
  set φ := θ - (k : ℝ) * (2 * π / 3) - π / 3
  set c := (k : ℝ) * (2 * π / 3) + π / 3
  have hθ : θ = φ + c := by simp [φ, c]
  push_cast; ring_nf
  -- Remaining goal: prove using exp_neg_mul_I and hθ
  rw [show -(↑w * (↑(Real.sqrt 3))⁻¹ * Complex.cos ↑φ * Complex.exp (I * ↑θ)) +
      ↑w * (↑(Real.sqrt 3))⁻¹ * Complex.sin ↑φ * I * Complex.exp (I * ↑θ) +
      ↑w * Complex.exp (I * ↑θ) =
      ↑w * Complex.exp (I * ↑θ) + -(↑w * (↑(Real.sqrt 3))⁻¹) *
      (Complex.cos ↑φ - Complex.sin ↑φ * I) * Complex.exp (I * ↑θ) by ring]
  rw [show Complex.cos ↑φ - Complex.sin ↑φ * I = Complex.exp (-(↑φ * I)) from by
    rw [exp_neg_mul_I]; push_cast; ring]
  rw [show -(↑w * (↑(Real.sqrt 3))⁻¹) * Complex.exp (-(↑φ * I)) * Complex.exp (I * ↑θ) =
      -(↑w * (↑(Real.sqrt 3))⁻¹) * (Complex.exp (-(↑φ * I)) * Complex.exp (I * ↑θ)) by ring]
  rw [← Complex.exp_add]
  rw [show -(↑φ * I) + I * ↑θ = I * ↑c by push_cast [hθ]; ring]
  ring

private lemma arc_eqOn_Icc {w : ℝ} (hw : 0 < w) (k : ℤ) :
    EqOn (curve (reuleaux w))
      (fun θ => ↑w * exp (↑θ * I) - ↑(w / Real.sqrt 3) * exp (↑((k : ℝ) * (2 * π / 3) + π / 3) * I))
      (Set.Icc (π / 6 + (k : ℝ) * (2 * π / 3)) (π / 2 + (k : ℝ) * (2 * π / 3))) :=
  (arc_eqOn_Ioo hw k).of_subset_closure
    (continuous_curve_reuleaux hw).continuousOn
    (Continuous.continuousOn (by fun_prop))
    Ioo_subset_Icc_self
    (by rw [closure_Ioo (by linarith [Real.pi_pos] : π / 6 + (k : ℝ) * (2 * π / 3) ≠
        π / 2 + (k : ℝ) * (2 * π / 3))])

private lemma eVariationOn_arc_piece {w : ℝ} (hw : 0 < w) (k : ℤ) :
    eVariationOn (curve (reuleaux w))
      (Set.Icc (π / 6 + (k : ℝ) * (2 * π / 3)) (π / 2 + (k : ℝ) * (2 * π / 3))) =
      ENNReal.ofReal (w * (π / 3)) := by
  rw [eVariationOn.congr (arc_eqOn_Icc hw k)]
  have hfun : ContDiff ℝ 1 (fun θ : ℝ =>
      (w : ℂ) * exp (↑θ * I) - ↑(w / Real.sqrt 3) * exp (↑((k : ℝ) * (2 * π / 3) + π / 3) * I)) :=
    (contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp contDiff_id).mul
        contDiff_const |>.cexp)).sub contDiff_const
  have hab : π / 6 + (k : ℝ) * (2 * π / 3) ≤ π / 2 + (k : ℝ) * (2 * π / 3) := by
    linarith [Real.pi_pos]
  rw [← ENNReal.ofReal_toReal (eVariationOn_ne_top_of_contDiff hfun hab),
    (length_eq_integral_norm_deriv hfun hab).2]
  have hderiv : ∀ t : ℝ, deriv (fun θ : ℝ =>
      (w : ℂ) * exp (↑θ * I) -
      ↑(w / Real.sqrt 3) * exp (↑((k : ℝ) * (2 * π / 3) + π / 3) * I)) t =
      (w : ℂ) * I * exp (↑t * I) := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I t := by
      have := ((hasDerivAt_id t).ofReal_comp).mul_const I
      simp at this; exact this
    have h2 := Complex.hasDerivAt_exp ((t : ℂ) * I)
    have hexp : HasDerivAt (fun θ : ℝ => Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((t : ℂ) * I) * I) t := (h2.comp t h1).congr_deriv (by ring)
    have hconst : HasDerivAt
        (fun _ : ℝ => (w / Real.sqrt 3 : ℝ) * Complex.exp (((k : ℝ) * (2 * π / 3) + π / 3 : ℝ) * I))
        0 t := hasDerivAt_const t _
    exact ((hexp.const_mul (w : ℂ)).sub hconst).congr_deriv (by ring) |>.deriv
  simp_rw [hderiv]
  simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw,
    Complex.norm_I, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [intervalIntegral.integral_const]
  ring_nf

/-! ### eVariation on corner subsets -/

private lemma eVariationOn_corner_subset_zero {w : ℝ} (hw : 0 < w) (k : ℤ) {a b : ℝ}
    (ha : -(π / 6) + (k : ℝ) * (2 * π / 3) ≤ a) (hb : b ≤ π / 6 + (k : ℝ) * (2 * π / 3)) :
    eVariationOn (curve (reuleaux w)) (Set.Icc a b) = 0 := by
  rcases le_or_gt a b with hab | hab
  · have hle : eVariationOn (curve (reuleaux w)) (Set.Icc a b) ≤ 0 := by
      calc eVariationOn (curve (reuleaux w)) (Set.Icc a b)
          ≤ eVariationOn (curve (reuleaux w))
              (Set.Icc (-(π / 6) + (k : ℝ) * (2 * π / 3)) (π / 6 + (k : ℝ) * (2 * π / 3))) :=
            eVariationOn.mono _ (Set.Icc_subset_Icc ha hb)
        _ = 0 := eVariationOn_corner_zero hw k
    exact le_zero_iff.mp hle
  · simp [Set.Icc_eq_empty (not_le.mpr hab)]

/-! ### Partition points for main theorem -/

private noncomputable def segPts : ℕ → ℝ
  | 0 => 0
  | 1 => π / 6
  | 2 => π / 2
  | 3 => 5 * π / 6
  | 4 => 7 * π / 6
  | 5 => 3 * π / 2
  | 6 => 11 * π / 6
  | _ => 2 * π

private lemma segPts_mono : Monotone segPts := by
  have hpi := Real.pi_pos
  apply monotone_nat_of_le_succ
  intro n
  match n with
  | 0 => simp [segPts]; linarith
  | 1 => simp [segPts]; linarith
  | 2 => simp [segPts]; linarith
  | 3 => simp [segPts]; linarith
  | 4 => simp [segPts]; linarith
  | 5 => simp [segPts]; linarith
  | 6 => simp [segPts]; linarith
  | (n + 7) => simp [segPts]

/-! ### Main theorem -/

theorem reuleaux_length {w : ℝ} (hw : 0 < w) :
    eVariationOn (curve (reuleaux w)) (Set.Icc 0 (2 * π)) = ENNReal.ofReal (π * w) := by
  have hpi := Real.pi_pos
  -- Split [0, 2π] into 7 pieces
  have hsum : ∑ i ∈ Finset.range 7,
      eVariationOn (curve (reuleaux w)) (Set.Icc (segPts i) (segPts (i + 1))) =
      eVariationOn (curve (reuleaux w)) (Set.Icc 0 (2 * π)) := by
    have h0 : segPts 0 = 0 := by simp [segPts]
    have h7 : segPts 7 = 2 * π := by simp [segPts]
    rw [← h0, ← h7]
    exact eVariationOn.sum' (curve (reuleaux w)) segPts_mono (n := 7)
  rw [← hsum]
  have p0 : eVariationOn (curve (reuleaux w)) (Set.Icc (segPts 0) (segPts 1)) = 0 := by
    simp only [segPts]
    exact eVariationOn_corner_subset_zero hw 0 (by norm_num; linarith) (by norm_num)
  have p1 : eVariationOn (curve (reuleaux w)) (Set.Icc (segPts 1) (segPts 2)) =
      ENNReal.ofReal (w * (π / 3)) := by
    simp only [segPts]
    convert eVariationOn_arc_piece hw 0 using 2
    norm_num
  have p2 : eVariationOn (curve (reuleaux w)) (Set.Icc (segPts 2) (segPts 3)) = 0 := by
    simp only [segPts]
    convert eVariationOn_corner_zero hw 1 using 2
    simp [Int.cast_one]; ring
  have p3 : eVariationOn (curve (reuleaux w)) (Set.Icc (segPts 3) (segPts 4)) =
      ENNReal.ofReal (w * (π / 3)) := by
    simp only [segPts]
    convert eVariationOn_arc_piece hw 1 using 2
    simp [Int.cast_one]; ring
  have p4 : eVariationOn (curve (reuleaux w)) (Set.Icc (segPts 4) (segPts 5)) = 0 := by
    simp only [segPts]
    convert eVariationOn_corner_zero hw 2 using 2
    push_cast; ring
  have p5 : eVariationOn (curve (reuleaux w)) (Set.Icc (segPts 5) (segPts 6)) =
      ENNReal.ofReal (w * (π / 3)) := by
    simp only [segPts]
    convert eVariationOn_arc_piece hw 2 using 2
    push_cast; ring
  have p6 : eVariationOn (curve (reuleaux w)) (Set.Icc (segPts 6) (segPts 7)) = 0 := by
    simp only [segPts]
    exact eVariationOn_corner_subset_zero hw 3 (by push_cast; linarith) (by push_cast; linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [p0, p1, p2, p3, p4, p5, p6]
  simp only [zero_add, add_zero]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; linarith

theorem reuleaux_length_ne_top {w : ℝ} (hw : 0 < w) :
    eVariationOn (curve (reuleaux w)) (Set.Icc 0 (2 * π)) ≠ ⊤ := by
  rw [reuleaux_length hw]; exact ENNReal.ofReal_ne_top

theorem reuleaux_perimeter_eq_eVariationOn {w : ℝ} (hw : 0 < w) :
    perimeter (reuleaux w) = (eVariationOn (curve (reuleaux w)) (Set.Icc 0 (2 * π))).toReal := by
  rw [reuleaux_length hw, ENNReal.toReal_ofReal (by positivity), reuleaux_perimeter hw]

end Barbier
end
