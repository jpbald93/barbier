import Barbier.Piecewise
import Mathlib.Topology.Order.LeftRightNhds

noncomputable section

open Real intervalIntegral MeasureTheory AddCommGroup Filter Topology Set Interval

namespace Barbier

def reuleauxPiece (w p : ℝ) : ℝ :=
  if p ≤ π / 6 then (w / Real.sqrt 3) * Real.cos p
  else w - (w / Real.sqrt 3) * Real.cos (p - π / 3)

lemma reuleaux_period_pos : (0 : ℝ) < 2 * π / 3 := by positivity

def reuleaux (w : ℝ) (θ : ℝ) : ℝ :=
  reuleauxPiece w (toIcoMod reuleaux_period_pos (-(π / 6)) θ)

private lemma toIcoMod_zero :
    toIcoMod reuleaux_period_pos (-(π / 6)) 0 = 0 := by
  rw [toIcoMod_eq_self]
  exact ⟨by linarith [Real.pi_pos], by
    show (0 : ℝ) < -(π/6) + 2*π/3; linarith [Real.pi_pos]⟩

private lemma toIcoMod_two_pi_div_three :
    toIcoMod reuleaux_period_pos (-(π / 6)) (2 * π / 3) = 0 := by
  have h : (2 * π / 3 : ℝ) = 0 + (1 : ℤ) • (2 * π / 3) := by simp
  calc toIcoMod reuleaux_period_pos (-(π / 6)) (2 * π / 3)
      = toIcoMod reuleaux_period_pos (-(π / 6)) (0 + (1 : ℤ) • (2 * π / 3)) := by rw [← h]
    _ = toIcoMod reuleaux_period_pos (-(π / 6)) 0 := toIcoMod_add_zsmul _ _ _ _
    _ = 0 := toIcoMod_zero

private lemma toIcoMod_four_pi_div_three :
    toIcoMod reuleaux_period_pos (-(π / 6)) (4 * π / 3) = 0 := by
  have h : (4 * π / 3 : ℝ) = 0 + (2 : ℤ) • (2 * π / 3) := by push_cast; ring
  calc toIcoMod reuleaux_period_pos (-(π / 6)) (4 * π / 3)
      = toIcoMod reuleaux_period_pos (-(π / 6)) (0 + (2 : ℤ) • (2 * π / 3)) := by rw [← h]
    _ = toIcoMod reuleaux_period_pos (-(π / 6)) 0 := toIcoMod_add_zsmul _ _ _ _
    _ = 0 := toIcoMod_zero

private lemma pi_div6_pos : (0 : ℝ) < π / 6 := by positivity
private lemma pi6_neg_lt_pi6 : -(Real.pi / 6) < Real.pi / 6 := by linarith [Real.pi_pos]
private lemma pi6_lt_pi2 : Real.pi / 6 < Real.pi / 2 := by linarith [Real.pi_pos]

private lemma reuleaux_val_zero {p : ℝ} (hp : toIcoMod reuleaux_period_pos (-(π/6)) p = 0) (w : ℝ) :
    reuleaux w p = w / Real.sqrt 3 := by
  simp [reuleaux, reuleauxPiece, hp, if_pos (le_of_lt pi_div6_pos)]

private lemma reuleaux_zero (w : ℝ) : reuleaux w 0 = w / Real.sqrt 3 :=
  reuleaux_val_zero toIcoMod_zero w

private lemma reuleaux_two_pi_div_three (w : ℝ) : reuleaux w (2 * π / 3) = w / Real.sqrt 3 :=
  reuleaux_val_zero toIcoMod_two_pi_div_three w

private lemma reuleaux_four_pi_div_three (w : ℝ) : reuleaux w (4 * π / 3) = w / Real.sqrt 3 :=
  reuleaux_val_zero toIcoMod_four_pi_div_three w

/-! Derivatives at corners: reuleaux locally equals (w/√3)*cos(θ - θ₀) near each corner. -/

-- Near 0: θ ∈ (-π/6, π/6) ⟹ toIcoMod = θ and θ ≤ π/6 ✓
private lemma reuleaux_locally_eq_cos_zero (w : ℝ) :
    reuleaux w =ᶠ[nhds 0] (fun θ => (w / Real.sqrt 3) * Real.cos θ) := by
  apply Filter.eventually_of_mem
    (Ioo_mem_nhds (by linarith [pi_div6_pos] : -(π/6) < 0) pi_div6_pos)
  intro θ ⟨hlo, hhi⟩
  unfold reuleaux reuleauxPiece
  have hmod : toIcoMod reuleaux_period_pos (-(π/6)) θ = θ := by
    rw [toIcoMod_eq_self]
    exact ⟨le_of_lt hlo, by show θ < -(π/6) + 2*π/3; linarith [Real.pi_pos]⟩
  rw [hmod, if_pos (le_of_lt hhi)]

-- Near 2π/3: θ ∈ (π/2, 5π/6) ⟹ toIcoMod = θ - 2π/3 and θ - 2π/3 ∈ (-π/6, π/6) ≤ π/6 ✓
private lemma reuleaux_locally_eq_cos_two_pi_div_three (w : ℝ) :
    reuleaux w =ᶠ[nhds (2*π/3)] (fun θ => (w / Real.sqrt 3) * Real.cos (θ - 2*π/3)) := by
  apply Filter.eventually_of_mem
    (Ioo_mem_nhds (by linarith [pi_div6_pos] : 2*π/3 - π/6 < 2*π/3)
                  (by linarith [pi_div6_pos] : 2*π/3 < 2*π/3 + π/6))
  intro θ ⟨hlo, hhi⟩
  unfold reuleaux reuleauxPiece
  have hmod : toIcoMod reuleaux_period_pos (-(π/6)) θ = θ - 2*π/3 := by
    rw [toIcoMod_eq_iff]
    exact ⟨⟨by linarith, by show θ - 2*π/3 < -(π/6) + 2*π/3; linarith⟩,
           1, by push_cast; ring⟩
  rw [hmod, if_pos (by linarith)]

-- Near 4π/3: θ ∈ (7π/6, 3π/2) ⟹ toIcoMod = θ - 4π/3 and θ - 4π/3 ∈ (-π/6, π/6) ≤ π/6 ✓
private lemma reuleaux_locally_eq_cos_four_pi_div_three (w : ℝ) :
    reuleaux w =ᶠ[nhds (4*π/3)] (fun θ => (w / Real.sqrt 3) * Real.cos (θ - 4*π/3)) := by
  apply Filter.eventually_of_mem
    (Ioo_mem_nhds (by linarith [pi_div6_pos] : 4*π/3 - π/6 < 4*π/3)
                  (by linarith [pi_div6_pos] : 4*π/3 < 4*π/3 + π/6))
  intro θ ⟨hlo, hhi⟩
  unfold reuleaux reuleauxPiece
  have hmod : toIcoMod reuleaux_period_pos (-(π/6)) θ = θ - 4*π/3 := by
    rw [toIcoMod_eq_iff]
    exact ⟨⟨by linarith, by show θ - 4*π/3 < -(π/6) + 2*π/3; linarith⟩,
           2, by push_cast; ring⟩
  rw [hmod, if_pos (by linarith)]

-- General version for not_smooth proof
private lemma reuleaux_locally_eq_cos_of_mem {θ₀ : ℝ} (hlo : -(Real.pi/6) < θ₀)
    (hhi : θ₀ < Real.pi/6) (w : ℝ) :
    reuleaux w =ᶠ[nhds θ₀] (fun θ => (w / Real.sqrt 3) * Real.cos θ) := by
  apply Filter.eventually_of_mem (Ioo_mem_nhds hlo hhi)
  intro θ ⟨hlo', hhi'⟩
  unfold reuleaux reuleauxPiece
  have hmod : toIcoMod reuleaux_period_pos (-(Real.pi/6)) θ = θ := by
    rw [toIcoMod_eq_self]
    exact ⟨le_of_lt hlo', by linarith [Real.pi_pos]⟩
  rw [hmod, if_pos (le_of_lt hhi')]

private lemma reuleaux_locally_eq_arc_of_mem {θ₀ : ℝ} (hlo : Real.pi/6 < θ₀)
    (hhi : θ₀ < Real.pi/2) (w : ℝ) :
    reuleaux w =ᶠ[nhds θ₀] (fun θ => w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi / 3)) := by
  apply Filter.eventually_of_mem (Ioo_mem_nhds hlo hhi)
  intro θ ⟨hlo', hhi'⟩
  unfold reuleaux reuleauxPiece
  have hmod : toIcoMod reuleaux_period_pos (-(Real.pi/6)) θ = θ := by
    rw [toIcoMod_eq_self]
    exact ⟨by linarith, by linarith [Real.pi_pos]⟩
  rw [hmod, if_neg (not_le.mpr hlo')]

private lemma hasDerivAt_cos_sub (k θ₀ : ℝ) :
    HasDerivAt (fun θ => Real.cos (θ - k)) (-Real.sin (θ₀ - k)) θ₀ := by
  have h1 : HasDerivAt (fun θ => θ - k) (1 - 0) θ₀ :=
    (hasDerivAt_id θ₀).sub (hasDerivAt_const θ₀ k)
  have h1' : HasDerivAt (fun θ => θ - k) 1 θ₀ := h1.congr_deriv (by ring)
  have h2 := (Real.hasDerivAt_cos (θ₀ - k)).comp θ₀ h1'
  simp only [Function.comp_def, mul_one] at h2
  exact h2

private lemma deriv_reuleaux_zero (w : ℝ) : deriv (reuleaux w) 0 = 0 := by
  rw [(reuleaux_locally_eq_cos_zero w).deriv_eq]
  have hd : HasDerivAt (fun θ => w / Real.sqrt 3 * Real.cos θ)
      (w / Real.sqrt 3 * (-Real.sin 0)) 0 :=
    ((Real.hasDerivAt_cos 0).const_mul _)
  rw [hd.deriv, Real.sin_zero, neg_zero, mul_zero]

private lemma deriv_reuleaux_two_pi_div_three (w : ℝ) : deriv (reuleaux w) (2 * π / 3) = 0 := by
  rw [(reuleaux_locally_eq_cos_two_pi_div_three w).deriv_eq]
  have hd : HasDerivAt (fun θ => w / Real.sqrt 3 * Real.cos (θ - 2 * π / 3))
      (w / Real.sqrt 3 * (-Real.sin (2 * π / 3 - 2 * π / 3))) (2 * π / 3) :=
    (hasDerivAt_cos_sub (2*π/3) (2*π/3)).const_mul _
  rw [hd.deriv, show 2*π/3 - 2*π/3 = (0:ℝ) from by ring, Real.sin_zero, neg_zero, mul_zero]

private lemma deriv_reuleaux_four_pi_div_three (w : ℝ) : deriv (reuleaux w) (4 * π / 3) = 0 := by
  rw [(reuleaux_locally_eq_cos_four_pi_div_three w).deriv_eq]
  have hd : HasDerivAt (fun θ => w / Real.sqrt 3 * Real.cos (θ - 4 * π / 3))
      (w / Real.sqrt 3 * (-Real.sin (4 * π / 3 - 4 * π / 3))) (4 * π / 3) :=
    (hasDerivAt_cos_sub (4*π/3) (4*π/3)).const_mul _
  rw [hd.deriv, show 4*π/3 - 4*π/3 = (0:ℝ) from by ring, Real.sin_zero, neg_zero, mul_zero]

/-! curve values at corners -/

private lemma curve_reuleaux_zero (w : ℝ) :
    curve (reuleaux w) 0 = ((w / Real.sqrt 3 : ℝ) : ℂ) := by
  simp [curve, reuleaux_zero, deriv_reuleaux_zero]

private lemma curve_reuleaux_two_pi_div_three (w : ℝ) :
    curve (reuleaux w) (2 * π / 3) =
      ((w / Real.sqrt 3 : ℝ) : ℂ) * Complex.exp (↑(2 * π / 3) * Complex.I) := by
  simp only [curve, reuleaux_two_pi_div_three, deriv_reuleaux_two_pi_div_three]
  push_cast; ring

private lemma curve_reuleaux_four_pi_div_three (w : ℝ) :
    curve (reuleaux w) (4 * π / 3) =
      ((w / Real.sqrt 3 : ℝ) : ℂ) * Complex.exp (↑(4 * π / 3) * Complex.I) := by
  simp only [curve, reuleaux_four_pi_div_three, deriv_reuleaux_four_pi_div_three]
  push_cast; ring

/-! Distance computations -/

private lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
private lemma sqrt3_ne_zero : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos

-- normSq of exp(i*θ) - 1 = 2 - 2*cos θ
private lemma normSq_exp_sub_one (θ : ℝ) :
    Complex.normSq (Complex.exp (↑θ * Complex.I) - 1) = 2 - 2 * Real.cos θ := by
  have heq : Complex.exp (↑θ * Complex.I) - 1 =
      ↑(Real.cos θ - 1) + ↑(Real.sin θ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [heq, Complex.normSq_add_mul_I]
  nlinarith [Real.sin_sq_add_cos_sq θ]

private lemma normSq_exp_two_pi3_sub_one :
    Complex.normSq (Complex.exp (↑(2 * π / 3) * Complex.I) - 1) = 3 := by
  rw [normSq_exp_sub_one]
  have : Real.cos (2 * π / 3) = -1/2 := by
    rw [show 2*π/3 = π - π/3 from by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  linarith

private lemma normSq_exp_four_pi3_sub_one :
    Complex.normSq (Complex.exp (↑(4 * π / 3) * Complex.I) - 1) = 3 := by
  rw [normSq_exp_sub_one]
  have : Real.cos (4 * π / 3) = -1/2 := by
    rw [show 4*π/3 = 2*π - 2*π/3 from by ring, Real.cos_two_pi_sub,
        show 2*π/3 = π - π/3 from by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  linarith

-- ‖z‖ = w from normSq z = w² and w > 0
private lemma norm_eq_of_normSq {z : ℂ} {w : ℝ} (hw : 0 < w) (h : Complex.normSq z = w ^ 2) :
    ‖z‖ = w := by
  have hnn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hsq : ‖z‖ ^ 2 = w ^ 2 := by
    rw [Complex.normSq_eq_norm_sq] at h; linarith
  nlinarith [sq_nonneg (‖z‖ - w)]

private lemma dist_reuleaux_0_2pi3 {w : ℝ} (hw : 0 < w) :
    dist (curve (reuleaux w) 0) (curve (reuleaux w) (2 * π / 3)) = w := by
  rw [curve_reuleaux_zero, curve_reuleaux_two_pi_div_three, dist_comm, dist_eq_norm]
  rw [show ((w / Real.sqrt 3 : ℝ) : ℂ) * Complex.exp (↑(2 * π / 3) * Complex.I) -
        ((w / Real.sqrt 3 : ℝ) : ℂ) =
      ↑(w / Real.sqrt 3) * (Complex.exp (↑(2 * π / 3) * Complex.I) - 1) by push_cast; ring]
  apply norm_eq_of_normSq hw
  rw [Complex.normSq_mul, Complex.normSq_ofReal, normSq_exp_two_pi3_sub_one]
  field_simp; nlinarith [sqrt3_sq]

private lemma dist_reuleaux_2pi3_4pi3 {w : ℝ} (hw : 0 < w) :
    dist (curve (reuleaux w) (2 * π / 3)) (curve (reuleaux w) (4 * π / 3)) = w := by
  rw [curve_reuleaux_two_pi_div_three, curve_reuleaux_four_pi_div_three, dist_eq_norm]
  rw [show ((w / Real.sqrt 3 : ℝ) : ℂ) * Complex.exp (↑(2 * π / 3) * Complex.I) -
        ((w / Real.sqrt 3 : ℝ) : ℂ) * Complex.exp (↑(4 * π / 3) * Complex.I) =
      ↑(w / Real.sqrt 3) * Complex.exp (↑(2 * π / 3) * Complex.I) *
        (1 - Complex.exp (↑(2 * π / 3) * Complex.I)) by
    have : Complex.exp (↑(4 * π / 3) * Complex.I) =
        Complex.exp (↑(2 * π / 3) * Complex.I) * Complex.exp (↑(2 * π / 3) * Complex.I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [this]; push_cast; ring]
  apply norm_eq_of_normSq hw
  have hnsq_exp : Complex.normSq (Complex.exp (↑(2 * π / 3) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal, hnsq_exp, mul_one,
      show (1 : ℂ) - Complex.exp (↑(2 * π / 3) * Complex.I) =
          -(Complex.exp (↑(2 * π / 3) * Complex.I) - 1) from by ring,
      Complex.normSq_neg, normSq_exp_two_pi3_sub_one]
  field_simp; nlinarith [sqrt3_sq]

private lemma dist_reuleaux_4pi3_0 {w : ℝ} (hw : 0 < w) :
    dist (curve (reuleaux w) (4 * π / 3)) (curve (reuleaux w) 0) = w := by
  rw [curve_reuleaux_zero, curve_reuleaux_four_pi_div_three, dist_eq_norm]
  rw [show ((w / Real.sqrt 3 : ℝ) : ℂ) * Complex.exp (↑(4 * π / 3) * Complex.I) -
        ((w / Real.sqrt 3 : ℝ) : ℂ) =
      ↑(w / Real.sqrt 3) * (Complex.exp (↑(4 * π / 3) * Complex.I) - 1) by push_cast; ring]
  apply norm_eq_of_normSq hw
  rw [Complex.normSq_mul, Complex.normSq_ofReal, normSq_exp_four_pi3_sub_one]
  field_simp; nlinarith [sqrt3_sq]

/-! Second derivative computations for not_smooth -/

private lemma dderiv_left {θ₀ : ℝ} (hlo : -(Real.pi/6) < θ₀) (hhi : θ₀ < Real.pi/6) (w : ℝ)
    (_ : ContDiff ℝ 2 (reuleaux w)) :
    deriv (deriv (reuleaux w)) θ₀ = -(w / Real.sqrt 3) * Real.cos θ₀ := by
  have hd1eq : deriv (reuleaux w) =ᶠ[nhds θ₀] (fun θ => -(w / Real.sqrt 3) * Real.sin θ) := by
    apply Filter.eventually_of_mem (Ioo_mem_nhds hlo hhi)
    intro θ ⟨hlo', hhi'⟩
    rw [(reuleaux_locally_eq_cos_of_mem hlo' hhi' w).deriv_eq]
    rw [(((Real.hasDerivAt_cos θ).const_mul (w / Real.sqrt 3))).deriv]; ring
  rw [hd1eq.deriv_eq]
  rw [((Real.hasDerivAt_sin θ₀).const_mul (-(w / Real.sqrt 3))).deriv]

private lemma dderiv_right {θ₀ : ℝ} (hlo : Real.pi/6 < θ₀) (hhi : θ₀ < Real.pi/2) (w : ℝ)
    (_ : ContDiff ℝ 2 (reuleaux w)) :
    deriv (deriv (reuleaux w)) θ₀ = (w / Real.sqrt 3) * Real.cos (θ₀ - Real.pi / 3) := by
  have hd1eq : deriv (reuleaux w) =ᶠ[nhds θ₀]
      (fun θ => (w / Real.sqrt 3) * Real.sin (θ - Real.pi / 3)) := by
    apply Filter.eventually_of_mem (Ioo_mem_nhds hlo hhi)
    intro θ ⟨hlo', hhi'⟩
    rw [(reuleaux_locally_eq_arc_of_mem hlo' hhi' w).deriv_eq]
    have hd : HasDerivAt (fun θ => w - w / Real.sqrt 3 * Real.cos (θ - Real.pi / 3))
        (w / Real.sqrt 3 * Real.sin (θ - Real.pi / 3)) θ :=
      ((hasDerivAt_const θ w).sub ((hasDerivAt_cos_sub (Real.pi/3) θ).const_mul
        (w / Real.sqrt 3))).congr_deriv (by ring)
    rw [hd.deriv]
  rw [hd1eq.deriv_eq]
  have h1 : HasDerivAt (fun θ => θ - Real.pi / 3) 1 θ₀ :=
    ((hasDerivAt_id θ₀).sub (hasDerivAt_const θ₀ _)).congr_deriv (by ring)
  have h2 := (Real.hasDerivAt_sin (θ₀ - Real.pi/3)).comp θ₀ h1
  simp only [Function.comp_def, mul_one] at h2
  rw [(h2.const_mul (w / Real.sqrt 3)).deriv]

private lemma Ioo_mem_nhdsGT' {a b : ℝ} (h : a < b) : Ioo a b ∈ 𝓝[>] a := by
  rw [(nhdsGT_basis_of_exists_gt ⟨b, h⟩).mem_iff]
  exact ⟨b, h, Subset.rfl⟩


-- ========== Proofs from RcwTest ==========

-- ========== Helper: sqrt 3 bounds ==========

private lemma one_le_sqrt_three' : (1 : ℝ) ≤ Real.sqrt 3 := by
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by norm_num)

private lemma sqrt_three_pos' : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

private lemma w_div_sqrt3_le_w (w : ℝ) (hw : 0 < w) : w / Real.sqrt 3 ≤ w :=
  div_le_self hw.le one_le_sqrt_three'

-- ========== reuleaux w bounds ==========

private lemma reuleaux_le_w (w : ℝ) (hw : 0 < w) (θ : ℝ) : reuleaux w θ ≤ w := by
  simp only [reuleaux, reuleauxPiece]
  split_ifs with h
  · calc (w / Real.sqrt 3) * Real.cos (toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ)
        ≤ w / Real.sqrt 3 * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) (by positivity)
      _ = w / Real.sqrt 3 := mul_one _
      _ ≤ w := w_div_sqrt3_le_w w hw
  · push_neg at h
    have hcos_nn : 0 ≤ Real.cos (toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ - Real.pi / 3) := by
      apply Real.cos_nonneg_of_mem_Icc
      have hrange := toIcoMod_mem_Ico reuleaux_period_pos (-(Real.pi / 6)) θ
      constructor <;> linarith [hrange.1, hrange.2, Real.pi_pos]
    linarith [mul_nonneg (div_nonneg hw.le (Real.sqrt_nonneg 3)) hcos_nn]

private lemma reuleaux_nonneg' (w : ℝ) (hw : 0 < w) (θ : ℝ) : 0 ≤ reuleaux w θ := by
  simp only [reuleaux, reuleauxPiece]
  split_ifs with h
  · apply mul_nonneg; · positivity
    · apply Real.cos_nonneg_of_mem_Icc
      have hrange := toIcoMod_mem_Ico reuleaux_period_pos (-(Real.pi / 6)) θ
      constructor <;> linarith [hrange.1, hrange.2, Real.pi_pos]
  · push_neg at h
    apply sub_nonneg.mpr
    have hrange := toIcoMod_mem_Ico reuleaux_period_pos (-(Real.pi / 6)) θ
    have hcos_nn : 0 ≤ Real.cos (toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ - Real.pi / 3) := by
      apply Real.cos_nonneg_of_mem_Icc; constructor <;> linarith [hrange.1, hrange.2, Real.pi_pos]
    calc w / Real.sqrt 3 * Real.cos (toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ - Real.pi / 3)
        ≤ w / Real.sqrt 3 * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) (by positivity)
      _ ≤ w := by rw [mul_one]; exact w_div_sqrt3_le_w w hw

-- ========== Periodic ==========

private lemma toIcoMod_two_pi_eq' (θ : ℝ) :
    toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (θ + 2 * Real.pi) =
    toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ := by
  have heq : θ + 2 * Real.pi = θ + (3 : ℤ) • (2 * Real.pi / 3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [heq, toIcoMod_add_zsmul]

lemma reuleaux_periodic (w : ℝ) : Function.Periodic (reuleaux w) (2 * Real.pi) := fun θ => by
  simp only [reuleaux, toIcoMod_two_pi_eq']

-- ========== Width ==========

private lemma toIcoMod_k_int' (k : ℤ) (θ : ℝ)
    (hlo : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3)) :
    toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ - (k : ℝ) * (2 * Real.pi / 3) := by
  rw [toIcoMod_eq_iff]
  exact ⟨⟨by linarith, by linarith [Real.pi_pos]⟩, k,
         by simp only [zsmul_eq_mul]; push_cast; ring⟩

lemma reuleaux_width (w : ℝ) (θ : ℝ) : reuleaux w θ + reuleaux w (θ + Real.pi) = w := by
  -- Let p = toIcoMod θ ∈ [-π/6, π/2), and θ = p + k*(2π/3)
  have hp_range : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ ∈
      Set.Ico (-(Real.pi / 6)) (-(Real.pi / 6) + 2 * Real.pi / 3) :=
    toIcoMod_mem_Ico reuleaux_period_pos (-(Real.pi / 6)) θ
  set p := toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ with hp_def
  obtain ⟨k, hk⟩ : ∃ k : ℤ, θ = p + (k : ℝ) * (2 * Real.pi / 3) := by
    use toIcoDiv reuleaux_period_pos (-(Real.pi / 6)) θ
    have h := toIcoMod_add_toIcoDiv_zsmul reuleaux_period_pos (-(Real.pi / 6)) θ
    simp only [zsmul_eq_mul] at h; linarith
  have hpθ : p = θ - (k : ℝ) * (2 * Real.pi / 3) := by rw [hk]; ring
  have hhi_θ : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3) := by
    rw [hk]; linarith [hp_range.2, show -(Real.pi / 6) + 2 * Real.pi / 3 = Real.pi / 2 from by ring]
  -- Split on p vs π/6 and p vs -(π/6) to determine which piece applies
  -- First handle the boundary case p = -(π/6) (left period boundary)
  rcases eq_or_lt_of_le hp_range.1 with hlo_eq | hlo_lt
  · -- p = -(π/6): θ = -(π/6) + k*(2π/3)
    have hp_eq : p = -(Real.pi / 6) := hlo_eq.symm
    -- reuleaux w θ: p = -(π/6) ≤ π/6, so cos piece
    have hmod_θ : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = -(Real.pi / 6) :=
      hp_def.symm.trans hp_eq
    have hval_θ : reuleaux w θ = (w / Real.sqrt 3) * Real.cos (-(Real.pi / 6)) := by
      simp only [reuleaux, reuleauxPiece, hmod_θ]; rw [if_pos (by linarith [Real.pi_pos])]
    -- θ + π maps to π/6 (which is ≤ π/6, so cos piece)
    have hmod_θpi : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (θ + Real.pi) =
        Real.pi / 6 := by
      rw [toIcoMod_eq_iff]
      exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, k + 1,
             by push_cast; rw [hk, hp_eq]; ring⟩
    have hval_θpi : reuleaux w (θ + Real.pi) = (w / Real.sqrt 3) * Real.cos (Real.pi / 6) := by
      simp only [reuleaux, reuleauxPiece, hmod_θpi]
      rw [if_pos le_rfl]
    rw [hval_θ, hval_θpi]
    have h3 : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    simp only [Real.cos_neg, Real.cos_pi_div_six]
    field_simp
    nlinarith
  · -- p ∈ (-π/6, π/2): we have hlo_lt : -(π/6) < p
    have hlo_θ : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ := by rw [hk]; linarith
    have hmod_θ := toIcoMod_k_int' k θ hlo_θ hhi_θ
    rcases lt_trichotomy p (Real.pi / 6) with hlt | heq | hgt
    · -- cos piece: p ∈ (-π/6, π/6)
      have hval_θ : reuleaux w θ = (w / Real.sqrt 3) * Real.cos p := by
        simp only [reuleaux, reuleauxPiece]; rw [if_pos (le_of_lt hlt)]
      have hk1 : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by norm_cast
      have hmod_θpi : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (θ + Real.pi) =
          θ + Real.pi - (k + 1 : ℤ) * (2 * Real.pi / 3) :=
        toIcoMod_k_int' (k + 1) (θ + Real.pi) (by rw [hk1, hk]; linarith [Real.pi_pos])
          (by rw [hk1, hk]; linarith [Real.pi_pos])
      have hval_θpi : reuleaux w (θ + Real.pi) =
          w - (w / Real.sqrt 3) * Real.cos (θ + Real.pi - (k + 1 : ℤ) * (2 * Real.pi / 3) - Real.pi / 3) := by
        simp only [reuleaux, reuleauxPiece, hmod_θpi]
        rw [if_neg (by rw [hk1, hk]; linarith [Real.pi_pos])]
      rw [hval_θ, hval_θpi, hk1, hpθ]; push_cast; ring
    · -- p = π/6: reuleaux w θ = (w/√3)*cos(π/6) = w/2
      have hmod_θ_eq : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = Real.pi / 6 :=
        hmod_θ.trans (hpθ.symm.trans heq)
      have hval_θ : reuleaux w θ = (w / Real.sqrt 3) * Real.cos (Real.pi / 6) := by
        simp only [reuleaux, reuleauxPiece, hmod_θ_eq]; rw [if_pos le_rfl]
      have hmod_θpi : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (θ + Real.pi) = -(Real.pi / 6) := by
        rw [toIcoMod_eq_iff]
        exact ⟨⟨le_refl _, by linarith [Real.pi_pos]⟩, k + 2,
               by push_cast; rw [hk, heq]; ring⟩
      have hval_θpi : reuleaux w (θ + Real.pi) = (w / Real.sqrt 3) * Real.cos (-(Real.pi / 6)) := by
        simp only [reuleaux, reuleauxPiece, hmod_θpi]
        rw [if_pos (by linarith [Real.pi_pos])]
      rw [hval_θ, hval_θpi]
      have h3 : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      simp only [Real.cos_pi_div_six, Real.cos_neg]
      field_simp
      nlinarith
    · -- arc piece: p ∈ (π/6, π/2)
      have hval_θ : reuleaux w θ = w - (w / Real.sqrt 3) * Real.cos (p - Real.pi / 3) := by
        simp only [reuleaux, reuleauxPiece]; rw [if_neg (by linarith)]
      have hk2 : ((k + 2 : ℤ) : ℝ) = (k : ℝ) + 2 := by norm_cast
      have hmod_θpi : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (θ + Real.pi) =
          θ + Real.pi - (k + 2 : ℤ) * (2 * Real.pi / 3) :=
        toIcoMod_k_int' (k + 2) (θ + Real.pi) (by rw [hk2, hk]; linarith)
          (by rw [hk2, hk]; linarith)
      have hval_θpi : reuleaux w (θ + Real.pi) =
          (w / Real.sqrt 3) * Real.cos (θ + Real.pi - (k + 2 : ℤ) * (2 * Real.pi / 3)) := by
        simp only [reuleaux, reuleauxPiece, hmod_θpi]; rw [if_pos (by rw [hk2, hk]; linarith)]
      rw [hval_θ, hval_θpi, hk2, hpθ]; push_cast; ring

-- ========== Second derivative helpers ==========

private lemma hasDerivAt_cos_sub_kk' (c θ₀ : ℝ) :
    HasDerivAt (fun θ => Real.cos (θ - c)) (-Real.sin (θ₀ - c)) θ₀ := by
  have h1 : HasDerivAt (fun θ => θ - c) 1 θ₀ :=
    ((hasDerivAt_id θ₀).sub (hasDerivAt_const θ₀ c)).congr_deriv (by ring)
  have h2 := (Real.hasDerivAt_cos (θ₀ - c)).comp θ₀ h1
  simp only [Function.comp_def, mul_one] at h2; exact h2

private lemma hasDerivAt_sin_sub_kk' (c θ₀ : ℝ) :
    HasDerivAt (fun θ => Real.sin (θ - c)) (Real.cos (θ₀ - c)) θ₀ := by
  have h1 : HasDerivAt (fun θ => θ - c) 1 θ₀ :=
    ((hasDerivAt_id θ₀).sub (hasDerivAt_const θ₀ c)).congr_deriv (by ring)
  have h2 := (Real.hasDerivAt_sin (θ₀ - c)).comp θ₀ h1
  simp only [Function.comp_def, mul_one] at h2; exact h2

private lemma hasDerivAt_cos_fn'' (w : ℝ) (k : ℤ) (θ₀ : ℝ) :
    HasDerivAt (fun θ => (w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * Real.pi / 3)))
      (-(w / Real.sqrt 3) * Real.sin (θ₀ - (k : ℝ) * (2 * Real.pi / 3))) θ₀ :=
  ((hasDerivAt_cos_sub_kk' ((k : ℝ) * (2 * Real.pi / 3)) θ₀).const_mul (w / Real.sqrt 3)).congr_deriv (by ring)

private lemma hasDerivAt_arc_fn'' (w : ℝ) (k : ℤ) (θ₀ : ℝ) :
    HasDerivAt (fun θ => w - (w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3))
      ((w / Real.sqrt 3) * Real.sin (θ₀ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) θ₀ := by
  have hd := ((hasDerivAt_const θ₀ w).sub
    ((hasDerivAt_cos_sub_kk' ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3) θ₀).const_mul (w / Real.sqrt 3)))
  have hd' : HasDerivAt (fun θ => w - w / Real.sqrt 3 * Real.cos (θ - ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3)))
      (w / Real.sqrt 3 * Real.sin (θ₀ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) θ₀ :=
    hd.congr_deriv (by
      rw [show θ₀ - ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3) =
          θ₀ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3 from by ring]; ring)
  rwa [show (fun θ => w - w / Real.sqrt 3 * Real.cos (θ - ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3))) =
            (fun θ => w - w / Real.sqrt 3 * Real.cos (θ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) from by
    ext θ; congr 2; ring] at hd'

private lemma deriv_reuleaux_cos_eq'' (w : ℝ) (k : ℤ) (θ : ℝ)
    (hlo : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) :
    deriv (reuleaux w) θ = -(w / Real.sqrt 3) * Real.sin (θ - (k : ℝ) * (2 * Real.pi / 3)) := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_cos_fn'' w k θ).congr_of_eventuallyEq
  apply eventually_of_mem (Ioo_mem_nhds hlo hhi)
  intro θ' hθ'
  obtain ⟨hloθ', hhiθ'⟩ := hθ'
  have hmod := toIcoMod_k_int' k θ' hloθ' (by linarith [Real.pi_pos])
  simp only [reuleaux, reuleauxPiece, hmod]; rw [if_pos (by linarith)]

private lemma deriv_reuleaux_arc_eq'' (w : ℝ) (k : ℤ) (θ : ℝ)
    (hlo : Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3)) :
    deriv (reuleaux w) θ = (w / Real.sqrt 3) * Real.sin (θ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3) := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_arc_fn'' w k θ).congr_of_eventuallyEq
  apply eventually_of_mem (Ioo_mem_nhds hlo hhi)
  intro θ' hθ'
  obtain ⟨hloθ', hhiθ'⟩ := hθ'
  have hmod := toIcoMod_k_int' k θ' (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simp only [reuleaux, reuleauxPiece, hmod]; rw [if_neg (by linarith)]

private lemma differentiableAt_deriv_reuleaux_cos'' (w : ℝ) (k : ℤ) (θ : ℝ)
    (hlo : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) :
    DifferentiableAt ℝ (deriv (reuleaux w)) θ := by
  have hlocal : deriv (reuleaux w) =ᶠ[nhds θ]
      (fun θ' => -(w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3))) :=
    eventually_of_mem (Ioo_mem_nhds hlo hhi) fun θ' hθ' =>
      deriv_reuleaux_cos_eq'' w k θ' hθ'.1 hθ'.2
  exact hlocal.differentiableAt_iff.mpr (by fun_prop)

private lemma differentiableAt_deriv_reuleaux_arc'' (w : ℝ) (k : ℤ) (θ : ℝ)
    (hlo : Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3)) :
    DifferentiableAt ℝ (deriv (reuleaux w)) θ := by
  have hlocal : deriv (reuleaux w) =ᶠ[nhds θ]
      (fun θ' => (w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) :=
    eventually_of_mem (Ioo_mem_nhds hlo hhi) fun θ' hθ' =>
      deriv_reuleaux_arc_eq'' w k θ' hθ'.1 hθ'.2
  exact hlocal.differentiableAt_iff.mpr (by fun_prop)

private lemma dderiv_reuleaux_cos'' (w : ℝ) (k : ℤ) (θ : ℝ)
    (hlo : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) :
    deriv (deriv (reuleaux w)) θ = -(w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * Real.pi / 3)) := by
  have hlocal : deriv (reuleaux w) =ᶠ[nhds θ]
      (fun θ' => -(w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3))) :=
    eventually_of_mem (Ioo_mem_nhds hlo hhi) fun θ' hθ' =>
      deriv_reuleaux_cos_eq'' w k θ' hθ'.1 hθ'.2
  rw [hlocal.deriv_eq]
  exact ((hasDerivAt_sin_sub_kk' ((k : ℝ) * (2 * Real.pi / 3)) θ).const_mul
    (-(w / Real.sqrt 3))).congr_deriv (by ring) |>.deriv

private lemma dderiv_reuleaux_arc'' (w : ℝ) (k : ℤ) (θ : ℝ)
    (hlo : Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3)) :
    deriv (deriv (reuleaux w)) θ = (w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3) := by
  have hlocal : deriv (reuleaux w) =ᶠ[nhds θ]
      (fun θ' => (w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) :=
    eventually_of_mem (Ioo_mem_nhds hlo hhi) fun θ' hθ' =>
      deriv_reuleaux_arc_eq'' w k θ' hθ'.1 hθ'.2
  rw [hlocal.deriv_eq]
  -- Compute deriv of (w/√3)*sin(θ' - k*(2π/3) - π/3) at θ
  have hd : HasDerivAt (fun θ' => (w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3))
      ((w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) θ := by
    have h1 : HasDerivAt (fun θ' => (w / Real.sqrt 3) * Real.sin (θ' - ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3)))
        ((w / Real.sqrt 3) * Real.cos (θ - ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3))) θ :=
      ((hasDerivAt_sin_sub_kk' ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3) θ).const_mul (w / Real.sqrt 3))
    rwa [show (fun θ' => (w / Real.sqrt 3) * Real.sin (θ' - ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3))) =
              (fun θ' => (w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) from by
          ext θ''; congr 2; ring,
         show θ - ((k : ℝ) * (2 * Real.pi / 3) + Real.pi / 3) =
              θ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3 from by ring] at h1
  exact hd.deriv

-- ========== Smooth (ContDiff ℝ 1) ==========

-- Helper: HasDerivAt at the π/6 breakpoint (cos→arc transition in period 0)
private lemma hasDerivAt_reuleaux_pi6 (w : ℝ) :
    HasDerivAt (reuleaux w) (-(w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (Real.pi / 6) := by
  have hd_cos : HasDerivAt (fun θ => (w / Real.sqrt 3) * Real.cos θ)
      (-(w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (Real.pi / 6) :=
    ((Real.hasDerivAt_cos _).const_mul _).congr_deriv (by ring)
  have hd_arc : HasDerivAt (fun θ => w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi / 3))
      (-(w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (Real.pi / 6) := by
    have h1 : HasDerivAt (fun θ => θ - Real.pi / 3) 1 (Real.pi / 6) :=
      ((hasDerivAt_id _).sub (hasDerivAt_const _ _)).congr_deriv (by ring)
    have h2 := (Real.hasDerivAt_cos _).comp _ h1
    have h3 := ((hasDerivAt_const _ w).sub (h2.const_mul (w / Real.sqrt 3)))
    exact h3.congr_deriv (by
      simp only [mul_one, neg_mul]
      rw [show Real.pi / 6 - Real.pi / 3 = -(Real.pi / 6) from by ring, Real.sin_neg]; ring)
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · apply (hd_cos.tendsto_slope.mono_left (nhdsLT_le_nhdsNE _)).congr'
    apply Filter.eventually_of_mem (Ioo_mem_nhdsLT (by positivity : (0 : ℝ) < Real.pi / 6))
    intro θ ⟨hlo, hhi⟩
    have hmod : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ := by
      rw [toIcoMod_eq_self]; constructor <;> linarith [Real.pi_pos]
    have hmod6 : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (Real.pi / 6) = Real.pi / 6 := by
      rw [toIcoMod_eq_self]; constructor <;> linarith [Real.pi_pos]
    have hθ : reuleaux w θ = (w / Real.sqrt 3) * Real.cos θ := by
      simp only [reuleaux, reuleauxPiece, hmod]; rw [if_pos (le_of_lt hhi)]
    have h6 : reuleaux w (Real.pi / 6) = (w / Real.sqrt 3) * Real.cos (Real.pi / 6) := by
      simp only [reuleaux, reuleauxPiece, hmod6]; rw [if_pos le_rfl]
    simp only [slope, hθ, h6]
  · apply (hd_arc.tendsto_slope.mono_left (nhdsGT_le_nhdsNE _)).congr'
    apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : Real.pi / 6 < Real.pi / 2))
    intro θ ⟨hlo, hhi⟩
    have hmod : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ := by
      rw [toIcoMod_eq_self]; constructor <;> linarith [Real.pi_pos]
    have hmod6 : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (Real.pi / 6) = Real.pi / 6 := by
      rw [toIcoMod_eq_self]; constructor <;> linarith [Real.pi_pos]
    have hθ : reuleaux w θ = w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi / 3) := by
      simp only [reuleaux, reuleauxPiece, hmod]; rw [if_neg (not_le.mpr hlo)]
    have h6 : reuleaux w (Real.pi / 6) = w - (w / Real.sqrt 3) * Real.cos (Real.pi / 6 - Real.pi / 3) := by
      simp only [reuleaux, reuleauxPiece, hmod6]; rw [if_pos le_rfl]
      rw [show Real.pi / 6 - Real.pi / 3 = -(Real.pi / 6) from by ring, Real.cos_neg, Real.cos_pi_div_six]
      have h : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      field_simp; nlinarith
    simp only [slope, hθ, h6]

-- Period 2π/3 (from toIcoMod definition)
private lemma reuleaux_periodic_third (w : ℝ) (θ : ℝ) :
    reuleaux w (θ + 2 * Real.pi / 3) = reuleaux w θ := by
  simp only [reuleaux]
  congr 1
  have heq : θ + 2 * Real.pi / 3 = θ + (1 : ℤ) • (2 * Real.pi / 3) := by
    simp [zsmul_eq_mul]
  rw [heq]
  exact toIcoMod_add_zsmul reuleaux_period_pos (-(Real.pi / 6)) θ 1

-- Integer periodicity: reuleaux w (t + n*(2π/3)) = reuleaux w t for n : ℤ
private lemma reuleaux_period_shift (w : ℝ) (n : ℤ) (t : ℝ) :
    reuleaux w (t + (n : ℝ) * (2 * Real.pi / 3)) = reuleaux w t := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show t + (↑k + 1) * (2 * Real.pi / 3) = t + ↑k * (2 * Real.pi / 3) + 2 * Real.pi / 3 from by ring]
    rw [reuleaux_periodic_third]; exact ih
  | pred k ih =>
    push_cast at ih ⊢
    rw [show t + (-↑k - 1) * (2 * Real.pi / 3) = t + -↑k * (2 * Real.pi / 3) - 2 * Real.pi / 3 from by ring]
    have : reuleaux w (t + -↑k * (2 * Real.pi / 3) - 2 * Real.pi / 3 + 2 * Real.pi / 3) =
        reuleaux w (t + -↑k * (2 * Real.pi / 3) - 2 * Real.pi / 3) :=
      reuleaux_periodic_third w _
    rw [show t + -↑k * (2 * Real.pi / 3) - 2 * Real.pi / 3 + 2 * Real.pi / 3 =
        t + -↑k * (2 * Real.pi / 3) from by ring] at this
    rw [← this]; exact ih

-- HasDerivAt at any breakpoint π/6 + k*(2π/3) via periodicity
private lemma hasDerivAt_reuleaux_kbreak (w : ℝ) (k : ℤ) :
    HasDerivAt (reuleaux w) (-(w / Real.sqrt 3) * Real.sin (Real.pi / 6))
      (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) := by
  have hfun : ∀ t, reuleaux w t = reuleaux w (t - (k : ℝ) * (2 * Real.pi / 3)) := fun t => by
    have h := reuleaux_period_shift w k (t - (k : ℝ) * (2 * Real.pi / 3))
    rwa [show t - (k : ℝ) * (2 * Real.pi / 3) + (k : ℝ) * (2 * Real.pi / 3) = t from by ring] at h
  have hfunEq : reuleaux w =ᶠ[𝓝 (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3))]
      (fun t => reuleaux w (t - (k : ℝ) * (2 * Real.pi / 3))) :=
    Filter.Eventually.of_forall hfun
  apply hfunEq.hasDerivAt_iff.mpr
  have h1 : HasDerivAt (fun t => t - (k : ℝ) * (2 * Real.pi / 3)) 1
      (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) :=
    ((hasDerivAt_id _).sub (hasDerivAt_const _ _)).congr_deriv (by ring)
  have hpi6 : HasDerivAt (reuleaux w) (-(w / Real.sqrt 3) * Real.sin (Real.pi / 6))
      ((fun t => t - (k : ℝ) * (2 * Real.pi / 3)) (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3))) := by
    simp only [show Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) - (k : ℝ) * (2 * Real.pi / 3) =
        Real.pi / 6 from by ring]
    exact hasDerivAt_reuleaux_pi6 w
  exact (hpi6.comp (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) h1).congr_deriv (mul_one _)

-- HasDerivAt at -(π/6) + k*(2π/3): function is differentiable there
private lemma hasDerivAt_reuleaux_neg_pi6_kbreak (w : ℝ) (k : ℤ) :
    HasDerivAt (reuleaux w) ((w / Real.sqrt 3) * Real.sin (Real.pi / 6))
      (-(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3)) := by
  -- Reduce to k=0 via periodicity shift
  have hfun : ∀ t, reuleaux w t = reuleaux w (t - (k : ℝ) * (2 * Real.pi / 3)) := fun t => by
    have h := reuleaux_period_shift w k (t - (k : ℝ) * (2 * Real.pi / 3))
    rwa [show t - (k : ℝ) * (2 * Real.pi / 3) + (k : ℝ) * (2 * Real.pi / 3) = t from by ring] at h
  have hfunEq : reuleaux w =ᶠ[𝓝 (-(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3))]
      (fun t => reuleaux w (t - (k : ℝ) * (2 * Real.pi / 3))) :=
    Filter.Eventually.of_forall hfun
  apply hfunEq.hasDerivAt_iff.mpr
  have h1 : HasDerivAt (fun t => t - (k : ℝ) * (2 * Real.pi / 3)) 1
      (-(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3)) :=
    ((hasDerivAt_id _).sub (hasDerivAt_const _ _)).congr_deriv (by ring)
  -- HasDerivAt reuleaux at -(π/6): prove using hasDerivAt_iff_tendsto_slope_left_right
  have hneg_pi6 : HasDerivAt (reuleaux w) ((w / Real.sqrt 3) * Real.sin (Real.pi / 6))
      ((fun t => t - (k : ℝ) * (2 * Real.pi / 3)) (-(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3))) := by
    simp only [show -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) - (k : ℝ) * (2 * Real.pi / 3) =
        -(Real.pi / 6) from by ring]
    -- Arc formula derivative: w - (w/√3)*cos(θ+π/3), deriv = (w/√3)*sin(θ+π/3). At -(π/6): (w/√3)*sin(π/6)
    have hd_arc : HasDerivAt (fun θ => w - (w / Real.sqrt 3) * Real.cos (θ + Real.pi / 3))
        ((w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (-(Real.pi / 6)) := by
      have hadd : HasDerivAt (fun θ => θ + Real.pi / 3) 1 (-(Real.pi / 6)) :=
        ((hasDerivAt_id _).add (hasDerivAt_const _ _)).congr_deriv (by ring)
      have h2 := (Real.hasDerivAt_cos _).comp _ hadd
      have h3 := ((hasDerivAt_const _ w).sub (h2.const_mul (w / Real.sqrt 3)))
      exact h3.congr_deriv (by
        simp only [mul_one]
        rw [show -(Real.pi / 6) + Real.pi / 3 = Real.pi / 6 from by ring]; ring)
    -- Cos formula derivative: (w/√3)*cos θ, deriv = -(w/√3)*sin θ. At -(π/6): (w/√3)*sin(π/6)
    have hd_cos : HasDerivAt (fun θ => (w / Real.sqrt 3) * Real.cos θ)
        ((w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (-(Real.pi / 6)) :=
      ((Real.hasDerivAt_cos (-(Real.pi / 6))).const_mul (w / Real.sqrt 3)).congr_deriv (by
        rw [Real.sin_neg]; ring)
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    constructor
    · -- Left: arc piece (θ ∈ (-π/2, -π/6))
      apply (hd_arc.tendsto_slope.mono_left (nhdsLT_le_nhdsNE _)).congr'
      apply Filter.eventually_of_mem
        (Ioo_mem_nhdsLT (show -(Real.pi / 2) < -(Real.pi / 6) by linarith [Real.pi_pos]))
      intro θ ⟨hlo, hhi⟩
      have hmod : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ + 2 * Real.pi / 3 := by
        rw [toIcoMod_eq_iff]
        exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
               -1, by push_cast; ring⟩
      have hmodneg : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (-(Real.pi / 6)) = -(Real.pi / 6) := by
        rw [toIcoMod_eq_self]; exact ⟨le_refl _, by linarith [Real.pi_pos, reuleaux_period_pos]⟩
      -- reuleaux at θ ∈ (-π/2,-π/6) = arc formula w - (w/√3)*cos(θ + π/3)
      have hθ : reuleaux w θ = w - (w / Real.sqrt 3) * Real.cos (θ + Real.pi / 3) := by
        simp only [reuleaux, reuleauxPiece, hmod]
        rw [if_neg (by linarith)]
        congr 1; congr 1; push_cast; ring
      -- base value via arc formula: reuleaux w (-(π/6)) = w - (w/√3)*cos(-(π/6)+π/3)
      have h6 : reuleaux w (-(Real.pi / 6)) = w - (w / Real.sqrt 3) * Real.cos (-(Real.pi / 6) + Real.pi / 3) := by
        have hcosval : reuleaux w (-(Real.pi / 6)) = (w / Real.sqrt 3) * Real.cos (-(Real.pi / 6)) := by
          simp only [reuleaux, reuleauxPiece, hmodneg]; rw [if_pos (by linarith [Real.pi_pos])]
        rw [hcosval, show -(Real.pi / 6) + Real.pi / 3 = Real.pi / 6 from by ring,
            Real.cos_neg, Real.cos_pi_div_six]
        have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
        field_simp; nlinarith
      simp only [slope, hθ, h6]
    · -- Right: cos piece (θ ∈ (-π/6, π/6))
      apply (hd_cos.tendsto_slope.mono_left (nhdsGT_le_nhdsNE _)).congr'
      apply Filter.eventually_of_mem
        (Ioo_mem_nhdsGT (show -(Real.pi / 6) < Real.pi / 6 by linarith [Real.pi_pos]))
      intro θ ⟨hlo, hhi⟩
      have hmod : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ := by
        rw [toIcoMod_eq_self]; exact ⟨by linarith, by linarith [Real.pi_pos]⟩
      have hmodneg : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (-(Real.pi / 6)) = -(Real.pi / 6) := by
        rw [toIcoMod_eq_self]; exact ⟨le_refl _, by linarith [Real.pi_pos, reuleaux_period_pos]⟩
      have hθ : reuleaux w θ = (w / Real.sqrt 3) * Real.cos θ := by
        simp only [reuleaux, reuleauxPiece, hmod]; rw [if_pos (by linarith)]
      have h6 : reuleaux w (-(Real.pi / 6)) = (w / Real.sqrt 3) * Real.cos (-(Real.pi / 6)) := by
        simp only [reuleaux, reuleauxPiece, hmodneg]; rw [if_pos (by linarith [Real.pi_pos])]
      simp only [slope, hθ, h6]
  exact (hneg_pi6.comp (-(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3)) h1).congr_deriv (mul_one _)

private lemma reuleaux_smooth' (w : ℝ) : ContDiff ℝ 1 (reuleaux w) := by
  rw [contDiff_one_iff_deriv]
  have toIco_k : ∀ (k : ℤ) (θ : ℝ),
      -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ →
      θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3) →
      toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ - (k : ℝ) * (2 * Real.pi / 3) := by
    intro k θ hlo hhi
    rw [toIcoMod_eq_iff]
    exact ⟨⟨by linarith, by linarith [Real.pi_pos]⟩, k, by simp only [zsmul_eq_mul]; push_cast; ring⟩
  constructor
  · -- Differentiable ℝ (reuleaux w)
    intro θ
    set p := toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ
    have hp_range := toIcoMod_mem_Ico reuleaux_period_pos (-(Real.pi / 6)) θ
    obtain ⟨k, hk⟩ : ∃ k : ℤ, θ = p + (k : ℝ) * (2 * Real.pi / 3) := by
      use toIcoDiv reuleaux_period_pos (-(Real.pi / 6)) θ
      have h := toIcoMod_add_toIcoDiv_zsmul reuleaux_period_pos (-(Real.pi / 6)) θ
      simp only [zsmul_eq_mul] at h; linarith
    rcases lt_trichotomy p (-(Real.pi / 6)) with h_neg | h_neg_eq | h_pos
    · -- p < -(π/6): impossible since p ∈ Ico (-(π/6)) ...
      exact absurd h_neg (not_lt.mpr hp_range.1)
    · -- p = -(π/6): left breakpoint
      rw [hk, h_neg_eq]
      exact (hasDerivAt_reuleaux_neg_pi6_kbreak w k).differentiableAt
    · rcases lt_or_ge p (Real.pi / 6) with hlt | hge
      · -- Cos piece: p ∈ (-(π/6), π/6)
        have hlocal : reuleaux w =ᶠ[𝓝 θ]
            (fun θ' => (w / Real.sqrt 3) * Real.cos (θ' - (k : ℝ) * (2 * Real.pi / 3))) :=
          Filter.eventually_of_mem
            (show Ioo (-(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3))
                (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) ∈ 𝓝 θ from
              Ioo_mem_nhds (by rw [hk]; linarith) (by rw [hk]; linarith))
            fun θ' hθ' => by
              have hmod := toIco_k k θ' hθ'.1 (by linarith [Real.pi_pos, hθ'.2])
              simp only [reuleaux, reuleauxPiece, hmod]; rw [if_pos (by linarith [hθ'.2])]
        exact (Filter.EventuallyEq.differentiableAt_iff hlocal).mpr (by fun_prop)
      · rcases eq_or_lt_of_le hge with heq | hgt
        · -- Breakpoint p = π/6 (heq : π/6 = p)
          rw [hk, ← heq]
          exact (hasDerivAt_reuleaux_kbreak w k).differentiableAt
        · -- Arc piece: p ∈ (π/6, π/2)
          have hhi_θ : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3) := by
            rw [hk]; linarith [hp_range.2, show -(Real.pi / 6) + 2 * Real.pi / 3 = Real.pi / 2 from by ring]
          have hlocal : reuleaux w =ᶠ[𝓝 θ]
              (fun θ' => w - (w / Real.sqrt 3) * Real.cos (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) :=
            Filter.eventually_of_mem
              (show Ioo (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3))
                  (Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3)) ∈ 𝓝 θ from
                Ioo_mem_nhds (by rw [hk]; linarith) hhi_θ)
              fun θ' hθ' => by
                have hmod := toIco_k k θ' (by linarith [Real.pi_pos, hθ'.1]) (by linarith [hθ'.2])
                simp only [reuleaux, reuleauxPiece, hmod]; rw [if_neg (by linarith [hθ'.1])]
          exact (Filter.EventuallyEq.differentiableAt_iff hlocal).mpr (by fun_prop)
  · -- Continuous (deriv (reuleaux w))
    apply continuous_iff_continuousAt.mpr
    intro θ
    set p := toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ
    have hp_range := toIcoMod_mem_Ico reuleaux_period_pos (-(Real.pi / 6)) θ
    obtain ⟨k, hk⟩ : ∃ k : ℤ, θ = p + (k : ℝ) * (2 * Real.pi / 3) := by
      use toIcoDiv reuleaux_period_pos (-(Real.pi / 6)) θ
      have h := toIcoMod_add_toIcoDiv_zsmul reuleaux_period_pos (-(Real.pi / 6)) θ
      simp only [zsmul_eq_mul] at h; linarith
    have hhi_θ : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3) := by
      rw [hk]; linarith [hp_range.2, show -(Real.pi / 6) + 2 * Real.pi / 3 = Real.pi / 2 from by ring]
    rcases lt_trichotomy p (-(Real.pi / 6)) with h_neg | h_neg_eq | h_pos
    · exact absurd h_neg (not_lt.mpr hp_range.1)
    · -- p = -(π/6): left breakpoint - continuity of deriv
      have hθ_eq : θ = -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) := by rw [hk, h_neg_eq]
      subst hθ_eq
      set θ0 := -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3)
      rw [continuousAt_iff_continuous_left_right]
      have hval : deriv (reuleaux w) θ0 = (w / Real.sqrt 3) * Real.sin (Real.pi / 6) :=
        (hasDerivAt_reuleaux_neg_pi6_kbreak w k).deriv
      constructor
      · -- Left: arc piece deriv = (w/√3)*sin(θ' - (k-1)*(2π/3) - π/3) → (w/√3)*sin(π/6)
        show Filter.Tendsto (deriv (reuleaux w)) (nhdsWithin θ0 (Iic θ0)) (nhds (deriv (reuleaux w) θ0))
        rw [hval]
        have hev : (λ θ' => (w / Real.sqrt 3) * Real.sin (θ' - ((k - 1 : ℤ) : ℝ) * (2 * Real.pi / 3) - Real.pi / 3))
            =ᶠ[nhdsWithin θ0 (Iic θ0)] deriv (reuleaux w) := by
          apply Filter.eventually_of_mem
            (Ioc_mem_nhdsLE (show θ0 - Real.pi / 3 < θ0 by linarith [Real.pi_pos]))
          intro θ' ⟨hlo', hhi'⟩
          rcases eq_or_lt_of_le hhi' with rfl | hlt'
          · rw [hval]; push_cast
            congr 1; congr 1
            simp only [θ0]; push_cast; ring
          · have hlo_k1 : Real.pi / 6 + ((k - 1 : ℤ) : ℝ) * (2 * Real.pi / 3) < θ' := by
              push_cast; simp only [θ0] at hlo'; push_cast at hlo'; linarith
            have hhi_k1 : θ' < Real.pi / 2 + ((k - 1 : ℤ) : ℝ) * (2 * Real.pi / 3) := by
              push_cast; simp only [θ0] at hlt'; push_cast at hlt'; linarith [Real.pi_pos]
            exact (deriv_reuleaux_arc_eq'' w (k - 1) θ' hlo_k1 hhi_k1).symm
        have hcont : ContinuousAt
            (λ θ' => (w / Real.sqrt 3) * Real.sin (θ' - ((k - 1 : ℤ) : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) θ0 :=
          by fun_prop
        have heq2 : (w / Real.sqrt 3) * Real.sin (θ0 - ((k - 1 : ℤ) : ℝ) * (2 * Real.pi / 3) - Real.pi / 3) =
            (w / Real.sqrt 3) * Real.sin (Real.pi / 6) := by
          push_cast; congr 1; congr 1
          simp only [θ0]; push_cast; ring
        exact Filter.Tendsto.congr' hev (heq2 ▸ hcont.continuousWithinAt)
      · -- Right: cos piece deriv = -(w/√3)*sin(θ' - k*(2π/3)) → (w/√3)*sin(π/6)
        show Filter.Tendsto (deriv (reuleaux w)) (nhdsWithin θ0 (Ici θ0)) (nhds (deriv (reuleaux w) θ0))
        rw [hval]
        have hev : (λ θ' => -(w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3)))
            =ᶠ[nhdsWithin θ0 (Ici θ0)] deriv (reuleaux w) := by
          apply Filter.eventually_of_mem
            (Ico_mem_nhdsGE (show θ0 < Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) by
              simp only [θ0]; linarith [Real.pi_pos]))
          intro θ' ⟨hlo', hhi'⟩
          rcases eq_or_lt_of_le hlo' with rfl | hlt'
          · rw [hval]
            simp only [θ0]
            rw [show -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) - (k : ℝ) * (2 * Real.pi / 3) =
                -(Real.pi / 6) from by ring, Real.sin_neg]; ring
          · exact (deriv_reuleaux_cos_eq'' w k θ' (by
              simp only [θ0] at hlt' ⊢; linarith) hhi').symm
        have hcont : ContinuousAt
            (λ θ' => -(w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3))) θ0 := by fun_prop
        have heq2 : -(w / Real.sqrt 3) * Real.sin (θ0 - (k : ℝ) * (2 * Real.pi / 3)) =
            (w / Real.sqrt 3) * Real.sin (Real.pi / 6) := by
          simp only [θ0]
          rw [show -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) - (k : ℝ) * (2 * Real.pi / 3) =
              -(Real.pi / 6) from by ring, Real.sin_neg]; ring
        exact Filter.Tendsto.congr' hev (heq2 ▸ hcont.continuousWithinAt)
    · rcases lt_or_ge p (Real.pi / 6) with hlt | hge
      · -- Cos piece: deriv locally = -(w/√3)*sin(θ' - k*(2π/3))
        have hlocal : deriv (reuleaux w) =ᶠ[𝓝 θ]
            (fun θ' => -(w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3))) :=
          Filter.eventually_of_mem
            (show Ioo (-(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3))
                (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) ∈ 𝓝 θ from
              Ioo_mem_nhds (by rw [hk]; linarith) (by rw [hk]; linarith))
            fun θ' hθ' => deriv_reuleaux_cos_eq'' w k θ' hθ'.1 hθ'.2
        exact ContinuousAt.congr (by fun_prop : ContinuousAt
            (fun θ' => -(w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3))) θ) hlocal.symm
      · rcases eq_or_lt_of_le hge with heq | hgt
        · -- Breakpoint p = π/6: continuity via Tendsto.congr'
          have hθ_eq : θ = Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) := by rw [hk, ← heq]
          subst hθ_eq
          set θ0 := Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)
          rw [continuousAt_iff_continuous_left_right]
          have hval : deriv (reuleaux w) θ0 = -(w / Real.sqrt 3) * Real.sin (Real.pi / 6) :=
            (hasDerivAt_reuleaux_kbreak w k).deriv
          constructor
          · -- Left continuity: deriv equals cos formula on left neighborhood
            show Filter.Tendsto (deriv (reuleaux w)) (nhdsWithin θ0 (Iic θ0))
                (nhds (deriv (reuleaux w) θ0))
            rw [hval]
            have hev : (λ θ' => -(w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3)))
                =ᶠ[nhdsWithin θ0 (Iic θ0)] deriv (reuleaux w) := by
              apply Filter.eventually_of_mem
                (Ioc_mem_nhdsLE (show -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ0 by
                  simp only [θ0]; linarith [Real.pi_pos]))
              intro θ' ⟨hlo', hhi'⟩
              rcases eq_or_lt_of_le hhi' with rfl | hlt'
              · rw [hval]; simp only [θ0]; congr 1; congr 1; ring
              · exact (deriv_reuleaux_cos_eq'' w k θ' (by
                  have : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ0 := by
                    simp only [θ0]; linarith [Real.pi_pos]
                  linarith) hlt').symm
            have hcont : ContinuousAt
                (λ θ' => -(w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3))) θ0 :=
              by fun_prop
            have heq2 : -(w / Real.sqrt 3) * Real.sin (θ0 - (k : ℝ) * (2 * Real.pi / 3)) =
                -(w / Real.sqrt 3) * Real.sin (Real.pi / 6) := by
              simp only [θ0]; congr 1; congr 1; ring
            exact Filter.Tendsto.congr' hev (heq2 ▸ hcont.continuousWithinAt)
          · -- Right continuity: deriv equals arc formula on right neighborhood
            show Filter.Tendsto (deriv (reuleaux w)) (nhdsWithin θ0 (Ici θ0))
                (nhds (deriv (reuleaux w) θ0))
            rw [hval]
            have hev : (λ θ' => (w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3))
                =ᶠ[nhdsWithin θ0 (Ici θ0)] deriv (reuleaux w) := by
              apply Filter.eventually_of_mem
                (Ico_mem_nhdsGE (show θ0 < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3) by
                  simp only [θ0]; linarith [Real.pi_pos]))
              intro θ' ⟨hlo', hhi'⟩
              rcases eq_or_lt_of_le hlo' with rfl | hlt'
              · rw [hval]
                have heq3' : (w / Real.sqrt 3) * Real.sin (θ0 - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3) =
                    -(w / Real.sqrt 3) * Real.sin (Real.pi / 6) := by
                  simp only [θ0]
                  rw [show Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3 =
                      -(Real.pi / 6) from by ring, Real.sin_neg]; ring
                exact heq3'
              · exact (deriv_reuleaux_arc_eq'' w k θ' hlt' hhi').symm
            have hcont : ContinuousAt
                (λ θ' => (w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) θ0 :=
              by fun_prop
            have heq3 : (w / Real.sqrt 3) * Real.sin (θ0 - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3) =
                -(w / Real.sqrt 3) * Real.sin (Real.pi / 6) := by
              simp only [θ0]
              rw [show Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3 =
                  -(Real.pi / 6) from by ring, Real.sin_neg]; ring
            exact Filter.Tendsto.congr' hev (heq3 ▸ hcont.continuousWithinAt)

        · -- Arc piece: deriv locally = (w/√3)*sin(θ' - k*(2π/3) - π/3)
          have hlocal : deriv (reuleaux w) =ᶠ[𝓝 θ]
              (fun θ' => (w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) :=
            Filter.eventually_of_mem
              (show Ioo (Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3))
                  (Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3)) ∈ 𝓝 θ from
                Ioo_mem_nhds (by rw [hk]; linarith) hhi_θ)
              fun θ' hθ' => deriv_reuleaux_arc_eq'' w k θ' hθ'.1 hθ'.2
          exact ContinuousAt.congr (by fun_prop : ContinuousAt
              (fun θ' => (w / Real.sqrt 3) * Real.sin (θ' - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3)) θ) hlocal.symm

-- ========== h + h'' formulas ==========

private lemma reuleaux_hphdd_cos'' (w : ℝ) (k : ℤ) (θ : ℝ)
    (hlo : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3)) :
    reuleaux w θ + deriv (deriv (reuleaux w)) θ = 0 := by
  have hmod := toIcoMod_k_int' k θ hlo (by linarith [Real.pi_pos])
  have hval : reuleaux w θ = (w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * Real.pi / 3)) := by
    simp only [reuleaux, reuleauxPiece, hmod]; rw [if_pos (by linarith)]
  rw [hval, dderiv_reuleaux_cos'' w k θ hlo hhi]; ring

private lemma reuleaux_hphdd_arc'' (w : ℝ) (k : ℤ) (θ : ℝ)
    (hlo : Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) < θ)
    (hhi : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3)) :
    reuleaux w θ + deriv (deriv (reuleaux w)) θ = w := by
  have hmod := toIcoMod_k_int' k θ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hval : reuleaux w θ = w - (w / Real.sqrt 3) * Real.cos (θ - (k : ℝ) * (2 * Real.pi / 3) - Real.pi / 3) := by
    simp only [reuleaux, reuleauxPiece, hmod]; rw [if_neg (by linarith)]
  rw [hval, dderiv_reuleaux_arc'' w k θ hlo hhi]; ring

-- ========== Breakpoint set and breaks field ==========

private def reuleaux_breaks' : Set ℝ :=
  (⋃ (n : ℤ), {Real.pi / 6 + (n : ℝ) * (2 * Real.pi / 3)}) ∪
  (⋃ (n : ℤ), {-(Real.pi / 6) + (n : ℝ) * (2 * Real.pi / 3)})

private lemma reuleaux_breaks_countable' : reuleaux_breaks'.Countable :=
  (Set.countable_iUnion (fun _ => Set.countable_singleton _)).union
  (Set.countable_iUnion (fun _ => Set.countable_singleton _))

private lemma reuleaux_breaks_field' (w : ℝ) (hw : 0 < w) :
    ∀ θ ∉ reuleaux_breaks',
      DifferentiableAt ℝ (deriv (reuleaux w)) θ ∧
      0 ≤ reuleaux w θ + deriv (deriv (reuleaux w)) θ := by
  intro θ hθ
  set p := toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ with hp_def
  have hp_range : p ∈ Set.Ico (-(Real.pi / 6)) (-(Real.pi / 6) + 2 * Real.pi / 3) :=
    toIcoMod_mem_Ico reuleaux_period_pos (-(Real.pi / 6)) θ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, θ = p + (k : ℝ) * (2 * Real.pi / 3) := by
    use toIcoDiv reuleaux_period_pos (-(Real.pi / 6)) θ
    have h := toIcoMod_add_toIcoDiv_zsmul reuleaux_period_pos (-(Real.pi / 6)) θ
    simp only [zsmul_eq_mul] at h; linarith
  have hp_ne : p ≠ Real.pi / 6 := by
    intro heq; apply hθ
    simp only [reuleaux_breaks', Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff]
    exact Or.inl ⟨k, by rw [hk, heq]⟩
  have hp_lo_ne : p ≠ -(Real.pi / 6) := by
    intro heq; apply hθ
    simp only [reuleaux_breaks', Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff]
    exact Or.inr ⟨k, by rw [hk, heq]⟩
  have hp_lo : -(Real.pi / 6) < p := lt_of_le_of_ne hp_range.1 (Ne.symm hp_lo_ne)
  have hlo_θ : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ := by rw [hk]; linarith
  have hhi_θ : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3) := by
    rw [hk]; linarith [hp_range.2, show -(Real.pi / 6) + 2 * Real.pi / 3 = Real.pi / 2 from by ring]
  rcases lt_or_gt_of_ne hp_ne with hlt | hgt
  · have hhi : θ < Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) := by rw [hk]; linarith
    refine ⟨differentiableAt_deriv_reuleaux_cos'' w k θ hlo_θ hhi, ?_⟩
    rw [reuleaux_hphdd_cos'' w k θ hlo_θ hhi]
  · have hlo : Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) < θ := by rw [hk]; linarith
    refine ⟨differentiableAt_deriv_reuleaux_arc'' w k θ hlo hhi_θ, ?_⟩
    rw [reuleaux_hphdd_arc'' w k θ hlo hhi_θ]; exact hw.le

-- ========== Measurability ==========

private lemma measurable_toIcoMod_reuleaux :
    Measurable (toIcoMod reuleaux_period_pos (-(Real.pi / 6))) := by
  apply ContinuousOn.measurable_of_countable_compl
    (s := {x | ¬x ≡ -(Real.pi / 6) [PMOD (2 * Real.pi / 3)]})
  · intro x hx
    exact (continuousAt_toIcoMod reuleaux_period_pos _ hx).continuousWithinAt
  · have hsub : {x : ℝ | x ≡ -(Real.pi / 6) [PMOD (2 * Real.pi / 3)]} ⊆
        ⋃ (n : ℤ), ({-(Real.pi / 6) + (n : ℝ) * (2 * Real.pi / 3)} : Set ℝ) := by
      intro x (heq : x ≡ -(Real.pi / 6) [PMOD (2 * Real.pi / 3)])
      rw [modEq_iff_zsmul] at heq
      obtain ⟨m, hm⟩ := heq; simp only [zsmul_eq_mul] at hm
      have hx : x = -(Real.pi / 6) + (-m : ℤ) * (2 * Real.pi / 3) := by push_cast; linarith
      rw [hx]; exact Set.mem_iUnion_of_mem (-m) (Set.mem_singleton _)
    apply (Set.countable_iUnion (fun (n : ℤ) => Set.countable_singleton _)).mono
    calc {x | ¬x ≡ -(Real.pi / 6) [PMOD (2 * Real.pi / 3)]}ᶜ
        = {x | x ≡ -(Real.pi / 6) [PMOD (2 * Real.pi / 3)]} := by ext x; simp
      _ ⊆ ⋃ (n : ℤ), ({-(Real.pi / 6) + (n : ℝ) * (2 * Real.pi / 3)} : Set ℝ) := hsub

private lemma measurable_reuleaux (w : ℝ) : Measurable (reuleaux w) := by
  have h1 : Measurable (fun p : ℝ => reuleauxPiece w p) := by
    unfold reuleauxPiece
    exact Measurable.ite measurableSet_Iic
      (measurable_const.mul Real.measurable_cos)
      (measurable_const.sub (measurable_const.mul
        (Real.measurable_cos.comp (measurable_id.sub measurable_const))))
  exact h1.comp measurable_toIcoMod_reuleaux

-- ========== Integrable ==========

-- Bound on |h + h''| for θ NOT in breakpoints
private lemma reuleaux_hphdd_bound_nbp (w : ℝ) (hw : 0 < w) (θ : ℝ) (hθ : θ ∉ reuleaux_breaks') :
    |reuleaux w θ + deriv (deriv (reuleaux w)) θ| ≤ 2 * w := by
  set p := toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ
  have hp_range := toIcoMod_mem_Ico reuleaux_period_pos (-(Real.pi / 6)) θ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, θ = p + (k : ℝ) * (2 * Real.pi / 3) := by
    use toIcoDiv reuleaux_period_pos (-(Real.pi / 6)) θ
    have h := toIcoMod_add_toIcoDiv_zsmul reuleaux_period_pos (-(Real.pi / 6)) θ
    simp only [zsmul_eq_mul] at h; linarith
  have hp_ne : p ≠ Real.pi / 6 := by
    intro heq; apply hθ
    simp only [reuleaux_breaks', Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff]
    exact Or.inl ⟨k, by rw [hk, heq]⟩
  have hp_lo_ne : p ≠ -(Real.pi / 6) := by
    intro heq; apply hθ
    simp only [reuleaux_breaks', Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff]
    exact Or.inr ⟨k, by rw [hk, heq]⟩
  have hp_lo : -(Real.pi / 6) < p := lt_of_le_of_ne hp_range.1 (Ne.symm hp_lo_ne)
  have hlo_θ : -(Real.pi / 6) + (k : ℝ) * (2 * Real.pi / 3) < θ := by rw [hk]; linarith
  have hhi_θ : θ < Real.pi / 2 + (k : ℝ) * (2 * Real.pi / 3) := by
    rw [hk]; linarith [hp_range.2, show -(Real.pi / 6) + 2 * Real.pi / 3 = Real.pi / 2 from by ring]
  rcases lt_or_gt_of_ne hp_ne with hlt | hgt
  · -- cos piece: h + h'' = 0
    have hhi : θ < Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) := by rw [hk]; linarith
    rw [reuleaux_hphdd_cos'' w k θ hlo_θ hhi, abs_zero]; linarith
  · -- arc piece: h + h'' = w
    have hlo : Real.pi / 6 + (k : ℝ) * (2 * Real.pi / 3) < θ := by rw [hk]; linarith
    rw [reuleaux_hphdd_arc'' w k θ hlo hhi_θ, abs_of_pos hw]; linarith

private lemma reuleaux_integrable' (w : ℝ) (hw : 0 < w) :
    IntervalIntegrable (fun θ => reuleaux w θ + deriv (deriv (reuleaux w)) θ) volume 0 (2 * Real.pi) := by
  apply IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := 2 * w))
  · apply AEStronglyMeasurable.add
    · exact (measurable_reuleaux w).aestronglyMeasurable
    · exact (measurable_deriv (deriv (reuleaux w))).aestronglyMeasurable
  · -- Bound holds AE: the breakpoints are a null set (countable), bound holds off them
    apply ae_restrict_of_ae
    have hbreaks : ∀ᵐ θ ∂volume, θ ∉ reuleaux_breaks' := by
      rw [Filter.eventually_iff, mem_ae_iff]
      have : {x : ℝ | x ∉ reuleaux_breaks'}ᶜ = reuleaux_breaks' := by ext; simp
      rw [this]
      exact reuleaux_breaks_countable'.measure_zero volume
    filter_upwards [hbreaks] with θ hθ
    exact reuleaux_hphdd_bound_nbp w hw θ hθ


theorem reuleaux_constWidth {w : ℝ} (hw : 0 < w) : PiecewiseConstWidth (reuleaux w) w :=
  { smooth := reuleaux_smooth' w
    periodic := reuleaux_periodic w
    width := reuleaux_width w
    breaks := ⟨reuleaux_breaks', reuleaux_breaks_countable',
               fun θ hθ => (reuleaux_breaks_field' w hw θ hθ).1,
               fun θ hθ => (reuleaux_breaks_field' w hw θ hθ).2⟩
    integrable := reuleaux_integrable' w hw }

theorem reuleaux_perimeter {w : ℝ} (hw : 0 < w) : perimeter (reuleaux w) = π * w :=
  barbier_piecewise (reuleaux_constWidth hw)

theorem reuleaux_not_smooth {w : ℝ} (hw : 0 < w) : ¬ ContDiff ℝ 2 (reuleaux w) := by
  intro hC
  have hD : ContDiff ℝ 1 (deriv (reuleaux w)) := contDiff_one_deriv hC
  have hcont : Continuous (deriv (deriv (reuleaux w))) := hD.continuous_deriv_one
  have hcat : ContinuousAt (deriv (deriv (reuleaux w))) (Real.pi / 6) := hcont.continuousAt
  -- Second deriv = -(w/√3) cos θ on left interval
  have hleft_eq : ∀ᶠ θ in 𝓝[<] (Real.pi/6),
      deriv (deriv (reuleaux w)) θ = -(w / Real.sqrt 3) * Real.cos θ :=
    Filter.eventually_of_mem (Ioo_mem_nhdsLT pi6_neg_lt_pi6)
      (fun θ ⟨hlo, hhi⟩ => dderiv_left hlo hhi w hC)
  -- Second deriv = (w/√3) cos(θ - π/3) on right interval
  have hright_eq : ∀ᶠ θ in 𝓝[>] (Real.pi/6),
      deriv (deriv (reuleaux w)) θ = (w / Real.sqrt 3) * Real.cos (θ - Real.pi / 3) :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT' pi6_lt_pi2)
      (fun θ ⟨hlo, hhi⟩ => dderiv_right hlo hhi w hC)
  -- Compute limit values
  have hval_L : -(w / Real.sqrt 3) * Real.cos (Real.pi / 6) = -w / 2 := by
    rw [Real.cos_pi_div_six]; field_simp
  have hval_R : (w / Real.sqrt 3) * Real.cos (Real.pi / 6 - Real.pi / 3) = w / 2 := by
    rw [show Real.pi / 6 - Real.pi / 3 = -(Real.pi / 6) from by ring,
        Real.cos_neg, Real.cos_pi_div_six]; field_simp
  -- Left tendsto: dderiv → -w/2 from the left
  have hg_left : Filter.Tendsto (fun θ => -(w / Real.sqrt 3) * Real.cos θ)
      (𝓝[<] (Real.pi/6)) (𝓝 (-w / 2)) := by
    rw [← hval_L]
    have hcL : ContinuousAt (fun θ => -(w / Real.sqrt 3) * Real.cos θ) (Real.pi/6) := by fun_prop
    exact hcL.tendsto.mono_left nhdsWithin_le_nhds
  have hleft : Filter.Tendsto (deriv (deriv (reuleaux w)))
      (𝓝[<] (Real.pi/6)) (𝓝 (-w / 2)) :=
    Tendsto.congr' (Filter.EventuallyEq.symm hleft_eq) hg_left
  -- Right tendsto: dderiv → w/2 from the right
  have hg_right : Filter.Tendsto (fun θ => (w / Real.sqrt 3) * Real.cos (θ - Real.pi / 3))
      (𝓝[>] (Real.pi/6)) (𝓝 (w / 2)) := by
    rw [← hval_R]
    have hcR : ContinuousAt (fun θ => (w / Real.sqrt 3) * Real.cos (θ - Real.pi / 3))
        (Real.pi/6) := by fun_prop
    exact hcR.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Filter.Tendsto (deriv (deriv (reuleaux w)))
      (𝓝[>] (Real.pi/6)) (𝓝 (w / 2)) :=
    Tendsto.congr' (Filter.EventuallyEq.symm hright_eq) hg_right
  -- Both limits = dderiv(π/6) by continuity
  have hval_left : deriv (deriv (reuleaux w)) (Real.pi / 6) = -w / 2 :=
    tendsto_nhds_unique (hcat.tendsto.mono_left nhdsWithin_le_nhds) hleft
  have hval_right : deriv (deriv (reuleaux w)) (Real.pi / 6) = w / 2 :=
    tendsto_nhds_unique (hcat.tendsto.mono_left nhdsWithin_le_nhds) hright
  linarith

theorem reuleaux_vertices {w : ℝ} (hw : 0 < w) :
    dist (curve (reuleaux w) 0) (curve (reuleaux w) (2 * π / 3)) = w ∧
    dist (curve (reuleaux w) (2 * π / 3)) (curve (reuleaux w) (4 * π / 3)) = w ∧
    dist (curve (reuleaux w) (4 * π / 3)) (curve (reuleaux w) 0) = w :=
  ⟨dist_reuleaux_0_2pi3 hw, dist_reuleaux_2pi3_4pi3 hw, dist_reuleaux_4pi3_0 hw⟩


/-! Arc helpers: normSq at endpoints -/

private lemma normSq_diff_5pi6 :
    Complex.normSq ((↑(Real.cos (Real.pi / 6)) - ↑(Real.sin (Real.pi / 6)) * Complex.I) *
      Complex.exp (↑(5 * Real.pi / 6) * Complex.I) - 1) = 3 := by
  rw [Complex.normSq_apply, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
             Complex.I_re, Complex.I_im, Complex.one_re, Complex.add_im, Complex.sub_im,
             Complex.mul_im, Complex.one_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
             Complex.cos_ofReal_im, Complex.sin_ofReal_im,
             mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero]
  have hc : Real.cos (5 * Real.pi / 6) = -Real.sqrt 3 / 2 := by
    rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_six]; ring
  have hs : Real.sin (5 * Real.pi / 6) = 1 / 2 := by
    rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 from by ring,
        Real.sin_pi_sub, Real.sin_pi_div_six]
  rw [hc, hs, Real.cos_pi_div_six, Real.sin_pi_div_six]
  nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num), sqrt3_sq]

private lemma normSq_diff_7pi6 :
    Complex.normSq ((↑(Real.cos (Real.pi / 6)) + ↑(Real.sin (Real.pi / 6)) * Complex.I) *
      Complex.exp (↑(7 * Real.pi / 6) * Complex.I) - 1) = 3 := by
  rw [Complex.normSq_apply, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
             Complex.I_re, Complex.I_im, Complex.one_re, Complex.add_im, Complex.sub_im,
             Complex.mul_im, Complex.one_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
             Complex.cos_ofReal_im, Complex.sin_ofReal_im,
             mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero]
  have hc : Real.cos (7 * Real.pi / 6) = -Real.sqrt 3 / 2 := by
    rw [show 7 * Real.pi / 6 = Real.pi / 6 + Real.pi from by ring,
        Real.cos_add_pi, Real.cos_pi_div_six]; ring
  have hs : Real.sin (7 * Real.pi / 6) = -(1 / 2) := by
    rw [show 7 * Real.pi / 6 = Real.pi / 6 + Real.pi from by ring,
        Real.sin_add_pi, Real.sin_pi_div_six]
  rw [hc, hs, Real.cos_pi_div_six, Real.sin_pi_div_six]
  nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num), sqrt3_sq]

private lemma toIcoMod_5pi6_val :
    toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (5 * Real.pi / 6) = Real.pi / 6 := by
  rw [toIcoMod_eq_iff]
  exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, 1, by push_cast; ring⟩

private lemma toIcoMod_7pi6_val :
    toIcoMod reuleaux_period_pos (-(Real.pi / 6)) (7 * Real.pi / 6) = -(Real.pi / 6) := by
  rw [toIcoMod_eq_iff]
  exact ⟨⟨le_refl _, by linarith [Real.pi_pos]⟩, 2, by push_cast; ring⟩

private lemma toIcoMod_arc_int {θ : ℝ} (hlo : 5 * Real.pi / 6 < θ) (hhi : θ < 7 * Real.pi / 6) :
    toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ - 2 * Real.pi / 3 := by
  rw [toIcoMod_eq_iff]
  exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, 1, by push_cast; ring⟩

private lemma reuleaux_5pi6_val (w : ℝ) :
    reuleaux w (5 * Real.pi / 6) = w / Real.sqrt 3 * Real.cos (Real.pi / 6) := by
  simp [reuleaux, reuleauxPiece, toIcoMod_5pi6_val, if_pos le_rfl]

private lemma reuleaux_7pi6_val (w : ℝ) :
    reuleaux w (7 * Real.pi / 6) = w / Real.sqrt 3 * Real.cos (Real.pi / 6) := by
  simp only [reuleaux, reuleauxPiece, toIcoMod_7pi6_val]
  rw [if_pos (by linarith [Real.pi_pos] : -(Real.pi / 6) ≤ Real.pi / 6), Real.cos_neg]

private lemma reuleaux_arc_int_val {θ : ℝ} (hlo : 5 * Real.pi / 6 < θ) (hhi : θ < 7 * Real.pi / 6)
    (w : ℝ) : reuleaux w θ = w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi) := by
  simp only [reuleaux, reuleauxPiece, toIcoMod_arc_int hlo hhi]
  rw [if_neg (by linarith [Real.pi_pos] : ¬ θ - 2 * Real.pi / 3 ≤ Real.pi / 6)]
  congr 1; ring

private lemma reuleaux_left_piece {w θ : ℝ}
    (hlo : 2 * Real.pi / 3 ≤ θ) (hhi : θ ≤ 5 * Real.pi / 6) :
    reuleaux w θ = (w / Real.sqrt 3) * Real.cos (θ - 2 * Real.pi / 3) := by
  simp only [reuleaux, reuleauxPiece]
  have hmod : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ - 2 * Real.pi / 3 := by
    rw [toIcoMod_eq_iff]
    exact ⟨⟨by linarith, by linarith [Real.pi_pos]⟩, 1, by push_cast; ring⟩
  rw [hmod, if_pos (by linarith)]

private lemma reuleaux_right_piece {w θ : ℝ}
    (hlo : 5 * Real.pi / 6 ≤ θ) (hhi : θ ≤ 7 * Real.pi / 6) :
    reuleaux w θ = w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi) := by
  rcases eq_or_lt_of_le hlo with rfl | hlo'
  · rw [reuleaux_5pi6_val, show 5 * Real.pi / 6 - Real.pi = -(Real.pi / 6) from by ring,
        Real.cos_neg, Real.cos_pi_div_six]
    field_simp; nlinarith [sqrt3_sq, sqrt3_pos]
  · rcases eq_or_lt_of_le hhi with rfl | hhi'
    · rw [reuleaux_7pi6_val, show 7 * Real.pi / 6 - Real.pi = Real.pi / 6 from by ring,
          Real.cos_pi_div_six]
      field_simp; nlinarith [sqrt3_sq, sqrt3_pos]
    · exact reuleaux_arc_int_val hlo' hhi' w

private lemma reuleaux_right7_piece {w θ : ℝ}
    (hlo : 7 * Real.pi / 6 ≤ θ) (hhi : θ ≤ 4 * Real.pi / 3) :
    reuleaux w θ = (w / Real.sqrt 3) * Real.cos (θ - 4 * Real.pi / 3) := by
  rcases eq_or_lt_of_le hlo with rfl | hlo'
  · rw [reuleaux_7pi6_val, show 7 * Real.pi / 6 - 4 * Real.pi / 3 = -(Real.pi / 6) from by ring,
        Real.cos_neg]
  · simp only [reuleaux, reuleauxPiece]
    have hmod : toIcoMod reuleaux_period_pos (-(Real.pi / 6)) θ = θ - 4 * Real.pi / 3 := by
      rw [toIcoMod_eq_iff]
      exact ⟨⟨by linarith, by linarith [Real.pi_pos]⟩, 2, by push_cast; ring⟩
    rw [hmod, if_pos (by linarith)]

private lemma hasDerivAt_reuleaux_5pi6_val (w : ℝ) :
    HasDerivAt (reuleaux w) (-(w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (5 * Real.pi / 6) := by
  have hd_left : HasDerivAt (fun θ => (w / Real.sqrt 3) * Real.cos (θ - 2 * Real.pi / 3))
      (-(w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (5 * Real.pi / 6) := by
    have h := (hasDerivAt_cos_sub (2 * Real.pi / 3) (5 * Real.pi / 6)).const_mul (w / Real.sqrt 3)
    exact h.congr_deriv (by
      rw [show 5 * Real.pi / 6 - 2 * Real.pi / 3 = Real.pi / 6 from by ring]; ring)
  have hd_right : HasDerivAt (fun θ => w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi))
      (-(w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (5 * Real.pi / 6) := by
    have h := (hasDerivAt_cos_sub Real.pi (5 * Real.pi / 6)).const_mul (w / Real.sqrt 3)
    exact ((hasDerivAt_const _ w).sub h).congr_deriv (by
      rw [show 5 * Real.pi / 6 - Real.pi = -(Real.pi / 6) from by ring, Real.sin_neg]; ring)
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · apply (hd_left.tendsto_slope.mono_left (nhdsLT_le_nhdsNE _)).congr'
    apply Filter.eventually_of_mem
      (Ioo_mem_nhdsLT (show 2 * Real.pi / 3 < 5 * Real.pi / 6 by linarith [Real.pi_pos]))
    intro θ ⟨hlo, hhi⟩
    simp only [slope, reuleaux_left_piece (le_of_lt hlo) (le_of_lt hhi),
               reuleaux_left_piece (by linarith [Real.pi_pos]) le_rfl]
  · apply (hd_right.tendsto_slope.mono_left (nhdsGT_le_nhdsNE _)).congr'
    apply Filter.eventually_of_mem
      (Ioo_mem_nhdsGT (show 5 * Real.pi / 6 < 7 * Real.pi / 6 by linarith [Real.pi_pos]))
    intro θ ⟨hlo, hhi⟩
    simp only [slope, reuleaux_right_piece (le_of_lt hlo) (le_of_lt hhi),
               reuleaux_right_piece le_rfl (by linarith [Real.pi_pos])]

private lemma hasDerivAt_reuleaux_7pi6_val (w : ℝ) :
    HasDerivAt (reuleaux w) ((w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (7 * Real.pi / 6) := by
  have hd_left : HasDerivAt (fun θ => w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi))
      ((w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (7 * Real.pi / 6) := by
    have h := (hasDerivAt_cos_sub Real.pi (7 * Real.pi / 6)).const_mul (w / Real.sqrt 3)
    exact ((hasDerivAt_const _ w).sub h).congr_deriv (by
      rw [show 7 * Real.pi / 6 - Real.pi = Real.pi / 6 from by ring]; ring)
  have hd_right : HasDerivAt (fun θ => (w / Real.sqrt 3) * Real.cos (θ - 4 * Real.pi / 3))
      ((w / Real.sqrt 3) * Real.sin (Real.pi / 6)) (7 * Real.pi / 6) := by
    have h := (hasDerivAt_cos_sub (4 * Real.pi / 3) (7 * Real.pi / 6)).const_mul (w / Real.sqrt 3)
    exact h.congr_deriv (by
      rw [show 7 * Real.pi / 6 - 4 * Real.pi / 3 = -(Real.pi / 6) from by ring, Real.sin_neg]; ring)
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · apply (hd_left.tendsto_slope.mono_left (nhdsLT_le_nhdsNE _)).congr'
    apply Filter.eventually_of_mem
      (Ioo_mem_nhdsLT (show 5 * Real.pi / 6 < 7 * Real.pi / 6 by linarith [Real.pi_pos]))
    intro θ ⟨hlo, hhi⟩
    simp only [slope, reuleaux_right_piece (le_of_lt hlo) (le_of_lt hhi),
               reuleaux_right_piece (by linarith [Real.pi_pos]) le_rfl]
  · apply (hd_right.tendsto_slope.mono_left (nhdsGT_le_nhdsNE _)).congr'
    apply Filter.eventually_of_mem
      (Ioo_mem_nhdsGT (show 7 * Real.pi / 6 < 4 * Real.pi / 3 by linarith [Real.pi_pos]))
    intro θ ⟨hlo, hhi⟩
    simp only [slope, reuleaux_right7_piece (le_of_lt hlo) (le_of_lt hhi),
               reuleaux_right7_piece le_rfl (by linarith [Real.pi_pos])]

private lemma hasDerivAt_arc_formula_val (w θ : ℝ) :
    HasDerivAt (fun θ => w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi))
      ((w / Real.sqrt 3) * Real.sin (θ - Real.pi)) θ :=
  ((hasDerivAt_const θ w).sub
    ((hasDerivAt_cos_sub Real.pi θ).const_mul _)).congr_deriv (by ring)

private lemma reuleaux_locally_eq_arc_int {θ₀ : ℝ}
    (hlo : 5 * Real.pi / 6 < θ₀) (hhi : θ₀ < 7 * Real.pi / 6) (w : ℝ) :
    reuleaux w =ᶠ[nhds θ₀] (fun θ => w - (w / Real.sqrt 3) * Real.cos (θ - Real.pi)) := by
  apply Filter.eventually_of_mem (Ioo_mem_nhds hlo hhi)
  intro θ ⟨hlo', hhi'⟩; exact reuleaux_arc_int_val hlo' hhi' w

private lemma curve_reuleaux_arc_int {θ₀ : ℝ}
    (hlo : 5 * Real.pi / 6 < θ₀) (hhi : θ₀ < 7 * Real.pi / 6) (w : ℝ) :
    curve (reuleaux w) θ₀ = ↑w * Complex.exp (↑θ₀ * Complex.I) + ↑(w / Real.sqrt 3) := by
  rw [curve, reuleaux_arc_int_val hlo hhi,
      (reuleaux_locally_eq_arc_int hlo hhi w).deriv_eq,
      (hasDerivAt_arc_formula_val w θ₀).deriv]
  push_cast; rw [Complex.exp_mul_I]
  have hcos : Complex.cos (↑θ₀ - ↑Real.pi) = -Complex.cos ↑θ₀ := by
    rw [Complex.cos_sub, Complex.cos_pi, Complex.sin_pi]; ring
  have hsin : Complex.sin (↑θ₀ - ↑Real.pi) = -Complex.sin ↑θ₀ := by
    rw [Complex.sin_sub, Complex.cos_pi, Complex.sin_pi]; ring
  rw [hcos, hsin]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hcos2 : Complex.cos ↑θ₀ ^ 2 + Complex.sin ↑θ₀ ^ 2 = 1 :=
    Complex.cos_sq_add_sin_sq ↑θ₀
  have hsin2_eq : Complex.sin ↑θ₀ ^ 2 * Complex.I ^ 2 = -Complex.sin ↑θ₀ ^ 2 := by
    rw [hI2]; ring
  linear_combination (↑w / ↑(Real.sqrt 3)) * hcos2 - (↑w / ↑(Real.sqrt 3)) * hsin2_eq

private lemma w_div_sqrt3_sq_mul3 (w : ℝ) : (w / Real.sqrt 3) ^ 2 * 3 = w ^ 2 := by
  field_simp; nlinarith [sqrt3_sq, sqrt3_pos]

private lemma dist_arc_int {θ₀ : ℝ} (hlo : 5 * Real.pi / 6 < θ₀)
    (hhi : θ₀ < 7 * Real.pi / 6) {w : ℝ} (hw : 0 < w) :
    dist (curve (reuleaux w) θ₀) (curve (reuleaux w) 0) = w := by
  rw [curve_reuleaux_arc_int hlo hhi, curve_reuleaux_zero, dist_eq_norm]
  rw [show (↑w * Complex.exp (↑θ₀ * Complex.I) + ↑(w / Real.sqrt 3)) -
        ↑(w / Real.sqrt 3 : ℝ) = ↑w * Complex.exp (↑θ₀ * Complex.I) by push_cast; ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw,
      Complex.norm_exp_ofReal_mul_I, mul_one]

private lemma dist_arc_5pi6 {w : ℝ} (hw : 0 < w) :
    dist (curve (reuleaux w) (5 * Real.pi / 6)) (curve (reuleaux w) 0) = w := by
  rw [curve_reuleaux_zero, curve, reuleaux_5pi6_val,
      (hasDerivAt_reuleaux_5pi6_val w).deriv, dist_eq_norm]
  rw [show ((↑(w / Real.sqrt 3 * Real.cos (Real.pi / 6)) +
        ↑(-(w / Real.sqrt 3) * Real.sin (Real.pi / 6)) * Complex.I) *
       Complex.exp (↑(5 * Real.pi / 6) * Complex.I) - ↑(w / Real.sqrt 3 : ℝ)) =
      ↑(w / Real.sqrt 3) * ((↑(Real.cos (Real.pi / 6)) -
        ↑(Real.sin (Real.pi / 6)) * Complex.I) * Complex.exp (↑(5 * Real.pi / 6) * Complex.I) - 1)
    from by push_cast; ring]
  apply norm_eq_of_normSq hw
  rw [Complex.normSq_mul, Complex.normSq_ofReal, normSq_diff_5pi6]
  linarith [w_div_sqrt3_sq_mul3 w]

private lemma dist_arc_7pi6 {w : ℝ} (hw : 0 < w) :
    dist (curve (reuleaux w) (7 * Real.pi / 6)) (curve (reuleaux w) 0) = w := by
  rw [curve_reuleaux_zero, curve, reuleaux_7pi6_val,
      (hasDerivAt_reuleaux_7pi6_val w).deriv, dist_eq_norm]
  rw [show ((↑(w / Real.sqrt 3 * Real.cos (Real.pi / 6)) +
        ↑((w / Real.sqrt 3) * Real.sin (Real.pi / 6)) * Complex.I) *
       Complex.exp (↑(7 * Real.pi / 6) * Complex.I) - ↑(w / Real.sqrt 3 : ℝ)) =
      ↑(w / Real.sqrt 3) * ((↑(Real.cos (Real.pi / 6)) +
        ↑(Real.sin (Real.pi / 6)) * Complex.I) * Complex.exp (↑(7 * Real.pi / 6) * Complex.I) - 1)
    from by push_cast; ring]
  apply norm_eq_of_normSq hw
  rw [Complex.normSq_mul, Complex.normSq_ofReal, normSq_diff_7pi6]
  linarith [w_div_sqrt3_sq_mul3 w]


theorem reuleaux_arc {w : ℝ} (hw : 0 < w) :
    ∀ θ ∈ Set.Icc (5 * π / 6) (7 * π / 6),
      dist (curve (reuleaux w) θ) (curve (reuleaux w) 0) = w := by
  intro θ hθ
  rcases hθ with ⟨hlo, hhi⟩
  rcases eq_or_lt_of_le hlo with rfl | hlo'
  · exact dist_arc_5pi6 hw
  rcases eq_or_lt_of_le hhi with rfl | hhi'
  · exact dist_arc_7pi6 hw
  · exact dist_arc_int hlo' hhi' hw

end Barbier
