import Barbier.Basic

/-!
# Non-vacuity examples

* the circle of diameter `w`: `h θ = w / 2`;
* a non-circular smooth curve of constant width `2a`: `h θ = a + b cos 3θ` with `0 < b`, `8b ≤ a`.
-/

noncomputable section

open Real

namespace Barbier

/-- Support function of the circle of diameter `w`. -/
theorem circle_constWidth (w : ℝ) (hw : 0 ≤ w) : ConstWidthSupport (fun _ => w / 2) w where
  smooth := contDiff_const
  periodic := fun _ => rfl
  width := fun _ => by ring
  convex := fun _ => by simp only [deriv_const']; linarith

theorem circle_perimeter (w : ℝ) (hw : 0 ≤ w) : perimeter (fun _ => w / 2) = π * w :=
  barbier (circle_constWidth w hw)

/-- The support function `a + b cos 3θ`. -/
def trefoil (a b : ℝ) (θ : ℝ) : ℝ := a + b * Real.cos (3 * θ)

lemma hasDerivAt_trefoil (a b θ : ℝ) :
    HasDerivAt (trefoil a b) (-(3 * b) * Real.sin (3 * θ)) θ := by
  have h : HasDerivAt (trefoil a b) (b * (-Real.sin (3 * θ) * (3 * 1))) θ :=
    (((hasDerivAt_id θ).const_mul 3).cos.const_mul b).const_add a
  exact h.congr_deriv (by ring)

lemma deriv_trefoil (a b : ℝ) :
    deriv (trefoil a b) = fun θ => -(3 * b) * Real.sin (3 * θ) :=
  funext fun θ => (hasDerivAt_trefoil a b θ).deriv

lemma deriv_deriv_trefoil (a b θ : ℝ) :
    deriv (deriv (trefoil a b)) θ = -(9 * b) * Real.cos (3 * θ) := by
  rw [deriv_trefoil]
  have h : HasDerivAt (fun θ => -(3 * b) * Real.sin (3 * θ))
      (-(3 * b) * (Real.cos (3 * θ) * (3 * 1))) θ :=
    (((hasDerivAt_id θ).const_mul 3).sin).const_mul (-(3 * b))
  rw [h.deriv]
  ring

/-- `a + b cos 3θ` (with `0 ≤ b`, `8b ≤ a`) is the support function of a convex curve of
constant width `2a`. -/
theorem trefoil_constWidth {a b : ℝ} (hb : 0 ≤ b) (hab : 8 * b ≤ a) :
    ConstWidthSupport (trefoil a b) (2 * a) where
  smooth := by unfold trefoil; fun_prop
  periodic := fun θ => by
    unfold trefoil
    rw [show 3 * (θ + 2 * π) = 3 * θ + (3 : ℕ) * (2 * π) by push_cast; ring,
      Real.cos_add_nat_mul_two_pi]
  width := fun θ => by
    unfold trefoil
    rw [show 3 * (θ + π) = 3 * θ + π + 2 * π by ring, Real.cos_add_two_pi, Real.cos_add_pi]
    ring
  convex := fun θ => by
    rw [deriv_deriv_trefoil]
    unfold trefoil
    nlinarith [Real.cos_le_one (3 * θ), Real.neg_one_le_cos (3 * θ)]

theorem trefoil_perimeter {a b : ℝ} (hb : 0 ≤ b) (hab : 8 * b ≤ a) :
    perimeter (trefoil a b) = π * (2 * a) :=
  barbier (trefoil_constWidth hb hab)

/-- The example is genuinely non-circular when `b ≠ 0`: the support function is not constant. -/
theorem trefoil_not_const {a b : ℝ} (hb : b ≠ 0) : trefoil a b 0 ≠ trefoil a b (π / 3) := by
  unfold trefoil
  rw [mul_zero, Real.cos_zero, show 3 * (π / 3) = π by ring, Real.cos_pi]
  intro h
  apply hb
  linarith

end Barbier
