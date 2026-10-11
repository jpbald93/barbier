import Mathlib

/-!
# Barbier's theorem (support-function model)

A convex plane curve of constant width `w` is modelled by its support function
`h : ℝ → ℝ`: `C²`, `2π`-periodic, `h θ + h (θ + π) = w` (constant width) and
`h + h'' ≥ 0` (convexity / nonnegative radius of curvature).  The plane is `ℂ`
(isometric to Euclidean `ℝ²`), and the boundary is parametrised by
`γ(θ) = h(θ)·u(θ) + h'(θ)·u'(θ)` with `u(θ) = e^{iθ}`, i.e.
`γ(θ) = (h θ + i h' θ) e^{iθ}`.
-/

noncomputable section

open Real intervalIntegral MeasureTheory

namespace Barbier

/-- Hypotheses on a support function of a convex curve of constant width `w`. -/
structure ConstWidthSupport (h : ℝ → ℝ) (w : ℝ) : Prop where
  smooth : ContDiff ℝ 2 h
  periodic : Function.Periodic h (2 * π)
  width : ∀ θ, h θ + h (θ + π) = w
  convex : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ

/-- The boundary curve `γ(θ) = (h θ + i h'(θ)) e^{iθ}` determined by the support function. -/
def curve (h : ℝ → ℝ) (θ : ℝ) : ℂ := ((h θ : ℂ) + ((deriv h θ : ℝ) : ℂ) * Complex.I) * Complex.exp (θ * Complex.I)

/-- Perimeter of the curve: `∫₀^{2π} ‖γ'(θ)‖ dθ`. -/
def perimeter (h : ℝ → ℝ) : ℝ := ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (curve h) θ‖

/-- The width condition alone gives `∫₀^{2π} h = π w`. -/
theorem integral_support_eq {h : ℝ → ℝ} {w : ℝ} (hc : Continuous h)
    (hw : ∀ θ, h θ + h (θ + π) = w) :
    ∫ θ in (0 : ℝ)..(2 * π), h θ = π * w := by
  have h1 : IntervalIntegrable h volume 0 π := hc.intervalIntegrable _ _
  have h2 : IntervalIntegrable h volume π (2 * π) := hc.intervalIntegrable _ _
  rw [← integral_add_adjacent_intervals h1 h2]
  have h3 : ∫ θ in π..(2 * π), h θ = ∫ θ in (0 : ℝ)..π, h (θ + π) := by
    rw [integral_comp_add_right]; congr 1 <;> ring
  have h5 : IntervalIntegrable (fun θ => h (θ + π)) volume 0 π :=
    (hc.comp (continuous_add_const π)).intervalIntegrable _ _
  have h4 : ∫ θ in (0 : ℝ)..π, (h θ + h (θ + π)) = π * w := by
    simp only [hw, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [integral_add h1 h5] at h4
  rw [h3, h4]

lemma contDiff_one_deriv {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) : ContDiff ℝ 1 (deriv h) :=
  ContDiff.deriv' (by simpa [one_add_one_eq_two] using hh)

/-- Velocity of the curve: `γ'(θ) = (h + h'')(θ) · i e^{iθ}`. -/
theorem hasDerivAt_curve {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (θ : ℝ) :
    HasDerivAt (curve h) (((h θ + deriv (deriv h) θ : ℝ) : ℂ) * (Complex.I * Complex.exp (θ * Complex.I))) θ := by
  have d0 : HasDerivAt h (deriv h θ) θ :=
    ((hh.differentiable (by norm_num)) θ).hasDerivAt
  have d1 : HasDerivAt (deriv h) (deriv (deriv h) θ) θ :=
    (hh.differentiable_deriv_two θ).hasDerivAt
  have de : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I)) θ :=
    (((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).cexp
  have := ((d0.ofReal_comp).add ((d1.ofReal_comp).mul_const Complex.I)).mul de
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  refine this.congr_deriv ?_
  simp only [Pi.add_apply]
  push_cast
  linear_combination (((deriv h θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) * hI

theorem deriv_curve {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (θ : ℝ) :
    deriv (curve h) θ = ((h θ + deriv (deriv h) θ : ℝ) : ℂ) * (Complex.I * Complex.exp (θ * Complex.I)) :=
  (hasDerivAt_curve hh θ).deriv

/-- Speed of the curve: `‖γ'(θ)‖ = |h θ + h''(θ)|`. -/
theorem norm_deriv_curve {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (θ : ℝ) :
    ‖deriv (curve h) θ‖ = |h θ + deriv (deriv h) θ| := by
  rw [deriv_curve hh, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, Complex.norm_exp_ofReal_mul_I]
  ring

/-- Under convexity, the speed is the radius of curvature `h + h''`. -/
theorem norm_deriv_curve_of_convex {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hcv : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) (θ : ℝ) :
    ‖deriv (curve h) θ‖ = h θ + deriv (deriv h) θ := by
  rw [norm_deriv_curve hh, abs_of_nonneg (hcv θ)]

/-- `∫₀^{2π} h'' = 0` for a periodic `C²` function. -/
theorem integral_deriv_deriv_eq_zero {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), deriv (deriv h) θ = 0 := by
  have h1 := contDiff_one_deriv hh
  rw [integral_deriv_eq_sub (fun x _ => hh.differentiable_deriv_two x)
    (h1.continuous_deriv_one.intervalIntegrable _ _)]
  have : deriv h (0 + 2 * π) = deriv h 0 := by
    rw [← deriv_comp_add_const]
    exact congrArg (fun f => deriv f 0) (funext hp)
  rw [zero_add] at this
  rw [this, sub_self]

/-- Cauchy's formula in this model: perimeter `= ∫₀^{2π} h`. -/
theorem perimeter_eq_integral {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hcv : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    perimeter h = ∫ θ in (0 : ℝ)..(2 * π), h θ := by
  unfold perimeter
  simp_rw [norm_deriv_curve_of_convex hh hcv]
  rw [integral_add (hh.continuous.intervalIntegrable _ _)
    ((contDiff_one_deriv hh).continuous_deriv_one.intervalIntegrable _ _),
    integral_deriv_deriv_eq_zero hh hp, add_zero]

/-- **Barbier's theorem** (support-function model): a convex curve of constant width `w`
has perimeter `π w`. -/
theorem barbier {h : ℝ → ℝ} {w : ℝ} (H : ConstWidthSupport h w) :
    perimeter h = π * w := by
  rw [perimeter_eq_integral H.smooth H.periodic H.convex,
    integral_support_eq H.smooth.continuous H.width]

/-- Geometric sanity check: the projection of `γ(θ)` on the direction `e^{iθ}` is `h θ`. -/
theorem curve_proj (h : ℝ → ℝ) (θ : ℝ) :
    (curve h θ * Complex.exp (-(θ * Complex.I))).re = h θ := by
  unfold curve
  rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  simp

/-- The two points `γ(θ)`, `γ(θ + π)` (opposite normals) are at distance `w` measured
along the normal direction `e^{iθ}`. -/
theorem curve_width {h : ℝ → ℝ} {w : ℝ} (hw : ∀ θ, h θ + h (θ + π) = w) (θ : ℝ) :
    ((curve h θ - curve h (θ + π)) * Complex.exp (-(θ * Complex.I))).re = w := by
  have e : Complex.exp (-(θ * Complex.I)) = -Complex.exp (-(((θ + π : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    rw [add_mul, neg_add, Complex.exp_add, ← neg_mul, Complex.exp_neg (π * Complex.I),
      Complex.exp_pi_mul_I]
    ring
  rw [sub_mul, Complex.sub_re, curve_proj, e, mul_neg, Complex.neg_re, curve_proj, sub_neg_eq_add]
  exact hw θ

end Barbier
