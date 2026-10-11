import Barbier.Basic

/-!
# Barbier's theorem for piecewise-`C²` support functions

The smooth class `ConstWidthSupport` requires `h ∈ C²`, which excludes the Reuleaux triangle
(its `h''` jumps at six points per period).  Here `h` is only `C¹`, and `h'` is differentiable
off a countable set `S` of breakpoints.  Proof route (PLAN.md): off `S`, `‖γ'‖ = h + h''`; the
countable set `S` is null, so `perimeter h = ∫ (h + h'') = ∫ h + ∫ h''`; `∫₀^{2π} h'' = 0` by the
FTC off a countable set (`integral_eq_of_hasDerivAt_off_countable_of_le`) applied to the continuous,
periodic `h'`; and `∫₀^{2π} h = π w` by `integral_support_eq`.
-/

noncomputable section

open Real intervalIntegral MeasureTheory

namespace Barbier

/-- A support function of a convex curve of constant width `w` that is `C¹` and piecewise `C²`.
`S` ranges over all of `ℝ` (it is periodic for the Reuleaux triangle), hence only `Countable`,
not `Finite`. Integrability of `‖γ'‖` is not a field: it follows from `‖γ'‖ = h + h''` a.e. -/
structure PiecewiseConstWidth (h : ℝ → ℝ) (w : ℝ) : Prop where
  /-- `h` is `C¹`: the curve `γ` is continuous and `h'` is continuous (needed for the FTC). -/
  smooth : ContDiff ℝ 1 h
  /-- `2π`-periodicity: gives `h'(2π) = h'(0)`, so `∫₀^{2π} h'' = 0`. -/
  periodic : Function.Periodic h (2 * π)
  /-- Constant width `w`: gives `∫₀^{2π} h = π w`. -/
  width : ∀ θ, h θ + h (θ + π) = w
  /-- Breakpoints: a countable set `S` (Lebesgue-null, admissible in the countable-exception FTC)
  off which `h'` is differentiable (so `γ' = (h + h'') · i e^{iθ}` there) and the radius of
  curvature `h + h''` is nonnegative (convexity, so `‖γ'‖ = h + h''`). Stated as `∃ S` because a
  `Prop`-valued structure cannot carry the data field `S`. -/
  breaks : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
    (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ)
  /-- The radius of curvature is integrable on `[0, 2π]` (so `h''` is, for the FTC). -/
  integrable : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)

variable {h : ℝ → ℝ} {w : ℝ}


private lemma hasDerivAt_curve_pointwise (h1 : ContDiff ℝ 1 h) (theta : ℝ)
    (hd : DifferentiableAt ℝ (deriv h) theta) :
    HasDerivAt (curve h) (((h theta + deriv (deriv h) theta : ℝ) : ℂ) * (Complex.I * Complex.exp (theta * Complex.I))) theta := by
  have d0 : HasDerivAt h (deriv h theta) theta := (h1.differentiable one_ne_zero theta).hasDerivAt
  have d1 : HasDerivAt (deriv h) (deriv (deriv h) theta) theta := hd.hasDerivAt
  have de : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((theta : ℂ) * Complex.I) * (1 * Complex.I)) theta :=
    (((hasDerivAt_id theta).ofReal_comp).mul_const Complex.I).cexp
  have := ((d0.ofReal_comp).add ((d1.ofReal_comp).mul_const Complex.I)).mul de
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  refine this.congr_deriv ?_
  simp only [Pi.add_apply]; push_cast
  linear_combination (((deriv h theta : ℝ) : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) * hI

/-- The smooth class is an instance of the piecewise class (with `S = ∅`). -/
theorem ConstWidthSupport.toPiecewise (H : ConstWidthSupport h w) : PiecewiseConstWidth h w := by
  refine ⟨H.smooth.of_le (by norm_num), H.periodic, H.width,
          ⟨∅, Set.countable_empty, ?_, ?_⟩, ?_⟩
  · -- Off ∅ (= everywhere), deriv h is differentiable because h is C²
    intro θ _
    exact H.smooth.differentiable_deriv_two θ
  · -- h + h'' ≥ 0 everywhere (convexity hypothesis)
    intro θ _
    exact H.convex θ
  · -- h + h'' is continuous (h ∈ C²), hence interval-integrable
    have hdd : Continuous (fun θ => deriv (deriv h) θ) :=
      (contDiff_one_deriv H.smooth).continuous_deriv_one
    exact (H.smooth.continuous.add hdd).intervalIntegrable _ _

/-- **Barbier's theorem**, piecewise-`C²` support functions: perimeter `= π w`. -/
theorem barbier_piecewise (H : PiecewiseConstWidth h w) : perimeter h = π * w := by
  obtain ⟨S, hS_count, hS_diff, hS_conv⟩ := H.breaks
  -- h'' is integrable (from H.integrable - h)
  have h_intdd : IntervalIntegrable (fun theta => deriv (deriv h) theta) volume 0 (2 * π) := by
    have := H.integrable.sub (H.smooth.continuous.intervalIntegrable 0 (2 * π))
    simpa using this
  -- integral h'' = 0 (FTC off countable S + periodicity)
  have h_dd_zero : ∫ theta in (0:ℝ)..(2 * π), deriv (deriv h) theta = 0 := by
    rw [integral_eq_of_hasDerivAt_off_countable_of_le (deriv h) (fun theta => deriv (deriv h) theta)
          (by linarith [Real.pi_pos]) hS_count
          (H.smooth.continuous_deriv_one.continuousOn.mono (Set.subset_univ _))
          (fun x ⟨_, hxS⟩ => (hS_diff x hxS).hasDerivAt) h_intdd]
    have hperiod : deriv h (2 * π) = deriv h 0 := by
      rw [show (2 : ℝ) * π = 0 + 2 * π from by ring, ← deriv_comp_add_const]
      exact congrArg (fun f => deriv f 0) (funext H.periodic)
    linarith
  -- norm(curve') = h + h'' a.e.
  have h_norm_ae : ∀ᵐ theta ∂volume, theta ∈ Set.uIoc 0 (2 * π) →
      ‖deriv (curve h) theta‖ = h theta + deriv (deriv h) theta := by
    filter_upwards [hS_count.ae_notMem volume] with theta hthS _
    rw [(hasDerivAt_curve_pointwise H.smooth theta (hS_diff theta hthS)).deriv,
        norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, Complex.norm_exp_ofReal_mul_I, mul_one, mul_one]
    exact abs_of_nonneg (hS_conv theta hthS)
  -- Conclude: perimeter = integral h = pi*w
  unfold perimeter
  rw [integral_congr_ae h_norm_ae,
      integral_add (H.smooth.continuous.intervalIntegrable _ _) h_intdd,
      h_dd_zero, add_zero,
      integral_support_eq H.smooth.continuous H.width]

end Barbier
