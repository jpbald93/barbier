import Barbier.Bridge
import Barbier.Piecewise

/-!
# Bridge theorems for piecewise-C² support functions (layer 10, piecewise extension)

Extends `bridge_support`, `curve_mem_body`, `support_body`, `width_body`
from `ConstWidthSupport` (C²) to `PiecewiseConstWidth` (C¹, piecewise C² off a countable set).

## Proof route for `bridge_support_piecewise`

Set `f φ = (curve h φ * exp(-iθ)).re`. Off the countable breakpoint set `S`, `h'` is
differentiable, so `f' φ = (h φ + h'' φ) * sin(θ - φ)`.
For any `y ≤ θ`, by the FTC off a countable set
(`MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`):
  `∫_y^θ f' = f θ - f y`.
On `[y, θ] ⊆ [θ-π, θ]`: `h + h'' ≥ 0` off S (null), `sin(θ-φ) ≥ 0`, so `f' ≥ 0` a.e., hence
`f y ≤ f θ`. Similarly for `θ ≤ y ≤ θ+π`. By 2π-periodicity, every φ reduces to this range.
-/

noncomputable section

open Real MeasureTheory Set intervalIntegral

namespace Barbier

variable {h : ℝ → ℝ} {w : ℝ}

/-! ### Pointwise HasDerivAt for the projection, off the breakpoint set -/

private lemma hasDerivAt_proj_curve_at (hh : ContDiff ℝ 1 h)
    {φ : ℝ} (hdiffφ : DifferentiableAt ℝ (deriv h) φ) (θ : ℝ) :
    HasDerivAt (fun ψ => (curve h ψ * Complex.exp (-(θ * Complex.I))).re)
      ((h φ + deriv (deriv h) φ) * Real.sin (θ - φ)) φ := by
  have d0 : HasDerivAt h (deriv h φ) φ :=
    ((hh.differentiable (by norm_num)) φ).hasDerivAt
  have d1 : HasDerivAt (deriv h) (deriv (deriv h) φ) φ := hdiffφ.hasDerivAt
  have de : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((φ : ℂ) * Complex.I) * (1 * Complex.I)) φ :=
    (((hasDerivAt_id φ).ofReal_comp).mul_const Complex.I).cexp
  have hcurve : HasDerivAt (curve h)
      (((h φ + deriv (deriv h) φ : ℝ) : ℂ) * (Complex.I * Complex.exp (φ * Complex.I))) φ := by
    have hmul := ((d0.ofReal_comp).add ((d1.ofReal_comp).mul_const Complex.I)).mul de
    refine hmul.congr_deriv ?_
    simp only [Pi.add_apply]
    push_cast
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (((deriv h φ : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) * hI
  have hg := hcurve.mul_const (Complex.exp (-(θ * Complex.I)))
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt φ hg
  refine hr.congr_deriv ?_
  have key : ((h φ + deriv (deriv h) φ : ℝ) : ℂ) * (Complex.I * Complex.exp (φ * Complex.I))
      * Complex.exp (-(θ * Complex.I))
      = ((h φ + deriv (deriv h) φ : ℝ) : ℂ) *
        (Complex.I * Complex.exp ((φ - θ : ℝ) * Complex.I)) := by
    push_cast
    rw [show (φ - θ : ℂ) * Complex.I = φ * Complex.I + -(θ * Complex.I) by ring,
      Complex.exp_add]; ring
  simp only [Complex.reCLM_apply]
  rw [key, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.exp_ofReal_mul_I_im,
    show θ - φ = -(φ - θ) by ring, Real.sin_neg]

/-! ### Auxiliary lemmas -/

private lemma continuous_proj_curve (hh : ContDiff ℝ 1 h) (θ : ℝ) :
    Continuous (fun φ : ℝ => (curve h φ * Complex.exp (-(θ * Complex.I))).re) := by
  unfold curve; fun_prop

private lemma periodic_proj_curve (hh : ContDiff ℝ 1 h) (hp : Function.Periodic h (2 * π))
    (θ : ℝ) :
    Function.Periodic (fun φ : ℝ => (curve h φ * Complex.exp (-(θ * Complex.I))).re) (2 * π) := by
  intro φ
  simp only [curve]
  have hdp : Function.Periodic (deriv h) (2 * π) := by
    intro x; rw [← deriv_comp_add_const]
    exact congrArg (fun F => deriv F x) (funext hp)
  rw [hp φ, hdp φ]; congr 2; push_cast
  rw [show (φ + 2 * π : ℂ) * Complex.I = φ * Complex.I + 2 * π * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private lemma deriv_deriv_h_periodic (hp : Function.Periodic h (2 * π)) :
    Function.Periodic (deriv (deriv h)) (2 * π) := by
  have hdp : Function.Periodic (deriv h) (2 * π) := by
    intro x; rw [← deriv_comp_add_const]
    exact congrArg (fun F => deriv F x) (funext hp)
  intro x; rw [← deriv_comp_add_const]
  exact congrArg (fun F => deriv F x) (funext hdp)

/-- `h + deriv(deriv h)` is 2π-periodic. -/
private lemma sum_hdd_periodic (hp : Function.Periodic h (2 * π)) :
    Function.Periodic (fun φ => h φ + deriv (deriv h) φ) (2 * π) := fun φ => by
  show h (φ + 2 * π) + deriv (deriv h) (φ + 2 * π) = h φ + deriv (deriv h) φ
  rw [hp φ, deriv_deriv_h_periodic hp φ]

/-- `(h + h'') * sin(θ - ·)` is integrable on any interval `[a, b]`. -/
private lemma intervalIntegrable_g (H : PiecewiseConstWidth h w) (θ a b : ℝ) :
    IntervalIntegrable (fun φ => (h φ + deriv (deriv h) φ) * Real.sin (θ - φ)) volume a b := by
  apply IntervalIntegrable.mul_continuousOn
  · -- `h + h''` is integrable on any interval by 2π-periodicity + H.integrable
    exact (sum_hdd_periodic H.periodic).intervalIntegrable₀
      (by linarith [Real.two_pi_pos]) H.integrable a b
  · exact (Real.continuous_sin.comp (continuous_const.sub continuous_id)).continuousOn.mono
        (Set.subset_univ _)

/-! ### Main theorem -/

/-- **Bridge for `PiecewiseConstWidth` (support function).**
`h θ` is the maximum of `⟪γ(φ), e^{iθ}⟫` over the whole curve. -/
theorem bridge_support_piecewise (H : PiecewiseConstWidth h w) (θ : ℝ) :
    IsGreatest (Set.range fun φ => inner ℝ (curve h φ) (Complex.exp (θ * Complex.I))) (h θ) := by
  set f : ℝ → ℝ := fun φ => (curve h φ * Complex.exp (-(θ * Complex.I))).re with hfdef
  have hfi : ∀ φ, inner ℝ (curve h φ) (Complex.exp (θ * Complex.I)) = f φ :=
    fun φ => bridge_inner_exp _ _
  have hfθ : f θ = h θ := curve_proj h θ
  have hfcont : Continuous f := continuous_proj_curve H.smooth θ
  have hfper : Function.Periodic f (2 * π) := periodic_proj_curve H.smooth H.periodic θ
  obtain ⟨S, hSct, hSdiff, hSconv⟩ := H.breaks
  set g : ℝ → ℝ := fun φ => (h φ + deriv (deriv h) φ) * Real.sin (θ - φ)
  have hder : ∀ φ ∉ S, HasDerivAt f (g φ) φ :=
    fun φ hφS => hasDerivAt_proj_curve_at H.smooth (hSdiff φ hφS) θ
  have hSae : ∀ᵐ (φ : ℝ) ∂volume, φ ∉ S := hSct.ae_notMem volume
  -- FTC: ∫_a^b g = f b - f a for a ≤ b
  have hftc : ∀ a b : ℝ, a ≤ b → ∫ φ in a..b, g φ = f b - f a := by
    intro a b hab
    exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le f g hab hSct
      (hfcont.continuousOn.mono (Set.subset_univ _))
      (fun φ hφ => hder φ hφ.2)
      (intervalIntegrable_g H θ a b)
  -- Monotone on [θ-π, θ]
  have hmono : ∀ y : ℝ, θ - π ≤ y → y ≤ θ → f y ≤ f θ := by
    intro y hy1 hy2
    have hftcy := hftc y θ hy2
    have hnn : 0 ≤ ∫ φ in y..θ, g φ := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hy2
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      filter_upwards [hSae] with φ hφS hφ
      exact mul_nonneg (hSconv φ hφS)
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.2]) (by linarith [hφ.1, hy1]))
    linarith
  -- Antitone on [θ, θ+π]
  have hanti : ∀ y : ℝ, θ ≤ y → y ≤ θ + π → f y ≤ f θ := by
    intro y hy1 hy2
    have hftcy := hftc θ y hy1
    have hnp : ∫ φ in θ..y, g φ ≤ 0 := by
      apply neg_nonneg.mp; rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_nonneg_of_ae_restrict hy1
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      filter_upwards [hSae] with φ hφS hφ
      -- goal: (0 : ℝ → ℝ) φ ≤ -g φ, i.e. 0 ≤ -g φ
      simp only [Pi.zero_apply, neg_nonneg]
      apply mul_nonpos_of_nonneg_of_nonpos (hSconv φ hφS)
      have hsin : 0 ≤ Real.sin (φ - θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.1]) (by linarith [hφ.2, hy2])
      have hsinθφ : Real.sin (θ - φ) = -Real.sin (φ - θ) := by
        rw [show θ - φ = -(φ - θ) by ring, Real.sin_neg]
      linarith
    linarith
  -- Conclude
  refine ⟨⟨θ, by simp only [hfi θ, hfθ]⟩, ?_⟩
  rintro _ ⟨φ, rfl⟩
  simp only [hfi φ, ← hfθ]
  obtain ⟨y, hy, hfy⟩ := hfper.exists_mem_Ico Real.two_pi_pos φ (θ - π)
  rw [hfy]
  rcases le_total y θ with hyθ | hyθ
  · exact hmono y hy.1 hyθ
  · exact hanti y hyθ (by linarith [hy.2, Real.pi_pos])

/-! ### Derived theorems (proofs identical to Bridge.lean) -/

theorem curve_mem_body_piecewise (H : PiecewiseConstWidth h w) (θ : ℝ) :
    curve h θ ∈ body h := by
  refine Set.mem_iInter.2 fun φ => ?_
  have := (bridge_support_piecewise H φ).2 ⟨θ, rfl⟩
  simp only [bridge_inner_exp] at this
  simpa [neg_mul] using this

theorem support_body_piecewise (H : PiecewiseConstWidth h w) (θ : ℝ) :
    sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' body h) = h θ := by
  refine IsGreatest.csSup_eq ⟨⟨curve h θ, curve_mem_body_piecewise H θ, ?_⟩, ?_⟩
  · simpa [neg_mul] using curve_proj h θ
  · rintro _ ⟨z, hz, rfl⟩
    exact Set.mem_iInter.1 hz θ

theorem width_body_piecewise (H : PiecewiseConstWidth h w) (θ : ℝ) :
    sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' body h)
      + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) '' body h) = w := by
  rw [support_body_piecewise H θ, support_body_piecewise H (θ + π)]
  exact H.width θ

end Barbier
