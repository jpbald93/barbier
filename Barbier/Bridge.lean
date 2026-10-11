import Barbier.Examples
import Barbier.Arclen

/-!
# Definition bridges (layer 10)

Each local definition is tied to the standard notion it is meant to be, using Mathlib's real
inner product on `ℂ ≅ ℝ²` (`Complex.inner`) and Mathlib's `circleMap`.

* `curve`: the point `γ(θ)` lies on the line `⟪x, u(θ)⟫ = h(θ)` (`u(θ) = e^{iθ}`) and the
  velocity is orthogonal to the normal `u(θ)`: `bridge_curve`.
* `ConstWidthSupport`: `h` is the genuine support function of the curve
  (`h θ = max_φ ⟪γ(φ), u(θ)⟫`), the two parallel support lines with normals `±u(θ)` are
  `w` apart, the speed is the radius of curvature, and `w ≥ 0`: `bridge_constWidth`,
  `bridge_support`.
* `perimeter`: for a constant support function the curve is Mathlib's `circleMap 0 r` and the
  perimeter is the circumference `2π|r|`: `bridge_perimeter`.
* `trefoil`: width `2a` in every direction and radius of curvature `a − 8b cos 3θ`:
  `bridge_trefoil`.
-/

noncomputable section

open Real

namespace Barbier

/-- The real inner product with the unit normal `e^{iθ}` is the projection used in the
library (`curve_proj`, `curve_width`). -/
theorem bridge_inner_exp (z : ℂ) (θ : ℝ) :
    inner ℝ z (Complex.exp (θ * Complex.I)) = (z * Complex.exp (-(θ * Complex.I))).re := by
  rw [Complex.inner, ← Complex.conj_re, map_mul, Complex.conj_conj, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, mul_comm, show (θ : ℂ) * -Complex.I = -(θ * Complex.I) by ring]

/-- **Bridge for `curve`.** `γ(θ)` lies on the line with unit normal `e^{iθ}` at signed distance
`h θ` from the origin, and its velocity is tangent to that line (orthogonal to the normal). -/
theorem bridge_curve {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (θ : ℝ) :
    inner ℝ (curve h θ) (Complex.exp (θ * Complex.I)) = h θ ∧
    inner ℝ (deriv (curve h) θ) (Complex.exp (θ * Complex.I)) = 0 := by
  refine ⟨by rw [bridge_inner_exp, curve_proj], ?_⟩
  rw [bridge_inner_exp, deriv_curve hh, mul_assoc, mul_assoc, ← Complex.exp_add,
    add_neg_cancel, Complex.exp_zero, mul_one, Complex.re_ofReal_mul, Complex.I_re, mul_zero]

/-- **Bridge for `ConstWidthSupport` (support function).** Under the hypotheses, `h θ` is the
maximum of `⟪γ(φ), e^{iθ}⟫` over the whole curve: `h` is the support function of `γ`, so the
line `⟪x, e^{iθ}⟫ = h θ` is a genuine support line. -/
theorem bridge_support {h : ℝ → ℝ} {w : ℝ} (H : ConstWidthSupport h w) (θ : ℝ) :
    IsGreatest (Set.range fun φ => inner ℝ (curve h φ) (Complex.exp (θ * Complex.I))) (h θ) := by
  set f : ℝ → ℝ := fun φ => (curve h φ * Complex.exp (-(θ * Complex.I))).re with hf
  have hfi : (fun φ => inner ℝ (curve h φ) (Complex.exp (θ * Complex.I))) = f := by
    funext φ; rw [bridge_inner_exp]
  rw [hfi]
  have hfθ : f θ = h θ := curve_proj h θ
  -- derivative of `f`
  have hd : ∀ φ, HasDerivAt f ((h φ + deriv (deriv h) φ) * Real.sin (θ - φ)) φ := by
    intro φ
    have hg := (hasDerivAt_curve H.smooth φ).mul_const (Complex.exp (-(θ * Complex.I)))
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt φ hg
    refine hr.congr_deriv ?_
    have key : ((h φ + deriv (deriv h) φ : ℝ) : ℂ) * (Complex.I * Complex.exp (φ * Complex.I))
        * Complex.exp (-(θ * Complex.I))
        = ((h φ + deriv (deriv h) φ : ℝ) : ℂ) * (Complex.I * Complex.exp (((φ - θ : ℝ) : ℂ) * Complex.I)) := by
      rw [show (((φ - θ : ℝ) : ℂ) * Complex.I) = φ * Complex.I + -(θ * Complex.I) by push_cast; ring,
        Complex.exp_add]
      ring
    simp only [Complex.reCLM_apply]
    rw [key, Complex.re_ofReal_mul, Complex.I_mul_re, Complex.exp_ofReal_mul_I_im,
      show θ - φ = -(φ - θ) by ring, Real.sin_neg]
  have hcont : ContinuousOn f Set.univ := fun x _ => (hd x).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Set.Icc (θ - π) θ) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (hcont.mono (Set.subset_univ _))
      (fun x _ => (hd x).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hs : 0 ≤ Real.sin (θ - x) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.2]) (by linarith [hx.1])
    exact mul_nonneg (H.convex x) hs
  have hanti : AntitoneOn f (Set.Icc θ (θ + π)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (hcont.mono (Set.subset_univ _))
      (fun x _ => (hd x).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hs : 0 ≤ Real.sin (x - θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2])
    rw [show θ - x = -(x - θ) by ring, Real.sin_neg]
    have := H.convex x
    nlinarith
  -- periodicity of `f`
  have hdp : Function.Periodic (deriv h) (2 * π) := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun F => deriv F x) (funext H.periodic)
  have hper : Function.Periodic f (2 * π) := by
    intro x
    simp only [hf, curve, H.periodic x, hdp x]
    congr 3
    rw [show (((x + 2 * π : ℝ)) : ℂ) * Complex.I = x * Complex.I + 2 * π * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  refine ⟨⟨θ, hfθ⟩, ?_⟩
  rintro _ ⟨φ, rfl⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico Real.two_pi_pos φ (θ - π)
  rw [hfy, ← hfθ]
  rcases le_total y θ with hyθ | hyθ
  · exact hmono ⟨hy.1, hyθ⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩ hyθ
  · exact hanti ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨hyθ, by linarith [hy.2]⟩ hyθ

/-- **Bridge for `ConstWidthSupport` (width).** The support lines with normals `e^{iθ}` and
`-e^{iθ}` are `w` apart in every direction, the speed of `γ` is the radius of curvature
`h + h''`, and the width is nonnegative. -/
theorem bridge_constWidth {h : ℝ → ℝ} {w : ℝ} (H : ConstWidthSupport h w) :
    (∀ θ : ℝ, inner ℝ (curve h θ - curve h (θ + π)) (Complex.exp (θ * Complex.I)) = w) ∧
    (∀ θ, ‖deriv (curve h) θ‖ = h θ + deriv (deriv h) θ) ∧ 0 ≤ w := by
  refine ⟨fun θ => by rw [bridge_inner_exp]; exact curve_width H.width θ,
    norm_deriv_curve_of_convex H.smooth H.convex, ?_⟩
  have hp : 0 ≤ perimeter h :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun _ _ => norm_nonneg _)
  rw [barbier H] at hp
  exact nonneg_of_mul_nonneg_right (by linarith) Real.pi_pos

/-- **Bridge for `perimeter`.** For a constant support function `r` the curve is Mathlib's
circle `circleMap 0 r` and `perimeter` is its circumference `2π|r|`. -/
theorem bridge_perimeter (r : ℝ) :
    curve (fun _ => r) = circleMap 0 r ∧ perimeter (fun _ => r) = 2 * π * |r| := by
  refine ⟨funext fun θ => by simp [curve, circleMap], ?_⟩
  unfold perimeter
  simp_rw [norm_deriv_curve (contDiff_const (c := r))]
  simp

/-- **Bridge for `trefoil`.** `a + b cos 3θ` has width `2a` in every direction and radius of
curvature `a − 8b cos 3θ`. -/
theorem bridge_trefoil (a b θ : ℝ) :
    trefoil a b θ + trefoil a b (θ + π) = 2 * a ∧
    trefoil a b θ + deriv (deriv (trefoil a b)) θ = a - 8 * b * Real.cos (3 * θ) := by
  refine ⟨?_, ?_⟩
  · unfold trefoil
    rw [show 3 * (θ + π) = 3 * θ + π + 2 * π by ring, Real.cos_add_two_pi, Real.cos_add_pi]
    ring
  · rw [deriv_deriv_trefoil]; unfold trefoil; ring

/-! ## Paper C bridges: Mathlib curve length, the convex body, its support function and width -/

/-- **General arclength helper** (not in Mathlib at our pin): the length (total variation,
`eVariationOn`) of a `C¹` curve in `ℂ` over `[a, b]` is `∫ₐᵇ ‖γ'‖`. -/
theorem eVariationOn_eq_integral_norm_deriv {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) {a b : ℝ}
    (hab : a ≤ b) :
    (eVariationOn γ (Set.Icc a b)).toReal = ∫ t in a..b, ‖deriv γ t‖ :=
  _root_.eVariationOn_eq_integral_norm_deriv hγ hab

private lemma contDiff_curve_of_contDiff2 {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 1 (curve h) := by
  unfold curve
  apply ContDiff.mul
  · apply ContDiff.add
    · exact Complex.ofRealCLM.contDiff.comp (hh.of_le (by norm_num))
    · apply ContDiff.mul
      · exact Complex.ofRealCLM.contDiff.comp (contDiff_one_deriv hh)
      · exact contDiff_const
  · apply ContDiff.cexp
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp contDiff_id
    · exact contDiff_const

/-- **Length bridge.** Our  is Mathlib's length (total variation) of 
on . -/
theorem perimeter_eq_eVariationOn {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hcv : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    perimeter h = (eVariationOn (curve h) (Set.Icc 0 (2 * π))).toReal := by
  unfold perimeter
  rw [eVariationOn_eq_integral_norm_deriv (contDiff_curve_of_contDiff2 hh) (by linarith [Real.pi_pos])]

/-- The convex set cut out by the support half-planes `⟪z, e^{iθ}⟫ ≤ h θ`. -/
def body (h : ℝ → ℝ) : Set ℂ :=
  ⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}

theorem convex_body (h : ℝ → ℝ) : Convex ℝ (body h) := by
  refine convex_iInter fun θ => convex_halfSpace_le ?_ (h θ)
  refine ⟨fun x y => by simp [add_mul], fun r x => ?_⟩
  simp [Complex.real_smul, mul_assoc]

theorem curve_mem_body {h : ℝ → ℝ} {w : ℝ} (H : ConstWidthSupport h w) (θ : ℝ) :
    curve h θ ∈ body h := by
  refine Set.mem_iInter.2 fun φ => ?_
  have := (bridge_support H φ).2 ⟨θ, rfl⟩
  simp only [bridge_inner_exp] at this
  simpa [neg_mul] using this

/-- `h` **is** the support function of `body h`. -/
theorem support_body {h : ℝ → ℝ} {w : ℝ} (H : ConstWidthSupport h w) (θ : ℝ) :
    sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' body h) = h θ := by
  refine IsGreatest.csSup_eq ⟨⟨curve h θ, curve_mem_body H θ, ?_⟩, ?_⟩
  · simpa [neg_mul] using curve_proj h θ
  · rintro _ ⟨z, hz, rfl⟩
    exact Set.mem_iInter.1 hz θ

/-- **Constant width of the set.** In every direction `θ`, the support values of `body h`
in directions `θ` and `θ + π` add up to `w`: `body h` has width `w` in every direction. -/
theorem width_body {h : ℝ → ℝ} {w : ℝ} (H : ConstWidthSupport h w) (θ : ℝ) :
    sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' body h)
      + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) '' body h) = w := by
  rw [support_body H θ, support_body H (θ + π)]
  exact H.width θ

end Barbier
