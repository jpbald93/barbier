import Barbier.ReuleauxLength
import Barbier.ConvexBodyBridge

/-!
# Layer 14: Mathlib-only restatements of the Barbier side

Every `l14_*` theorem below has a statement mentioning only Mathlib notions: the curve
`γ_h(t) = (h t + i h'(t)) e^{it}` is written out as a lambda, the perimeter is the integral
`∫₀^{2π} ‖γ_h'‖`, length is Mathlib's `eVariationOn`, the body is the intersection of half-planes
written out, and the Reuleaux support function is any `R` satisfying its defining equation.
The `l14b_*` lemmas are the bridges to the library's own definitions; the `l14w_*` theorems are
explicit witnesses (non-vacuity).
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace Barbier

/-! ### Bridges -/

theorem l14b_curve (h : ℝ → ℝ) :
    (fun t : ℝ => ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      = curve h := rfl

theorem l14b_perimeter (h : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖)
      = perimeter h := rfl

theorem l14b_body (h : ℝ → ℝ) :
    (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}) = body h := rfl

theorem l14b_constWidth {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hc : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) : ConstWidthSupport h w := ⟨hs, hp, hw, hc⟩

theorem l14b_piecewise {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 1 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hS : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ))
    (hi : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :
    PiecewiseConstWidth h w := ⟨hs, hp, hw, hS, hi⟩

theorem l14b_piecewise_iff {h : ℝ → ℝ} {w : ℝ} : PiecewiseConstWidth h w ↔
    (ContDiff ℝ 1 h ∧ Function.Periodic h (2 * π) ∧ (∀ θ, h θ + h (θ + π) = w) ∧
    (∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ)) ∧
    IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :=
  ⟨fun H => ⟨H.smooth, H.periodic, H.width, H.breaks, H.integrable⟩,
   fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

theorem l14b_reuleaux {w : ℝ} {R : ℝ → ℝ}
    (hR : ∀ θ, R θ =
      if toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ ≤ π / 6 then
        (w / Real.sqrt 3) * Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ)
      else w - (w / Real.sqrt 3) *
        Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ - π / 3)) :
    R = reuleaux w := funext fun θ => hR θ

theorem l14b_contDiff_curve {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) : ContDiff ℝ 1 (curve h) := by
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

/-! ### Theorem (Barbier, smooth) -/

/-- Barbier, smooth: the perimeter integral is `π w`, and so is Mathlib's length
(`eVariationOn`) of the curve over one period. -/
theorem l14_barbier {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hc : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖) = π * w ∧
    eVariationOn (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      (Set.Icc 0 (2 * π)) = ENNReal.ofReal (π * w) := by
  have H := l14b_constWidth hs hp hw hc
  refine ⟨barbier H, ?_⟩
  rw [l14b_curve]
  have nt := eVariationOn_ne_top_of_contDiff (l14b_contDiff_curve hs)
    (by positivity : (0 : ℝ) ≤ 2 * π)
  rw [← ENNReal.ofReal_toReal nt, ← perimeter_eq_eVariationOn hs hp hc, barbier H]

/-! ### Proposition (smooth ⇒ piecewise) -/

theorem l14_toPiecewise {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hc : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    ContDiff ℝ 1 h ∧ Function.Periodic h (2 * π) ∧ (∀ θ, h θ + h (θ + π) = w) ∧
    (∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ)) ∧
    IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π) :=
  l14b_piecewise_iff.1 (l14b_constWidth hs hp hw hc).toPiecewise

/-! ### Theorem (Barbier, with corners) -/

theorem l14_barbier_piecewise {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 1 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hS : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ))
    (hi : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖) = π * w :=
  barbier_piecewise (l14b_piecewise hs hp hw hS hi)

/-! ### Theorem (Reuleaux triangle), parts (a)–(f) -/

theorem l14_reuleaux {w : ℝ} (hw0 : 0 < w) {R : ℝ → ℝ}
    (hR : ∀ θ, R θ =
      if toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ ≤ π / 6 then
        (w / Real.sqrt 3) * Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ)
      else w - (w / Real.sqrt 3) *
        Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ - π / 3)) :
    -- (a)
    (ContDiff ℝ 1 R ∧ Function.Periodic R (2 * π) ∧ (∀ θ, R θ + R (θ + π) = w) ∧
      (∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv R) θ) ∧
        (∀ θ ∉ S, 0 ≤ R θ + deriv (deriv R) θ)) ∧
      IntervalIntegrable (fun θ => R θ + deriv (deriv R) θ) volume 0 (2 * π)) ∧
    -- (b)
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖) = π * w ∧
    -- (c)
    ¬ ContDiff ℝ 2 R ∧
    -- (d)
    (let γ := fun t : ℝ =>
        ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I);
      dist (γ 0) (γ (2 * π / 3)) = w ∧ dist (γ (2 * π / 3)) (γ (4 * π / 3)) = w ∧
      dist (γ (4 * π / 3)) (γ 0) = w) ∧
    -- (e)
    (∀ θ ∈ Set.Icc (5 * π / 6) (7 * π / 6),
      dist ((fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (t * Complex.I)) θ)
        ((fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (t * Complex.I)) 0) = w) ∧
    -- (f)
    eVariationOn (fun t : ℝ =>
      ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      (Set.Icc 0 (2 * π)) = ENNReal.ofReal (π * w) := by
  obtain rfl := l14b_reuleaux hR
  exact ⟨l14b_piecewise_iff.1 (reuleaux_constWidth hw0), reuleaux_perimeter hw0,
    reuleaux_not_smooth hw0, reuleaux_vertices hw0, reuleaux_arc hw0, reuleaux_length hw0⟩

/-! ### Theorem (length of a `C¹` curve): already Mathlib-only -/

theorem l14_length {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a ≤ b) :
    eVariationOn γ (Set.Icc a b) ≠ ⊤ ∧
      (eVariationOn γ (Set.Icc a b)).toReal = ∫ t in a..b, ‖deriv γ t‖ :=
  length_eq_integral_norm_deriv hγ hab

/-! ### Corollary (perimeter is length) -/

theorem l14_perimeter_eq_eVariationOn {h : ℝ → ℝ} (hs : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hc : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖) =
    (eVariationOn (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      (Set.Icc 0 (2 * π))).toReal ∧
    eVariationOn (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      (Set.Icc 0 (2 * π)) ≠ ⊤ :=
  ⟨perimeter_eq_eVariationOn hs hp hc,
   eVariationOn_ne_top_of_contDiff (l14b_contDiff_curve hs) (by positivity)⟩

/-! ### Theorem (the body) -/

theorem l14_body {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 1 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hS : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ))
    (hi : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :
    Convex ℝ (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}) ∧
    ∀ θ : ℝ,
      IsGreatest (Set.range fun φ => inner ℝ ((fun t : ℝ =>
        ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) φ)
        (Complex.exp (θ * Complex.I))) (h θ) ∧
      (fun t : ℝ => ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (t * Complex.I)) θ ∈
        (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}) ∧
      sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) ''
        (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ})) = h θ ∧
      sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) ''
        (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}))
      + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) ''
        (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ})) = w := by
  have H := l14b_piecewise hs hp hw hS hi
  exact ⟨convex_body h, fun θ => ⟨bridge_support_piecewise H θ, curve_mem_body_piecewise H θ,
    support_body_piecewise H θ, width_body_piecewise H θ⟩⟩

/-! ### Theorem (the body is a convex body) -/

theorem l14_convexBody {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 1 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hS : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ))
    (hi : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :
    IsCompact (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}) ∧
    (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}).Nonempty ∧
    ∃ K : ConvexBody ℂ, (K : Set ℂ) = ⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ} ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ)) = h θ) ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ))
        + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) '' (K : Set ℂ)) = w) := by
  have H := l14b_piecewise hs hp hw hS hi
  exact ⟨isCompact_body_piecewise H, body_nonempty_piecewise H, exists_convexBody_piecewise H⟩

theorem l14_reuleaux_convexBody {w : ℝ} (hw0 : 0 < w) {R : ℝ → ℝ}
    (hR : ∀ θ, R θ =
      if toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ ≤ π / 6 then
        (w / Real.sqrt 3) * Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ)
      else w - (w / Real.sqrt 3) *
        Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ - π / 3)) :
    ∃ K : ConvexBody ℂ, (K : Set ℂ) = ⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ R θ} ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ))
        + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) '' (K : Set ℂ)) = w) := by
  obtain rfl := l14b_reuleaux hR
  exact reuleaux_convexBody hw0

/-! ### Witnesses (non-vacuity) -/

/-- The smooth witness `h θ = 2 + cos(3θ)/4` (width 4) satisfies every hypothesis of
`l14_barbier`, `l14_toPiecewise` and `l14_perimeter_eq_eVariationOn`; it is not constant (not a
circle), and its curve is non-degenerate: `γ(0) ≠ γ(π)` and `γ(0) ≠ γ(π/3)`. -/
theorem l14w_barbier :
    ContDiff ℝ 2 (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) ∧ Function.Periodic (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) (2 * π) ∧
    (∀ θ, (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) θ + (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) (θ + π) = 4) ∧
    (∀ θ, 0 ≤ (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) θ + deriv (deriv (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ))) θ) ∧
    (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) 0 ≠ (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) (π / 3) ∧
    (fun t : ℝ => (((fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) t : ℂ) + ((deriv (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) 0 ≠ (fun t : ℝ => (((fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) t : ℂ) + ((deriv (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) π ∧
    0 < π * 4 := by
  have H : ConstWidthSupport (trefoil 2 (1 / 4)) (2 * 2) :=
    trefoil_constWidth (by norm_num) (by norm_num)
  have hw := (bridge_constWidth H).1 0
  refine ⟨H.smooth, H.periodic, fun θ => by have := H.width θ; norm_num at this ⊢; exact this,
    H.convex, trefoil_not_const (by norm_num), ?_, by positivity⟩
  intro he
  change curve (trefoil 2 (1 / 4)) 0 = curve (trefoil 2 (1 / 4)) π at he
  rw [zero_add, he, sub_self, inner_zero_left] at hw
  norm_num at hw

/-- Reuleaux witness (`w = 1`): the function pinned down by the defining equation exists and
satisfies every hypothesis of `l14_barbier_piecewise`, `l14_body` and `l14_convexBody`; it is
genuinely non-smooth (`¬ C²`, so the smooth theorem does not apply) and its three corners
`γ(0), γ(2π/3), γ(4π/3)` are pairwise distinct; the perimeter `π · 1` is nonzero. -/
theorem l14w_reuleaux :
    ∃ R : ℝ → ℝ, (∀ θ, R θ =
      if toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ ≤ π / 6 then
        (1 / Real.sqrt 3) * Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ)
      else 1 - (1 / Real.sqrt 3) *
        Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ - π / 3)) ∧
    (ContDiff ℝ 1 R ∧ Function.Periodic R (2 * π) ∧ (∀ θ, R θ + R (θ + π) = 1) ∧
    (∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv R) θ) ∧
      (∀ θ ∉ S, 0 ≤ R θ + deriv (deriv R) θ)) ∧
    IntervalIntegrable (fun θ => R θ + deriv (deriv R) θ) volume 0 (2 * π)) ∧
    ¬ ContDiff ℝ 2 R ∧
    (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) 0 ≠ (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (2 * π / 3) ∧
    (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (2 * π / 3) ≠ (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (4 * π / 3) ∧
    (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (4 * π / 3) ≠ (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) 0 ∧
    (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) 0 ∈ (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ R θ}) ∧ (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (2 * π / 3) ∈ (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ R θ}) ∧
    0 < π * 1 := by
  have hw : (0 : ℝ) < 1 := one_pos
  obtain ⟨d1, d2, d3⟩ := reuleaux_vertices hw
  refine ⟨reuleaux 1, fun θ => rfl, l14b_piecewise_iff.1 (reuleaux_constWidth hw),
    reuleaux_not_smooth hw, ?_, ?_, ?_, curve_mem_body_piecewise (reuleaux_constWidth hw) 0,
    curve_mem_body_piecewise (reuleaux_constWidth hw) _, by positivity⟩
  · intro he; change curve _ _ = curve _ _ at he; rw [he, dist_self] at d1; exact zero_ne_one d1
  · intro he; change curve _ _ = curve _ _ at he; rw [he, dist_self] at d2; exact zero_ne_one d2
  · intro he; change curve _ _ = curve _ _ at he; rw [he, dist_self] at d3; exact zero_ne_one d3

/-- Witness for `l14_length`: the `C¹` curve `t ↦ t` on `[0, 1]` (non-constant), whose length
integral is `1 ≠ 0`. -/
theorem l14w_length :
    ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) ∧ (0 : ℝ) ≤ 1 ∧
    (fun t : ℝ => (t : ℂ)) 0 ≠ (fun t : ℝ => (t : ℂ)) 1 ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (fun t : ℝ => (t : ℂ)) t‖) = 1 := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => (t : ℂ)) t = 1 := fun t =>
    ((hasDerivAt_id t).ofReal_comp).deriv
  refine ⟨Complex.ofRealCLM.contDiff, zero_le_one, by simp, ?_⟩
  simp [hd]

end Barbier
