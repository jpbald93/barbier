# Barbier's theorem — spike report (`barbier`, lib `Barbier`)

**Status: DONE** (support-function model; honest core, see "Not done").

## Prior art (Step 0)
- Mathlib v4.33.1: no constant-width / Barbier / Reuleaux material. `docs/1000.yaml:1484` lists "Barbier's theorem" with no formalisation.
- `gh search code` "Barbier", "constant width", "constantWidth", "Reuleaux" (language:lean): no hits that matter (only bit-width / NN strings). Isabelle/Coq code searches and a web search (Isabelle AFP, HOL Light, Coq/Rocq, Mizar): no formal proof of Barbier found.
- Conclusion: no complete formal proof known → proceeded.

## Model (stated honestly)
Plane = ℂ (isometric to Euclidean ℝ²). A convex curve of constant width `w` is given by its **support function** `h : ℝ → ℝ` with
(`ConstWidthSupport h w`): `ContDiff ℝ 2 h`; `Function.Periodic h (2π)`; `h θ + h (θ+π) = w` for all θ (width in direction θ is w);
`0 ≤ h θ + h'' θ` (convexity: radius of curvature ≥ 0).
Boundary: `curve h θ = (h θ + i·h' θ)·e^{iθ}` = h(θ)(cos θ, sin θ) + h'(θ)(−sin θ, cos θ).
**Perimeter is defined as** `∫₀^{2π} ‖γ'(θ)‖ dθ` (NOT linked to Mathlib's `eVariationOn`; Mathlib has no "variation = ∫‖f'‖" theorem, would need extra groundwork).

## Headline statements (Barbier/Basic.lean, Barbier/Examples.lean)
```lean
-- Basic.lean:21
structure ConstWidthSupport (h : ℝ → ℝ) (w : ℝ) : Prop where
  smooth : ContDiff ℝ 2 h
  periodic : Function.Periodic h (2 * π)
  width : ∀ θ, h θ + h (θ + π) = w
  convex : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ
-- Basic.lean:28
def curve (h : ℝ → ℝ) (θ : ℝ) : ℂ := ((h θ : ℂ) + ((deriv h θ : ℝ) : ℂ) * Complex.I) * Complex.exp (θ * Complex.I)
-- Basic.lean:31
def perimeter (h : ℝ → ℝ) : ℝ := ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (curve h) θ‖
-- Basic.lean:34
theorem integral_support_eq {h : ℝ → ℝ} {w : ℝ} (hc : Continuous h)
    (hw : ∀ θ, h θ + h (θ + π) = w) : ∫ θ in (0 : ℝ)..(2 * π), h θ = π * w
-- Basic.lean:68
theorem deriv_curve {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (θ : ℝ) :
    deriv (curve h) θ = ((h θ + deriv (deriv h) θ : ℝ) : ℂ) * (Complex.I * Complex.exp (θ * Complex.I))
-- Basic.lean:80
theorem norm_deriv_curve_of_convex {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hcv : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) (θ : ℝ) :
    ‖deriv (curve h) θ‖ = h θ + deriv (deriv h) θ
-- Basic.lean:99  (Cauchy's formula in this model)
theorem perimeter_eq_integral {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hcv : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    perimeter h = ∫ θ in (0 : ℝ)..(2 * π), h θ
-- Basic.lean:110
theorem barbier {h : ℝ → ℝ} {w : ℝ} (H : ConstWidthSupport h w) : perimeter h = π * w
-- Basic.lean:124  (sanity: opposite boundary points are w apart along the normal)
theorem curve_width {h : ℝ → ℝ} {w : ℝ} (hw : ∀ θ, h θ + h (θ + π) = w) (θ : ℝ) :
    ((curve h θ - curve h (θ + π)) * Complex.exp (-(θ * Complex.I))).re = w
-- Examples.lean:23, 50, 66, 71  (non-vacuity)
theorem circle_perimeter (w : ℝ) (hw : 0 ≤ w) : perimeter (fun _ => w / 2) = π * w
theorem trefoil_constWidth {a b : ℝ} (hb : 0 ≤ b) (hab : 8 * b ≤ a) : ConstWidthSupport (trefoil a b) (2 * a)
theorem trefoil_perimeter {a b : ℝ} (hb : 0 ≤ b) (hab : 8 * b ≤ a) : perimeter (trefoil a b) = π * (2 * a)
theorem trefoil_not_const {a b : ℝ} (hb : b ≠ 0) : trefoil a b 0 ≠ trefoil a b (π / 3)
```
(`trefoil a b θ = a + b cos 3θ`: a smooth, non-circular constant-width curve.)
Also `curve_proj`: `(γ(θ)·e^{-iθ}).re = h θ` (h is the support value along the normal).

## Numerical check (code/check_barbier.py)
Circle and a+b·cos3θ (a=1,b=0.1): polygonal perimeter = 2πa to 1e-5. Negative control a=1,b=0.2 (a<8b, non-convex, curve has cusps/loops): ‖γ'‖-length 7.70 ≠ 2π — shows convexity hypothesis is needed for ‖γ'‖ = h+h''.

## Gate
- Clean full rebuild of the Barbier modules (`.lake/build` Barbier artefacts removed): `Build completed successfully (8709 jobs).` EXIT 0, no warnings in log.
- Forbidden-token grep over `Barbier Barbier.lean`: empty.
- `scratch/Ax.lean` → `scratch/ax.out`:
```
'Barbier.barbier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.perimeter_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.integral_support_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.deriv_curve' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.norm_deriv_curve_of_convex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.integral_deriv_deriv_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.curve_width' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.circle_perimeter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.trefoil_constWidth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.trefoil_perimeter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Barbier.trefoil_not_const' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Not done
- Perimeter is ∫‖γ'‖, not tied to Mathlib `eVariationOn` / rectifiable length.
- No proof that an arbitrary convex set of constant width has a C² support function (general convex bodies have only Lipschitz support functions; Reuleaux triangle itself is not C²/strictly convex, so it is NOT covered by this model).
- No proof that `curve h` is simple/closed-convex boundary of a set whose width is w in the metric sense (only the support-line / normal-direction identities `curve_proj`, `curve_width`).
