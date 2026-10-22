import Mathlib
import Barbier.Basic
import Barbier.Examples
import Barbier.Bridge
import Barbier.ArclenFinite
import Barbier.BridgePiecewise
import Barbier.Piecewise
import Barbier.Reuleaux
import Barbier.ConvexBodyBridge
import Barbier.ReuleauxLength
import Barbier.L14

/-!
# Layer 15: classical statements

Layer 15. These definitions and statements were written independently, from textbook statements, by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves (or proves part of) one of them from this development.

Items: C1 (Barbier), C2 (Reuleaux triangle / polygons), C3 (four-vertex theorem).
-/

open Real Set MeasureTheory EuclideanGeometry

noncomputable section

namespace Barbier.Classical

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## Conventions -/

/-- OWN DEFINITION. A plane convex body: compact convex subset of `ℝ²` with nonempty interior. -/
def IsPlaneConvexBody (K : Set Plane) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- OWN DEFINITION. Support function `h_K(u) = max_{x ∈ K} ⟨x, u⟩` (as a `sSup`;
it is a max for compact nonempty `K`). -/
def supportFn (K : Set Plane) (u : Plane) : ℝ :=
  sSup ((fun x => inner ℝ x u) '' K)

/-- Well-formedness obligation for `supportFn`: for a plane convex body the `sSup` is a
maximum attained on `K`. -/
def obl_supportFn : Prop := ∀ (K : Set Plane) (hK : IsPlaneConvexBody K) (u : Plane) ,
    ∃ x ∈ K, supportFn K u = inner ℝ x u ∧ ∀ y ∈ K, inner ℝ y u ≤ inner ℝ x u 

/-- OWN DEFINITION. Width of `K` in direction `u`: `w_K(u) = h_K(u) + h_K(-u)`. -/
def widthIn (K : Set Plane) (u : Plane) : ℝ :=
  supportFn K u + supportFn K (-u)

/-- OWN DEFINITION. `K` has constant width `w > 0`. -/
def HasConstantWidth (K : Set Plane) (w : ℝ) : Prop :=
  0 < w ∧ ∀ u : Plane, ‖u‖ = 1 → widthIn K u = w

/-- OWN DEFINITION. `γ : ℝ → ℝ²` restricted to `[0,1]` is a parametrisation of the boundary of
`K` as a simple closed curve (continuous, `γ 0 = γ 1`, injective on `[0,1)`, image `∂K`). -/
def IsBoundaryParam (K : Set Plane) (γ : ℝ → Plane) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ γ 0 = γ 1 ∧ InjOn γ (Ico 0 1) ∧ γ '' Icc 0 1 = frontier K

/-- OWN DEFINITION. Perimeter of `K` = length of its boundary curve, i.e. the supremum of
lengths of inscribed polygons (vertices taken in the order of the curve), which is the total
variation `eVariationOn γ [0,1]` of a boundary parametrisation `γ`. This does not depend on
the parametrisation; we take the supremum over all of them (existence: see
`perimeter_obligation`). -/
def perimeter (K : Set Plane) : ENNReal :=
  ⨆ (γ : ℝ → Plane) (_ : IsBoundaryParam K γ), eVariationOn γ (Icc 0 1)

/-- Well-formedness obligation for `perimeter`: a plane convex body has a boundary
parametrisation as a simple closed curve. -/
def obl_perimeter : Prop := ∀ (K : Set Plane) (hK : IsPlaneConvexBody K) ,
    ∃ γ : ℝ → Plane, IsBoundaryParam K γ 

/-- Length of a parametrised `C¹` curve over one period `[0,T]`. -/
def curveLength (γ : ℝ → Plane) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, ‖deriv γ t‖

/-! ## C1. Barbier's theorem -/

/-- C1(a), smooth form. A closed (period `T`), regular, simple, `C²`, convex plane curve whose
convex hull has constant width `w` has length `π w`.
-- AMBIGUOUS: "convex / positively curved"; we take "convex" = the trace is the boundary of its
-- convex hull. Alternative: signed curvature `> 0` everywhere (strictly convex oval).
-- AMBIGUOUS: "the curve has constant width" is read as: the convex region it bounds,
-- `convexHull ℝ (range γ)`, has constant width `w`. -/
def classical_C1_a : Prop := ∀ (γ : ℝ → Plane) (T w : ℝ) (hT : 0 < T)
    (hper : Function.Periodic γ T) (hC2 : ContDiff ℝ 2 γ)
    (hreg : ∀ t, deriv γ t ≠ 0) (hsimple : InjOn γ (Ico 0 T))
    (hconvex : range γ = frontier (convexHull ℝ (range γ)))
    (hwidth : HasConstantWidth (convexHull ℝ (range γ)) w) ,
    curveLength γ T = π * w 

/-- C1(a), support-function form. Let `p` be a `C²`, `2π`-periodic support function with
`p + p'' > 0` (so that the envelope curve
`x(θ) = p(θ)(cos θ, sin θ) + p'(θ)(-sin θ, cos θ)` is a regular convex `C¹` curve),
satisfying the width condition `p(θ) + p(θ + π) = w`. Then
`L = ∫₀^{2π} p(θ) dθ = π w`, where `L` is the length of the envelope curve.
-- AMBIGUOUS: the text only says "C² support function of C"; we encode "support function of a
-- C² convex curve" via the standard condition `p + p'' > 0` and the envelope formula. -/
def classical_C1_a_support : Prop := ∀ (p : ℝ → ℝ) (w : ℝ)
    (hC2 : ContDiff ℝ 2 p) (hper : Function.Periodic p (2 * π))
    (hpos : ∀ θ, 0 < p θ + deriv (deriv p) θ)
    (hwidth : ∀ θ, p θ + p (θ + π) = w) ,
    curveLength (fun θ => !₂[p θ * Real.cos θ - deriv p θ * Real.sin θ,
                             p θ * Real.sin θ + deriv p θ * Real.cos θ]) (2 * π)
        = (∫ θ in (0 : ℝ)..(2 * π), p θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π), p θ) = π * w 

/-- C1(b), general form. Every plane convex body of constant width `w` has perimeter `π w`. -/
def classical_C1_b : Prop := ∀ (K : Set Plane) (w : ℝ) (hK : IsPlaneConvexBody K)
    (hw : HasConstantWidth K w) ,
    perimeter K = ENNReal.ofReal (π * w) 

/-- C1(b), equivalent form: a plane convex body of constant width `w` has the same perimeter
as the disk of diameter `w`. -/
def classical_C1_b_equiv : Prop := ∀ (K : Set Plane) (w : ℝ) (hK : IsPlaneConvexBody K)
    (hw : HasConstantWidth K w) ,
    perimeter K = perimeter (Metric.closedBall (0 : Plane) (w / 2)) 

/-! ## C2. The Reuleaux triangle -/

/-- OWN DEFINITION. The Reuleaux triangle on `A, B, C`: intersection of the closed disks of
radius `w` centred at the three points. -/
def reuleauxTriangle (A B C : Plane) (w : ℝ) : Set Plane :=
  Metric.closedBall A w ∩ Metric.closedBall B w ∩ Metric.closedBall C w

/-- OWN DEFINITION. Interior angle of a convex set `K` at a point `p`: the opening angle of the
tangent cone of `K` at `p`, computed as the supremum of `∠ x p y` over `x, y ∈ K \ {p}`. -/
def interiorAngleAt (K : Set Plane) (p : Plane) : ℝ :=
  sSup {θ | ∃ x ∈ K, ∃ y ∈ K, x ≠ p ∧ y ≠ p ∧ θ = ∠ x p y}

/-- OWN DEFINITION. A corner point of a convex body: a boundary point at which the interior
angle is `< π` (equivalently, more than one supporting line passes through it). -/
def IsCornerPoint (K : Set Plane) (p : Plane) : Prop :=
  p ∈ frontier K ∧ interiorAngleAt K p < π

/-- C2, description of the boundary: three circular arcs of radius `w`, the arc centred at
each vertex joining the other two, each of angle `π/3`. -/
def classical_C2_boundary : Prop := ∀ (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w) ,
    frontier (reuleauxTriangle A B C w) =
        {p | dist p A = w ∧ ∠ B A p ≤ π / 3 ∧ ∠ p A C ≤ π / 3 ∧ ∠ B A p + ∠ p A C = π / 3} ∪
        {p | dist p B = w ∧ ∠ C B p ≤ π / 3 ∧ ∠ p B A ≤ π / 3 ∧ ∠ C B p + ∠ p B A = π / 3} ∪
        {p | dist p C = w ∧ ∠ A C p ≤ π / 3 ∧ ∠ p C B ≤ π / 3 ∧ ∠ A C p + ∠ p C B = π / 3} ∧
      ∠ B A C = π / 3 ∧ ∠ C B A = π / 3 ∧ ∠ A C B = π / 3 

/-- C2(a). The Reuleaux triangle is a plane convex body of constant width `w`, it is not a
disk, its corner points are exactly `A, B, C`, and the interior angle at each is `2π/3`. -/
def classical_C2_a : Prop := ∀ (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w) ,
    IsPlaneConvexBody (reuleauxTriangle A B C w) ∧
      HasConstantWidth (reuleauxTriangle A B C w) w ∧
      (¬ ∃ (c : Plane) (r : ℝ), reuleauxTriangle A B C w = Metric.closedBall c r) ∧
      {p | IsCornerPoint (reuleauxTriangle A B C w) p} = {A, B, C} ∧
      interiorAngleAt (reuleauxTriangle A B C w) A = 2 * π / 3 ∧
      interiorAngleAt (reuleauxTriangle A B C w) B = 2 * π / 3 ∧
      interiorAngleAt (reuleauxTriangle A B C w) C = 2 * π / 3 

/-- C2(b). The perimeter of the Reuleaux triangle is `3 · (w · π/3) = π w`. -/
def classical_C2_b : Prop := ∀ (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w) ,
    perimeter (reuleauxTriangle A B C w) = ENNReal.ofReal (3 * (w * (π / 3))) ∧
      perimeter (reuleauxTriangle A B C w) = ENNReal.ofReal (π * w) 

/-- C2(c). The area of the Reuleaux triangle is `(1/2)(π - √3) w²`. -/
def classical_C2_c : Prop := ∀ (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w) ,
    volume (reuleauxTriangle A B C w) = ENNReal.ofReal ((1 / 2) * (π - √3) * w ^ 2) 

/-- C2(c), Blaschke–Lebesgue (with the disk as maximiser): among plane convex bodies of
constant width `w`, the Reuleaux triangle has minimal area and the disk (area `π w²/4`)
maximal area. -/
def classical_C2_c_blaschke_lebesgue : Prop := ∀ (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w)
    (K : Set Plane) (hK : IsPlaneConvexBody K) (hKw : HasConstantWidth K w) ,
    volume (reuleauxTriangle A B C w) ≤ volume K ∧
      volume K ≤ volume (Metric.closedBall (0 : Plane) (w / 2)) ∧
      volume (Metric.closedBall (0 : Plane) (w / 2)) = ENNReal.ofReal (π * w ^ 2 / 4) 

/-- OWN DEFINITION. Reuleaux polygon with `2m+1` vertices (`m ≥ 1`), regular or irregular:
the vertices `v 0, …, v (2m)` are in convex position, listed cyclically, every pairwise
distance is `≤ w`, and each vertex `v i` is at distance exactly `w` from its two opposite
vertices `v (i+m)` and `v (i+m+1)`; the polygon is `⋂ i, closedBall (v i) w`.
-- AMBIGUOUS: the text gives no definition of (irregular) Reuleaux polygon; alternative:
-- a constant-width body whose boundary is a finite union of circular arcs of radius `w`
-- centred at its corner points. -/
def IsReuleauxPolygonData (m : ℕ) (v : Fin (2 * m + 1) → Plane) (w : ℝ) : Prop :=
  1 ≤ m ∧ 0 < w ∧
    (∀ i, v i ∉ convexHull ℝ (v '' {j | j ≠ i})) ∧
    (∀ i j, dist (v i) (v j) ≤ w) ∧
    (∀ i : Fin (2 * m + 1),
      dist (v i) (v ⟨(i.val + m) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩) = w ∧
      dist (v i) (v ⟨(i.val + m + 1) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩) = w)

/-- C2, general remark: Reuleaux polygons of width `w` are plane convex bodies of constant
width `w` and have perimeter `π w`. -/
def classical_C2_reuleaux_polygon : Prop := ∀ (m : ℕ) (v : Fin (2 * m + 1) → Plane) (w : ℝ)
    (hv : IsReuleauxPolygonData m v w) ,
    IsPlaneConvexBody (⋂ i, Metric.closedBall (v i) w) ∧
      HasConstantWidth (⋂ i, Metric.closedBall (v i) w) w ∧
      perimeter (⋂ i, Metric.closedBall (v i) w) = ENNReal.ofReal (π * w) 

/-! ## C3. Four-vertex theorem -/

/-- OWN DEFINITION (standard formula). Signed curvature of a regular plane curve `α`:
`k = det(α', α'') / ‖α'‖³`. It is invariant under orientation-preserving reparametrisation,
so it agrees with `k(s)` in arc length. -/
def signedCurvature (α : ℝ → Plane) (t : ℝ) : ℝ :=
  (deriv α t 0 * deriv (deriv α) t 1 - deriv α t 1 * deriv (deriv α) t 0) / ‖deriv α t‖ ^ 3

/-- OWN DEFINITION. A vertex of `α`: a parameter at which the curvature has a local extremum. -/
def IsVertex (α : ℝ → Plane) (t : ℝ) : Prop :=
  IsLocalExtr (signedCurvature α) t

/-- OWN DEFINITION. Regular closed `C²` plane curve with period `T > 0`. -/
def IsRegularClosedC2 (α : ℝ → Plane) (T : ℝ) : Prop :=
  0 < T ∧ Function.Periodic α T ∧ ContDiff ℝ 2 α ∧ ∀ t, deriv α t ≠ 0

/-- C3(a), Mukhopadhyaya. A simple closed regular `C²` oval (curvature of constant strict sign)
has at least four vertices (four distinct parameters in one period).
-- AMBIGUOUS: "convex" read as strict `k > 0` (for one orientation, so we allow `k > 0`
-- everywhere or `k < 0` everywhere); alternative: `k ≥ 0` (just convex). -/
def classical_C3_a : Prop := ∀ (α : ℝ → Plane) (T : ℝ) (hα : IsRegularClosedC2 α T)
    (hsimple : InjOn α (Ico 0 T))
    (hoval : (∀ t, 0 < signedCurvature α t) ∨ (∀ t, signedCurvature α t < 0)) ,
    ∃ t₁ t₂ t₃ t₄ : ℝ, t₁ ∈ Ico 0 T ∧ t₂ ∈ Ico 0 T ∧ t₃ ∈ Ico 0 T ∧ t₄ ∈ Ico 0 T ∧
      t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧
      IsVertex α t₁ ∧ IsVertex α t₂ ∧ IsVertex α t₃ ∧ IsVertex α t₄ 

/-- C3(a), "more precisely": the curvature has at least two local maxima and at least two
local minima (at four distinct parameters in one period).
-- AMBIGUOUS: we require the four points to be pairwise distinct (relevant only when `k` is
-- locally constant, where a point is both a local max and a local min). -/
def classical_C3_a_precise : Prop := ∀ (α : ℝ → Plane) (T : ℝ) (hα : IsRegularClosedC2 α T)
    (hsimple : InjOn α (Ico 0 T))
    (hoval : (∀ t, 0 < signedCurvature α t) ∨ (∀ t, signedCurvature α t < 0)) ,
    ∃ s₁ s₂ s₃ s₄ : ℝ, s₁ ∈ Ico 0 T ∧ s₂ ∈ Ico 0 T ∧ s₃ ∈ Ico 0 T ∧ s₄ ∈ Ico 0 T ∧
      s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₁ ≠ s₄ ∧ s₂ ≠ s₃ ∧ s₂ ≠ s₄ ∧ s₃ ≠ s₄ ∧
      IsLocalMax (signedCurvature α) s₁ ∧ IsLocalMax (signedCurvature α) s₂ ∧
      IsLocalMin (signedCurvature α) s₃ ∧ IsLocalMin (signedCurvature α) s₄ 

/-- C3(a), do Carmo's variant: for a `C³` curve (so `k` is `C¹`), with vertices defined as
zeros of `k'`, an oval has at least four vertices. -/
def classical_C3_a_doCarmo : Prop := ∀ (α : ℝ → Plane) (T : ℝ) (hα : IsRegularClosedC2 α T)
    (hC3 : ContDiff ℝ 3 α) (hsimple : InjOn α (Ico 0 T))
    (hoval : (∀ t, 0 < signedCurvature α t) ∨ (∀ t, signedCurvature α t < 0)) ,
    ∃ t₁ t₂ t₃ t₄ : ℝ, t₁ ∈ Ico 0 T ∧ t₂ ∈ Ico 0 T ∧ t₃ ∈ Ico 0 T ∧ t₄ ∈ Ico 0 T ∧
      t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧
      deriv (signedCurvature α) t₁ = 0 ∧ deriv (signedCurvature α) t₂ = 0 ∧
      deriv (signedCurvature α) t₃ = 0 ∧ deriv (signedCurvature α) t₄ = 0 

/-- C3(b), Kneser. Every simple closed regular `C²` plane curve has at least four vertices. -/
def classical_C3_b : Prop := ∀ (α : ℝ → Plane) (T : ℝ) (hα : IsRegularClosedC2 α T)
    (hsimple : InjOn α (Ico 0 T)) ,
    ∃ t₁ t₂ t₃ t₄ : ℝ, t₁ ∈ Ico 0 T ∧ t₂ ∈ Ico 0 T ∧ t₃ ∈ Ico 0 T ∧ t₄ ∈ Ico 0 T ∧
      t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧
      IsVertex α t₁ ∧ IsVertex α t₂ ∧ IsVertex α t₃ ∧ IsVertex α t₄ 

/-- C3 remark: sharpness — a non-circular ellipse `(a cos t, b sin t)`, `a ≠ b`, has exactly
four vertices in one period, at the ends of its axes. -/
def classical_C3_remark_ellipse : Prop := ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) ,
    {t ∈ Ico 0 (2 * π) | IsVertex (fun t => !₂[a * Real.cos t, b * Real.sin t]) t} =
      {0, π / 2, π, 3 * π / 2} 

/-- C3 remark: for a circle every point is a vertex (curvature is constant). -/
def classical_C3_remark_circle : Prop := ∀ (c : Plane) (r : ℝ) (hr : 0 < r) (t : ℝ) ,
    IsVertex (fun t => c + !₂[r * Real.cos t, r * Real.sin t]) t 

/-- C3 remark: "simple" cannot be dropped — there is a regular closed `C²` plane curve which
is not simple and has exactly two vertices in one period (e.g. a limaçon with an inner loop).
-- AMBIGUOUS: stated existentially; alternative: the specific limaçon `r = 1/2 + cos θ`. -/
def classical_C3_remark_nonsimple : Prop :=
    ∃ (α : ℝ → Plane) (T : ℝ), IsRegularClosedC2 α T ∧ ¬ InjOn α (Ico 0 T) ∧
      {t ∈ Ico 0 T | IsVertex α t}.ncard = 2 


/-! ## Coverage: proofs of (parts of) the statements above from this development -/
open Real Set

/-- The standard isometry `ℂ ≃ ℝ²`, `z ↦ (re z, im z)`. -/
noncomputable abbrev E : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

lemma E_apply0 (z : ℂ) : (E z) 0 = z.re := rfl
lemma E_apply1 (z : ℂ) : (E z) 1 = z.im := rfl

lemma deriv_E_comp (γ : ℝ → ℂ) (t : ℝ) : deriv (fun s => E (γ s)) t = E (deriv γ t) := by
  show fderiv ℝ (E ∘ γ) t 1 = E (fderiv ℝ γ t 1)
  rw [LinearIsometryEquiv.comp_fderiv]; rfl

lemma curveLength_E (γ : ℝ → ℂ) (T : ℝ) :
    curveLength (fun s => E (γ s)) T = ∫ t in (0:ℝ)..T, ‖deriv γ t‖ := by
  unfold curveLength; congr 1; funext t; rw [deriv_E_comp, LinearIsometryEquiv.norm_map]

lemma eVariationOn_E (f : ℝ → ℂ) (s : Set ℝ) :
    eVariationOn (fun t => E (f t)) s = eVariationOn f s := by
  simp only [eVariationOn, LinearIsometryEquiv.edist_map]

/-- NEW PROOF: `supportFn_obligation`. -/
theorem cov_supportFn_obligation : obl_supportFn := by
  intro K hK u
  obtain ⟨x, hx, hmax⟩ := hK.1.exists_isMaxOn (hK.2.2.mono interior_subset)
    ((by fun_prop : Continuous fun x : Plane => inner ℝ x u).continuousOn)
  refine ⟨x, hx, ?_, fun y hy => hmax hy⟩
  unfold supportFn
  exact IsGreatest.csSup_eq ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmax hy⟩

/-- NEW PROOF: a finite intersection of closed `w`-balls about points pairwise at distance `≤ w`
is a plane convex body (the centroid is an interior point). -/
theorem isPlaneConvexBody_iInter {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → Plane) (w : ℝ)
    (hw : 0 < w) (hd : ∀ i j, dist (v i) (v j) ≤ w) :
    IsPlaneConvexBody (⋂ i, Metric.closedBall (v i) w) := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty ι›
  refine ⟨(isCompact_closedBall (v i0) w).of_isClosed_subset
      (isClosed_iInter fun i => Metric.isClosed_closedBall) (Set.iInter_subset _ i0),
    convex_iInter fun i => convex_closedBall _ _, ?_⟩
  have hn1 : (1:ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨(1 / (Fintype.card ι : ℝ)) • ∑ j, v j, ?_⟩
  rw [interior_iInter_of_finite]
  refine Set.mem_iInter.2 fun i => interior_mono Metric.ball_subset_closedBall ?_
  rw [Metric.isOpen_ball.interior_eq, Metric.mem_ball, dist_eq_norm]
  have hid : (1 / (Fintype.card ι : ℝ)) • ∑ j, v j - v i
      = (1 / (Fintype.card ι : ℝ)) • ∑ j, (v j - v i) := by
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div, inv_mul_cancel₀ (by linarith), one_smul]
  have hsum : ‖∑ j, (v j - v i)‖ ≤ ((Fintype.card ι : ℝ) - 1) * w := by
    calc ‖∑ j, (v j - v i)‖ ≤ ∑ j, ‖v j - v i‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase i, ‖v j - v i‖ := (Finset.sum_erase _ (by simp)).symm
      _ ≤ ∑ j ∈ Finset.univ.erase i, w :=
          Finset.sum_le_sum fun j _ => by rw [← dist_eq_norm]; exact hd j i
      _ = ((Fintype.card ι : ℝ) - 1) * w := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]; simp
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (Fintype.card ι : ℝ) * ‖∑ j, (v j - v i)‖
      ≤ 1 / (Fintype.card ι : ℝ) * (((Fintype.card ι : ℝ) - 1) * w) := by gcongr
    _ < w := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by linarith)]; nlinarith

section BB
open Barbier

variable {h : ℝ → ℝ} {w : ℝ}

lemma E_curve (h : ℝ → ℝ) (θ : ℝ) :
    E (Barbier.curve h θ) = !₂[h θ * Real.cos θ - deriv h θ * Real.sin θ,
                               h θ * Real.sin θ + deriv h θ * Real.cos θ] := by
  ext i; fin_cases i
  · simp [E_apply0, Barbier.curve, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
  · simp [E_apply1, Barbier.curve, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]

/-- C1(a), support-function form: COVERED (`perimeter_eq_integral`, `integral_support_eq`). -/
theorem cov_C1_a_support : classical_C1_a_support := by
  intro p w hC2 hper hpos hwidth
  have hcv : ∀ θ, 0 ≤ p θ + deriv (deriv p) θ := fun θ => (hpos θ).le
  have e : (fun θ => !₂[p θ * Real.cos θ - deriv p θ * Real.sin θ,
      p θ * Real.sin θ + deriv p θ * Real.cos θ]) = fun θ => E (Barbier.curve p θ) :=
    funext fun θ => (E_curve p θ).symm
  rw [e, curveLength_E]
  exact ⟨perimeter_eq_integral hC2 hper hcv, integral_support_eq hC2.continuous hwidth⟩

/-! ### The body `K_h`, transported to `ℝ²`, has constant width in the writer's sense -/

lemma supportFn_E_body (H : PiecewiseConstWidth h w) (θ : ℝ) :
    supportFn (E '' body h) (E (Complex.exp (θ * Complex.I))) = h θ := by
  unfold supportFn
  rw [Set.image_image]
  have : (fun z => inner ℝ (E z) (E (Complex.exp (θ * Complex.I)))) =
      fun z => (z * Complex.exp (-θ * Complex.I)).re := by
    funext z; rw [LinearIsometryEquiv.inner_map_map, bridge_inner_exp, neg_mul]
  rw [this]; exact support_body_piecewise H θ

lemma unit_eq_E_exp (u : Plane) (hu : ‖u‖ = 1) :
    u = E (Complex.exp ((Complex.arg (E.symm u) : ℝ) * Complex.I)) := by
  have h1 : ‖E.symm u‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hu]
  have := Complex.norm_mul_exp_arg_mul_I (E.symm u)
  rw [h1, Complex.ofReal_one, one_mul] at this
  rw [this, LinearIsometryEquiv.apply_symm_apply]

lemma hasConstantWidth_E_body (H : PiecewiseConstWidth h w) (hw : 0 < w) :
    HasConstantWidth (E '' body h) w := by
  refine ⟨hw, fun u hu => ?_⟩
  obtain ⟨θ, rfl⟩ : ∃ θ : ℝ, u = E (Complex.exp (θ * Complex.I)) := ⟨_, unit_eq_E_exp u hu⟩
  have hneg : -E (Complex.exp (θ * Complex.I)) =
      E (Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I)) := by
    rw [← map_neg]; congr 1
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  unfold widthIn
  rw [hneg, supportFn_E_body H, supportFn_E_body H]
  exact H.width θ

/-- C1(b), the part the repository reaches: for a piecewise constant-width support function `h`,
the transported body `E '' K_h` is compact, convex and of constant width `w` in the writer's
sense, and Barbier's perimeter (∫|γ'|) of its support-function curve is `π w`. -/
theorem cov_C1_b_part (H : PiecewiseConstWidth h w) (hw : 0 < w) :
    IsCompact (E '' body h) ∧ Convex ℝ (E '' body h) ∧ HasConstantWidth (E '' body h) w ∧
      Barbier.perimeter h = π * w :=
  ⟨(isCompact_body_piecewise H).image E.continuous,
    (convex_body h).linear_image E.toLinearEquiv.toLinearMap,
    hasConstantWidth_E_body H hw, barbier_piecewise H⟩

/-- C1(a), part: for a smooth (`C²`) constant-width support function, the transported curve has
`curveLength = π w`, its length is Mathlib's total variation, and `E '' K_h` has constant width. -/
theorem cov_C1_a_part (H : ConstWidthSupport h w) (hw : 0 < w) :
    curveLength (fun θ => E (Barbier.curve h θ)) (2 * π) = π * w ∧
      eVariationOn (fun θ => E (Barbier.curve h θ)) (Set.Icc 0 (2 * π)) = ENNReal.ofReal (π * w) ∧
      HasConstantWidth (E '' body h) w := by
  have hc1 : ContDiff ℝ 1 (Barbier.curve h) := by
    have h1 : ContDiff ℝ 1 (fun θ => ((h θ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (H.smooth.of_le (by norm_num))
    have h2 : ContDiff ℝ 1 (fun θ => ((deriv h θ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_one_deriv H.smooth)
    have c3 : ContDiff ℝ 1 (fun θ : ℝ => ((θ : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff
    unfold Barbier.curve
    exact (h1.add (h2.mul contDiff_const)).mul (c3.mul contDiff_const).cexp
  have hL := length_eq_integral_norm_deriv hc1 (a := 0) (b := 2 * π) Real.two_pi_pos.le
  refine ⟨by rw [curveLength_E]; exact barbier H, ?_, hasConstantWidth_E_body H.toPiecewise hw⟩
  rw [eVariationOn_E, ← ENNReal.ofReal_toReal hL.1, hL.2]
  congr 1; exact barbier H

/-- C1(b) equivalent form, part: the circle of diameter `w` has the same Barbier perimeter. -/
theorem cov_C1_b_equiv_part (H : PiecewiseConstWidth h w) (hw : 0 < w) :
    Barbier.perimeter h = Barbier.perimeter (fun _ => w / 2) := by
  rw [barbier_piecewise H, circle_perimeter w hw.le]

/-! ### C2 -/

lemma reuleauxTriangle_eq (A B C : Plane) (w : ℝ) :
    reuleauxTriangle A B C w = ⋂ i : Fin 3, Metric.closedBall (![A, B, C] i) w := by
  ext x; simp [reuleauxTriangle, Fin.forall_fin_succ, and_assoc]

/-- NEW PROOF: the Reuleaux triangle is a plane convex body. -/
theorem isPlaneConvexBody_reuleaux (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w) :
    IsPlaneConvexBody (reuleauxTriangle A B C w) := by
  rw [reuleauxTriangle_eq]
  apply isPlaneConvexBody_iInter _ w hw
  have hBA : dist B A = w := by rw [dist_comm]; exact hAB
  have hCB : dist C B = w := by rw [dist_comm]; exact hBC
  have hAC : dist A C = w := by rw [dist_comm]; exact hCA
  intro i j; fin_cases i <;> fin_cases j <;> simp [hAB, hBC, hCA, hBA, hCB, hAC, hw.le]

lemma vertex_near_center {R : Set Plane} {X c : Plane} {r w : ℝ} (hR : R = Metric.closedBall c r)
    (hX : X ∈ R) (hsub : R ⊆ Metric.closedBall X w) : dist c X ≤ w / 2 := by
  have hXr : dist c X ≤ r := by
    rw [hR, Metric.mem_closedBall, dist_comm] at hX; exact hX
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist c X) with h0 | hX0
  · rw [← h0]
    have : X ∈ Metric.closedBall X w := hsub hX
    rw [Metric.mem_closedBall, dist_self] at this; linarith
  rw [dist_eq_norm] at hX0 hXr ⊢
  have hr : 0 ≤ r := le_trans (norm_nonneg _) hXr
  set x : Plane := c + (r / ‖c - X‖) • (c - X)
  have hxD : x ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [x, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), div_mul_cancel₀ _ hX0.ne']
  have hxX : dist x X = ‖c - X‖ + r := by
    rw [dist_eq_norm]
    have : x - X = (1 + r / ‖c - X‖) • (c - X) := by
      simp only [x, add_smul, one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul, one_mul,
      div_mul_cancel₀ _ hX0.ne']
  rw [← hR] at hxD
  have := hsub hxD
  rw [Metric.mem_closedBall, hxX] at this
  linarith

/-- NEW PROOF: the Reuleaux triangle is not a closed disk. -/
theorem reuleaux_not_disk (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w) :
    ¬ ∃ (c : Plane) (r : ℝ), reuleauxTriangle A B C w = Metric.closedBall c r := by
  rintro ⟨c, r, hR⟩
  have hAC : dist A C = w := by rw [dist_comm]; exact hCA
  have hBA : dist B A = w := by rw [dist_comm]; exact hAB
  have hCB : dist C B = w := by rw [dist_comm]; exact hBC
  have memA : A ∈ reuleauxTriangle A B C w :=
    ⟨⟨by simp [hw.le], by rw [Metric.mem_closedBall, hAB]⟩, by rw [Metric.mem_closedBall, hAC]⟩
  have memB : B ∈ reuleauxTriangle A B C w :=
    ⟨⟨by rw [Metric.mem_closedBall, hBA], by simp [hw.le]⟩, by rw [Metric.mem_closedBall, hBC]⟩
  have memC : C ∈ reuleauxTriangle A B C w :=
    ⟨⟨by rw [Metric.mem_closedBall, hCA], by rw [Metric.mem_closedBall, hCB]⟩, by simp [hw.le]⟩
  have sA : reuleauxTriangle A B C w ⊆ Metric.closedBall A w := fun x hx => hx.1.1
  have sB : reuleauxTriangle A B C w ⊆ Metric.closedBall B w := fun x hx => hx.1.2
  have sC : reuleauxTriangle A B C w ⊆ Metric.closedBall C w := fun x hx => hx.2
  have a := vertex_near_center hR memA sA
  have b := vertex_near_center hR memB sB
  have g := vertex_near_center hR memC sC
  have ap1 := dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq c A B
  have ap2 := dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq C A B
  have tri := dist_triangle C c (midpoint ℝ A B)
  rw [hAB] at ap1 ap2
  rw [hCA, hCB] at ap2
  have h0 := dist_nonneg (x := c) (y := A)
  have h1 := dist_nonneg (x := c) (y := B)
  have h2 := dist_nonneg (x := c) (y := midpoint ℝ A B)
  have h3 := dist_nonneg (x := c) (y := C)
  have hm : dist c (midpoint ℝ A B) ^ 2 ≤ 0 := by nlinarith
  have hm0 : dist c (midpoint ℝ A B) = 0 := by nlinarith
  rw [hm0, add_zero, dist_comm C c] at tri
  have hCm : dist C (midpoint ℝ A B) ≤ w / 2 := le_trans tri g
  have hCm0 := dist_nonneg (x := C) (y := midpoint ℝ A B)
  have : dist C (midpoint ℝ A B) ^ 2 ≤ (w / 2) ^ 2 := pow_le_pow_left₀ hCm0 hCm 2
  nlinarith

/-- C2(a), part (NEW PROOFS on the writer's object): plane convex body and not a disk. -/
theorem cov_C2_a_part (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w) :
    IsPlaneConvexBody (reuleauxTriangle A B C w) ∧
      (¬ ∃ (c : Plane) (r : ℝ), reuleauxTriangle A B C w = Metric.closedBall c r) :=
  ⟨isPlaneConvexBody_reuleaux A B C w hw hAB hBC hCA, reuleaux_not_disk A B C w hw hAB hBC hCA⟩

/-- C2(a)/(b), part from the repository: the repository's Reuleaux curve, transported to `ℝ²`,
has three vertices pairwise at distance `w` (so they satisfy the writer's hypotheses), an arc of
radius `w` about the first vertex, Mathlib length (total variation) `3 (w π/3) = π w`, and its body
`E '' K_{R_w}` is a compact convex set of constant width `w` in the writer's sense. -/
theorem cov_C2_b_part (hw : 0 < w) :
    let γ : ℝ → Plane := fun θ => E (Barbier.curve (reuleaux w) θ)
    dist (γ 0) (γ (2 * π / 3)) = w ∧ dist (γ (2 * π / 3)) (γ (4 * π / 3)) = w ∧
      dist (γ (4 * π / 3)) (γ 0) = w ∧
      (∀ θ ∈ Set.Icc (5 * π / 6) (7 * π / 6), dist (γ θ) (γ 0) = w) ∧
      eVariationOn γ (Set.Icc 0 (2 * π)) = ENNReal.ofReal (3 * (w * (π / 3))) ∧
      eVariationOn γ (Set.Icc 0 (2 * π)) = ENNReal.ofReal (π * w) ∧
      IsCompact (E '' body (reuleaux w)) ∧ Convex ℝ (E '' body (reuleaux w)) ∧
      HasConstantWidth (E '' body (reuleaux w)) w := by
  intro γ
  obtain ⟨v1, v2, v3⟩ := reuleaux_vertices hw
  have hb := cov_C1_b_part (reuleaux_constWidth hw) hw
  refine ⟨?_, ?_, ?_, fun θ hθ => ?_, ?_, ?_, hb.1, hb.2.1, hb.2.2.1⟩
  · simp only [γ, LinearIsometryEquiv.dist_map]; exact v1
  · simp only [γ, LinearIsometryEquiv.dist_map]; exact v2
  · simp only [γ, LinearIsometryEquiv.dist_map]; exact v3
  · simp only [γ, LinearIsometryEquiv.dist_map]; exact reuleaux_arc hw θ hθ
  · simp only [γ]; rw [eVariationOn_E, reuleaux_length hw]; congr 1; ring
  · simp only [γ]; rw [eVariationOn_E, reuleaux_length hw]

/-- C2(c), Blaschke–Lebesgue, part (NEW PROOF, Mathlib only): the disk of diameter `w` has area
`π w² / 4`. -/
theorem cov_C2_c_disk_area (w : ℝ) (hw : 0 < w) :
    MeasureTheory.volume (Metric.closedBall (0 : Plane) (w / 2)) = ENNReal.ofReal (π * w ^ 2 / 4) := by
  rw [EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

/-- C2 Reuleaux polygons, part (NEW PROOF): the polygon is a plane convex body. -/
theorem cov_C2_reuleaux_polygon_part (m : ℕ) (v : Fin (2 * m + 1) → Plane) (w : ℝ)
    (hv : IsReuleauxPolygonData m v w) :
    IsPlaneConvexBody (⋂ i, Metric.closedBall (v i) w) :=
  isPlaneConvexBody_iInter v w hv.2.1 hv.2.2.2.1

/-- NEW PROOF (Mathlib only): the angles of an equilateral triangle are `π/3`. -/
lemma angle_equilateral (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hCA : dist C A = w) (hBC : dist B C = w) :
    EuclideanGeometry.angle B A C = π / 3 := by
  have hl := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B A C
  rw [dist_comm B A, hAB, hCA, hBC] at hl
  have hc : Real.cos (EuclideanGeometry.angle B A C) = Real.cos (π / 3) := by
    rw [Real.cos_pi_div_three]
    have : w * w * (2 * Real.cos (EuclideanGeometry.angle B A C) - 1) = 0 := by nlinarith
    have hww : w * w ≠ 0 := by positivity
    have := (mul_eq_zero.1 this).resolve_left hww
    linarith
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ hc

/-- C2 boundary description, part (NEW PROOF): the three angles are `π/3`. -/
theorem cov_C2_boundary_part (A B C : Plane) (w : ℝ) (hw : 0 < w)
    (hAB : dist A B = w) (hBC : dist B C = w) (hCA : dist C A = w) :
    EuclideanGeometry.angle B A C = π / 3 ∧ EuclideanGeometry.angle C B A = π / 3 ∧
      EuclideanGeometry.angle A C B = π / 3 :=
  ⟨angle_equilateral A B C w hw hAB hCA hBC,
   angle_equilateral B C A w hw hBC hAB hCA,
   angle_equilateral C A B w hw hCA hBC hAB⟩

end BB

end Barbier.Classical
