import Barbier.BridgePiecewise
import Barbier.Reuleaux

noncomputable section

open Real

namespace Barbier

variable {h : ℝ → ℝ} {w : ℝ}

/-! ### Closed -/

private lemma isClosed_body (h : ℝ → ℝ) : IsClosed (body h) := by
  apply isClosed_iInter; intro θ
  apply isClosed_le <;> fun_prop

/-! ### Key identity: z * exp(-arg(z)*I) = ‖z‖ as a complex number -/

private lemma mul_exp_neg_arg (z : ℂ) :
    z * Complex.exp (-(Complex.arg z : ℂ) * Complex.I) = ↑‖z‖ := by
  have hne : Complex.exp ((Complex.arg z : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hne
  rw [mul_assoc, ← Complex.exp_add]
  norm_num

private lemma re_mul_exp_neg_arg (z : ℂ) :
    (z * Complex.exp (-(Complex.arg z : ℂ) * Complex.I)).re = ‖z‖ := by
  rw [mul_exp_neg_arg]; simp

/-! ### Bounded -/

private lemma norm_le_of_mem_body {z : ℂ} (hz : z ∈ body h) : ‖z‖ ≤ h (Complex.arg z) := by
  have hθ : (z * Complex.exp (-(↑(Complex.arg z) : ℂ) * Complex.I)).re ≤ h (Complex.arg z) :=
    Set.mem_iInter.mp hz (Complex.arg z)
  linarith [re_mul_exp_neg_arg z]

private lemma exists_bound_h (H : PiecewiseConstWidth h w) : ∃ M : ℝ, ∀ θ : ℝ, h θ ≤ M := by
  obtain ⟨x, hx_mem, hx_max⟩ :=
    isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) (2 * π))
      ⟨0, by constructor <;> [linarith; linarith [Real.two_pi_pos]]⟩
      H.smooth.continuous.continuousOn
  refine ⟨h x, fun θ => ?_⟩
  obtain ⟨y, hy, hfy⟩ := H.periodic.exists_mem_Ico₀ Real.two_pi_pos θ
  rw [hfy]
  exact hx_max ⟨by linarith [hy.1], by linarith [hy.2, Real.pi_pos]⟩

private lemma isBounded_body (H : PiecewiseConstWidth h w) : Bornology.IsBounded (body h) := by
  obtain ⟨M, hM⟩ := exists_bound_h H
  rw [Metric.isBounded_iff_subset_closedBall 0]
  exact ⟨M, fun z hz => by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_of_mem_body hz).trans (hM _)⟩

/-! ### Main theorems -/

theorem isCompact_body_piecewise (H : PiecewiseConstWidth h w) : IsCompact (body h) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_body h) (isBounded_body H)

theorem body_nonempty_piecewise (H : PiecewiseConstWidth h w) : (body h).Nonempty :=
  ⟨curve h 0, curve_mem_body_piecewise H 0⟩

/-- The body as a Mathlib `ConvexBody`, with support function `h` and constant width `w`. -/
theorem exists_convexBody_piecewise (H : PiecewiseConstWidth h w) :
    ∃ K : ConvexBody ℂ, (K : Set ℂ) = body h ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ)) = h θ) ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ))
        + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) '' (K : Set ℂ)) = w) := by
  refine ⟨⟨body h, convex_body h, isCompact_body_piecewise H, body_nonempty_piecewise H⟩,
    ConvexBody.coe_mk _ _ _ _, ?_, ?_⟩
  · intro θ; simp only [ConvexBody.coe_mk]; exact support_body_piecewise H θ
  · intro θ; simp only [ConvexBody.coe_mk]; exact width_body_piecewise H θ

/-- The Reuleaux triangle is a Mathlib `ConvexBody` of constant width `w`. -/
theorem reuleaux_convexBody {w : ℝ} (hw : 0 < w) :
    ∃ K : ConvexBody ℂ, (K : Set ℂ) = body (reuleaux w) ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ))
        + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) '' (K : Set ℂ)) = w) := by
  obtain ⟨K, hK, _, hwidth⟩ := exists_convexBody_piecewise (reuleaux_constWidth hw)
  exact ⟨K, hK, hwidth⟩

end Barbier
