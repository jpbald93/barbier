import Barbier.Bridge

namespace Barbier

open MeasureTheory intervalIntegral Set eVariationOn Asymptotics ENNReal Topology

theorem eVariationOn_ne_top_of_contDiff {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) {a b : ℝ}
    (hab : a ≤ b) :
    eVariationOn γ (Set.Icc a b) ≠ ⊤ := by
  have hγ_diff : Differentiable ℝ γ := hγ.differentiable_one
  have hγ_deriv_cont : Continuous (deriv γ) := hγ.continuous_deriv_one
  have hnorm_cont : Continuous (fun t => ‖deriv γ t‖) := hγ_deriv_cont.norm
  have hnn : ∀ c d : ℝ, c ≤ d → 0 ≤ ∫ t in c..d, ‖deriv γ t‖ := fun c d hcd =>
    intervalIntegral.integral_nonneg_of_ae_restrict hcd
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  have hstep : ∀ c d : ℝ, c ≤ d → ‖γ d - γ c‖ ≤ ∫ t in c..d, ‖deriv γ t‖ := fun c d hcd => by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le hcd
    · exact hγ.continuous.continuousOn
    · exact hγ_diff.differentiableOn.mono (subset_univ _)
    · filter_upwards with t _ using le_refl _
    · exact hnorm_cont.intervalIntegrable c d
  have hlocal_ub : ∀ c d : ℝ, c ≤ d →
      eVariationOn γ (Icc c d) ≤ ENNReal.ofReal (∫ t in c..d, ‖deriv γ t‖) := by
    intro c d hcd
    apply iSup_le
    rintro ⟨n, u, hu, us⟩
    calc ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
        ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in u i..u (i + 1), ‖deriv γ t‖) := by
          apply Finset.sum_le_sum
          intro i _
          have hui := hu (Nat.le_succ i)
          rw [edist_le_ofReal (hnn _ _ hui), dist_eq_norm]
          exact hstep (u i) (u (i + 1)) hui
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ t in u i..u (i + 1), ‖deriv γ t‖) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn _ _ (hu (Nat.le_succ i)))]
      _ = ENNReal.ofReal (∫ t in u 0..u n, ‖deriv γ t‖) := by
          congr 1
          apply sum_integral_adjacent_intervals
          intro k _
          exact hnorm_cont.intervalIntegrable (u k) (u (k + 1))
      _ ≤ ENNReal.ofReal (∫ t in c..d, ‖deriv γ t‖) := by
          apply ENNReal.ofReal_le_ofReal
          apply integral_mono_interval (us 0).1 (hu (Nat.zero_le n)) (us n).2
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact hnorm_cont.intervalIntegrable c d
  have hupper : eVariationOn γ (Icc a b) ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) :=
    hlocal_ub a b hab
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper

theorem length_eq_integral_norm_deriv {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) {a b : ℝ}
    (hab : a ≤ b) :
    eVariationOn γ (Set.Icc a b) ≠ ⊤ ∧
      (eVariationOn γ (Set.Icc a b)).toReal = ∫ t in a..b, ‖deriv γ t‖ :=
  ⟨eVariationOn_ne_top_of_contDiff hγ hab,
   eVariationOn_eq_integral_norm_deriv hγ hab⟩

end Barbier
