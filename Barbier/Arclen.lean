import Mathlib

open MeasureTheory intervalIntegral Set eVariationOn Asymptotics ENNReal Topology

/-- For a C¹ function γ : ℝ → ℂ, the total variation on [a,b] equals ∫ₐᵇ ‖deriv γ t‖ dt -/
theorem eVariationOn_eq_integral_norm_deriv {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) {a b : ℝ}
    (hab : a ≤ b) :
    (eVariationOn γ (Set.Icc a b)).toReal = ∫ t in a..b, ‖deriv γ t‖ := by
  have hγ_diff : Differentiable ℝ γ := hγ.differentiable_one
  have hγ_deriv_cont : Continuous (deriv γ) := hγ.continuous_deriv_one
  have hnorm_cont : Continuous (fun t => ‖deriv γ t‖) := hγ_deriv_cont.norm
  have hint : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b :=
    hnorm_cont.intervalIntegrable a b
  have hint_nonneg : 0 ≤ ∫ t in a..b, ‖deriv γ t‖ :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  -- integrals are nonneg
  have hnn : ∀ c d : ℝ, c ≤ d → 0 ≤ ∫ t in c..d, ‖deriv γ t‖ := fun c d hcd =>
    intervalIntegral.integral_nonneg_of_ae_restrict hcd
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  -- Helper: norm (γ d - γ c) <= integral of norm deriv on [c, d]
  have hstep : ∀ c d : ℝ, c ≤ d → ‖γ d - γ c‖ ≤ ∫ t in c..d, ‖deriv γ t‖ := fun c d hcd => by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le hcd
    · exact hγ.continuous.continuousOn
    · exact hγ_diff.differentiableOn.mono (subset_univ _)
    · filter_upwards with t _ using le_refl _
    · exact hnorm_cont.intervalIntegrable c d
  -- Helper: eVarOn(Icc c d) ≤ ENNReal.ofReal (∫_c^d ‖γ'‖)
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
  -- Upper bound: eVariationOn <= ENNReal.ofReal (integral norm deriv)
  have hupper : eVariationOn γ (Icc a b) ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) :=
    hlocal_ub a b hab
  -- Helper: eVarOn(Icc c d).toReal ≤ ∫_c^d ‖γ'‖
  have hlocal_ub_real : ∀ c d : ℝ, c ≤ d →
      (eVariationOn γ (Icc c d)).toReal ≤ ∫ t in c..d, ‖deriv γ t‖ :=
    fun c d hcd => ENNReal.toReal_le_of_le_ofReal (hnn c d hcd) (hlocal_ub c d hcd)
  -- gamma has Lipschitz constant K and bounded variation on [a, b]
  obtain ⟨K, hK⟩ := hγ.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc a b) isCompact_Icc
  have hbv : BoundedVariationOn γ (Icc a b) := by
    have := hK.locallyBoundedVariationOn a b (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rwa [inter_self] at this
  -- Lower bound: integral norm deriv <= eVariationOn.toReal
  have hlower : ∫ t in a..b, ‖deriv γ t‖ ≤ (eVariationOn γ (Icc a b)).toReal := by
    -- eVariationOn γ (Icc a t) is finite for a ≤ t ≤ b
    have hbv_at : ∀ t : ℝ, a ≤ t → t ≤ b → eVariationOn γ (Icc a t) ≠ ⊤ :=
      fun t hat htb =>
        (eVariationOn.mono γ (Icc_subset_Icc_right htb) |>.trans_lt hbv.lt_top).ne
    -- eVariationOn γ (Icc t s) is finite when a ≤ t, s ≤ b
    have hbv_sub : ∀ {t s : ℝ}, a ≤ t → s ≤ b → eVariationOn γ (Icc t s) ≠ ⊤ :=
      fun {t s} hat hsb =>
        (eVariationOn.mono γ (Icc_subset_Icc hat hsb) |>.trans_lt hbv.lt_top).ne
    -- Define V(t) = eVarOn(Icc a t).toReal
    let V : ℝ → ℝ := fun t => (eVariationOn γ (Icc a t)).toReal
    -- Helper: for a ≤ t ≤ s ≤ b, V(s) - V(t) = eVarOn(Icc t s).toReal
    have hVincr : ∀ {t s : ℝ}, a ≤ t → t ≤ s → s ≤ b →
        V s - V t = (eVariationOn γ (Icc t s)).toReal := by
      intro t s hat hts hsb
      simp only [V]
      have hAt : eVariationOn γ (Icc a t) ≠ ⊤ := hbv_at t hat (hts.trans hsb)
      have hBt : eVariationOn γ (Icc t s) ≠ ⊤ := hbv_sub hat hsb
      have hadd : eVariationOn γ (Icc a t) + eVariationOn γ (Icc t s) =
          eVariationOn γ (Icc a s) := by
        rw [← univ_inter (Icc a t), ← univ_inter (Icc t s), ← univ_inter (Icc a s)]
        exact eVariationOn.Icc_add_Icc γ hat hts (mem_univ t)
      have hadd_real : (eVariationOn γ (Icc a t)).toReal + (eVariationOn γ (Icc t s)).toReal =
          (eVariationOn γ (Icc a s)).toReal := by
        rw [← ENNReal.toReal_add hAt hBt, hadd]
      linarith
    -- Helper: eVarOn(Icc t s).toReal ≤ K * (s - t) for a ≤ t ≤ s ≤ b
    have hVarK : ∀ {t s : ℝ}, a ≤ t → t ≤ s → s ≤ b →
        (eVariationOn γ (Icc t s)).toReal ≤ K * (s - t) := by
      intro t s hat hts hsb
      have hMaps : MapsTo id (Icc t s) (Icc a b) :=
        fun x hx => ⟨hat.trans hx.1, hx.2.trans hsb⟩
      have hbound : eVariationOn γ (Icc t s) ≤ K * eVariationOn id (Icc t s) := by
        have := hK.comp_eVariationOn_le hMaps
        simpa using this
      rw [eVariationOn_id_Icc] at hbound
      have h1 : (K * ENNReal.ofReal (s - t)).toReal = K * (s - t) := by
        rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (sub_nonneg.mpr hts)]
      rw [← h1]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
        hbound
    -- V is LipschitzOnWith K on [a, b]
    have hVlip : LipschitzOnWith K V (Icc a b) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro t ht s hs
      rw [Real.dist_eq, Real.dist_eq]
      rcases le_total t s with hts | hst
      · -- t ≤ s: |V t - V s| = V s - V t = eVarOn(Icc t s).toReal ≤ K * (s - t) = K * |t - s|
        have hVdiff_ts : V s - V t = (eVariationOn γ (Icc t s)).toReal := hVincr ht.1 hts hs.2
        have hVnn : (0 : ℝ) ≤ (eVariationOn γ (Icc t s)).toReal := ENNReal.toReal_nonneg
        have hVmono : V t ≤ V s := by linarith
        rw [abs_of_nonpos (sub_nonpos.mpr hVmono), neg_sub, hVdiff_ts,
            abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
        exact hVarK ht.1 hts hs.2
      · -- s ≤ t: |V t - V s| = V t - V s = eVarOn(Icc s t).toReal ≤ K * (t - s) = K * |t - s|
        have hVdiff_st : V t - V s = (eVariationOn γ (Icc s t)).toReal := hVincr hs.1 hst ht.2
        have hVnn : (0 : ℝ) ≤ (eVariationOn γ (Icc s t)).toReal := ENNReal.toReal_nonneg
        have hVmono : V s ≤ V t := by linarith
        rw [abs_of_nonneg (sub_nonneg.mpr hVmono), hVdiff_st,
            abs_of_nonneg (sub_nonneg.mpr hst)]
        exact hVarK hs.1 hst ht.2
    -- V is ContinuousOn [a, b] (from Lipschitz)
    have hVcont : ContinuousOn V (Icc a b) := hVlip.continuousOn
    -- V(a) = 0
    have hVa : V a = 0 := by simp [V]
    -- V has right-derivative ‖deriv γ t‖ at each t ∈ (a, b)
    have hVderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt V ‖deriv γ t‖ (Ioi t) t := by
      intro t ht
      rw [hasDerivWithinAt_iff_isLittleO]
      -- FTC: ∫_a^s ‖γ'‖ has derivative ‖γ'(t)‖ at t
      have hFTC : HasDerivAt (fun u => ∫ x in a..u, ‖deriv γ x‖) ‖deriv γ t‖ t :=
        integral_hasDerivAt_right (hnorm_cont.intervalIntegrable a t)
          (hnorm_cont.stronglyMeasurableAtFilter _ _) hnorm_cont.continuousAt
      -- γ has derivative deriv γ t at t
      have hγt : HasDerivAt γ (deriv γ t) t := (hγ_diff t).hasDerivAt
      -- isLittleO proof via squeeze
      apply IsLittleO.of_bound
      intro ε hε
      have hFTC_bd := hFTC.isLittleO.def (half_pos hε)
      have hγ_bd := hγt.isLittleO.def (half_pos hε)
      have hsb_ev : ∀ᶠ s in 𝓝[>] t, s ≤ b := by
        apply eventually_nhdsWithin_of_eventually_nhds
        filter_upwards [Iio_mem_nhds ht.2] with s hs using le_of_lt hs
      filter_upwards [hFTC_bd.filter_mono nhdsWithin_le_nhds,
                      hγ_bd.filter_mono nhdsWithin_le_nhds,
                      self_mem_nhdsWithin, hsb_ev] with s hFTC_s hγ_s hst hsb'
      have hst_pos : t < s := hst
      have hts_le : t ≤ s := hst_pos.le
      -- eVarOn(Icc t s) is finite
      have hBne : eVariationOn γ (Icc t s) ≠ ⊤ := hbv_sub ht.1.le hsb'
      -- V(s) - V(t) = eVarOn(Icc t s).toReal
      have hVdiff : V s - V t = (eVariationOn γ (Icc t s)).toReal :=
        hVincr ht.1.le hts_le hsb'
      -- ∫_t^s ‖γ'‖ = (∫_a^s ‖γ'‖) - (∫_a^t ‖γ'‖)
      have hI_split : ∫ x in t..s, ‖deriv γ x‖ =
          (∫ x in a..s, ‖deriv γ x‖) - ∫ x in a..t, ‖deriv γ x‖ :=
        (intervalIntegral.integral_interval_sub_left
          (hnorm_cont.intervalIntegrable a s) (hnorm_cont.intervalIntegrable a t)).symm
      -- Upper: eVarOn(Icc t s).toReal ≤ ∫_t^s ‖γ'‖
      have hVub : (eVariationOn γ (Icc t s)).toReal ≤ ∫ x in t..s, ‖deriv γ x‖ :=
        hlocal_ub_real t s hts_le
      -- Lower: ‖γ(s) - γ(t)‖ ≤ eVarOn(Icc t s).toReal
      have hVlb : ‖γ s - γ t‖ ≤ (eVariationOn γ (Icc t s)).toReal := by
        have h := eVariationOn.edist_le γ
          (show t ∈ Icc t s from ⟨le_refl t, hts_le⟩)
          (show s ∈ Icc t s from ⟨hts_le, le_refl s⟩)
        rw [edist_dist, dist_comm, dist_eq_norm] at h
        exact (ENNReal.ofReal_le_iff_le_toReal hBne).mp h
      -- FTC bound: |(∫_t^s ‖γ'‖) - (s-t)*‖γ'(t)‖| ≤ ε/2 * |s-t|
      have key_FTC : |(∫ x in t..s, ‖deriv γ x‖) - (s - t) * ‖deriv γ t‖| ≤ ε / 2 * ‖s - t‖ := by
        have bound := hFTC_s
        simp only [smul_eq_mul] at bound
        rw [← hI_split] at bound
        rwa [Real.norm_eq_abs] at bound
      -- Norm bound: |‖γ(s)-γ(t)‖ - (s-t)*‖γ'(t)‖| ≤ ε/2 * |s-t|
      have key_γ_norm : |‖γ s - γ t‖ - (s - t) * ‖deriv γ t‖| ≤ ε / 2 * ‖s - t‖ := by
        calc |‖γ s - γ t‖ - (s - t) * ‖deriv γ t‖|
            = |‖γ s - γ t‖ - ‖(s - t) • deriv γ t‖| := by
                congr 1; rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hts_le)]
          _ ≤ ‖(γ s - γ t) - (s - t) • deriv γ t‖ := abs_norm_sub_norm_le _ _
          _ = ‖γ s - γ t - (s - t) • deriv γ t‖ := rfl
          _ ≤ ε / 2 * ‖s - t‖ := hγ_s
      -- Squeeze: |eVarOn - (s-t)*‖γ'‖| ≤ ε * |s-t|
      rw [Real.norm_eq_abs, hVdiff, smul_eq_mul]
      rcases le_total ((eVariationOn γ (Icc t s)).toReal) ((s - t) * ‖deriv γ t‖) with hcase | hcase
      · -- eVarOn ≤ (s-t)*‖γ'‖: bound by |‖γs-γt‖ - (s-t)‖γ'‖|
        rw [abs_of_nonpos (sub_nonpos.mpr hcase), neg_sub]
        calc (s - t) * ‖deriv γ t‖ - (eVariationOn γ (Icc t s)).toReal
            ≤ (s - t) * ‖deriv γ t‖ - ‖γ s - γ t‖ := by linarith
          _ ≤ |(s - t) * ‖deriv γ t‖ - ‖γ s - γ t‖| := le_abs_self _
          _ = |‖γ s - γ t‖ - (s - t) * ‖deriv γ t‖| := abs_sub_comm _ _
          _ ≤ ε / 2 * ‖s - t‖ := key_γ_norm
          _ ≤ ε * ‖s - t‖ := by nlinarith [norm_nonneg (s - t)]
      · -- eVarOn ≥ (s-t)*‖γ'‖: bound by |∫_t^s ‖γ'‖ - (s-t)‖γ'‖|
        rw [abs_of_nonneg (sub_nonneg.mpr hcase)]
        calc (eVariationOn γ (Icc t s)).toReal - (s - t) * ‖deriv γ t‖
            ≤ (∫ x in t..s, ‖deriv γ x‖) - (s - t) * ‖deriv γ t‖ := sub_le_sub_right hVub _
          _ ≤ |(∫ x in t..s, ‖deriv γ x‖) - (s - t) * ‖deriv γ t‖| := le_abs_self _
          _ ≤ ε / 2 * ‖s - t‖ := key_FTC
          _ ≤ ε * ‖s - t‖ := by nlinarith [norm_nonneg (s - t)]
    -- Apply integral_le_sub_of_hasDeriv_right_of_le
    calc ∫ t in a..b, ‖deriv γ t‖
        ≤ V b - V a :=
          integral_le_sub_of_hasDeriv_right_of_le hab hVcont hVderiv
            hnorm_cont.integrableOn_Icc (fun t _ => le_refl _)
      _ = (eVariationOn γ (Icc a b)).toReal := by simp [V, hVa]
  -- Combine upper and lower bounds
  apply le_antisymm
  · exact ENNReal.toReal_le_of_le_ofReal hint_nonneg hupper
  · exact hlower
