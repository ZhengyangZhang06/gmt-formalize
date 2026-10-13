# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.bf_trichotomy-a1`
- Child DAG node: `root.rectifiability-a1.bf_trichotomy-a1.cone_ratio_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent-supplied proof of rectifiability_bf_trichotomy. There, Φ = 0 gives (T1), and Φ = ∞ gives (T2) because X_v(a,r,s) ⊆ L_v⁻¹(B(L_va, rs)). The statement here is for an arbitrary measure μ; the parent applies it with μ := Hᵏ⌞E.

Notation. c(x) := ENNReal.ofReal x; R(r,s) := μ(X_v(a,r,s))/c((rs)ᵏ); F(s) := sup_{r∈(0,δ)} R(r,s); so Φ = limsup_{s→0⁺} F(s). Write L := L_v.

Part (i): Φ = 0.
1. Let η > 0. Then c(η) > 0 = Φ = limsup F, so F(s) < c(η) for all s in some set U ∈ 𝓝[>]0 (Mathlib Filter.eventually_lt_of_limsup_lt; its boundedness side condition is automatic in the complete lattice [0,∞]). Since (0,1) ∈ 𝓝[>]0 and 𝓝[>]0 is a proper filter, U ∩ (0,1) ≠ ∅. Pick s in it.
2. Let r ∈ (0,δ). Then R(r,s) ≤ F(s) < c(η). As r, s > 0, c((rs)ᵏ) ∈ (0,∞). So R(r,s) < c(η) gives μ(X_v(a,r,s)) < c(η)·c((rs)ᵏ) (ENNReal.div_lt_iff), and c(η)·c((rs)ᵏ) = c(η(rs)ᵏ) (ENNReal.ofReal_mul, η ≥ 0). In particular μ(X_v(a,r,s)) ≤ c(η·(rs)ᵏ). So s ∈ (0,1) is as required.

Part (ii): Φ = ∞.
3. Push-forward. L is linear and continuous ℝ^N → ℝᵏ: each coordinate x ↦ ⟨v_i,x⟩ is continuous linear, and WithLp.toLp is continuous. So L is measurable. For every ρ the closed ball B̄(La,ρ) is closed, hence measurable, and ν(B̄(La,ρ)) = μ(L⁻¹(B̄(La,ρ))) (Measure.map_apply).
4. Cones lie in preimages of balls. Let r, s > 0, ρ := rs and x ∈ X_v(a,r,s).
 - Lx − La = L(x − a), by linearity of the inner product in its second argument.
 - |L(x − a)| < s|x − a| ≤ s·r = ρ, using |x − a| < r and s > 0.
 Hence dist(Lx, La) < ρ. So X_v(a,r,s) ⊆ L⁻¹(B̄(La,ρ)), and μ(X_v(a,r,s)) ≤ ν(B̄(La,ρ)) = ν(univ ∩ B̄(La,ρ)).
5. The constant ω := realUnitBallVolume(k) = c(π^{k/2}/Γ(k/2 + 1)) lies in (0,∞): π^{k/2} > 0, and Γ(k/2 + 1) > 0 because k/2 + 1 > 0 (Real.Gamma_pos_of_pos). For ρ > 0, the density quotient in dimensionalUpperDensity ν k univ (La) is Q(ρ) := ν(univ ∩ B̄(La,ρ))/(ω·c(ρ)^k), with real exponent k. Here c(ρ)^k = c(ρᵏ) (ENNReal.ofReal_rpow_of_nonneg and Real.rpow_natCast).
6. Let b ∈ [0,∞) and ρ₀ > 0. We find ρ ∈ (0,ρ₀) with Q(ρ) > b.
 - Put Λ := b·ω < ∞. Since Λ < ∞ = Φ = limsup F, F(s) > Λ frequently as s → 0⁺ (Filter.frequently_lt_of_lt_limsup).
 - δ > 0: if δ ≤ 0, then (0,δ) = ∅ and F ≡ 0, contradicting F(s) > Λ ≥ 0.
 - The interval (0, ρ₀/δ) belongs to 𝓝[>]0, so some s ∈ (0, ρ₀/δ) has F(s) > Λ. Then some r ∈ (0,δ) has R(r,s) > Λ (lt_biSup_iff).
 - Put ρ := rs. Then 0 < ρ < δ·(ρ₀/δ) = ρ₀.
 - By steps 4 and 5, Q(ρ) = ν(univ ∩ B̄(La,ρ))/(ω·c((rs)ᵏ)) ≥ μ(X_v(a,r,s))/(ω·c((rs)ᵏ)) = R(r,s)/ω > Λ/ω = b. This uses x/(ω·y) = (x/y)/ω, the fact that division by the constant ω ∈ (0,∞) is strictly increasing, and Λ/ω = b.
7. By step 6, for every b < ∞ the set {ρ : Q(ρ) > b} meets every interval (0,ρ₀), ρ₀ > 0. These intervals form a basis of 𝓝[>]0, so Q > b frequently along 𝓝[>]0. Hence b ≤ limsup_{ρ→0⁺} Q(ρ) = dimensionalUpperDensity ν k univ (La) (Filter.le_limsup_of_frequently_le). If this limsup θ were finite, b := θ + 1 would give θ + 1 ≤ θ, which is impossible. Hence dimensionalUpperDensity ν k univ (La) = ∞. ∎

Lean reference proof (appendix; written by the independent Lean reviewer of this decomposition and re-compiled by the author). It is compile-checked as a single declaration against the exact frozen statement inside `namespace GMT.Ch06` of a scratch copy of the frozen project (commit d8d46c9587747dee0751a1f780fcafdba16a3886, Lean v4.35.0-rc3, pinned Mathlib 25730c7c), with no sibling dependencies; #print axioms = [propext, Classical.choice, Quot.sound]. It introduces no auxiliary declarations.
```lean
theorem Submission.rectifiability_bf_cone_ratio_reduction : (∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (v : Fin (m + 1) → Eucl N), (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = 0 → ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))) ∧ (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = ⊤ → dimensionalUpperDensity (Measure.map (fun x : Eucl N => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) μ).toOuterMeasure ((m + 1 : ℕ) : ℝ) univ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) = ⊤)) := by
  intro N m μ δ a v
  constructor
  · intro h0 η hη
    have hlt : limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) < ENNReal.ofReal η := by
      rw [h0]; exact ENNReal.ofReal_pos.2 hη
    have hev := Filter.eventually_lt_of_limsup_lt hlt
    have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    obtain ⟨s, hs1, hs2⟩ := (hev.and hev2).exists
    refine ⟨s, hs2, fun r hr => ?_⟩
    have hle : μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1)) ≤ ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1)) :=
      le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) => μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) r hr
    have hpos : 0 < (r * s) ^ (m + 1) := pow_pos (mul_pos hr.1 hs2.1) _
    have h3 := hle.trans_lt hs1
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.2 hpos).ne') (Or.inl ENNReal.ofReal_ne_top)] at h3
    rw [ENNReal.ofReal_mul hη.le]
    exact h3.le
  · intro htop
    set L : Eucl N → Eucl (m + 1) := fun x => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1)) with hLdef
    have hLc : Continuous L := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      exact continuous_const.inner continuous_id
    have hLsub : ∀ x y, L x - L y = L (x - y) := by
      intro x y
      simp only [hLdef, ← WithLp.toLp_sub]
      congr 1
      funext i
      simp [inner_sub_right]
    set ω := Poincare.SimonGMT.Chapter01.realUnitBallVolume (((m + 1 : ℕ) : ℝ)) with hω
    have hω0 : ω ≠ 0 := by
      rw [hω, Poincare.SimonGMT.Chapter01.realUnitBallVolume]
      refine (ENNReal.ofReal_pos.2 (div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos ?_))).ne'
      positivity
    have hωt : ω ≠ ⊤ := by
      rw [hω, Poincare.SimonGMT.Chapter01.realUnitBallVolume]; exact ENNReal.ofReal_ne_top
    -- δ > 0
    have hδ : 0 < δ := by
      by_contra hδ
      push Not at hδ
      have : (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) = fun _ => 0 := by
        funext s
        rw [Ioo_eq_empty (not_lt.2 hδ)]
        simp
      rw [this, limsup_const] at htop
      exact ENNReal.zero_ne_top htop
    unfold dimensionalUpperDensity
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro b
    refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    rw [(nhdsGT_basis (0 : ℝ)).frequently_iff]
    intro ρ₀ hρ₀
    have hΛ : (b : ℝ≥0∞) * ω < limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) := by
      rw [htop]; exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.2 hωt)
    have hfr := Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hΛ
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) (ρ₀ / δ) := Ioo_mem_nhdsGT (div_pos hρ₀ hδ)
    obtain ⟨s, hs1, hs2⟩ := (hfr.and_eventually hev).exists
    rw [lt_biSup_iff] at hs1
    obtain ⟨r, hr, hrs⟩ := hs1
    have hrs0 : 0 < r * s := mul_pos hr.1 hs2.1
    have hrsρ : r * s < ρ₀ := by
      have h1 : r * s < δ * (ρ₀ / δ) := mul_lt_mul'' hr.2 hs2.2 hr.1.le hs2.1.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at h1
    refine ⟨r * s, ⟨hrs0, hrsρ⟩, ?_⟩
    have hpos : 0 < (r * s) ^ (m + 1) := pow_pos hrs0 _
    -- the cone lies in the preimage of the closed ball
    have hsub : {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} ⊆ L ⁻¹' closedBall (L a) (r * s) := by
      intro x hx
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, hLsub]
      have h1 : ‖x - a‖ < r := by rw [← dist_eq_norm]; exact hx.1
      have h2 := hx.2
      calc ‖L (x - a)‖ ≤ s * ‖x - a‖ := h2.le
        _ ≤ s * r := by gcongr; exact hs2.1.le
        _ = r * s := mul_comm _ _
    have hmap : (Measure.map L μ).toOuterMeasure (univ ∩ closedBall (L a) (r * s)) ≥ μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} := by
      rw [Measure.coe_toOuterMeasure, univ_inter, Measure.map_apply hLc.measurable isClosed_closedBall.measurableSet]
      exact measure_mono hsub
    unfold Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient
    rw [ENNReal.ofReal_rpow_of_nonneg hrs0.le (by positivity), Real.rpow_natCast]
    rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hω0 (ENNReal.ofReal_pos.2 hpos).ne')) (Or.inl (ENNReal.mul_ne_top hωt ENNReal.ofReal_ne_top))]
    refine le_trans ?_ hmap
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 hpos).ne') (Or.inl ENNReal.ofReal_ne_top)] at hrs
    rw [← mul_assoc]
    exact hrs.le
```

## Key steps

1. Φ = 0: eventually F(s) < η, so some s ∈ (0,1) satisfies μ(X_v(a,r,s)) ≤ η(rs)ᵏ for all r ∈ (0,δ).
2. X_v(a,r,s) ⊆ L_v⁻¹(B̄(L_va, rs)), so μ(X_v(a,r,s)) ≤ ν(B̄(L_va, rs)).
3. Φ = ∞: for every b < ∞ and ρ₀ > 0 there are s < ρ₀/δ and r < δ with μ(X_v(a,r,s)) > bω_k(rs)ᵏ. This gives a density quotient > b at ρ = rs < ρ₀.
4. Large density quotients occur frequently as ρ → 0⁺, so the upper density limsup is ∞.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git archive d8d46c9 into /tmp/bft-decomp-1791847446; cmp GMT/Ch06/Submission.lean (workspace) and project/GMT/Ch06/Contract.lean (snapshot) against the scratch copy (identical); lake build GMT.Ch06.Submission (success, 3152 jobs)`
- `rg -n 'theorem ae_ae_comm|theorem measurable_measure_prodMk_left |theorem _root_.Monotone.measure_iUnion|theorem _root_.Directed.measure_iUnion|theorem measure_biUnion_eq_iSup|theorem prod_apply_symm|theorem prod_apply |lemma IsSigmaCompact.image|theorem limsup_add_le|theorem limsup_const_mul_of_ne_top|theorem inner_single_left' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'measure_preimage_add_right|measure_univ_of_isAddLeftInvariant|measure_univ_of_isMulLeftInvariant' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n -i 'mickle|besicovitch.federer|purely.unrectifiable' local-references/197bdd4b88278494/mathlib/Mathlib local-references/197bdd4b88278494/project (no match); rg -n 'IsSigmaCompact.measurableSet' local-references/197bdd4b88278494/mathlib/Mathlib (no match)`
- `rg -n 'def dimensionalDensityQuotient|def realUnitBallVolume' lake-packages-25730c7c/simongmt/Poincare; sed -n 1,70p Chapter01/Densities.lean`
- `python3 verifier/gmt-compare.py contract_scope + child_modules (contract mode) for all 8 child statements; lake env lean Scratch/Chal_*.lean (0 errors)`
- `lake env lean Scratch/Names.lean and Scratch/Inst.lean (#check of the cited lemma names; instance checks for IsAddHaarMeasure, IsAddRightInvariant, SFinite of volume on Fin (m+1) → Eucl N, volume univ = ⊤ on Eucl (m+1), BorelSpace of the product types)`
- `lake env lean Scratch/Assembly.lean (parent from child stubs; #print axioms), Scratch/Iface1.lean (cone_ratio_measurable proved from the limsup_sup_measurable stub; ϑ_j instance), Scratch/Iface2.lean (OuterMeasure.mk + rectifiability_mickle_rado interface; later found vacuous because of a binder capture in the test example, and superseded by the complete slice_density_null proof)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (658 names); byte comparison of reused lean_statement/title/statement against dag.json and the accepted handoffs`
- `lake env lean Verify/AllProofsFull.lean (independent reviewer's complete proofs of all six new children + accepted mickle_rado subtree + parent assembly; 0 errors; #print axioms [propext, Classical.choice, Quot.sound] for every declaration) and Verify/Standalone/<key>.lean for each new child with only its declared siblings stubbed (0 errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-trichotomy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mickle-rado-a1-limsup-eq-iinf-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1/decomposition-v1.json`
- `/tmp/bft-decomp-1791847446/Scratch/Assembly.lean`
- `/tmp/bft-decomp-1791847446/Scratch/Iface1.lean`
- `/tmp/bft-decomp-1791847446/Verify/AllProofsFull.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/slice_density_null.lean`
- `/tmp/bft-decomp-1791847446/Verify/Standalone/limsup_sup_measurable.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract, byte-identical to the workspace Submission.lean and to the scratch copy. Neither the snapshot Mathlib nor the project contains a Besicovitch–Federer, Mickle–Radó or purely-unrectifiable result (rg: no match), and Mathlib has no IsSigmaCompact.measurableSet. So all six new child obligations are genuine; the two accepted declarations rectifiability_mickle_rado and rectifiability_mickle_rado_limsup_eq_iInf are reused with byte-identical types. Every library input cited by the child proofs exists in the pinned environment: measurable_measure_prodMk_left, Measure.prod_apply and prod_apply_symm, Measure.ae_ae_comm (Prod.lean), Monotone.measure_iUnion, Directed.measure_iUnion and measure_biUnion_eq_iSup (Continuity.lean), measure_preimage_add_right and measure_univ_of_isAddLeftInvariant (additive forms of Group/Measure.lean), ENNReal.limsup_const_mul_of_ne_top (Order/Filter/ENNReal.lean), IsSigmaCompact.image, EuclideanSpace.inner_single_left (PiL2.lean:318), and dimensionalDensityQuotient and realUnitBallVolume (SimonGMT Chapter01/Densities.lean:39, Hausdorff.lean:34). ENNReal.limsup_add_le (ENNReal.lean:231) requires CountableInterFilter, which 𝓝[>]0 is not, so fibre_cone_comparison proves limsup subadditivity directly. In the scratch build, all eight child types elaborate in the comparator's exact child scope. The parent compiles from the five stubbed children it uses. Complete single-declaration Lean proofs of all six new children compile against their exact frozen types, using only their declared siblings, and with the accepted mickle_rado subtree the whole tree including Submission.rectifiability_bf_trichotomy compiles with axioms [propext, Classical.choice, Quot.sound].
