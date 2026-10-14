# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.smooth_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2 (F_j := Mo(F, Λ), G_j := Mo(G, Λ), H_j the interpolation, properties (a)–(d)). Notation: ℝ^N = Euclid N; ι(t, x) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) ∈ ℝ^{N+1} (the point (t, x_1, …, x_N)); Jv := ι(0, v); e₀ := EuclideanSpace.single 0 1; |α| := covectorEuclideanNorm α; D = fderiv ℝ; F^#ω(x) := (ω(F x)).compContinuousLinearMap (DF(x)); NC X means IsCompact X.support, X.mass < ∞ and boundaryMassOn X univ < ∞; C(K) := {ι(t, x) : t ∈ [0, 1], x ∈ K}; d := exteriorDerivative, on test forms exteriorDerivativeTestOn univ m (whose coercion is exteriorDerivative of the coercion, by rfl).
1. Mollification. By Submission.cmcdt_lpo_mollify_lipschitz (the sibling (Mo)) applied to F and to G there are C^∞, Λ-Lipschitz maps F_j, G_j with dist(F_j x, F x) ≤ Λ/(j + 1) and dist(G_j x, G x) ≤ Λ/(j + 1) for all j, x. For each j apply Submission.cmcdt_lpoh_interp_calculus to f := F_j, g := G_j and let H_j be the resulting map h (choice over j). So H_j is C^∞ and, for all t, x, v: (a) H_j(ι(t, x)) = F_j x + t(G_j x − F_j x); (b) DH_j(ι(t, x))e₀ = G_j x − F_j x; (c) DH_j(ι(t, x))(Jv) = DF_j(x)v + t(DG_j(x)v − DF_j(x)v); (d) ‖DH_j(ι(t, x))‖ ≤ ‖G_j x − F_j x‖ + ‖DF_j(x)‖ + |t|(‖DG_j(x)‖ + ‖DF_j(x)‖). This gives (1).
2. Claim (2). A Λ-Lipschitz map has ‖DF_j(x)‖ ≤ Λ at every point (norm_fderiv_le_of_lipschitz); same for G_j.
3. Claim (3). Λ/(j + 1) → 0 (tendsto_one_div_add_atTop_nhds_zero_nat multiplied by Λ). Given ε > 0, for all large j we have Λ/(j + 1) < ε, hence dist(F x, F_j x) < ε for every x ∈ ℝ^N; this is uniform convergence (Metric.tendstoUniformly_iff). Same for G.
4. Claim (4). (a) with t = 1 gives H_j(ι(1, x)) = F_j x + (G_j x − F_j x) = G_j x; with t = 0 it gives F_j x.
5. Claim (5). (c) with t = 1 gives DF_j(x)v + (DG_j(x)v − DF_j(x)v) = DG_j(x)v; with t = 0 it gives DF_j(x)v.
6. A difference estimate. By the triangle inequality, for all j, x: ‖G_j x − F_j x‖ = dist(G_j x, F_j x) ≤ dist(G_j x, G x) + dist(G x, F x) + dist(F x, F_j x) ≤ dist(F x, G x) + 2Λ/(j + 1). (*)
7. Claim (6). By (b) and (*), ‖DH_j(ι(t, x))e₀‖ = ‖G_j x − F_j x‖ ≤ dist(F x, G x) + 2Λ/(j + 1).
8. Claim (7). By (c), DH_j(ι(t, x))(Jv) = (1 − t)DF_j(x)v + t·DG_j(x)v. For t ∈ [0, 1], 1 − t ≥ 0 and t ≥ 0, so by step 2 its norm is ≤ (1 − t)Λ‖v‖ + tΛ‖v‖ = Λ‖v‖.
9. Claim (8). F and G are Lipschitz, hence continuous, so x ↦ dist(F x, G x) is continuous and bounded on the compact K by some M (IsCompact.exists_bound_of_continuousOn). Put Λ' := M + 5Λ. For t ∈ [0, 1] (so |t| ≤ 1) and x ∈ K, by (d), (*), step 2 and 2Λ/(j + 1) ≤ 2Λ: ‖DH_j(ι(t, x))‖ ≤ (M + 2Λ) + Λ + 1·(Λ + Λ) = Λ'.
10. Claim (9). Let y ∈ C(K), y = ι(t, x) with t ∈ [0, 1], x ∈ K. By the hypothesis on H and (a), H(y) − H_j(y) = (F x + t(G x − F x)) − (F_j x + t(G_j x − F_j x)) = (1 − t)(F x − F_j x) + t(G x − G_j x), so dist(H y, H_j y) ≤ (1 − t)Λ/(j + 1) + tΛ/(j + 1) = Λ/(j + 1), a bound independent of y that tends to 0; hence H_j → H uniformly on C(K) (Metric.tendstoUniformlyOn_iff). □

Appendix (informative; the numbered proof above is the contract). The following tactic script was compiled with `lake env lean` after `import GMT.Ch07.Submission` (Mathlib 25730c7c) as the `by` block of the declaration `theorem Submission.cmcdt_lpoh_smooth_approx` whose type is exactly this node's frozen lean_statement, with every cited dependency declared under its exact frozen type; it produced no errors or warnings:
  intro N N' Λ F G H K hF hG hK hHK
  obtain ⟨Fs, hFs, hFL, hFd⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ F hF
  obtain ⟨Gs, hGs, hGL, hGd⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ G hG
  choose Hs hHs hHι hHe hHJ hHn using
    fun j => Submission.cmcdt_lpoh_interp_calculus N N' (Fs j) (Gs j) (hFs j) (hGs j)
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ K, dist (F x) (G x) ≤ M := by
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      ((hF.continuous.dist hG.continuous).continuousOn)
    exact ⟨M, fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM x hx)⟩
  have hΛ : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
  have hDF : ∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ) :=
    fun j x => norm_fderiv_le_of_lipschitz ℝ (hFL j)
  have hDG : ∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Gs j) x‖ ≤ (Λ : ℝ) :=
    fun j x => norm_fderiv_le_of_lipschitz ℝ (hGL j)
  have hsmall : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Λ : ℝ)
    rw [mul_zero] at h
    refine h.congr (fun j => ?_)
    rw [mul_one_div]
  have hunif : ∀ (Es : ℕ → Euclid N → Euclid N') (E : Euclid N → Euclid N'),
      (∀ (j : ℕ) (x : Euclid N), dist (Es j x) (E x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) →
      TendstoUniformly Es E atTop := by
    intro Es E hE
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj x
    rw [dist_comm]
    exact (hE j x).trans_lt hj
  have hjpos : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 := fun j => by positivity
  have hGF : ∀ (j : ℕ) (x : Euclid N),
      ‖Gs j x - Fs j x‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) := by
    intro j x
    rw [← dist_eq_norm]
    calc dist (Gs j x) (Fs j x) ≤ dist (Gs j x) (G x) + dist (G x) (F x) + dist (F x) (Fs j x) :=
          dist_triangle4 _ _ _ _
      _ ≤ (Λ : ℝ) / ((j : ℝ) + 1) + dist (F x) (G x) + (Λ : ℝ) / ((j : ℝ) + 1) := by
          gcongr
          · exact hGd j x
          · rw [dist_comm]
          · rw [dist_comm]; exact hFd j x
      _ = dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) := by ring
  refine ⟨Fs, Gs, Hs, M + 5 * (Λ : ℝ), hFs, hGs, hHs, hDF, hDG, hunif Fs F hFd, hunif Gs G hGd,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x; rw [hHι]; simp
  · intro j x; rw [hHι]; simp
  · intro j x v; rw [hHJ]; simp
  · intro j x v; rw [hHJ]; simp
  · intro j t x; rw [hHe]; exact hGF j x
  · intro j t ht x v
    rw [hHJ]
    have h1 : fderiv ℝ (Fs j) x v + t • (fderiv ℝ (Gs j) x v - fderiv ℝ (Fs j) x v) =
        (1 - t) • fderiv ℝ (Fs j) x v + t • fderiv ℝ (Gs j) x v := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [h1]
    have hF' : ‖fderiv ℝ (Fs j) x v‖ ≤ (Λ : ℝ) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hDF j x)
    have hG' : ‖fderiv ℝ (Gs j) x v‖ ≤ (Λ : ℝ) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hDG j x)
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    calc ‖(1 - t) • fderiv ℝ (Fs j) x v + t • fderiv ℝ (Gs j) x v‖
        ≤ ‖(1 - t) • fderiv ℝ (Fs j) x v‖ + ‖t • fderiv ℝ (Gs j) x v‖ := norm_add_le _ _
      _ = (1 - t) * ‖fderiv ℝ (Fs j) x v‖ + t * ‖fderiv ℝ (Gs j) x v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * ((Λ : ℝ) * ‖v‖) + t * ((Λ : ℝ) * ‖v‖) := by gcongr
      _ = (Λ : ℝ) * ‖v‖ := by ring
  · intro j t ht x hx
    refine (hHn j t x).trans ?_
    have h2 : 2 * (Λ : ℝ) / ((j : ℝ) + 1) ≤ 2 * (Λ : ℝ) :=
      div_le_self (by positivity) (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
    have habs : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc ‖Gs j x - Fs j x‖ + ‖fderiv ℝ (Fs j) x‖ + |t| * (‖fderiv ℝ (Gs j) x‖ + ‖fderiv ℝ (Fs j) x‖)
        ≤ (M + 2 * (Λ : ℝ)) + (Λ : ℝ) + 1 * ((Λ : ℝ) + (Λ : ℝ)) := by
          gcongr
          · exact (hGF j x).trans (by linarith [hM x hx])
          · exact hDF j x
          · exact hDG j x
          · exact hDF j x
      _ = M + 5 * (Λ : ℝ) := by ring
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj y hy
    obtain ⟨t, ht, x, hx, rfl⟩ := hy
    rw [hHK x hx t ht, hHι, dist_eq_norm]
    have h1 : F x + t • (G x - F x) - (Fs j x + t • (Gs j x - Fs j x)) =
        (1 - t) • (F x - Fs j x) + t • (G x - Gs j x) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [h1]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    calc ‖(1 - t) • (F x - Fs j x) + t • (G x - Gs j x)‖
        ≤ ‖(1 - t) • (F x - Fs j x)‖ + ‖t • (G x - Gs j x)‖ := norm_add_le _ _
      _ = (1 - t) * ‖F x - Fs j x‖ + t * ‖G x - Gs j x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * ((Λ : ℝ) / ((j : ℝ) + 1)) + t * ((Λ : ℝ) / ((j : ℝ) + 1)) := by
          gcongr
          · rw [← dist_eq_norm, dist_comm]; exact hFd j x
          · rw [← dist_eq_norm, dist_comm]; exact hGd j x
      _ = (Λ : ℝ) / ((j : ℝ) + 1) := by ring
      _ < ε := hj

## Key steps

1. Mollify F, G by Submission.cmcdt_lpo_mollify_lipschitz; interpolate each pair (F_j, G_j) by Submission.cmcdt_lpoh_interp_calculus to get H_j.
2. Derivative bounds ‖DF_j‖, ‖DG_j‖ ≤ Λ from Lipschitz; uniform convergence from dist ≤ Λ/(j+1) → 0.
3. End values and end derivatives of H_j from the interpolation formulas at t = 1, 0; ‖G_j x − F_j x‖ ≤ dist(F x, G x) + 2Λ/(j+1).
4. ‖DH_j(ι(t,x))(Jv)‖ ≤ Λ‖v‖ for t ∈ [0,1]; ‖DH_j‖ ≤ M + 5Λ on C(K) with M a bound of dist(F, G) on K.
5. H − H_j = (1−t)(F − F_j) + t(G − G_j) on C(K), so H_j → H uniformly there.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical)`
- `git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, as in manifest.json)`
- `rg -n cmcdt_lpoh local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name fields (only the eight cmcdt_lpo_* siblings; no cmcdt_lpoh_* reserved), depth of the selected node (5) and ancestor depends_on lean names`
- `rg -n 'def curryLeft\b|theorem curryLeft_apply_apply|def curryLeftLI|def compContinuousLinearMap\b|theorem compContinuousLinearMap_apply|compContinuousLinearMapCLM' mathlib/Mathlib -g '*.lean'`
- `sed -n 1,200p mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `rg -n 'theorem norm_fderiv_le_of_lipschitz|theorem HasFDerivAt.smul\b|theorem Continuous.finCons|theorem IsCompact.exists_bound_of_continuousOn|theorem comp_cons|theorem norm_apply_le' mathlib/Mathlib -g '*.lean'`
- `rg -n 'EuclideanSpace.proj|EuclideanSpace.equiv' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; sed -n 705,725p mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean; sed -n 940,960p mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean; sed -n 975,995p mathlib/Mathlib/Topology/Constructions.lean`
- `rg -n 'theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem dist_triangle4|def compContinuousLinearMapCLM' mathlib/Mathlib -g '*.lean'`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `lake env lean /tmp/htpy-decomp-r5/Base.lean (#check of the API above in the frozen import closure)`
- `lake env lean /tmp/htpy-decomp-r5/Children.lean (eight child types elaborate; sorry-free assembly of the selected frozen type; #print axioms)`
- `lake env lean /tmp/htpy-decomp-r5/Glue.lean, Glue2.lean, Glue3.lean, Glue4.lean, Full.lean (child proofs from exact dependency types; Full.lean derives Submission.cmcdt_lpo_lipschitz_homotopy)`
- `python3 validate_lean_statement from /runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/lean_contract.py on all eight lean_statements`
- `sed of /runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/inherited.py and runtime.py (_decompose depth gate, _dependency_problem, _existing_lean_name_problem)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-d8380d2126/parent-child-handoff.json`
- `/tmp/htpy-decomp-r5/Children.lean`
- `/tmp/htpy-decomp-r5/Full.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Submission.lean. It contains no cmcdt_lpoh_* declaration and no reusable proof of the homotopy statement. The Lean API the child proofs use is in the frozen import closure: ContinuousAlternatingMap.curryLeft, curryLeft_apply_apply, curryLeftLI, curryLeft_compContinuousLinearMap, compContinuousLinearMap_apply, compContinuousLinearMapCLM, EuclideanSpace.proj, PiLp.norm_apply_le, EuclideanSpace.norm_eq, norm_fderiv_le_of_lipschitz, HasFDerivAt.smul, Continuous.finCons, Fin.comp_cons, IsCompact.exists_bound_of_continuousOn, tendsto_one_div_add_atTop_nhds_zero_nat, dist_triangle4, tendsto_nhds_unique, le_of_tendsto_of_tendsto' and ContinuousLinearMap.opNorm_le_bound. ContinuousLinearMap.add_apply, smul_apply, sub_apply and coe_comp' are deprecated here; the generic add_apply, smul_apply, sub_apply and ContinuousLinearMap.coe_comp are used instead. From SimonGMT Chapter 6 they use GeometricCurrentOn.ext, boundary_apply, boundary_boundary, exteriorDerivativeTestOn, support = univ \ zeroRegion with isOpen_zeroRegion, and massOn as a supremum over massAdmissibleOn. All eight child types elaborate. With the four inherited sibling theorems declared under their exact frozen types, the eight child proofs and the parent assembly of the exact selected frozen type compile without errors or warnings; interp_calculus and phi_bound are axiom-clean.
