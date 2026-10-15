# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.weakly_harmonic_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step A3 of the parent proof, which replaces the weak convergence of gradients in Simon, Ch. 5, Lemma 3.1. Notation as in the statement; μ := volume.restrict B. Unlike the parent's step A3 (which integrates by parts against w_k and then uses ∫Δζ = 0), integration by parts is applied below directly to the Lipschitz function u_j − c_j, whose derivative equals Du_j, so ∫_B Δζ = 0 is not needed. The proof is self-contained apart from the two sibling lemmas named in steps 4 and 6.
1. (Fix the test function.) Fix ζ of class C² with compact support and tsupport ζ ⊆ B. The function Δζ is continuous: y ↦ iteratedFDeriv ℝ 2 ζ y is continuous because ζ is C² (ContDiff.continuous_iteratedFDeriv), evaluation of a continuous multilinear map at the fixed pair ![e_i, e_i] is continuous, and a finite sum of continuous functions is continuous.
2. (Continuous functions lie in L²(B).) Let f : ℝⁿ → ℝ be continuous. The closed ball closedBall 0 R is compact and contains B, so |f| ≤ K on B for some K (IsCompact.exists_bound_of_continuousOn); B has finite Lebesgue measure (measure_ball_lt_top), so μ is a finite measure; and f is a.e.-strongly measurable. Hence f ∈ L²(μ) (MemLp.of_bound). In particular Δζ ∈ L²(μ), and for each j, v_j := u_j − c_j ∈ L²(μ) (v_j is continuous because u_j is Lipschitz).
3. (Gradient bound for ζ.) ζ is C¹ (C² implies C¹). Dζ is continuous and has compact support, because its support lies in tsupport ζ (HasCompactSupport.fderiv). So there is G_ζ ∈ ℝ with ‖Dζ(v)‖ ≤ G_ζ for all v (HasCompactSupport.exists_bound_of_continuous).
4. (Integration by parts.) Fix j and let L_j be a Lipschitz constant of u_j. Then v_j = u_j − c_j is Lipschitz (constant L_j + 0) and Dv_j(y) = Du_j(y) for every y (fderiv_sub_const). The sibling lemma lipschitz_ibp (dorag_haa_lipschitz_ibp), applied to v_j and ζ, gives
   ∫_B Σ_i Du_j(y)e_i·Dζ(y)e_i dy = −∫_B v_j(y)·Δζ(y) dy.
   The hypothesis, applied to this j, the C¹ test function ζ (compact support, tsupport ζ ⊆ B, step 3) and G := G_ζ, gives |∫_B Σ_i Du_j e_i·Dζ e_i| ≤ δ_j·G_ζ. Since |−x| = |x|,
   |∫_B v_j·Δζ| ≤ δ_j·G_ζ for every j.
5. (The pairings tend to 0.) δ_j → 0, so δ_j·G_ζ → 0. Since 0 ≤ |∫_B v_j·Δζ| ≤ δ_j·G_ζ, the squeeze theorem gives ∫_B v_j·Δζ → 0.
6. (The pairings tend to ∫_B W·Δζ.) The sibling lemma l2_pairing (dorag_haa_l2_pairing_tendsto) applies with f_j := v_j, the given W and g := Δζ: all lie in L²(μ) by step 2 and the hypothesis on W, and ∫_B (v_j − W)² = ∫_B (u_j − c_j − W)² → 0 by hypothesis. It gives ∫_B v_j·Δζ → ∫_B W·Δζ.
7. (Conclusion.) Limits in ℝ are unique (tendsto_nhds_unique), so steps 5 and 6 give ∫_B W·Δζ = 0. As ζ was arbitrary, the claim follows. ∎

## Key steps

1. Δζ and every v_j := u_j − c_j are continuous, hence bounded on the bounded ball and in L²(B).
2. Dζ is continuous with compact support, so G_ζ := sup‖Dζ‖ < ∞.
3. lipschitz_ibp for v_j (Dv_j = Du_j): ∫_B v_jΔζ = −∫_B ∇u_j·∇ζ, so |∫_B v_jΔζ| ≤ δ_jG_ζ → 0.
4. l2_pairing with f_j := v_j, g := Δζ: ∫_B v_jΔζ → ∫_B WΔζ.
5. Uniqueness of limits: ∫_B WΔζ = 0.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `grep -n 'integral_lineDeriv_mul_eq|ae_differentiableAt|ae_lineDeriv_sum_eq' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `grep -rn 'setIntegral_comp_smul_of_pos|integrable_comp_smul_iff|map_addHaar_smul|smul_unitBall_of_pos|smul_ball' <snapshot>/mathlib/Mathlib`
- `grep -rn 'comp_right_fderiv|iteratedFDeriv_comp_right|iteratedFDeriv_comp_left|fderiv_comp_smul|fderiv_const_smul_field|fderiv_add_const|fderiv_sub_const|iteratedFDeriv_two_apply|iteratedFDeriv_add_const' <snapshot>/mathlib/Mathlib`
- `grep -rn 'integral_mul_le_Lp_mul_Lq_of_nonneg|MemLp.integrable_sq|MemLp.integrable_mul|MemLp.of_bound|Integrable.bdd_mul' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `grep -rn 'support_fderiv_subset|support_iteratedFDeriv_subset|HasCompactSupport.fderiv|HasCompactSupport.comp_smul|tsupport_comp_eq_preimage|ContDiff.lipschitzWith_of_hasCompactSupport|norm_fderiv_le_of_lipschitz|measurable_fderiv_apply_const|DifferentiableAt.lineDeriv_eq_fderiv' <snapshot>/mathlib/Mathlib`
- `grep -rn -E 'integral_lineDeriv_mul_eq|setIntegral_comp_smul|integral_mul_le_Lp_mul_Lq|lipschitz_ibp|weakly_harmonic|rescale' <snapshot>/project/GMT; grep -rln (same terms, plus fderiv_comp_smul, IntegrationByParts) .lake/packages/simongmt/Poincare`
- `grep -n 'Lemma 3.1|Rellich|Poincar' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt; sed -n 585,660p chapter-05.txt`
- `python3 -I scan of lean_name fields in dag.json and nodes/*/*.json plus grep -rl for the six proposed dorag_haa_* names (0 hits)`
- `lean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = workspace .lake builds): /tmp/dorag-ha-approx-split/Types.lean, Names.lean (#check of cited lemmas; MemLp.integrable_sq unknown), Assembly.lean, Checks.lean, Checks2.lean, Checks3.lean, Checks4.lean, Checks5.lean, Full.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9c9f0b580c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/dorag-ha-approx-split/Types.lean`
- `/tmp/dorag-ha-approx-split/Names.lean`
- `/tmp/dorag-ha-approx-split/Assembly.lean`
- `/tmp/dorag-ha-approx-split/Checks.lean`
- `/tmp/dorag-ha-approx-split/Checks2.lean`
- `/tmp/dorag-ha-approx-split/Checks3.lean`
- `/tmp/dorag-ha-approx-split/Checks4.lean`
- `/tmp/dorag-ha-approx-split/Checks5.lean`
- `/tmp/dorag-ha-approx-split/Full.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

The pinned Mathlib, within the contract's import closure, supplies everything the children cite:
- LipschitzWith.integral_lineDeriv_mul_eq (Rademacher.lean:169) and LipschitzWith.ae_differentiableAt (:385);
- Measure.setIntegral_comp_smul_of_pos and integrable_comp_smul_iff (Haar/NormedSpace.lean:148, :175), and smul_unitBall_of_pos (Ball/Pointwise.lean:139);
- fderiv_comp_smul (FDeriv/Equiv.lean:503) and fderiv_const_smul_field (FDeriv/Add.lean:175), both unconditional, and iteratedFDeriv_two_apply (FTaylorSeries.lean:948);
- integral_mul_le_Lp_mul_Lq_of_nonneg (Bochner/Basic.lean:1230), MemLp.integrable_mul, Integrable.bdd_mul and MemLp.of_bound;
- support_fderiv_subset, support_iteratedFDeriv_subset, HasCompactSupport.comp_smul, tsupport_comp_eq_preimage, ContDiff.lipschitzWith_of_hasCompactSupport and norm_fderiv_le_of_lipschitz.
The one exception is MemLp.integrable_sq (L2Space.lean:42), which is outside the import closure; the child proofs say so and use MemLp.integrable_mul instead.

Nothing is reusable from the project or SimonGMT. The project GMT tree matches only unrelated rescaledMeasure varifold definitions in Ch08. SimonGMT's only hit is a Hölder call inside Chapter04/LpMeanCurvature.lean. No declaration in either provides the six child statements, so no comparator-approved declaration can be reused.

Lean checks in comparator scope:
- all six child types elaborate;
- full Lean proofs of all six children use only propext, Classical.choice and Quot.sound;
- the exact frozen type of dorag_ha_approximation compiles from the six children plus unproved stubs of dorag_ha_poincare_ball, dorag_ha_rellich_ball, dorag_ha_weyl_lemma and dorag_ha_energy_lsc, with sorryAx coming only from those stubs.

The six dorag_haa_* names have no collisions in dag.json or nodes/*/*.json.
