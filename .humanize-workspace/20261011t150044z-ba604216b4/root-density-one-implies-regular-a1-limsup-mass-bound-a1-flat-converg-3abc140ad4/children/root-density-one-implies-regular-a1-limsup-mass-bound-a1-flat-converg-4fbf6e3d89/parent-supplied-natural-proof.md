# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cutoff_pullback-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cutoff_pullback-a1.cutoff_converges-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the supplied proof of the selected node (sequential continuity of ω ↦ ζ·p^#ω at 0), here for a general continuous linear L and a general smooth compactly supported ζ. The Leibniz bound is the sibling child leibniz_smul (Submission.dor_lmb_fc_dtop_cp_leibniz_smul_bound). Notation: ‖·‖ denotes operator norms, and Λ : Covector(ℝ^P, d) →L[ℝ] Covector(ℝ^Q, d), Λα := α.compContinuousLinearMap L (ContinuousAlternatingMap.compContinuousLinearMapCLM L), a continuous linear map.
1. Unpacking. By TestFormOnConverges ωs 0 there is a compact C ⊆ ℝ^P with tsupport ωs_j ⊆ C for all j. Moreover, for every l, D^l ωs_j → D^l 0 uniformly on C; D^l of the zero form is the zero function.
2. Global decay. For every l and every ε > 0, eventually in j we have ‖D^l ωs_j(x)‖ < ε for all x ∈ ℝ^P.
   - For x ∈ C this is the uniform convergence of step 1, since dist(0, D^l ωs_j(x)) = ‖D^l ωs_j(x)‖.
   - For x ∉ C we have x ∉ tsupport ωs_j ⊇ tsupport D^l ωs_j (tsupport_iteratedFDeriv_subset). So D^l ωs_j(x) = 0 < ε.
3. The pulled-back forms. Put g_j := Λ ∘ ωs_j ∘ L, i.e. g_j(y) = (ωs_j(Ly)).compContinuousLinearMap L. By hypothesis ηs_j = (y ↦ ζ(y)·g_j(y)) as functions on ℝ^Q (funext). Each ωs_j is C^∞ as a test form, so g_j is C^∞, being a composition with the continuous linear maps L and Λ.
4. Derivatives of g_j. By the chain rule for compositions with continuous linear maps on the left and on the right (ContinuousLinearMap.iteratedFDeriv_comp_left, ContinuousLinearMap.iteratedFDeriv_comp_right): D^l g_j(y) = Λ ∘ (D^l ωs_j(Ly))(L·, …, L·). This is affinePullbackJet L d l applied to D^l ωs_j(0 + Ly). Hence ‖D^l g_j(y)‖ ≤ ‖Λ‖·‖L‖^l·‖D^l ωs_j(Ly)‖ for all l, j, y (ContinuousLinearMap.norm_compContinuousMultilinearMap_le and ContinuousMultilinearMap.norm_compContinuousLinearMap_le, with Π_{k<l} ‖L‖ = ‖L‖^l).
5. Bounds for ζ. For each i, D^i ζ is continuous (ζ is C^∞) and has compact support (HasCompactSupport.iteratedFDeriv). So it is bounded: there is Z_i with ‖D^i ζ(y)‖ ≤ Z_i for all y (Continuous.bounded_above_of_compact_support).
6. The common compact set. Let K′ := tsupport ζ. It is compact because ζ has compact support, and K′ ⊆ univ. For every j, tsupport ηs_j = tsupport(y ↦ ζ(y)·g_j(y)) ⊆ tsupport ζ = K′ (tsupport_smul_subset_left). Also tsupport of the zero form is ∅ ⊆ K′.
7. Uniform convergence of every derivative. Fix k and ε > 0.
   - Put S := Σ_{i=0}^{k} C(k,i)·|Z_i|·‖Λ‖·‖L‖^{k−i} ≥ 0 and δ := ε/(S + 1) > 0.
   - Apply step 2 to the finitely many orders k − i with i ≤ k (Finset.eventually_all). Eventually in j, ‖D^{k−i} ωs_j(x)‖ < δ for all i ≤ k and all x.
   - For such j and every y ∈ ℝ^Q, apply leibniz_smul with f = ζ, g = g_j and F = Covector(ℝ^Q, d), then steps 5 and 4:
     ‖D^k ηs_j(y)‖ ≤ Σ_{i=0}^{k} C(k,i)‖D^i ζ(y)‖‖D^{k−i} g_j(y)‖ ≤ Σ_{i=0}^{k} C(k,i)|Z_i|·(‖Λ‖‖L‖^{k−i}·δ) = S·δ = S·ε/(S + 1) < ε.
   - D^k of the zero form vanishes, so dist(D^k 0(y), D^k ηs_j(y)) = ‖D^k ηs_j(y)‖ < ε for all y ∈ K′, eventually in j. Thus D^k ηs_j → D^k 0 uniformly on K′.
8. Conclusion. Steps 6 and 7 are exactly TestFormOnConverges ηs 0, with the compact set K′ ⊆ univ. ∎
Formalization note (checked in Lean as one theorem): bound D^l g_j through Λ and L as in step 4, not through ‖affinePullbackJet L d l‖. That operator norm does not elaborate under the frozen contract options: SimonGMT builds affinePullbackJet with backward.isDefEq.respectTransparency false, and a leaf may not set options. Rewrite ηs_j via the hypothesis before applying leibniz_smul; the zero form's derivative is handled by ZeroMemClass.coe_zero and iteratedFDeriv_zero_fun.

## Key steps

1. From TestFormOnConverges ωs 0, every derivative of ωs_j tends to 0 uniformly on all of ℝ^P (it vanishes off the common compact set C).
2. D^l g_j(y) = Λ ∘ D^l ωs_j(Ly) ∘ (L, …, L), so ‖D^l g_j(y)‖ ≤ ‖Λ‖‖L‖^l‖D^l ωs_j(Ly)‖.
3. All derivatives of ζ are bounded (continuous with compact support).
4. leibniz_smul gives ‖D^k ηs_j(y)‖ ≤ Sδ < ε eventually, uniformly in y.
5. All tsupports lie in the compact tsupport ζ; conclude TestFormOnConverges ηs 0.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp <snapshot>/project/GMT/Ch07/Contract.lean <workspace>/GMT/Ch07/Submission.lean (identical); git show cc4b64395af400c3e25de523ef6f16a61dd6621d:GMT/Ch07/Submission.lean (node base: contract imports only)`
- `rg -n "theorem norm_iteratedFDeriv_smul_le" <snapshot>/mathlib/Mathlib --glob '*.lean' (only Analysis/Calculus/ContDiff/Bounds.lean:250); sed -n 1,140p <snapshot>/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean (norm_iteratedFDerivWithin_le_of_bilinear_aux)`
- `python3 -I import-closure scan of the Contract.lean imports through .lake/packages/simongmt (SimonGMT Chapter01-06 modules; Mathlib roots include Analysis.Calculus.ContDiff.Operations, DifferentialForm.Basic, IteratedDeriv.Defs; no ContDiff.Bounds)`
- `lake env lean Avail.lean/Avail2.lean after import GMT.Ch07.Submission: #check @norm_iteratedFDeriv_smul_le, @ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear, @iteratedFDeriv_smul_apply (Unknown); @ContinuousLinearMap.precompR, precompL, norm_precompR_le, norm_precompL_le, fderiv_of_bilinear, le_opNorm₂, opNorm_lsmul_le, iteratedFDeriv_comp_left, @norm_iteratedFDeriv_fderiv, @fun_iteratedFDeriv_add_apply, @Finset.sum_choose_succ_mul, @IsBoundedBilinearMap.contDiff, @Continuous.bounded_above_of_compact_support, @HasCompactSupport.iteratedFDeriv, @tsupport_iteratedFDeriv_subset, @Filter.EventuallyEq.extDeriv_eq, @Fintype.sum_of_injective, @ContDiffBump.contDiff (available)`
- `grep -n declarations in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{AffineCurrentPushforward,Currents,Forms,Mass}.lean (affinePullbackForm, affinePullbackForm_isSmoothForm, tsupport_affinePullbackForm_subset, affinePullbackJet, affinePullbackJet_uniformContinuous, iteratedFDeriv_affinePullbackForm, exteriorDerivative_affinePullbackForm, TestFormOn, TestFormOnConverges, covectorEuclideanNorm, covectorEuclideanNorm_nonneg)`
- `grep -rn "theorem TestFormOnConverges\." .lake/packages/simongmt/Poincare/SimonGMT (only affinePullback, exteriorDerivative, tendsto_eval, pointSlice, tendsto_testFunction; no multiplication-by-function lemma)`
- `rg -n "one_of_mem_closedBall|tsupport_eq|nonneg|le_one|hasCompactSupport|contDiff" BumpFunction/Basic.lean; "tsupport_smul_subset_left|tsupport_smul_subset_right|HasCompactSupport.smul_right" Topology/Algebra/Support.lean; "Filter.EventuallyEq.extDeriv_eq" Calculus/DifferentialForm/Basic.lean; "tsupport_iteratedFDeriv_subset" ContDiff/FTaylorSeries.lean; "prod_of_injective" Algebra/BigOperators/Group/Finset/Basic.lean; "IsBounded.subset_ball_lt" Topology/MetricSpace/Bounded.lean; "bounded_above_of_compact_support" Analysis/Normed/Group/Bounded.lean (all in the snapshot mathlib)`
- `python3 -I scans of the run's dag.json: lean_statements with covectorEuclideanNorm and smul (accepted rsd_mw_tfa_norm_props, regcomp_covectorEuclideanNorm_seminorm_retract), with TestFormOnConverges/iteratedFDeriv (only accepted dpf_pfc_testFormOnConverges_zero_uniform, order 0), the ContDiff ℝ (⊤ : ℕ∞) convention, and name collisions of dor_lmb_fc_dtop_cp_proj_covector_norm / _leibniz_smul_bound / _cutoff_pullback_converges (0 occurrences)`
- `git show f492ba4a003c8f1324077e050d48667ae23c7100 (accepted proof of Submission.rsd_mw_tfa_norm_props); git show 14cdd14d8 (leaf that added an import rejected); grep -n 'def check_source_delta' -A 40 /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/leaf_verification.py`
- `Lean probes without set_option: ‖affinePullbackJet L d l‖ (failed to synthesize Norm), Metric.uniformContinuous_iff on affinePullbackJet_uniformContinuous (instance mismatch), ‖B.precompR (Euclid Q)‖ (fails; works with local let-instances)`
- `lean_contract.validate_lean_statement and gmt-compare.child_modules (contract mode) on the four lean_statements; lake env lean /tmp/cp-decomp/final/Challenge_*.lean (4 files, only the sorry warning); lake env lean /tmp/cp-decomp/lean/{ChildA,ChildC1,ChildC2,Assembly}.lean and /tmp/cp-decomp/final/Chain.lean (#print axioms [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-3abc140ad4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-b4c8dbc0a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cp-decomp/final/Chain.lean`
- `/tmp/cp-decomp/lean/Assembly.lean`

Snapshot: project b4d606db and Mathlib 25730c7c. Its Ch07 Contract.lean is byte-identical to the workspace Submission.lean, and this node's base commit cc4b6439 has the contract imports only.

Findings:
- The Leibniz bound norm_iteratedFDeriv_smul_le exists only in Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:250, which is not reachable from the frozen imports. All ingredients of its proof (Bounds.lean:38–111, norm_iteratedFDerivWithin_le_of_bilinear_aux) are reachable: precompR/precompL with their norm bounds, fderiv_of_bilinear, norm_iteratedFDeriv_fderiv, fun_iteratedFDeriv_add_apply and Finset.sum_choose_succ_mul. leibniz_smul's proof follows that argument.
- SimonGMT supplies the pull-back API in AffineCurrentPushforward.lean, plus TestFormOnConverges (Currents.lean) and covectorEuclideanNorm (Mass.lean). It has no continuity lemma for multiplication by a function, and ‖affinePullbackJet‖ does not elaborate without its transparency options.
- In the DAG, the accepted rsd_mw_tfa_norm_props supplies homogeneity and is reused with an identical type. dpf_pfc_testFormOnConverges_zero_uniform only treats order 0, and no accepted node gives the projection norm identity or cut-off continuity.
- Mathlib basics used: ContDiffBump, tsupport_smul_subset_left/right, HasCompactSupport.smul_right, Filter.EventuallyEq.extDeriv_eq, tsupport_iteratedFDeriv_subset, Fintype.sum_of_injective, Continuous.bounded_above_of_compact_support and IsBounded.subset_ball_lt.

The four child types compile as comparator challenges. The full chain compiles to the selected type with standard axioms.
