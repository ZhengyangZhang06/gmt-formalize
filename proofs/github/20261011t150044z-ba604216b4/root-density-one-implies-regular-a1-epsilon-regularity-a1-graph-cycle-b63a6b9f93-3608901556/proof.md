# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1.graph_tangent_finrank-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent-supplied proof of dgcr_approxTangent_eq_graph_tangent. There, DΦ(v₀) = ι + ι'∘Du(v₀) satisfies ι*DΦ(v₀) = id, hence is injective, so L = range DΦ(v₀) is n-dimensional. Here injectivity is shown directly by Pythagoras instead of through the adjoint ι*; this is the same orthogonality computation.

Notation: ℝ^m = Euclid m; Φ(v) := z + ιv + ι'(u(v)); Du := fderiv ℝ u v₀.

Formalization note: unless split further, this is a machine leaf: one theorem appended to GMT/Ch07/Submission.lean, with no new import or helper. Every lemma cited is in the import closure of GMT.Ch07.Submission.

1. Derivative.
- The map v ↦ z + ιv has derivative ι at v₀: the continuous linear map ι is its own derivative, and adding a constant does not change it (HasFDerivAt.const_add).
- The map v ↦ ι'(u(v)) has derivative ι' ∘ Du at v₀ by the chain rule, since u is differentiable at v₀ and ι' is a continuous linear map.
By the sum rule (HasFDerivAt.add), HasFDerivAt Φ F v₀ with F := ι + ι' ∘ Du. Hence fderiv ℝ Φ v₀ = F (HasFDerivAt.fderiv), i.e. F h = ιh + ι'(Du h).

2. Injectivity. Suppose F h = 0, i.e. ιh + ι'(Du h) = 0. The two summands are orthogonal by hypothesis. By Pythagoras (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero) and norm preservation of ι and ι', 0 = ‖ιh + ι'(Du h)‖² = ‖h‖² + ‖Du h‖². Hence ‖h‖² = 0 and h = 0. So ker F = ⊥ (LinearMap.ker_eq_bot'), and F, as a linear map, is injective.

3. Dimension. For an injective linear map, the range has the dimension of the domain (LinearMap.finrank_range_of_inj). So finrank (range F) = finrank ℝ (Euclid n) = n (finrank_euclideanSpace_fin). ∎

## Key steps

1. Sum and chain rules give DΦ(v₀) = ι + ι'∘Du(v₀).
2. Pythagoras with orthogonality gives ‖DΦ(v₀)h‖² = ‖h‖² + ‖Du(v₀)h‖², so DΦ(v₀)h = 0 forces h = 0; hence DΦ(v₀) is injective.
3. Rank–nullity for injective maps: finrank range DΦ(v₀) = finrank ℝⁿ = n.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; python3 read lake-manifest.json package revs; git rev-parse HEAD in .lake/packages/mathlib`
- `grep -n "def HasApproximateTangentSpaceAt\|def blowUpMap\|theorem HasApproximateTangentSpaceAt\|lemma HasApproximateTangentSpaceAt\|support_euclideanHausdorffMeasure_restrict_submodule\|regular_euclideanHausdorffMeasure_restrict_submodule\|^import" Chapter03/Rectifiable.lean (simongmt)`
- `grep -n -A12 "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" Chapter02/Lipschitz.lean; grep -n "^namespace\|^end" Chapter02/Lipschitz.lean`
- `rg -n "theorem .*[Aa]pproximateTangent|theorem .*approxTangent" --glob '*.lean' simongmt/Poincare/SimonGMT`
- `rg -n "theorem measure_eq_zero_iff_ae_notMem|theorem IsClosed.notMem_iff_infDist_pos|theorem infDist_le_infDist_add_dist|theorem infDist_le_dist_of_mem|theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero|theorem eq_of_le_of_finrank_eq|theorem integral_pos_iff_support_of_nonneg\b|theorem Continuous.integrable_of_hasCompactSupport|lemma mem_support_iff_forall|theorem finrank_euclideanSpace_fin|theorem ContDiffOn.differentiableOn\b|theorem integral_eq_zero_of_ae|theorem eventually_nhds_iff\b" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n "notMem_iff_infDist_pos|finrank_range_of_inj|closed_of_finiteDimensional|HasFDerivAt.isLittleO|HasFDerivAt.const_add|theorem intro \[|Ioo_mem_nhdsGT" local-references/123e8435b4a2469b/mathlib/Mathlib (snapshot)`
- `python3 scan of every lean_name in dag.json and nodes/*/*.json (566 names); grep -rl dgcr_atg over the run's nodes/ and dag.json; git grep -l dgcr_atg <all 979 refs> -- GMT/Ch07/Submission.lean (exit 1: no match)`
- `read nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/decomposition-v{1,2}.json and decomposition-audit-v{1,2}.json (atsm_approxTangent_le_of_flat); nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json (sibling types); git show <accepted child ref>:GMT/Ch07/Submission.lean (child placement)`
- `python3 -I /tmp/atg-work/gen_cmp.py (lean_contract.validate_lean_statement + gmt-compare.child_modules contract mode); lake env lean /tmp/atg-work/{Parent,Types,B2,All,CmpCheck,Inlined}.lean with #check and #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-b5ecd87c13/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-b5ecd87c13/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/decomposition-audit-v2.json`
- `/tmp/atg-work/gen_cmp.py`
- `/tmp/atg-work/children.json`
- `/tmp/atg-work/Types.lean`
- `/tmp/atg-work/All.lean`
- `/tmp/atg-work/CmpCheck.lean`
- `/tmp/atg-work/Inlined.lean`

Snapshot, project and package revisions agree:
- The snapshot manifest records project b4d606d and Mathlib 25730c7c, equal to the workspace HEAD and the lake-manifest Mathlib pin.
- simongmt is pinned at 2b36630.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean, and Submission.lean is byte-identical to the contract.

Reusable facts, all in the import closure of GMT.Ch07.Submission (checked by compiling files that import only that module):
- From simongmt Chapter03/Rectifiable.lean: HasApproximateTangentSpaceAt (finrank Q = n plus convergence of ∫_{blowUpMap x r '' M} f dμHE[n] along 𝓝[>] 0 for f ∈ C_c), HasApproximateTangentSpaceAt.finrank_eq, blowUpMap x r y = r⁻¹ • (y − x), regular_ and support_euclideanHausdorffMeasure_restrict_submodule.
- From Chapter02/Lipschitz.lean: Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- From snapshot Mathlib: measure_eq_zero_iff_ae_notMem, IsClosed.notMem_iff_infDist_pos, infDist_le_infDist_add_dist, infDist_le_dist_of_mem, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, Submodule.eq_of_le_of_finrank_eq, LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin, integral_pos_iff_support_of_nonneg, Continuous.integrable_of_hasCompactSupport, Measure.mem_support_iff_forall, integral_eq_zero_of_ae, HasFDerivAt.isLittleO and HasFDerivAt.const_add (aliases), Submodule.closed_of_finiteDimensional, HasCompactSupport.intro (to_additive), Ioo_mem_nhdsGT (confirmed by #check).
- ContDiffOn.differentiableOn takes n ≠ 0 in this Mathlib.

Existing lemmas and names:
- No existing simongmt lemma bounds an approximate tangent plane by a flat direction; the Chapter04 approximate-tangent results concern density.
- The analogous atsm_approxTangent_le_of_flat (global null hypothesis) is only reserved in another branch's decomposition and is not comparator-accepted, so a uniquely named local variant is used.
- No dgcr_atg_ name collides anywhere: DAG, node JSONs, and all 979 git refs.

Lean checks:
- All three child types and the parent type pass validate_lean_statement and elaborate in the exact comparator contract scope generated by gmt-compare.child_modules.
- The exact frozen parent type follows from the three exact child types without sorry.
- Complete single-theorem proofs of all three children compile, also when inserted into a byte copy of Submission.lean.
- Only propext, Classical.choice and Quot.sound are used.
