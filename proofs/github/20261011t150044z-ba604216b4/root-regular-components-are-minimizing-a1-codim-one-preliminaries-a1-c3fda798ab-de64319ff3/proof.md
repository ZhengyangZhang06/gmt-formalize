# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.dim_le_of_embedded-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1 (k ≥ 1), stated for an arbitrary nonempty embedded submanifold. The parent applies it with P := n + k, d := n + 1, r := 2, M := N (N ≠ ∅ because N ∩ U ≠ ∅ by InClassO) and concludes 1 ≤ k from n + 1 ≤ n + k.
1. Since M is nonempty, pick y ∈ M.
2. By IsEmbeddedSubmanifold r d M at y there are sets V ⊆ ℝ^d and W ⊆ ℝ^P and a map ψ : ℝ^d → ℝ^P such that y ∈ W, ψ(V) = W ∩ M, and Dψ(z) = fderiv ℝ ψ z : ℝ^d → ℝ^P is injective for every z ∈ V. (The remaining chart properties — openness, C^r regularity, injectivity of ψ on V, properness — are not needed.)
3. Since y ∈ W and y ∈ M, we have y ∈ W ∩ M = ψ(V), so there is z ∈ V (with ψ(z) = y).
4. Dψ(z) is an injective ℝ-linear map from ℝ^d to the finite-dimensional space ℝ^P. The dimension of the domain of an injective linear map is at most the dimension of its codomain (Mathlib LinearMap.finrank_le_finrank_of_injective), so finrank ℝ^d ≤ finrank ℝ^P.
5. Since finrank ℝ (EuclideanSpace ℝ (Fin q)) = q for every q (finrank_euclideanSpace_fin), step 4 reads d ≤ P.

## Key steps

1. Pick y ∈ M and a chart (V, W, ψ) of M at y.
2. y ∈ W ∩ M = ψ(V) yields a point z ∈ V.
3. Dψ(z) : ℝ^d → ℝ^P is an injective linear map, so d = finrank ℝ^d ≤ finrank ℝ^P = P.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n 'theorem setIntegral_eq_zero_of_forall_eq_zero|theorem hausdorffMeasure_zero_singleton|def constOfIsEmpty|hasContDiffBump_of_innerProductSpace|theorem closure_ball|image_eq_zero_of_notMem_tsupport' mathlib/Mathlib`
- `rg -n 'finrank_le_finrank_of_injective' mathlib/Mathlib`
- `rg -n 'regcomp_cop_|IsBoundaryOfRegion|InClassO' project/GMT/Ch07`
- `rg -n 'IsEmbeddedSubmanifold.*finrank|finrank_le_of_.*embedded' project mathlib/Mathlib (no match)`
- `grep -n 'tsupport_exteriorDerivative_subset|exteriorDerivative_sq|GeometricCurrentOn.boundary_apply|GeometricCurrentOn.ext' simongmt Chapter06/Currents.lean, Chapter06/Forms.lean`
- `grep -n 'VanishesOn|zeroRegion|support_subset_domain' simongmt Chapter06/CurrentLocalEquality.lean; grep -n 'covectorEuclideanNorm|massAdmissibleOn|massOn|le_massOn' Chapter06/Mass.lean`
- `grep -n 'blowUpMap|HasApproximateTangentSpaceAt|CountablyRectifiable.mono' simongmt Chapter03/Rectifiable.lean`
- `grep -n 'euclideanHausdorffMeasure_zero|setIntegral_eq_zero_of_ae_eq_zero' mathlib Geometry/Euclidean/Volume/Measure.lean, MeasureTheory/Integral/Bochner/Set.lean`
- `python3 scan of dag.json lean_name fields (no regcomp_cop_ collision; related dimension-0 nodes and their statuses); git grep regcomp_cop_ over all 1897 refs (no match)`
- `git show <theorems/solutions branch>:GMT/Ch07/Submission.lean for accepted dor_zdm_imrep_zero_structure, dtc_point_current, dtc_dim_zero_carrier_finite, dtc_approxTangent_sdiff_singleton, dtc_dim_zero_erase_point, rsd_cmr_support_subset_of_vanish, dor_ims_massOn_le_measure; verification.json machine_comparator_passed`
- `lake env lean /tmp/cop-decomp/gen/Assembly.lean (four child stubs + parent assembly, #print axioms)`
- `lake env lean /tmp/cop-decomp/Small.lean and in-situ leaf candidates; simulated _recursive_lean.leaf_verification.check_source_delta`
- `source env.sh && lean GMT/Scratch/regcomp_cop_decomposition/Full.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `sed -n 740,790p book/chapter-07.txt (Simon 7.5: 5.1 T = ∂[[E]], class 𝒪)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-codim-one-preliminaries-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/regcomp_cop_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/regcomp_cop_decomposition/Small.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/regcomp_cop_decomposition/Full.lean`

Snapshot and toolchain:
- The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean.
- SimonGMT supplies tsupport_exteriorDerivative_subset, exteriorDerivative_sq, GeometricCurrentOn.boundary_apply and ext, the definitions of zeroRegion, support and massOn, and covectorEuclideanNorm, blowUpMap and CountablyRectifiable.mono. These close C2 and C3 and the degree-0 steps of C4.
- Mathlib supplies:
  - setIntegral_eq_zero_of_forall_eq_zero, which needs no measurability of the integration set;
  - euclideanHausdorffMeasure_zero (μHE[0] = μH[0]) and hausdorffMeasure_zero_singleton;
  - LinearMap.finrank_le_finrank_of_injective and closure_ball;
  - ContinuousAlternatingMap.constOfIsEmpty and ContDiffBump.
- No library theorem states the dimension bound for IsEmbeddedSubmanifold (no match), so C1 is proved directly.

Accepted helpers in other branches:
- Comparator-accepted declarations exist in solution branches of other DAG branches: dor_zdm_imrep_zero_structure, dtc_point_current, dtc_dim_zero_carrier_finite, dtc_approxTangent_sdiff_singleton, dtc_dim_zero_erase_point, rsd_cmr_support_subset_of_vanish, dor_ims_massOn_le_measure and regcomp_rim_action_integrable.
- They are not present in the workspace Submission.lean. Copied verbatim, they compile against the frozen contract and cover several of C4's steps.

Verification:
- The four child types elaborate after `import GMT.Ch07.Submission`. The parent assembles from them; only the stubs contribute sorryAx.
- C1–C3 have proofs that pass the simulated leaf source-delta check and compile in place inside Submission.lean.
- A full end-to-end development of the node compiles with only propext, Classical.choice and Quot.sound. It is kept in the gitignored GMT/Scratch/regcomp_cop_decomposition/.
- No regcomp_cop_ name collides with anything in dag.json or any git ref.
