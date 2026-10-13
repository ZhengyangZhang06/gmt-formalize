# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.graph_gram_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 0 (the area Jacobian of the graph map Φ(v) = a + ιv + ι'(f v) is J(v) = (det(I + Df(v)ᵀDf(v)))^{1/2}); Simon Ch. 2, 3.1 and 3.3 (chapter-02.txt lines 743–777: Jf = (det(df* ∘ df))^{1/2}) and Example 3.6(3) (lines 834–841: for graphs the Jacobian is (det(δ_ij + D_i u·D_j u))^{1/2}), here for the graph map with derivative A := ι + ι'∘T. Notation: ⟨·,·⟩ are the Euclidean inner products, A := ι + ι'∘T : ℝⁿ → ℝ^{n+k}.
1. (Reduction to inner products.) Two linear maps S₁, S₂ : ℝⁿ → ℝⁿ are equal iff ⟨S₁x, y⟩ = ⟨S₂x, y⟩ for all x, y ∈ ℝⁿ (nondegeneracy of the inner product; Mathlib `LinearMap.ext` and `ext_inner_right`). Fix x, y ∈ ℝⁿ.
2. (Left side.) By the defining property of the adjoint (`LinearMap.adjoint_inner_left`: ⟨A*u, y⟩ = ⟨u, Ay⟩), ⟨(A*∘A)x, y⟩ = ⟨Ax, Ay⟩ = ⟨ιx + ι'(Tx), ιy + ι'(Ty)⟩.
3. (Expansion.) By bilinearity this equals ⟨ιx, ιy⟩ + ⟨ιx, ι'(Ty)⟩ + ⟨ι'(Tx), ιy⟩ + ⟨ι'(Tx), ι'(Ty)⟩. Linear isometries preserve inner products (`LinearIsometry.inner_map_map`), so ⟨ιx, ιy⟩ = ⟨x, y⟩ and ⟨ι'(Tx), ι'(Ty)⟩ = ⟨Tx, Ty⟩. By the orthogonality hypothesis ⟨ιx, ι'(Ty)⟩ = 0, and by symmetry of the real inner product ⟨ι'(Tx), ιy⟩ = ⟨ιy, ι'(Tx)⟩ = 0. Hence ⟨(A*∘A)x, y⟩ = ⟨x, y⟩ + ⟨Tx, Ty⟩.
4. (Right side.) ⟨(id + T*∘T)x, y⟩ = ⟨x, y⟩ + ⟨T*(Tx), y⟩ = ⟨x, y⟩ + ⟨Tx, Ty⟩, again by the adjoint property.
5. (Conclusion.) The two sides agree for all x, y, so A*∘A = id + T*∘T by Step 1. (Remark, not part of the statement: hence the area Jacobian (det(A*∘A))^{1/2} of A, Simon 3.3, equals (det(id + T*∘T))^{1/2}; the parent uses this with Mathlib's normDet.) ∎

## Key steps

1. Reduce equality of the two endomorphisms of ℝⁿ to equality of ⟨·x, y⟩ for all x, y.
2. By the adjoint property ⟨(A*A)x, y⟩ = ⟨ιx + ι'Tx, ιy + ι'Ty⟩.
3. Expand: isometries preserve inner products and the cross terms vanish by orthogonality, giving ⟨x, y⟩ + ⟨Tx, Ty⟩ = ⟨(id + T*T)x, y⟩.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n 'approxTangentPlane|HasApproximateTangentSpaceAt|area_formula|graph' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem LipschitzWith.ae_differentiableAt' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; rg -n 'theorem ae_tendsto_average_norm_sub' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/*.lean; rg -n 'theorem countable_cover_nhdsWithin' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib; rg -n 'theorem setIntegral_comp_smul_of_pos' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'theorem weighted_area_formula_lipschitz_injOn|def areaJacobianAt' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/*.lean; rg -n 'def HasApproximateTangentSpaceAt|theorem HasApproximateTangentSpaceAt.unique|def blowUpMap' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; rg -n 'theorem simon_theorem_3_6' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/*.lean  (simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197 from the snapshot lake-manifest.json)`
- `lake env lean /tmp/gtan3/api/Api.lean (import GMT.Ch07.Submission, contract scope): weighted_area_formula_lipschitz_injOn, areaJacobianAt, LinearMap.normDet, simon_theorem_3_6 unknown; LipschitzWith.ae_differentiableAt, IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, euclideanHausdorffMeasure_image_le_of_lipschitzOn, HasApproximateTangentSpaceAt.unique, blowUpMap, TopologicalSpace.countable_cover_nhdsWithin, euclideanHausdorffMeasure_homothety_image available`
- `python3 -I scans of dag.json: status/lean_statement/candidate_commit of regcomp_atl_upper_density_zero, regcomp_atl_local_density_zero, regcomp_atl_blowUp_measure_scaling; lean_name collision scan of the 8 doraggt_* names over dag.json and nodes/*/*.json; accepted candidates whose Submission.lean adds imports (dtc_isIntegerMultiplicity_sub); git grep doraggt_ over refs (no match)`
- `sed runtime gmt-claude-52228cbc47b2/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _decompose, _solve_children, _install_parent_supplied_child_handoff), store.py (refresh), leaf_verification.py (check_source_delta), parent_verification.py (check_parent_git_delta); verifier/gmt-compare.py (child_modules, contract_scope)`
- `python3 -I /tmp/gtan3-scripts/gen_challenges.py + lake env lean /tmp/gtan3/ch/AllStmts.lean; lake env lean /tmp/gtan3/Full3.lean and /tmp/gtan3/Kids3.lean with #print axioms; python3 -I /tmp/gtan3-scripts/check_full.py; python3 -I /tmp/gtan3-scripts/leafsim3.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-8c018a8a8b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-8c018a8a8b/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-approx-tangent-locality-a1-a0cdf4fb59/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-approx-tangent-locality-a1-65b9043b0e/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gtan3/ch/AllStmts.lean`
- `/tmp/gtan3/Full3.lean`
- `/tmp/gtan3/Kids3.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace contract and Submission, the compiler context of every child type. Nothing in the snapshot or in SimonGMT proves this node. The Lipschitz area formula lives in SimonGMT Chapter02: AreaLipschitz.lean has weighted_area_formula_lipschitz_injOn, and AreaDomain, AreaLiteral and AreaCompletion have variants. All of them are outside the contract import closure: areaJacobianAt, LinearMap.normDet and the area formula are unknown after `import GMT.Ch07.Submission`, and so is simon_theorem_3_6. Machine leaves cannot add imports, so the area-formula step stays in this parent, which may add `import Poincare.SimonGMT.Chapter02.AreaLipschitz` (precedent: the accepted parent dtc_isIntegerMultiplicity_sub added a SimonGMT import). All other ingredients are in scope for leaves: Rademacher, the Haar change of variables, Lebesgue differentiation, the Hausdorff Lipschitz-image bound, homothety scaling, the Lindelöf cover and HasApproximateTangentSpaceAt.unique. Two accepted declarations are reused at byte-identical types: regcomp_atl_upper_density_zero and regcomp_atl_blowUp_measure_scaling, both accepted with candidate commits. regcomp_atl_local_density_zero is not reused, as the correction requires; its statement is re-proved under the fresh name doraggt_local_density_zero. Every child type elaborates in comparator scope, and every child compiles without the extra import. The integrated build proves the exact frozen parent type with axioms propext, Classical.choice and Quot.sound only.
