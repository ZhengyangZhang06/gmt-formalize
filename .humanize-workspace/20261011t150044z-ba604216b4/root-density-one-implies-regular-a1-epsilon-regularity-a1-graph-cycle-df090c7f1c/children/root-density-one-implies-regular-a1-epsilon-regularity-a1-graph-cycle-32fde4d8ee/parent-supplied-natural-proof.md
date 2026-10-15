# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_embedded-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_embedded-a1.graph_left_inverse-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 2 of the parent-supplied proof (adjoint identities ι*ι = id and ι*ι' = 0, and the C¹ property of Φ), reduced to exactly the two facts that the sibling children and the parent assembly consume. Simon prints no proof of these facts (Ch. 2 §4, book/chapter-02.txt lines 849–871 only define submanifolds and tangent spaces).
Notation: ℝ^m := Euclid m = EuclideanSpace ℝ (Fin m) with its Euclidean inner product ⟨·,·⟩; D := B_s(0) ⊆ ℝⁿ (open ball; s ∈ ℝ arbitrary); Φ(v) := z + ιv + ι'u(v).
1. Smoothness of the linear pieces. ι and ι' are linear isometries between finite-dimensional spaces, hence continuous linear maps (LinearIsometry.toContinuousLinearMap), and every continuous linear map is C^∞ (ContinuousLinearMap.contDiff).
2. Φ is C¹ on D. The constant map v ↦ z is C¹ on D (contDiffOn_const) and v ↦ ιv is C¹ on D (step 1 and ContDiff.contDiffOn), so v ↦ z + ιv is C¹ on D (ContDiffOn.add). The map v ↦ ι'(u(v)) is the composition of the C^∞ map ι' with u, which is C¹ on D by hypothesis, so it is C¹ on D (ContDiff.comp_contDiffOn). Adding (ContDiffOn.add), Φ = (z + ι·) + ι'∘u is C¹ on D.
3. Choice of L. ℝ^{n+k} and ℝⁿ are finite-dimensional, hence complete, real inner-product spaces, so the continuous linear map ι has an adjoint L := ι* : ℝ^{n+k} → ℝⁿ (ContinuousLinearMap.adjoint applied to ι.toContinuousLinearMap). L is a continuous linear map and ⟨Lx, e⟩ = ⟨x, ιe⟩ for all x ∈ ℝ^{n+k} and e ∈ ℝⁿ (ContinuousLinearMap.adjoint_inner_left).
4. Fix v ∈ ℝⁿ. By associativity and cancellation (add_assoc, add_sub_cancel_left), Φ(v) − z = (z + (ιv + ι'u(v))) − z = ιv + ι'u(v).
5. Let e ∈ ℝⁿ. The isometry ι preserves inner products, so ⟨ιv, ιe⟩ = ⟨v, e⟩ (LinearIsometry.inner_map_map). The orthogonality hypothesis applied to e and u(v), together with symmetry of the real inner product (real_inner_comm), gives ⟨ι'u(v), ιe⟩ = ⟨ιe, ι'u(v)⟩ = 0. By steps 3 and 4 and additivity in the first slot (inner_add_left):
⟨L(Φ(v) − z), e⟩ = ⟨ιv + ι'u(v), ιe⟩ = ⟨ιv, ιe⟩ + ⟨ι'u(v), ιe⟩ = ⟨v, e⟩ + 0 = ⟨v, e⟩.
6. Since ⟨L(Φ(v) − z), e⟩ = ⟨v, e⟩ for every e ∈ ℝⁿ, L(Φ(v) − z) = v (ext_inner_right). As v ∈ ℝⁿ was arbitrary, L(Φ(v) − z) = v for every v ∈ ℝⁿ.
7. Step 2 is the first conjunct; step 6, with the continuous linear map L of step 3 as witness, is the second conjunct. ∎

## Key steps

1. Constants and continuous linear maps are smooth, ι'∘u is C¹ on D by composition, and sums preserve C¹; hence Φ = (z + ι·) + ι'∘u is C¹ on D.
2. Take L := ι* (ContinuousLinearMap.adjoint), so ⟨Lx, e⟩ = ⟨x, ιe⟩.
3. Φ(v) − z = ιv + ι'u(v), and ⟨L(Φ(v) − z), e⟩ = ⟨ιv, ιe⟩ + ⟨ι'u(v), ιe⟩ = ⟨v, e⟩ by the isometry property and orthogonality.
4. ext_inner_right gives L(Φ(v) − z) = v for every v.

## Reference use

### local-project

Queries:
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD (compared with manifest.json)`
- `rg -n 'def tangentSpace|def IsEmbeddedSubmanifold' project/GMT --glob '*.lean' (in the snapshot)`
- `rg -n 'dgce_|left_inverse_chart|left_inverse_tangentSpace|graph_contDiffOn_left_inverse' project --glob '*.lean' (in the snapshot; no match)`
- `rg -n 'theorem adjoint_inner_left|theorem LinearIsometry.inner_map_map|theorem ext_inner_right|theorem ContDiffOn.differentiableOn_one|theorem HasFDerivAt.comp_hasDerivAt |theorem HasFDerivAt.congr_of_eventuallyEq|theorem HasDerivAt.congr_of_eventuallyEq|theorem HasDerivAt.unique|theorem HasFDerivAt.unique|theorem IsCompact.exists_isMaxOn|theorem ContinuousOn.preimage_isClosed_of_isClosed|theorem IsCompact.of_isClosed_subset|theorem closedBall_subset_ball|theorem hasDerivAt_sin|theorem contDiff_sin|theorem abs_sin_le_one|theorem Ioo_mem_nhds|theorem ContDiffOn.comp |theorem ContinuousLinearMap.contDiff|theorem ContDiff.comp_contDiffOn|theorem LinearMap.mem_range' mathlib/Mathlib (in the snapshot)`
- `python3 scan of every lean_name value in dag.json and nodes/*/*.json (682 names); grep -rl dgce_ dag.json nodes; git grep -l dgce_ over all 977 refs (*.lean)`
- `inspect DAG nodes whose lean_statement mentions tangentSpace or IsEmbeddedSubmanifold, and the decomposition/audit files of nodes root-minimizing-implies-stationary-a1-chart-tangent-space-a1 and root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1`
- `python3 -I /tmp/dgce-decomp/scripts/gen_checks.py (lean_contract.validate_lean_statement and gmt-compare.contract_scope replay)`
- `lake env lean /tmp/dgce-decomp/Parent.lean; lake env lean /tmp/dgce-decomp/Full.lean; lake env lean /tmp/dgce-decomp/Scope.lean; lake env lean /tmp/dgce-decomp/Instances.lean`
- `grep -n 'Submanifolds of R|readily checks|is proper (i.e.|Local graphical representations' book/chapter-02.txt; grep -n '4.3 Theorem' book/chapter-07.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-df090c7f1c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-df090c7f1c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-df090c7f1c/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dgce-decomp/Parent.lean`
- `/tmp/dgce-decomp/Full.lean`
- `/tmp/dgce-decomp/Scope.lean`
- `/tmp/dgce-decomp/Instances.lean`
- `/tmp/dgce-decomp/scripts/gen_checks.py`

Pins and contract:
- The snapshot is project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b with Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Both match the workspace HEAD and .lake/packages/mathlib.
- The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. IsEmbeddedSubmanifold (line 221) and tangentSpace (line 228) are the frozen definitions used.

No reusable project declaration:
- No project file states the chart or tangent facts for graphs, or for maps with an affine left inverse: there is no match for dgce_ or left-inverse chart names.
- The Ch02 tangentSpace hit is a different, Submodule-valued definition in another chapter's contract, so it does not apply.
- The DAG's other chart-tangent nodes are chart_tangentSpace_eq_range_fderiv, dsmc_chart_tangentSpace_eq_range and dsmc_chart_range_subset_tangentSpace. They sit in other branches, none is accepted, and they assume properness rather than a left inverse. They are therefore neither reused nor duplicated.

Mathlib:
- Every cited lemma exists at the pinned revision with the expected signature, e.g. ContDiffOn.differentiableOn_one, ContinuousLinearMap.adjoint_inner_left, LinearIsometry.inner_map_map, ext_inner_right, HasFDerivAt.comp_hasDerivAt, HasDerivAt.congr_of_eventuallyEq, HasFDerivAt.unique, IsCompact.exists_isMaxOn, ContinuousOn.preimage_isClosed_of_isClosed, Real.contDiff_sin, Real.hasDerivAt_sin, Real.abs_sin_le_one and Ioo_mem_nhds.
- All of them are in the import closure of GMT.Ch07.Submission: the full sorry-free scratch proofs in /tmp/dgce-decomp/Full.lean compile after import GMT.Ch07.Submission.

Lean checks:
- The three child types pass validate_lean_statement unchanged and elaborate in the exact gmt-compare contract_scope replay.
- The parent's exact frozen type follows from them by a 6-line assembly.
- #print axioms reports only propext, Classical.choice and Quot.sound.
- The instance checks confirm the Euclidean ball, the Euclidean inner product, LinearMap.range coerced to Set.range, and the order ((1 : ℕ) : WithTop ℕ∞).

Names: the proposed names collide with none of the 682 DAG lean_name values and appear on none of the 977 git refs.

Book: Simon Ch. 2 §4 (book/chapter-02.txt lines 849–871) states 4.1–4.3 without proof ('One readily checks'). The child proofs are therefore extracted from the parent-supplied proof.
