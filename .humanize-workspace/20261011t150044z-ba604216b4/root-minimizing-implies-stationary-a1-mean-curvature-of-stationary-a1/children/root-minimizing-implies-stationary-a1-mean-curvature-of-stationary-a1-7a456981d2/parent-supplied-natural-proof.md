# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1.normal_trace_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof, i.e. Simon Ch. 2, 5.9 (chapter-02.txt lines 1326–1347: div_M X = div_M X^T − Σ_{i=1}^n X·B̄_y(τ_i, τ_i), B̄_y the second fundamental form of N at y) as used in Ch. 4, 2.7 (chapter-04.txt lines 185–209), at points where T_xM ⊆ T_xN. Notation: E := ℝ^P with the standard inner product; e_1, …, e_P the standard orthonormal basis (EuclideanSpace.basisFun, e_j = EuclideanSpace.single j 1); p := p_Q = Q.starProjection and P_S = S.starProjection the orthogonal projections; for T ∈ L(E, E), T^* := ContinuousLinearMap.adjoint T, characterised by ⟨T^*a, b⟩ = ⟨a, Tb⟩ (ContinuousLinearMap.adjoint_inner_left); A := DX(x) ∈ L(E, E); B := Dpr(x) ∈ L(E, L(E, E)); v := X(x).
1. Derivative of Y at x. Let Z(y) := X(y) − pr(y)(X(y)). Since Y = Z on a neighbourhood of x, DY(x) = DZ(x) (Filter.EventuallyEq.fderiv_eq). Since pr and X are differentiable at x, the map y ↦ pr(y)(X(y)) is differentiable at x (DifferentiableAt.clm_apply), and the product rule for evaluating an operator-valued map (HasFDerivAt.clm_apply; in fderiv form fderiv_clm_apply) shows that it has derivative h ↦ pr(x)(Ah) + (Bh)(v) at x, i.e. (pr x)∘A + B.flip v. With the difference rule (HasFDerivAt.sub) and pr(x) = P_S this gives DY(x)h = Ah − P_S(Ah) − (Bh)v for every h ∈ E.
2. Trace formula. For every C ∈ L(E, E), trace(p∘C) = Σ_j ⟨pe_j, C(pe_j)⟩. Proof: p(pw) = pw for all w, because pw ∈ Q and p fixes Q (Submodule.starProjection_apply_mem, Submodule.starProjection_eq_self_iff); hence p∘C = p∘(p∘C). By cyclicity of the trace (LinearMap.trace_comp_comm'), trace(p∘(p∘C)) = trace((p∘C)∘p). Expanding the trace in the orthonormal basis (LinearMap.trace_eq_sum_inner), trace((p∘C)∘p) = Σ_j ⟨e_j, p(C(pe_j))⟩, and self-adjointness of p (Submodule.inner_starProjection_left_eq_right) gives ⟨e_j, p(C(pe_j))⟩ = ⟨pe_j, C(pe_j)⟩.
3. One term. Fix j and put u := pe_j. Then u ∈ Q, hence u ∈ S because Q ≤ S, so P_S u = u. By step 1, ⟨u, DY(x)u⟩ = ⟨u, Au⟩ − ⟨u, P_S(Au)⟩ − ⟨u, (Bu)v⟩. Self-adjointness of P_S gives ⟨u, P_S(Au)⟩ = ⟨P_S u, Au⟩ = ⟨u, Au⟩, so the first two terms cancel. The adjoint identity for T := Bu and symmetry of the real inner product give ⟨u, (Bu)v⟩ = ⟨(Bu)^*u, v⟩ = ⟨v, (Bu)^*u⟩. Hence ⟨u, DY(x)u⟩ = −⟨v, (Bu)^*u⟩.
4. Summation. By steps 2 and 3 with C := DY(x), trace(p∘DY(x)) = Σ_j ⟨pe_j, DY(x)(pe_j)⟩ = Σ_j −⟨v, (B(pe_j))^*(pe_j)⟩ = −⟨X(x), Σ_j (Dpr(x)[pe_j])^*(pe_j)⟩, by linearity of the inner product in its second argument (inner_sum). This is the claim. For P = 0 all sums are empty and both sides are 0; the argument above covers this case.

## Key steps

1. DY(x) = DX(x) − P_S∘DX(x) − (h ↦ (Dpr(x)h)X(x)) by locality of the derivative and the product rule for y ↦ pr(y)(X(y)), using pr(x) = P_S.
2. trace(p∘C) = Σ_j ⟨pe_j, C(pe_j)⟩ from p² = p, cyclicity of the trace, the orthonormal-basis trace formula and self-adjointness of p.
3. For u = pe_j ∈ Q ≤ S: P_S u = u cancels ⟨u, DX(x)u⟩ − ⟨u, P_S DX(x)u⟩, and ⟨u, (Dpr(x)u)X(x)⟩ = ⟨X(x), (Dpr(x)u)^*u⟩ by the adjoint identity.
4. Summing over j gives trace(p∘DY(x)) = −⟨X(x), Σ_j (Dpr(x)[pe_j])^*(pe_j)⟩.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); git -C .lake/packages/mathlib rev-parse HEAD (25730c7c)`
- `rg -n 'mcs_trace_normal_part_eq_neg_inner|mcs_exists_c1_field_eq_proj_near|mcs_firstVariation_add|mcs_exists_meanCurvature_field' local-references/123e8435b4a2469b (no match)`
- `rg -n 'def tangentialDivergence|def IMRep.firstVariation|def IMRep.IsStationaryAlong|def IMRep.HasLocallyBoundedMeanCurvature|def approxTangentPlane|locallyIntegrable_mult|def tangentSpace' local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n -F in local-references/123e8435b4a2469b/mathlib/Mathlib: measurable_fderiv, exists_contDiff_support_eq_eq_one_iff, exists_compact_closed_between, exists_open_between_and_isCompact_closure, ContDiffOn.continuousOn_fderiv_of_isOpen, trace_eq_sum_inner, trace_comp_comm', starProjection_apply_mem, starProjection_norm_le, starProjection_eq_self_iff, inner_starProjection_left_eq_right, adjoint_inner_left, fderiv_clm_apply, fderiv_fun_sub, integral_withDensity_eq_integral_toReal_smul, withDensity_absolutelyContinuous, integrable_toReal_of_lintegral_ne_top, fderiv_of_notMem_tsupport, tsupport_smul_subset_left, exists_bound_of_continuousOn, continuous_finsetSum, notMem_mulTSupport_iff_eventuallyEq, image_eq_one_of_notMem_mulTSupport, isBoundedBilinearMap_comp, comp_aestronglyMeasurable₂, bounded_above_of_compact_support, span_eq, restrict_apply'`
- `python3 -I: dag.json (451 nodes, 451 distinct lean_names; this node decomposing, attempt 4, children []; the four sibling lean_statements; nodes whose lean_statement mentions firstVariation|tangentialDivergence|HasLocallyBoundedMeanCurvature|adjoint|IsStationaryAlong)`
- `python3 -I: nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1/{parent-child-handoff.json,parent-supplied-plan.md,decomposition-scope-v3.json,decomposition-v1.json,decomposition-v2.json,decomposition-v3.json,decomposition-audit-v1..v3.json,decomposition-review-receipt-v1..v3.json}; sha256(handoff natural_proof) = 3abf40da7d4e…`
- `grep -rl 'mcs_trace_normal_part_eq_neg_inner|mcs_exists_c1_field_eq_proj_near|mcs_firstVariation_add|mcs_exists_meanCurvature_field' .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/ (only this node's directory)`
- `git log --all --format=%H -G '<four lean_names>' -- '*.lean' (no commit); positive control git log --all -G 'dsmc_firstVariation_eq_integral' -- '*.lean' (6c199bd2, 583a6f2b)`
- `git show 2a7a318dbd3c29d1ba9b898d70abb5b1f0a6dcb8:GMT/Ch07/Submission.lean | sed -n 455,726p (accepted dsmc_firstVariation_eq_integral, dsmc_firstVariation_eq_neg_meanCurvature)`
- `sed -n 1320,1350p book/chapter-02.txt; sed -n 128,150p, 180,212p, 362,392p book/chapter-04.txt; sed -n 18,42p book/chapter-07.txt; grep -n '^5.9|^2.2|^2.7|3.14 Definition|^3.15'`
- `python3 -I /tmp/mcs-decomp-v4/py/gen.py verifier/ workspaces/gmt-ch07 out/children-v3.json lean (verifier validate_lean_statement + gmt-compare contract_scope/child_modules)`
- `lake env lean /tmp/mcs-decomp-v4/lean/NodeChallenge_{normal_trace_identity,tangential_cutoff_field,first_variation_additive,mean_curvature_field,parent}.lean`
- `lake env lean /tmp/mcs-decomp-v4/lean/Assembly.lean (#print axioms GMT.Ch07.mcsAssemblyCheck)`
- `lake env lean /tmp/mcs-decomp-v4/lean/Final.lean (four child proofs + assembly + mcsParentFromSiblings; #print axioms)`
- `lake env lean /tmp/mcs-decomp-v4/lean/Comparator.lean; lake env lean /tmp/mcs-decomp-v4/lean/Instances.lean; lake env lean /tmp/mcs-decomp-v4/lean/CitedNames.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Monoid.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/run.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1/decomposition-scope-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/mcs-decomp-v4/py/gen.py`
- `/tmp/mcs-decomp-v4/out/children-v4.json`
- `/tmp/mcs-decomp-v4/lean/NodeChallenge_normal_trace_identity.lean`
- `/tmp/mcs-decomp-v4/lean/NodeChallenge_tangential_cutoff_field.lean`
- `/tmp/mcs-decomp-v4/lean/NodeChallenge_first_variation_additive.lean`
- `/tmp/mcs-decomp-v4/lean/NodeChallenge_mean_curvature_field.lean`
- `/tmp/mcs-decomp-v4/lean/NodeChallenge_parent.lean`
- `/tmp/mcs-decomp-v4/lean/Assembly.lean`
- `/tmp/mcs-decomp-v4/lean/Child_normal_trace_identity.lean`
- `/tmp/mcs-decomp-v4/lean/Child_tangential_cutoff_field.lean`
- `/tmp/mcs-decomp-v4/lean/Child_first_variation_additive.lean`
- `/tmp/mcs-decomp-v4/lean/Child_mean_curvature_field.lean`
- `/tmp/mcs-decomp-v4/lean/Final.lean`
- `/tmp/mcs-decomp-v4/lean/Comparator.lean`
- `/tmp/mcs-decomp-v4/lean/Instances.lean`
- `/tmp/mcs-decomp-v4/lean/CitedNames.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) matches the compiler environment: its Contract.lean is byte-identical to the workspace contract and submission, and .lake/packages/mathlib is at 25730c7c. Neither the snapshot nor the 451-node DAG has a declaration of any of the four child types. The nearest, the accepted dsmc_firstVariation_eq_integral and dsmc_firstVariation_eq_neg_meanCurvature, have different types (the latter is ball-local), so the four children are new, and no lean_name collides with any DAG node, other node record, snapshot file or historical .lean file. Every library fact cited in the child proofs exists at the pinned revision (rg in the snapshot; #check in CitedNames.lean). The book citations are at the stated lines: Ch. 2, 5.9 at chapter-02.txt 1326–1347; Ch. 4, 2.2–2.3 at 132–147, 2.7 at 185–209, 3.14 at 366–381, 3.15 at 385. The four exact one-line child types elaborate in the verifier-generated comparator scope and are provable with only propext, Classical.choice and Quot.sound (Final.lean). Together with the four frozen sibling types they imply the exact selected parent type with no other assumptions (mcsAssemblyCheck, mcsParentFromSiblings).
