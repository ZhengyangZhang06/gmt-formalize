# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.local_retraction-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.local_retraction-a1.left_inverse_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (Q := L(ℝ^d); p the orthogonal projection onto Q, with p(q) = q for q ∈ Q and ‖p‖ ≤ 1; L₀ : ℝ^d ≅ Q the isomorphism induced by L (LinearEquiv.ofInjective); A := L₀⁻¹∘p, so that A∘L = id and L∘A = p), together with the bound ‖L∘A‖ = ‖p‖ ≤ 1 that step 7 uses to get ‖Dπ(x)‖ ≤ 1. Here L is an arbitrary injective continuous linear map (in the parent, L = Dψ(v₀)). No dependencies. Notation: ℝ^m = Euclid m with its Euclidean inner product; ‖·‖ is the operator norm of a continuous linear map.
1. (The range Q and the orthogonal projection onto it.) Let Q := L(ℝ^d) (Mathlib LinearMap.range L), a linear subspace of ℝ^P. Since ℝ^P is finite-dimensional, Q is finite-dimensional and hence complete, so the orthogonal projection onto Q exists: the continuous linear map p : ℝ^P → Q (Submodule.orthogonalProjectionOnto Q) such that y − p(y) is orthogonal to Q for every y ∈ ℝ^P. It fixes Q: p(q) = q for every q ∈ Q (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self). Let ι : Q → ℝ^P be the inclusion. The composite ι∘p : ℝ^P → ℝ^P is by definition Q.starProjection (= Q.subtypeL ∘L Q.orthogonalProjectionOnto), and its operator norm is at most 1 (Submodule.starProjection_norm_le). Directly: for y ∈ ℝ^P, y = ι(p(y)) + (y − ι(p(y))) with orthogonal summands, so |ι(p(y))|² ≤ |ι(p(y))|² + |y − ι(p(y))|² = |y|² by Pythagoras.
2. (L is a linear isomorphism of ℝ^d onto Q.) Every value L(w) lies in Q. Since L is injective, e : ℝ^d → Q, e(w) := L(w), is a linear bijection (LinearEquiv.ofInjective), and ι(e(w)) = L(w) for every w ∈ ℝ^d. Since ℝ^d and Q are finite-dimensional, every linear map between them is continuous, so e is a continuous linear equivalence (LinearEquiv.toContinuousLinearEquiv); in particular e⁻¹ : Q → ℝ^d is a continuous linear map.
3. (Definition of A.) Put A := e⁻¹∘p : ℝ^P → ℝ^d. As a composite of continuous linear maps, A is continuous linear.
4. (A∘L = id.) Let w ∈ ℝ^d. Since L(w) ∈ Q, step 1 gives p(L(w)) = L(w) as elements of Q. Since e(w) is the element of Q with ι(e(w)) = L(w), and an element of Q is determined by its image under ι, p(L(w)) = e(w). Hence A(L(w)) = e⁻¹(p(L(w))) = e⁻¹(e(w)) = w. As w is arbitrary, and two continuous linear maps are equal when they agree at every point, A∘L = id_{ℝ^d}.
5. (L∘A = ι∘p.) Let y ∈ ℝ^P and put q := p(y) ∈ Q. Then e(e⁻¹(q)) = q, so L(A(y)) = L(e⁻¹(q)) = ι(e(e⁻¹(q))) = ι(q) = ι(p(y)). As y is arbitrary, L∘A = ι∘p = Q.starProjection.
6. (Norm bound.) By steps 5 and 1, ‖L∘A‖ = ‖ι∘p‖ ≤ 1. Steps 3, 4 and 6 prove the claim. The case d = 0 needs no change: then Q = {0}, A = 0 and L∘A = 0, whose norm is 0 ≤ 1. ∎

## Key steps

1. Q := range L is finite-dimensional, so the orthogonal projection p : ℝ^P → Q exists, fixes Q, and ι∘p = Q.starProjection has operator norm ≤ 1.
2. Injectivity makes e : ℝ^d → Q, w ↦ Lw, a linear isomorphism; by finite dimensionality e and e⁻¹ are continuous.
3. A := e⁻¹∘p satisfies A(Lw) = e⁻¹(e w) = w, so A∘L = id.
4. L∘A = ι∘p = Q.starProjection, so ‖L∘A‖ ≤ 1.

## Reference use

### local-project

Queries:
- `cat SNAP/manifest.json; git -C SNAP/project rev-parse HEAD; git -C SNAP/mathlib rev-parse HEAD; cmp SNAP/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 205,240p GMT/Ch07/Contract.lean (def IsEmbeddedSubmanifold, abbrev Euclid, namespace/open scope)`
- `rg -n 'theorem starProjection_norm_le|def starProjection|theorem starProjection_eq_self_iff|theorem orthogonalProjectionOnto_mem_subspace_eq_self|orthogonalProjectionOnto' SNAP/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n 'noncomputable def ofInjective|theorem ofInjective_apply' SNAP/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `rg -n 'theorem norm_image_sub_le_of_norm_fderiv_le' SNAP/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem ContDiffOn.differentiableOn|theorem ContDiffOn.contDiffAt|theorem ContDiffAt.differentiableAt|theorem ContDiffOn.comp|theorem ContDiff.comp_contDiffOn|theorem ContDiffOn.of_le' SNAP/mathlib/Mathlib/Analysis/Calculus/ContDiff/*.lean`
- `rg -n 'theorem fderiv_comp|theorem fderiv_sub_const|theorem fderiv_comp_sub' SNAP/mathlib/Mathlib/Analysis/Calculus/FDeriv/*.lean`
- `rg -l 'def toContinuousLinearEquiv|def toOpenPartialHomeomorph|theorem mem_toOpenPartialHomeomorph_source|theorem to_localInverse|theorem OpenPartialHomeomorph.contDiffAt_symm|theorem ContDiffAt.hasStrictFDerivAt.|theorem isOpen_inter_preimage_symm|theorem ContinuousOn.isOpen_inter_preimage|theorem IsCompact.tendsto_subseq|theorem DifferentiableWithinAt.differentiableAt|theorem le_opNorm' SNAP/mathlib/Mathlib`
- `rg -n 'subset_compl_ball|isCompact_insert_range|def unitsEquiv|theorem continuousAt_iff' SNAP/mathlib/Mathlib`
- `rg -ln 'retraction' SNAP/project/GMT (no match)`
- `python3 scans of RUN/dag.json: nodes whose id or lean_name mentions retraction, with status; accepted nodes with left-inverse-type statements (Injective L, L.comp, A.comp): none; lean_name collisions for dimred_mbl_bh_lr_* (none); status of dtc_bc_lr_* and dtc_bc_local_retraction (re-checked at submission: left_inverse_projection still rlcr-lean)`
- `git show fe444362/86bfd8a4/349a0378:GMT/Ch07/Submission.lean | grep -n 'theorem Submission.dtc_bc_lr_'; git diff --stat b4d606d <commit> -- GMT/`
- `grep -n on /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, accepted-name reuse in _solve_children) and verifier/gmt-compare.py (contract_scope, child_modules)`
- `lake env lean /tmp/dimred_lr_split/{Elab,Assembly,LeftInv,Final}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-blowup-hypothes-bb396cc963/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-blowup-hypotheses-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retraction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retraction-a1/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dimred_lr_split/Assembly.lean`
- `/tmp/dimred_lr_split/Final.lean`

Pins match: snapshot project b4d606d and Mathlib 25730c7c. The snapshot Contract.lean equals the workspace's, and Submission.lean is byte-identical to Contract.lean. There is no local retraction onto submanifolds in the project ('retraction' in project/GMT: no match), and no accepted DAG declaration supplies a left inverse of an injective linear map. Three accepted declarations from the sibling branch dtc_bc_local_retraction (same type, same plan) are reused with byte-identical frozen types, each verified verbatim in its commit: dtc_bc_lr_local_inverse (349a0378), dtc_bc_lr_chart_image_nhds (fe444362) and dtc_bc_lr_lipschitz_near_point (86bfd8a4). The fourth, dtc_bc_lr_left_inverse_projection, is unaccepted (rlcr-lean), so its type is frozen under the fresh, collision-free name dimred_mbl_bh_lr_left_inverse_projection. The snapshot's Mathlib supplies everything the new child and the glue need: Submodule.orthogonalProjectionOnto/starProjection with starProjection_norm_le and orthogonalProjectionOnto_mem_subspace_eq_self (orthogonalProjection is deprecated); LinearEquiv.ofInjective with toContinuousLinearEquiv; ContDiffOn.comp, ContDiff.comp_contDiffOn, ContDiffOn.contDiffAt, ContDiffAt.differentiableAt and ContDiffOn.of_le; HasFDerivAt.comp, sub_const and fderiv; and ContinuousLinearMap.le_opNorm. Every name cited in the reused proofs also exists. All child types elaborate in the comparator scope, and the end-to-end file (accepted proofs, new child proof, parent assembly) compiles with only propext, Classical.choice and Quot.sound.
