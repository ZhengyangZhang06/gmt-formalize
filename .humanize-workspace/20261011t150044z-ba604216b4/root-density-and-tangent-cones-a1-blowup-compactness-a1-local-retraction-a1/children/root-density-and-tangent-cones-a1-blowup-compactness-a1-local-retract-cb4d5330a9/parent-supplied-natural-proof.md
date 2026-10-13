# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1.left_inverse_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (Q := L(ℝ^d), p the orthogonal projection onto Q with ‖p‖ ≤ 1 and p(Lw) = Lw, A := L⁻¹∘p), together with the identity L∘A = p used in step 7. No dependencies.
1. (The range and its orthogonal projection.) Let Q := L(ℝ^d) (Mathlib LinearMap.range L), a linear subspace of ℝ^P. Q is finite-dimensional, hence complete, so the orthogonal projection p : ℝ^P → Q onto Q exists (Submodule.orthogonalProjectionOnto Q). It is continuous and linear, and p(q) = q for every q ∈ Q (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self). Let ι : Q → ℝ^P be the inclusion. The composite ι∘p : ℝ^P → ℝ^P is the orthogonal projection of ℝ^P onto Q regarded as an endomorphism of ℝ^P (Q.starProjection, which is by definition Q.subtypeL ∘ Q.orthogonalProjectionOnto). Its operator norm is at most 1 (Submodule.starProjection_norm_le; indeed y = ι(p(y)) + (y − ι(p(y))) with orthogonal summands, so |ι(p(y))| ≤ |y|).
2. (L is an isomorphism onto Q.) Since L is injective, e : ℝ^d → Q, e(w) := L(w), is a linear bijection (LinearEquiv.ofInjective), and ι(e(w)) = L(w) for all w ∈ ℝ^d. Because ℝ^d and Q are finite-dimensional, e and its inverse e⁻¹ : Q → ℝ^d are continuous (LinearEquiv.toContinuousLinearEquiv).
3. (Definition of A.) Let A := e⁻¹∘p : ℝ^P → ℝ^d. It is a composite of continuous linear maps, hence continuous linear.
4. (A∘L = id.) Let w ∈ ℝ^d. Then L(w) ∈ Q, so p(L(w)) = L(w), i.e. p(L(w)) is the element e(w) of Q. Therefore A(L(w)) = e⁻¹(e(w)) = w. As w is arbitrary, A∘L = id_{ℝ^d} as continuous linear maps.
5. (L∘A = ι∘p.) Let y ∈ ℝ^P. Then L(A(y)) = ι(e(A(y))) = ι(e(e⁻¹(p(y)))) = ι(p(y)). Hence L∘A = ι∘p = Q.starProjection.
6. (Norm bound.) By steps 5 and 1, ‖L∘A‖ = ‖ι∘p‖ ≤ 1. Steps 3, 4 and 6 prove the claim. (For d = 0 the argument is unchanged: Q = {0}, A = 0 and L∘A = 0.) ∎

## Key steps

1. Q := range L is finite-dimensional, so the orthogonal projection p : ℝ^P → Q exists, fixes Q, and ι∘p has operator norm ≤ 1.
2. Injectivity makes e : ℝ^d → Q, w ↦ Lw, a linear isomorphism with continuous inverse.
3. A := e⁻¹∘p satisfies A(Lw) = e⁻¹(e w) = w, so A∘L = id.
4. L∘A = ι∘p is the orthogonal projection onto Q, so ‖L∘A‖ ≤ 1.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `grep -n IsEmbeddedSubmanifold -A 30 GMT/Ch07/Contract.lean (definition at lines 221-225)`
- `grep -n 'theorem|def ' mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean; grep -n 'theorem to_localInverse|def localInverse|def toOpenPartialHomeomorph|theorem localInverse_def' mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `grep -rn contDiffAt_symm mathlib/Mathlib (OpenPartialHomeomorph.contDiffAt_symm at Analysis/Calculus/ContDiff/Operations.lean:881); grep -rn hasStrictFDerivAt' mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `grep -n norm_image_sub_le_of_norm_fderiv_le mathlib/Mathlib/Analysis/Calculus/MeanValue.lean (line 499); grep -rn ContDiffOn.continuousOn_fderiv_of_isOpen mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean (line 916)`
- `grep -n 'orthogonalProjectionOnto|starProjection_norm_le|orthogonalProjection_mem_subspace_eq_self|def starProjection' mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean; grep -n 'def ofInjective' mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `grep -n 'oneSub|subset_compl_ball' mathlib/Mathlib/Analysis/Normed/Ring/Units.lean; grep -n unitsEquiv mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `grep -rln 'localInverse|toOpenPartialHomeomorph|orthogonalProjectionOnto|starProjection|norm_image_sub_le_of_norm_fderiv_le|isCompact_insert_range' simongmt/Poincare --include=*.lean; grep -rn retraction simongmt/Poincare; read Chapter08/ConstancyNormalCharts.lean and Chapter02/SubmanifoldTopology.lean`
- `python3 -I over dag.json: lean_name inventory and title/type regex 'retract|chart|nearest|tubular|inverse func|localInverse|proper'; grep -c dtc_bc_lr dag.json (0 matches)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope/child_modules (contract mode) on the four child types and the parent type`
- `lake env lean /tmp/lrdecomp/check/ChildA.lean ChildB.lean ChildC.lean ChildD.lean Assembly.lean EndToEnd.lean and /tmp/lrdecomp/challenges/Challenge_*.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retraction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/lrdecomp/check/EndToEnd.lean`
- `/tmp/lrdecomp/check/Assembly.lean`

The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean; IsEmbeddedSubmanifold is defined at Contract.lean:221-225. Every Mathlib ingredient named in the four child proofs exists at the pin:
- inverse function theorem: ContDiffAt.hasStrictFDerivAt', HasStrictFDerivAt.toOpenPartialHomeomorph, HasStrictFDerivAt.to_localInverse, OpenPartialHomeomorph.contDiffAt_symm, OpenPartialHomeomorph.isOpen_inter_preimage_symm, nonunits.subset_compl_ball, ContinuousLinearEquiv.unitsEquiv;
- calculus: ContDiffOn.continuousOn_fderiv_of_isOpen, Convex.norm_image_sub_le_of_norm_fderiv_le;
- orthogonal projection: Submodule.orthogonalProjectionOnto and its _mem_subspace_eq_self lemma, Submodule.starProjection and starProjection_norm_le, LinearEquiv.ofInjective;
- compactness: Filter.Tendsto.isCompact_insert_range, IsCompact.tendsto_subseq.
SimonGMT has only analogues with different predicates or weaker conclusions, so no library lemma is reused verbatim. Chapter08 exists_local_coordinate_leftInverse is a pointwise C² left inverse with no ‖L∘A‖ ≤ 1 bound and no inverse that is C¹ on a neighbourhood. Chapter02 IsSimonLocalRepresentation.exists_open_image_eq_inter is stated for the IsSimonLocalRepresentation predicate. The related accepted DAG nodes dsmc_chart_inverse_continuity and atsm_chart_image_flat are on other branches and absent from this node's proof base e34a71c, which contains only the frozen contract. So fresh dtc_bc_lr_* names are used, and none collides with any lean_name in dag.json. All four child types pass validate_lean_statement and elaborate in the comparator's contract scope. Scratch proofs of the four children, plus the parent assembled from them, compile with axioms [propext, Classical.choice, Quot.sound] only.
