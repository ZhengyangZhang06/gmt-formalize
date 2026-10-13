# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.offset_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.offset_plane-a1.translate_embedded-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is steps 2–4 of the supplied proof of the parent node codim1_zsl_offset_plane_inClassO (Lemma A-plane). The dimension n + 1 is replaced by a general d and the smoothness order 2 by a general r. The orthonormal frame τ, which the parent extracts from IsUnitOrientationOf ξ Q, is taken here as a hypothesis.

Notation. ℝ^m = Euclid m = EuclideanSpace ℝ (Fin m), with Euclidean norm |v| = (Σ_j v_j²)^{1/2} and inner product ⟨v, w⟩ = Σ_j v_j w_j. Put A := {y ∈ ℝ^P : y + a ∈ Q}. Every step below also holds for d = 0, since empty sums are 0 and ℝ^0 = {0}.

1. (The linear map ι.) Define ι : ℝ^d → ℝ^P by ι(v) := Σ_{j<d} v_j·τ_j. It is the finite sum over j of the continuous linear maps v ↦ v_j·τ_j. Each of these is the coordinate functional EuclideanSpace.proj j followed by t ↦ t·τ_j, i.e. (EuclideanSpace.proj j).smulRight (τ j). Hence ι is a continuous linear map ℝ^d →L[ℝ] ℝ^P.

2. (ι is an isometry.) Let v ∈ ℝ^d. Orthonormality of τ means ⟨τ_i, τ_j⟩ = 1 if i = j and 0 if i ≠ j. Therefore |ι(v)|² = ⟨Σ_i v_iτ_i, Σ_j v_jτ_j⟩ = Σ_i Σ_j v_i v_j ⟨τ_i, τ_j⟩ = Σ_j v_j·v_j = ⟨v, v⟩ = |v|². (Lemmas: Orthonormal.inner_sum, real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct.) Both norms are nonnegative, so |ι(v)| = |v|.

3. (ι is injective.) Suppose ι(v) = ι(w). By linearity and step 2, |v − w| = |ι(v − w)| = |ι(v) − ι(w)| = 0, so v = w.

4. (The range of ι is Q.)
(a) Let v ∈ ℝ^d. Each τ_j lies in span{τ_0, …, τ_{d−1}} = Q, and Q is closed under scalar multiplication and finite sums. Hence ι(v) = Σ_j v_jτ_j ∈ Q.
(b) Conversely, let q ∈ Q = span{τ_j : j < d}. The index type Fin d is finite, so there is c : Fin d → ℝ with q = Σ_j c_j·τ_j (Submodule.mem_span_range_iff_exists_fun). Let v ∈ ℝ^d be the vector with coordinates v_j = c_j (WithLp.toLp 2 c). Then ι(v) = q.

5. (A global parametrization.) Define ψ : ℝ^d → ℝ^P by ψ(v) := ι(v) − a. For z ∈ ℝ^P:
z ∈ A ⟺ z + a ∈ Q ⟺ z + a = ι(v) for some v ∈ ℝ^d (step 4) ⟺ z = ψ(v) for some v ∈ ℝ^d.
Hence ψ(ℝ^d) = A.

6. (The chart clauses at a point.) Let y ∈ A. Take V := ℝ^d (the whole of Euclid d), W := ℝ^P (the whole of Euclid P), and ψ from step 5.
(a) V and W are open because they are whole spaces, and y ∈ W.
(b) ψ is a continuous linear map minus a constant, so ψ is C^∞ (ContinuousLinearMap.contDiff, ContDiff.sub, contDiff_const). In particular ContDiffOn ℝ r ψ V.
(c) Let v, w ∈ V with ψ(v) = ψ(w). Then ι(v) − a = ι(w) − a, so ι(v) = ι(w), and v = w by step 3. Thus InjOn ψ V.
(d) ψ(V) = ψ(ℝ^d) = A = ℝ^P ∩ A = W ∩ A, by step 5.
(e) Let K ⊆ W be compact. Since V = ℝ^d, V ∩ ψ^{−1}(K) = ψ^{−1}(K).
- This set is closed: K is closed (a compact subset of the Hausdorff space ℝ^P) and ψ is continuous.
- This set is bounded: K is bounded, so there is R ∈ ℝ with |z| ≤ R for all z ∈ K (isBounded_iff_forall_norm_le). If ψ(v) ∈ K, then by step 2, |v| = |ι(v)| = |ψ(v) + a| ≤ |ψ(v)| + |a| ≤ R + |a|.
- A closed and bounded subset of ℝ^d is compact (Heine–Borel; ℝ^d is a proper metric space; isCompact_of_isClosed_isBounded).
Hence V ∩ ψ^{−1}(K) is compact.
(f) Let z ∈ V. A continuous linear map is its own derivative at every point (ContinuousLinearMap.hasFDerivAt), and subtracting the constant a does not change the derivative (HasFDerivAt.sub_const). So fderiv ℝ ψ z = ι, which is injective by step 3.

7. (Conclusion.) For every y ∈ A, step 6 provides V, W and ψ satisfying every clause in the definition of IsEmbeddedSubmanifold r d A. Hence IsEmbeddedSubmanifold r d {y | y + a ∈ Q}. ∎

## Key steps

1. ι(v) := Σ_j v_jτ_j is a continuous linear map ℝ^d → ℝ^P with |ι(v)| = |v| by orthonormality, so ι is injective.
2. The range of ι is span τ = Q, so ψ(v) := ι(v) − a satisfies ψ(ℝ^d) = A = {y | y + a ∈ Q}.
3. At each y ∈ A take V = ℝ^d and W = ℝ^P: ψ is C^∞, injective on V, and ψ(V) = W ∩ A.
4. Each preimage ψ^{−1}(K) of a compact K is closed and bounded (|v| ≤ R + |a|), hence compact by Heine–Borel. fderiv ψ ≡ ι is injective, so all clauses of IsEmbeddedSubmanifold r d A hold.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n '"rev"' local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 scan of dag.json lean_statement fields matching tangentSpace|IsEmbeddedSubmanifold|InClassO|IsOrientation (conclusions and Submodule-set hypotheses), plus '+ a ∈ Q' and codim1_zsl lean_names; status/depth/children of the selected node`
- `python3 lean_name lookup in dag.json of codim1_zsl_op_translate_isEmbeddedSubmanifold, codim1_zsl_op_translate_tangentSpace_eq and prefix codim1_zsl_op_ (raw count 0)`
- `grep -rl 'codim1_zsl_op_\|translate_isEmbeddedSubmanifold\|translate_tangentSpace_eq' runs/20261011T150044Z-ba604216b4/nodes; grep -rn same GMT .lake/packages/simongmt/Poincare`
- `git log --all --oneline -S'codim1_zsl_op_' | wc -l; same for -S'translate_isEmbeddedSubmanifold' and -S'translate_tangentSpace_eq' (1478 refs); positive control git log --all --oneline -S'dgcr_graph_orientation_jacobian'`
- `rg -n 'isClosedEmbedding_of_injective|theorem slope_def_module|theorem hasDerivAt_iff_tendsto_slope |theorem isCompact_of_isClosed_isBounded|theorem finrank_span_eq_card|theorem Orthonormal.inner_sum|theorem Fintype.linearIndependent_iff ' mathlib/Mathlib/{Analysis,LinearAlgebra,Topology}`
- `rg -n 'mem_span_range_iff_exists_fun|isBounded_iff_forall_norm_le|theorem inner_eq_star_dotProduct|theorem real_inner_self_eq_norm_sq' mathlib/Mathlib/{LinearAlgebra/Finsupp,Analysis/Normed,Analysis/InnerProductSpace}`
- `grep -n 'def check_source_delta' -A60 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `lake env lean -DautoImplicit=false /tmp/offset-plane-decomp/gen/Assembly.lean (children as axioms with the exact submitted types; #print axioms of codim1_zsl_offset_plane_inClassO)`
- `lake env lean -DautoImplicit=false /tmp/offset-plane-decomp/gen/TypeCheck.lean and /tmp/offset-plane-decomp/gen/FinalProofs.lean (verbatim child types; complete trial proofs of both children and the parent; #print axioms; python check of each proof body against the leaf forbidden-token regex)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/AffineSpace/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/LinearIndependent/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-b1cf5f0472/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-b1cf5f0472/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-b1cf5f0472/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/tmp/offset-plane-decomp/Types.lean`
- `/tmp/offset-plane-decomp/Proofs.lean`
- `/tmp/offset-plane-decomp/gen/Assembly.lean`
- `/tmp/offset-plane-decomp/gen/TypeCheck.lean`
- `/tmp/offset-plane-decomp/gen/FinalProofs.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) matches workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest pins simongmt 2b366308, which equals .lake/packages/simongmt. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

DAG: the selected node is 'decomposing' at depth 4 with no children and the handoff's exact frozen type. No DAG node (accepted or not) states that an affine translate is an embedded submanifold or computes its tangentSpace. The accepted chart lemmas chart_tangentSpace_eq_range_fderiv and dsmc_chart_tangentSpace_eq_range are general-chart statements with other types and are not reused. The two proposed names and the prefix codim1_zsl_op_ are unused in dag.json, node files, GMT/, simongmt and all 1478 git refs; the positive control was found.

Library: every lemma the child proofs cite exists in the pinned Mathlib. Examples: Orthonormal.inner_sum (Orthonormal.lean:167), hasDerivAt_iff_tendsto_slope (Deriv/Slope.lean:73), slope_def_module (AffineSpace/Slope.lean:51), finrank_span_eq_card (Dimension/Constructions.lean:463), Fintype.linearIndependent_iff (LinearIndependent/Defs.lean:770), isCompact_of_isClosed_isBounded (MetricSpace/Bounded.lean:320), Submodule.mem_span_range_iff_exists_fun (Finsupp/LinearCombination.lean:379), EuclideanSpace.inner_eq_star_dotProduct (PiL2.lean:213) and real_inner_self_eq_norm_sq (InnerProductSpace/Basic.lean:398).

Leaf rule: check_source_delta forbids auxiliary declarations in a leaf, so each child must be a single theorem; both trial proofs meet this.

Lean: both child types elaborate verbatim, and the assembly with the children as axioms proves the frozen selected type (axioms: propext, Classical.choice, Quot.sound and the two children). The complete child proofs compile with only propext, Classical.choice and Quot.sound.
