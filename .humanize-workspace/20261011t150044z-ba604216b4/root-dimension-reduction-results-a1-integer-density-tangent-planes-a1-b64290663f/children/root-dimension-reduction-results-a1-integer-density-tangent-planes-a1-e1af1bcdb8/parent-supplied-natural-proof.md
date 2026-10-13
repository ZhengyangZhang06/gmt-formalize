# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.angle_fderiv-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.angle_fderiv-a1.plane_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–3 of the supplied proof of idtp_cse_rc_angle_fderiv (its linear-algebra half). This is the standard formula for the orthogonal projection onto a subspace with an orthonormal basis.
Notation: π := Q.starProjection is the orthogonal projection of ℝ^P onto Q. It exists because Q is finite-dimensional, hence complete. ⟨·,·⟩ is the real inner product, which is symmetric and bilinear.
1. (Inner products of a and e.) ⟨a,a⟩ = |a|² = 1 and ⟨e,e⟩ = |e|² = 1, by real_inner_self_eq_norm_sq with ‖a‖ = ‖e‖ = 1. ⟨a,e⟩ = 0 by hypothesis, and ⟨e,a⟩ = ⟨a,e⟩ = 0 by symmetry (real_inner_comm).
2. (Orthonormality.) Let v := ![a, e] : Fin 2 → ℝ^P. By step 1, ⟨v_i, v_j⟩ = 1 when i = j and 0 when i ≠ j, for all i, j ∈ Fin 2. So v is orthonormal (orthonormal_iff_ite), hence linearly independent (Orthonormal.linearIndependent).
3. (span{a,e} = Q.) Each v_i lies in {a, e} ⊆ Q, so span(range v) ≤ Q (Submodule.span_le). By step 2 and finrank_span_eq_card, finrank span(range v) = card(Fin 2) = 2 = finrank Q. Q is finite-dimensional, and a subspace contained in a finite-dimensional subspace of the same finrank equals it (Submodule.eq_of_le_of_finrank_eq). Hence span{a,e} = span(range v) = Q.
4. (Projection formula.) Fix y ∈ ℝ^P and put w := ⟨y,a⟩a + ⟨y,e⟩e. Then w ∈ Q, because Q is a subspace containing a and e. By bilinearity and step 1:
   ⟨y − w, a⟩ = ⟨y,a⟩ − ⟨y,a⟩⟨a,a⟩ − ⟨y,e⟩⟨e,a⟩ = ⟨y,a⟩ − ⟨y,a⟩ − 0 = 0, and
   ⟨y − w, e⟩ = ⟨y,e⟩ − ⟨y,a⟩⟨a,e⟩ − ⟨y,e⟩⟨e,e⟩ = ⟨y,e⟩ − 0 − ⟨y,e⟩ = 0.
   The set K := {z ∈ ℝ^P : ⟨y − w, z⟩ = 0} is the kernel of the linear functional z ↦ ⟨y − w, z⟩ (innerₛₗ ℝ (y − w)), so K is a subspace. K contains a and e, so span{a,e} ≤ K, that is, Q ≤ K by step 3. Thus ⟨y − w, z⟩ = 0 for every z ∈ Q. Since w ∈ Q and y − w is orthogonal to Q, the uniqueness characterization of the orthogonal projection (Submodule.eq_starProjection_of_mem_of_inner_eq_zero) gives πy = w = ⟨y,a⟩a + ⟨y,e⟩e. This is the first conjunct.
5. (Norm formula.) By step 4 and real_inner_self_eq_norm_sq, |πy|² = ⟨w,w⟩. Expanding by bilinearity (inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right):
   ⟨w,w⟩ = ⟨y,a⟩²⟨a,a⟩ + ⟨y,a⟩⟨y,e⟩⟨a,e⟩ + ⟨y,e⟩⟨y,a⟩⟨e,a⟩ + ⟨y,e⟩²⟨e,e⟩ = ⟨y,a⟩² + ⟨y,e⟩²,
   using step 1 and ring arithmetic. This is the second conjunct.
6. Since y was arbitrary, both conjuncts hold for every y ∈ ℝ^P. ∎

## Key steps

1. ⟨a,a⟩ = ⟨e,e⟩ = 1 and ⟨a,e⟩ = ⟨e,a⟩ = 0, so ![a, e] is orthonormal and hence linearly independent.
2. span{a,e} ≤ Q and finrank span{a,e} = 2 = finrank Q, so span{a,e} = Q (Submodule.eq_of_le_of_finrank_eq).
3. w := ⟨y,a⟩a + ⟨y,e⟩e lies in Q, and y − w is orthogonal to a and e, hence to span{a,e} = Q. So πy = w (Submodule.eq_starProjection_of_mem_of_inner_eq_zero).
4. |πy|² = ⟨w,w⟩ = ⟨y,a⟩² + ⟨y,e⟩² by bilinear expansion with the orthonormality relations.

## Reference use

### local-project

Queries:
- `python3 scan of dag.json: selected node angle_fderiv-a1 (depth 5, status decomposing, depends_on []), its parent rotation_conservation-a1 and its 4 children (lean_name/status/depends_on/lean_statement); depth histogram (max depth 6, so children are leaves)`
- `python3 scan of all dag.json lean_statements for 'arctan', 'fderiv', the pattern 'starProjection <y> = inner ℝ <y> <a> • ' and 'inner ℝ y a ^ 2 + inner ℝ y e ^ 2' (no accepted node provides either child)`
- `rg -l -F idtp_cse_rc_af_ over dag.json, nodes/ and the snapshot project; loop of grep -l -F idtp_cse_rc_af_ over .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean (all no match)`
- `rg -n 'theorem eq_starProjection_of_mem_of_inner_eq_zero|theorem eq_of_le_of_finrank_eq|theorem finrank_span_eq_card|theorem Orthonormal.linearIndependent|theorem hasDerivAt_arctan|theorem contDiff_arctan|theorem ContDiffAt.div |theorem HasFDerivAt.mul |theorem HasFDerivAt.arctan|theorem ContDiffAt.arctan|theorem HasFDerivAt.inner|theorem fderiv_inner_apply' mathlib/Mathlib`
- `grep -rn 'HasFDerivAt.inv|HasFDerivAt.fun_inv|HasFDerivAt.div' Mathlib (absent for E → ℝ at this pin; use hasDerivAt_inv with HasDerivAt.comp_hasFDerivAt); grep innerₛₗ_apply_apply, orthonormal_iff_ite, real_inner_self_eq_norm_sq, innerSL_apply_apply, real_inner_comm`
- `rg -n arctan project/ (no match); rg -n starProjection project/GMT (only frozen definitions, no reusable projection-formula lemma)`
- `cmp -s of 11 cited Mathlib files and GMT/Ch07/Submission.lean between the snapshot and the workspace .lake/packages/mathlib (all identical)`
- `lake env lean /tmp/af_decomp/Stmts.lean (both child types elaborate)`
- `lake env lean /tmp/af_decomp/Full.lean (both children proved without sorry; parent proved from them; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/af_decomp/Assembly.lean (frozen parent type from the two child types used only as hypotheses; standard axioms; starProjection instance printed with pp.explicit)`
- `grep -n -i 'polar|arctan|angle|rotation|cone' book/chapter-07.txt (Ch. 7 proof of 3.3(1), lines 497–511)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b64290663f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b64290663f/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b3bbbebf7a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/af_decomp/Stmts.lean`
- `/tmp/af_decomp/Full.lean`
- `/tmp/af_decomp/Assembly.lean`
- `/tmp/af_decomp/proposal.md`

Compiler authority is the frozen GMT.Ch07 contract (snapshot Submission.lean is byte-identical to the workspace copy) at mathlib 25730c7c. Every cited Mathlib file in the snapshot matches .lake/packages/mathlib byte for byte. The needed declarations exist at this pin: Submodule.eq_starProjection_of_mem_of_inner_eq_zero, Submodule.eq_of_le_of_finrank_eq, finrank_span_eq_card, orthonormal_iff_ite, Orthonormal.linearIndependent, real_inner_self_eq_norm_sq, real_inner_comm, innerSL_apply_apply, innerₛₗ_apply_apply, ContDiffAt.div (fun form), ContDiffAt.arctan, Real.contDiff_arctan, hasDerivAt_inv, HasDerivAt.comp_hasFDerivAt, HasFDerivAt.mul (fun form), HasFDerivAt.arctan, Real.hasDerivAt_arctan and HasFDerivAt.fderiv. HasFDerivAt.inv and HasFDerivAt.div for E → ℝ are absent, and the child proofs avoid them. Neither the project snapshot nor any accepted DAG node already provides the projection formula or the polar-angle differential. The two proposed names are unreserved everywhere. Both child types elaborate, and both children are kernel-checked. The exact frozen parent type follows from the two child types alone, with only the standard axioms (propext, Classical.choice, Quot.sound).
