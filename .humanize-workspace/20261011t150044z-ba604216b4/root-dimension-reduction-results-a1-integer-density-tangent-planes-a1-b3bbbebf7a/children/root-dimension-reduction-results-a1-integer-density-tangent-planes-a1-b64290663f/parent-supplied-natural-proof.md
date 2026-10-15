# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.angle_fderiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 3 of the parent proof.
Notation: π := Q.starProjection; for a fixed x write α := ⟨x,a⟩ and β := ⟨x,e⟩.
1. (Orthonormal basis of Q.) ⟨a,a⟩ = |a|² = 1, ⟨e,e⟩ = 1 and ⟨a,e⟩ = ⟨e,a⟩ = 0, so the family (a, e) is orthonormal and hence linearly independent. span{a, e} ⊆ Q because a, e ∈ Q, and it has dimension 2 = finrank Q. Therefore span{a, e} = Q (Submodule.eq_of_le_of_finrank_eq, with finrank_span_eq_card).
2. (Formula for π.) Fix y and put w := ⟨y,a⟩a + ⟨y,e⟩e ∈ Q. Then ⟨y − w, a⟩ = ⟨y,a⟩ − ⟨y,a⟩⟨a,a⟩ − ⟨y,e⟩⟨e,a⟩ = 0, and likewise ⟨y − w, e⟩ = ⟨y,e⟩ − ⟨y,a⟩⟨a,e⟩ − ⟨y,e⟩⟨e,e⟩ = 0. The vectors orthogonal to y − w form a subspace containing a and e, so they contain span{a,e} = Q. By the characterization of the orthogonal projection (Submodule.eq_starProjection_of_mem_of_inner_eq_zero), πy = w.
3. ((i)) |πy|² = ⟨w,w⟩ = ⟨y,a⟩²⟨a,a⟩ + 2⟨y,a⟩⟨y,e⟩⟨a,e⟩ + ⟨y,e⟩²⟨e,e⟩ = ⟨y,a⟩² + ⟨y,e⟩².
4. ((ii) Smoothness.) Let α > 0. The maps y ↦ ⟨y,a⟩ and y ↦ ⟨y,e⟩ are continuous linear, hence C^∞, with derivatives v ↦ ⟨v,a⟩ and v ↦ ⟨v,e⟩. Since ⟨x,a⟩ ≠ 0, y ↦ ⟨y,e⟩/⟨y,a⟩ is C^∞ at x (ContDiffAt.div). arctan is C^∞ (Real.contDiff_arctan), so f is C¹ at x.
5. ((ii) Derivative.) Write ⟨y,e⟩/⟨y,a⟩ = ⟨y,e⟩·(⟨y,a⟩)⁻¹. The derivative of t ↦ t⁻¹ at α is −1/α² (hasDerivAt_inv). By the chain and product rules, D(⟨·,e⟩/⟨·,a⟩)(x)v = β·(−⟨v,a⟩/α²) + α⁻¹⟨v,e⟩ = (α⟨v,e⟩ − β⟨v,a⟩)/α². Since arctan'(t) = 1/(1 + t²) (Real.hasDerivAt_arctan), the chain rule at t = β/α gives Df(x)v = (α⟨v,e⟩ − β⟨v,a⟩)/(α²(1 + β²/α²)) = (α⟨v,e⟩ − β⟨v,a⟩)/(α² + β²).
6. The numerator is ⟨αe − βa, v⟩ = ⟨⟨x,a⟩e − ⟨x,e⟩a, v⟩ by symmetry of the real inner product. By (i) the denominator is α² + β² = |πx|², which is > 0. Hence fderiv f x v = ⟨⟨x,a⟩e − ⟨x,e⟩a, v⟩/|Q.starProjection x|². ∎

## Key steps

1. (a, e) is an orthonormal basis of Q: it is independent and finrank Q = 2.
2. πy = ⟨y,a⟩a + ⟨y,e⟩e, hence |πy|² = ⟨y,a⟩² + ⟨y,e⟩².
3. On ⟨x,a⟩ > 0, f = arctan(⟨·,e⟩/⟨·,a⟩) is C¹ at x.
4. Quotient and chain rules: Df(x)v = (⟨x,a⟩⟨v,e⟩ − ⟨x,e⟩⟨v,a⟩)/(⟨x,a⟩² + ⟨x,e⟩²) = ⟨Ax, v⟩/|πx|².

## Reference use

### local-project

Queries:
- `python3 scan of dag.json: selected node rotation_conservation-a1 (depth 4, depends_on []), parent cone_sector_endpoint_density-a1 and its 11 children (lean_name/status/depends_on/lean_statement)`
- `python3 scan of dag.json for lean_name in {imrep_approxTangent_starProjection_aesm, dsmc_firstVariation_eq_integral} (both accepted) and for lean_statements containing tangentialDivergence, smoothTransition, fderiv or LinearMap.trace`
- `grep -c idtp_cse_rc_ dag.json; grep -rl idtp_cse_rc_ nodes/ local-references/123e8435b4a2469b/project; grep -rl --include=*.lean idtp_cse_rc_ .swarm-worktrees/*/gmt-ch07/GMT (all no match)`
- `git show 1d65cf6d4d473fe727cd0ad43b45f3adfea87280:GMT/Ch07/Submission.lean (proof base = bare contract); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn 'trace_smulRight|trace_comp_comm|trace_eq_sum_inner' Mathlib; grep smoothTransition Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `grep -rn 'inner_starProjection_left_eq_right|eq_starProjection_of_mem_of_inner_eq_zero|norm_sq_eq_add_norm_sq_starProjection|starProjection_orthogonal_val|starProjection_eq_sum_rankOne' Mathlib/Analysis/InnerProductSpace`
- `grep -rn 'HasFDerivAt.smul|HasFDerivAt.mul|HasFDerivAt.pow|hasDerivAt_inv|HasFDerivAt.div|hasStrictFDerivAt_norm_sq|contDiffAt_norm|arctan_strictMono|arctan_one|hasDerivAt_arctan|contDiff_arctan|support_deriv_subset|notMem_tsupport_iff_eventuallyEq|pi_gt_three|two_le_pi|eq_of_le_of_finrank_eq|finrank_span_eq_card' Mathlib`
- `grep -rl 'theorem Submission.fvmb_trace_starProjection_comp_eq_sum_inner' .swarm-worktrees/*/gmt-ch07/GMT/Ch07 (accepted helper; Mathlib's trace_eq_sum_inner suffices instead)`
- `cmp of every cited Mathlib file between local-references/123e8435b4a2469b/mathlib and .lake/packages/mathlib (all identical)`
- `lake env lean /tmp/rc_decomp/Stmts.lean (4 child types elaborate; hypothesis-only parent assembly; #print axioms parent_from_children: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/rc_decomp/Full.lean (all 4 children proved without sorry; parent_given_external from children + external lemma types; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b3bbbebf7a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b3bbbebf7a/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/680526641c473b4bafe0/gmt-ch07/GMT/Ch07/Submission.lean`
- `/tmp/rc_decomp/Stmts.lean`
- `/tmp/rc_decomp/Small.lean`
- `/tmp/rc_decomp/Test.lean`
- `/tmp/rc_decomp/Full.lean`

The frozen opens and definitions of the snapshot and workspace Submission.lean (GMT.Ch07) are the compiler authority, with mathlib 25730c7c; the snapshot's Mathlib files equal .lake/packages/mathlib byte for byte. The proof base 1d65cf6 holds only the contract. The external lemmas imrep_approxTangent_starProjection_aesm and dsmc_firstVariation_eq_integral are accepted DAG nodes whose types match their use in the parent assembly. The children need no external lemma: they use only Mathlib. Relevant declarations exist at this pin: LinearMap.trace_smulRight, trace_comp_comm', trace_eq_sum_inner, Real.smoothTransition.{contDiffAt,one_of_one_le,zero_of_nonpos}, Submodule.{eq_starProjection_of_mem_of_inner_eq_zero,inner_starProjection_left_eq_right,norm_sq_eq_add_norm_sq_starProjection,starProjection_orthogonal_val}, HasFDerivAt.{fun_smul,fun_mul,pow}, hasDerivAt_inv, hasStrictFDerivAt_norm_sq, contDiffAt_norm, Real.{arctan_strictMono,arctan_one,arctan_neg,hasDerivAt_arctan,contDiff_arctan,two_le_pi}, support_deriv_subset and notMem_tsupport_iff_eventuallyEq. Some names are absent at this pin: HasFDerivAt.div for E -> R, HasFDerivAt.norm and an imported Real.pi_gt_three; the child proofs avoid them. The accepted helper fvmb_trace_starProjection_comp_eq_sum_inner is not needed. The four idtp_cse_rc_* names are unreserved. All four types elaborate. All four children are kernel-checked, and the exact parent type follows from them plus the two external lemma types with standard axioms only.
