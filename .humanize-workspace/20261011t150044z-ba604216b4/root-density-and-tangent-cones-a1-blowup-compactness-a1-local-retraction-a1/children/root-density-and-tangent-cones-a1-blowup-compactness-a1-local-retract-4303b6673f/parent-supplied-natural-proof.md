# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1.chart_image_nhds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof. There, with F := V ∖ V₀, ψ(F) is relatively closed in W, so W₀ := W ∖ ψ(F) is an open neighbourhood of x = ψ(v₀) with W₀ ∩ N = ψ(V₀), and B_δ(x) ⊆ W₀ for small δ. Here the same compactness argument is run at the single point x as a proof by contradiction, which is all the parent uses. Continuity of ψ on V is the only regularity needed. No dependencies.
1. (x lies in W.) Put x := ψ(v₀). Since v₀ ∈ V₀ ⊆ V, x ∈ ψ(V) = W ∩ N, so x ∈ W. As W is open, choose r_W > 0 with B_{r_W}(x) ⊆ W.
2. (Contradiction hypothesis and a sequence.) Suppose that no ρ > 0 satisfies N ∩ B_ρ(x) ⊆ ψ(V₀). For every i ∈ ℕ, apply this to ρ_i := min(r_W, 1/(i+1)) > 0: there is y_i ∈ N with |y_i − x| < ρ_i and y_i ∉ ψ(V₀). Then y_i ∈ B_{r_W}(x) ⊆ W and |y_i − x| < 1/(i+1). So y_i → x as i → ∞: given ε > 0, pick i₀ with 1/(i₀+1) < ε; then |y_i − x| < 1/(i+1) ≤ 1/(i₀+1) < ε for i ≥ i₀.
3. (Preimages outside V₀.) For each i, y_i ∈ W ∩ N = ψ(V), so choose f_i ∈ V with ψ(f_i) = y_i. Then f_i ∉ V₀, for otherwise y_i = ψ(f_i) ∈ ψ(V₀).
4. (A compact set in W.) Let K := {x} ∪ {y_i : i ∈ ℕ}. K is compact, being a convergent sequence together with its limit (Mathlib Filter.Tendsto.isCompact_insert_range), and K ⊆ W because x ∈ W (step 1) and every y_i ∈ W (step 2). By the properness hypothesis, V ∩ ψ⁻¹(K) is compact. It contains every f_i, since f_i ∈ V and ψ(f_i) = y_i ∈ K.
5. (Convergent subsequence.) Compact subsets of ℝ^d are sequentially compact (IsCompact.tendsto_subseq). So there are a ∈ V ∩ ψ⁻¹(K) and a strictly increasing φ : ℕ → ℕ with f_{φ(i)} → a. In particular a ∈ V.
6. (a ∉ V₀.) The complement ℝ^d ∖ V₀ is closed because V₀ is open, and it contains every f_{φ(i)} (step 3). Hence it contains the limit a, i.e. a ∉ V₀.
7. (ψ(a) = x.) ψ is continuous within V at a ∈ V, and f_{φ(i)} ∈ V with f_{φ(i)} → a, so ψ(f_{φ(i)}) → ψ(a). On the other hand ψ(f_{φ(i)}) = y_{φ(i)} → x, being a subsequence of the convergent sequence (y_i) (φ is strictly increasing, so φ(i) → ∞). Limits in ℝ^P are unique, so ψ(a) = x = ψ(v₀).
8. (Contradiction.) a ∈ V, v₀ ∈ V and ψ is injective on V, so a = v₀ ∈ V₀, contradicting step 6. Hence the assumption of step 2 is false, and there is ρ > 0 with N ∩ B_ρ(ψ(v₀)) ⊆ ψ(V₀). ∎

## Key steps

1. x := ψ(v₀) ∈ W; fix r_W > 0 with B_{r_W}(x) ⊆ W.
2. If no ρ works, pick y_i ∈ N ∩ B_{min(r_W, 1/(i+1))}(x) ∖ ψ(V₀); then y_i → x and y_i = ψ(f_i) with f_i ∈ V ∖ V₀.
3. K := {x} ∪ {y_i} is a compact subset of W, so the f_i lie in the compact set V ∩ ψ⁻¹(K) and a subsequence converges to some a ∈ V.
4. a ∉ V₀ because the complement of V₀ is closed; ψ(a) = x by continuity of ψ on V and uniqueness of limits.
5. Injectivity of ψ on V gives a = v₀ ∈ V₀, a contradiction.

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
