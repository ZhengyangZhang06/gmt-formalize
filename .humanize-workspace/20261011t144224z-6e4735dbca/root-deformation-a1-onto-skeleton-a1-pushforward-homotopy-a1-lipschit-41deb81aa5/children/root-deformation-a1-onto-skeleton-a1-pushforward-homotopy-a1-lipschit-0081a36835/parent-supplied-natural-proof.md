# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.support_closure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 11 of the parent proof. There the hypothesis is the characterization LipPF(X, G, S) of Step 9, applied to the reference sequence: the maps G_n are C^∞, hence continuous, and converge to G uniformly on (spt X)_{r/2} ⊇ spt X, hence on spt X. Recall the definitions. S vanishes on W (S.VanishesOn W) if S(ω) = 0 for every ω ∈ D^k(ℝ^{m′}) with tsupport ω ⊆ W. zeroRegion(S) is the union of all open W ⊆ ℝ^{m′} with closure W compact, closure W ⊆ univ and S vanishing on W. spt S = univ ∖ zeroRegion(S).

1. (Setup.) Let y₀ ∈ spt S. Suppose, for contradiction, that y₀ ∉ closure(G(spt X)). The complement of the closed set closure(G(spt X)) is open and contains y₀, so there is ε > 0 with ball(y₀, ε) ∩ closure(G(spt X)) = ∅ (Metric.isOpen_iff). Put ρ := ε/3 > 0. For every x ∈ spt X, G(x) ∈ G(spt X) ⊆ closure(G(spt X)), so G(x) ∉ ball(y₀, ε), i.e. dist(G(x), y₀) ≥ ε.
2. (S vanishes on W := ball(y₀, ρ).) Let ω ∈ D^k(ℝ^{m′}) with tsupport ω ⊆ W.
   (a) By uniform convergence on spt X (Metric.tendstoUniformlyOn_iff), for all sufficiently large n: dist(G(x), G_n(x)) < ρ for every x ∈ spt X.
   (b) Fix such an n and put N_n := G_n⁻¹(ℝ^{m′} ∖ tsupport ω). It is open: it is the preimage, under the continuous map G_n, of the open complement of the closed set tsupport ω.
   (c) spt X ⊆ N_n. Let x ∈ spt X and suppose G_n(x) ∈ tsupport ω. Then G_n(x) ∈ W, i.e. dist(G_n(x), y₀) < ρ. By step 1 and the triangle inequality, ε ≤ dist(G(x), y₀) ≤ dist(G(x), G_n(x)) + dist(G_n(x), y₀) < ρ + ρ = 2ε/3 < ε, a contradiction. So G_n(x) ∉ tsupport ω, i.e. x ∈ N_n.
   (d) Let x ∈ N_n. Then G_n(x) ∉ tsupport ω, so ω(G_n(x)) = 0 (image_eq_zero_of_notMem_tsupport). Hence ω(G_n(x))∘(fderiv ℝ G_n x) = 0, since the pull-back of the zero covector is zero. This is the value at x of the zero form 0 ∈ D^k(ℝ^m).
   (e) By (a)–(d), for all sufficiently large n the constant sequence η_n := 0 satisfies the compatibility condition of the hypothesis for ω, with N := N_n. Hence X(0) → S(ω). But X is linear, so X(0) = 0 for every n, and the constant sequence 0 converges to 0. Limits in ℝ are unique (tendsto_nhds_unique), so S(ω) = 0.
   As ω was arbitrary, S vanishes on W.
3. (y₀ ∈ zeroRegion(S).) W = ball(y₀, ρ) is open. Its closure lies in closedBall(y₀, ρ) (closure_ball_subset_closedBall), which is compact because ℝ^{m′} is proper (isCompact_closedBall). So closure W is compact, as a closed subset of a compact set, and closure W ⊆ univ. With step 2, W belongs to the family whose union is zeroRegion(S). Since ρ > 0, y₀ ∈ W, hence y₀ ∈ zeroRegion(S).
4. (Conclusion.) spt S = univ ∖ zeroRegion(S), so y₀ ∉ spt S, which contradicts step 1. Hence every point of spt S lies in closure(G(spt X)), i.e. spt S ⊆ closure(G(spt X)). ∎

## Key steps

1. A point y₀ ∉ closure(G(spt X)) has a ball of radius ε = 3ρ disjoint from that closure, so dist(G(x), y₀) ≥ 3ρ for x ∈ spt X.
2. Let ω be supported in ball(y₀, ρ), and let n be large enough that dist(G, G_n) < ρ on spt X. Then G_n(x) ∉ tsupport ω on the open set N_n := G_n⁻¹(ℝ^{m′} ∖ tsupport ω) ⊇ spt X, so the zero form is compatible with (G_n, ω).
3. The hypothesis then gives X(0) = 0 → S(ω), so S(ω) = 0, and S vanishes on ball(y₀, ρ).
4. That ball is open with compact closure, so y₀ ∈ zeroRegion(S), i.e. y₀ ∉ spt S.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); diff -q of the snapshot's project/GMT/Ch06/Contract.lean against the workspace contract (identical)`
- `python3 over dag.json (687 nodes): status, lean_name and lean_statement of the 4 resolved dependencies (current_criterion: unaccepted, owned by lipschitz_pushforward; compatible_form, mass_bound, pullback_norm: accepted, isolated-comparator-result.json passed = True). Also a search for related accepted lemmas: found fiw_tb_ext_covectorNorm_smul; no match for an index-map convergence criterion, a bounded compatible form or a push-forward support bound`
- `grep -n '^def|^structure|^theorem|^abbrev' over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,CurrentLocalEquality,Mass}.lean: IsSmoothForm, IsTestForm, testFormOnSubmodule (IsTestForm ∧ tsupport ⊆ U), GeometricCurrentOn (+ ext, Zero instance), VanishesOn, zeroRegion, support, isOpen_zeroRegion, covectorEuclideanNorm(_zero/_nonneg), massOn, mass`
- `git show fd5f1e29719e3bfa62df774678e3c6879599f8f9:GMT/Ch06/Submission.lean and git show 3e52d3e816fb507ab732d7ad15590fb7280bc981:GMT/Ch06/Submission.lean (accepted proofs of compatible_form and of pullback_norm with its prerequisites; layout `theorem Submission.X` inside namespace GMT.Ch06)`
- `rg -n over the snapshot's mathlib/Mathlib for Metric.cauchySeq_iff, cauchySeq_tendsto_of_complete, tendsto_atTop_mono, Metric.tendsto_nhds, Metric.tendstoUniformlyOn_iff, Metric.isOpen_iff, image_eq_one_of_notMem_mulTSupport (additive form image_eq_zero_of_notMem_tsupport), ProperSpace isCompact_closedBall, closure_ball_subset_closedBall, Finset.mul_sum, Real.sqrt_mul, Real.sqrt_sq_eq_abs, pow_le_pow_left₀, le_of_tendsto', tendsto_nhds_unique, ENNReal.ofReal_toReal/ofReal_coe_nnreal/ofReal_pow, isOpen_thickening, self_subset_thickening (all found)`
- `grep 'dph_lpfex' over dag.json, nodes/, GMT/ and SimonGMT, and git log --all -S'dph_lpfex' over 4135 refs: no match`
- `python3 -I with verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch06.main_theorem) and child_modules (contract mode); verifier/lean_contract.py validate_lean_statement on all child statements`
- `lake env lean on /tmp/dph-lpfex-decomp/lean/{AllStmts,Iface,C1,C2,C3,C1Real,Combined}.lean and /tmp/dph-lpfex-decomp/challenge/*_Challenge.lean: no errors`
- `read /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py: _decompose depth gate (depth 5 < max_depth 6), _existing_lean_name_problem, reuse-by-name id mapping, _overlay_accepted_children over children ∪ depends_on, _install_parent_supplied_child_handoff skipping accepted nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-41deb81aa5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/tmp/dph-lpfex-decomp/lean/AllStmts.lean`
- `/tmp/dph-lpfex-decomp/lean/Iface.lean`
- `/tmp/dph-lpfex-decomp/lean/C1.lean`
- `/tmp/dph-lpfex-decomp/lean/C1Real.lean`
- `/tmp/dph-lpfex-decomp/lean/C2.lean`
- `/tmp/dph-lpfex-decomp/lean/C3.lean`
- `/tmp/dph-lpfex-decomp/lean/Combined.lean`

Neither the pinned project nor SimonGMT nor the snapshot Mathlib contains the Lipschitz push-forward, a bounded compatible pull-back test form, an index-map convergence criterion for real sequences, or the push-forward support bound. The three new children are therefore new obligations, taken from Steps 2–3, 6 and 11 of the supplied proof. Two accepted declarations are reused by name with byte-identical types, titles and statements: iwl_sp_exists_compatible_testForm (compatible forms) and iwl_sp_covectorEuclideanNorm_pullback_le (pull-back norm bound). Both are prerequisites of bounded_compatible and both passed isolated comparators. The parent's other resolved dependencies, mass_bound and the unaccepted current_criterion, are used only in the parent assembly. The accepted fiw_tb_ext_covectorNorm_smul has the same content as the inline homogeneity step; it was found but deliberately not added as a dependency. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot. All statements elaborate in the exact comparator scope. The parent follows from the children and its resolved dependencies by a checked 149-line Lean assembly. Each new child has a complete Lean proof using only the standard axioms. The names dph_lpfex_* are globally unused.
