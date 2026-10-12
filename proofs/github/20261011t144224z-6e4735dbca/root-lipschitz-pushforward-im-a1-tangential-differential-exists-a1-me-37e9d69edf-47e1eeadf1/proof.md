# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1.countable_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. X, Y are measurable spaces, Y has a zero element 0 (any `Zero Y`; no algebraic structure is used), S_j ⊆ X (j ∈ ℕ) are measurable sets and G_j : X → Y (j ∈ ℕ) are measurable maps. This is Steps 6–7 of the parent proof (gluing by the first chart) in abstract form. Decidability of the predicates below is classical.

1. U := ⋃_i S_i is measurable as a countable union of measurable sets, so its complement X ∖ U is measurable.

2. For j ∈ ℕ and x ∈ X let p_j(x) be the statement "x ∈ S_j or x ∉ U". Then {x : p_j(x)} = S_j ∪ (X ∖ U) is measurable by step 1.

3. Every x ∈ X satisfies some p_j(x): if x ∈ U there is j with x ∈ S_j, so p_j(x) holds; if x ∉ U then p_0(x) holds. Let j(x) be the least j with p_j(x) (Nat.find).

4. For each j let G′_j : X → Y be G′_j(x) := G_j(x) for x ∈ S_j and G′_j(x) := 0 otherwise (Set.piecewise). G′_j is measurable as a piecewise combination, on the measurable set S_j, of the measurable map G_j and the constant (hence measurable) map 0 (Mathlib Measurable.piecewise).

5. Define L(x) := G′_{j(x)}(x). By the countable piecewise measurability lemma (Mathlib Measurable.find: if every f_j : X → Y is measurable, every {x : p_j(x)} is measurable and every x satisfies some p_j(x), then x ↦ f_{j(x)}(x) with j(x) the least such j is measurable), applied with f_j := G′_j and the data of steps 2–4, L is measurable.

6. Let x ∉ U. Then x ∉ S_{j(x)} (otherwise x ∈ U), so L(x) = G′_{j(x)}(x) = 0.

7. Let x ∈ U. Then p_{j(x)}(x) holds by the choice of j(x), and its second alternative "x ∉ U" is false, so x ∈ S_{j(x)} and L(x) = G′_{j(x)}(x) = G_{j(x)}(x). Hence j := j(x) satisfies x ∈ S_j and L(x) = G_j(x).

Steps 5, 6 and 7 prove the three claims. ∎

## Key steps

1. U = ⋃ S_i is measurable and each set {p_j} = S_j ∪ (X ∖ U) is measurable; every x satisfies some p_j.
2. G′_j := S_j.piecewise G_j 0 is measurable (Measurable.piecewise).
3. L(x) := G′_{j(x)}(x) with j(x) the least j satisfying p_j(x) (Nat.find) is measurable by Measurable.find.
4. Off U, x ∉ S_{j(x)}, so L(x) = 0; on U, x ∈ S_{j(x)}, so L(x) = G_{j(x)}(x).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/{Contract,Submission}.lean against workspace GMT/Ch06/{Contract,Submission}.lean, and cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (all identical)`
- `rg -n 'theorem Measurable.find|theorem measurable_fderiv |theorem ContinuousOn.measurable_piecewise|theorem MeasurableSet.image_of_continuousOn_injOn|theorem invFunOn_mem|theorem invFunOn_eq|instMeasurableSpace|theorem Measurable.piecewise' Mathlib (snapshot)`
- `grep -rn isBoundedBilinearMap_comp Mathlib/Analysis/Normed/Operator/; grep -n 'theorem Continuous.measurable2' Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean; grep -rn of_dist_le_mul Mathlib/Topology/MetricSpace/Lipschitz.lean; theorem piecewise_eq_of_notMem in Mathlib/Data/Set/Piecewise.lean`
- `python3 over dag.json: lean_name/lean_statement matching fderiv|lower_bound|antilip|glue|gluing|find|measurable|borel|piecewise|chart|invFunOn|Nat.find|Λ (found accepted lpf_wtc_cat_fderiv_lower_bound and lpf_wtc_chart_image_measurable_locally_finite; no generic gluing lemma)`
- `python3 over dag.json: duplicate lean_name check (none), cross-branch reused-child edges (71, all accepted with open PR), node count 362, status counts`
- `git show proof-workspace/gmt-ch06/20261011t144224z-6e4735dbca/theorems/solutions/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9-656700a018:GMT/Ch06/Submission.lean and …char-1f4173ea67-7381c3335e:GMT/Ch06/Submission.lean (accepted proofs)`
- `git grep -c lpf_tde_mcd over all 1102 refs from git for-each-ref refs/heads refs/remotes -- GMT (no match, exit 1)`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and child_modules (contract mode); verifier/lean_contract.validate_lean_statement on the 3 child types (all valid)`
- `lake build GMT.Ch06.Submission; lake env lean /tmp/mcd-decomp/{Stmts,Proofs,CmpCheck,Proofs2,CmpCheck2}.lean with #print axioms`
- `read nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json (reuse format and controller rules) and swarm-project.json (max_nodes 1000, max_depth 6, max_children 12)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Piecewise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-co-7afa0393aa/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/mcd-decomp/Proofs2.lean`
- `/tmp/mcd-decomp/CmpCheck2.lean`
- `/tmp/mcd-decomp/subproblems2.json`

Snapshot. It pins project d8d46c95 and Mathlib 25730c7c and holds the frozen Ch06 contract. Its project/GMT/Ch06/Contract.lean and Submission.lean are byte-identical to the workspace files, and Submission equals Contract.

Mathlib. Every lemma the children use is present with a compatible signature:
- Measurable.find (MeasurableSpace/Constructions.lean:515)
- measurable_fderiv, valid for any f (FDeriv/Measurable.lean:378)
- MeasurableSet.image_of_continuousOn_injOn, i.e. Lusin–Souslin (Polish/Basic.lean:821)
- ContinuousOn.measurable_piecewise and Continuous.measurable2 (BorelSpace/Basic.lean:523, 591)
- the Borel instMeasurableSpace/instBorelSpace on E →L[𝕜] F (BorelSpace/ContinuousLinearMap.lean:47–50)
- invFunOn_mem and invFunOn_eq (Data/Set/Function.lean:963–966)
- piecewise_eq_of_mem and piecewise_eq_of_notMem (Data/Set/Piecewise.lean:52–56)
- isBoundedBilinearMap_comp (Normed/Operator/BoundedLinearMaps.lean:379)
- LipschitzOnWith.of_dist_le_mul (MetricSpace/Lipschitz.lean:57)

DAG. The accepted lpf_wtc_cat_fderiv_lower_bound has exactly the content of Step 4 and is reused with an identical frozen type; 71 existing cross-branch reuse edges follow the same pattern. No accepted generic gluing lemma exists (no match), so countable_glue is new. The accepted lpf_wtc_chart_image_measurable_locally_finite would only replace the one-line Lusin–Souslin step, so it is not reused.

Kernel checks. Proofs2.lean and CmpCheck2.lean prove all three children with only propext, Classical.choice and Quot.sound. They also derive the exact frozen parent type from the children plus lpf_tde_continuous_left_inverse; sorryAx comes only from that uncle's stub.
