# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.locality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P := Eucl P. D^n(U) := TestFormOn U n is the real submodule of C^∞ n-forms ω : ℝ^P → Λ_n with compact support and tsupport ω ⊆ U; addition, subtraction and scalar multiplication are pointwise. D_n(U) := GeometricCurrentOn U n; its underlying map T.toCurrent : D^n(U) → ℝ is ℝ-linear, and T(ω) means T.toCurrent ω. spt T := T.support. tsupport f := closure(support f), where support f = {x : f(x) ≠ 0}.

Source: Step 7 of the parent proof, where ψ − Φ(ω) vanishes on an open neighbourhood N′ of spt X. Here it is stated for arbitrary U, T, ψ, φ and N. This is the locality behind Simon's remark after 2.23 that f_#T(ω) = T(ζ f^#ω) does not depend on the cut-off ζ.

1. Put η := ψ − φ. It lies in D^n(U), because a submodule is closed under subtraction, and η(x) = ψ(x) − φ(x) for every x ∈ ℝ^P.
2. For x ∈ N the hypothesis gives η(x) = ψ(x) − φ(x) = 0. Hence support η ⊆ ℝ^P ∖ N.
3. ℝ^P ∖ N is closed because N is open. The closure of a set is contained in every closed superset, so tsupport η = closure(support η) ⊆ ℝ^P ∖ N (Lean: `closure_minimal` with `IsOpen.isClosed_compl`).
4. Since spt T ⊆ N, the set ℝ^P ∖ N is disjoint from spt T. By step 3, tsupport η is also disjoint from spt T (`Set.disjoint_of_subset_left`, `Set.disjoint_compl_left_iff_subset`).
5. Apply the sibling isoperimetric_apply_eq_zero_of_disjoint_support to P, n, U, T and the test form η. By step 4 its hypothesis holds, so T(η) = 0.
6. T.toCurrent is ℝ-linear, so T(η) = T(ψ − φ) = T(ψ) − T(φ) (`map_sub`). By step 5, T(ψ) − T(φ) = 0, i.e. T(ψ) = T(φ). ∎

## Key steps

1. η := ψ − φ is a test form in U that vanishes on the open set N.
2. Hence tsupport η ⊆ ℝ^P ∖ N, a closed set disjoint from spt T ⊆ N.
3. isoperimetric_apply_eq_zero_of_disjoint_support gives T(η) = 0.
4. By linearity, T(ψ) − T(φ) = T(η) = 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean and Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3: dag.json statuses and frozen lean_statements of the cycle_reduction-a1 children (iwl_cr_*), isoperimetric_apply_eq_zero_of_disjoint_support and iwl_cr_radial_operator; scan of dag.json and nodes/*/decomposition-v*.json for TestFormOnConverges, open-neighbourhood locality statements, cutoff lemmas and lean_name collisions (iwl_cr_ce_*)`
- `python3: nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json (reused child record vanish_off_support); nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json (precedent for reusing accepted declarations); nodes/root-isoperimetric-a1-vanish-off-support-a1/accepted-candidate.json`
- `git show 3ccbe082:GMT/Ch06/Submission.lean (accepted isoperimetric_apply_eq_zero_of_disjoint_support); git show a46aa05:GMT/Ch06/Submission.lean (node proof base = contract copy); grep '^import' over accepted candidate commits and all local branches`
- `grep -n '^def|^structure|^theorem|^abbrev' simongmt Chapter06/{Forms,Currents,CurrentLocalEquality,FixedSupportCurrentTopology,AffineCurrentPushforward,CurrentDistributionEquivalence}.lean; grep -rn TestFormOnConverges simongmt`
- `rg -n 'theorem norm_iteratedFDeriv_smul_le|theorem support_iteratedFDeriv_subset|theorem HasCompactSupport.iteratedFDeriv|theorem tsupport_eq|theorem one_of_mem_closedBall|hasCompactSupport|iteratedFDeriv_fun_zero|bounded_above_of_compact_support|hasContDiffBump_of_innerProductSpace|continuous_eval_const|theorem integral_add|theorem integral_const_mul|tendstoUniformlyOn_iff' mathlib/Mathlib (snapshot)`
- `grep -n -i 'cone|homotopy' book/chapter-06.txt (Simon 2.23, 2.25, 2.30–2.32)`
- `python3 -I /tmp/ce-decomp/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/ce-decomp/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/ce-decomp/Scratch/{Avail,Assembly,Locality,Cutoff,Radial,Full,FullSol}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ce-decomp/children.json`
- `/tmp/ce-decomp/scripts/gen.py`
- `/tmp/ce-decomp/scripts/build.py`
- `/tmp/ce-decomp/Scratch/Assembly.lean`
- `/tmp/ce-decomp/Scratch/FullSol.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The snapshot's Ch06 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d), and the node's proof base a46aa05 is that clean copy.

DAG:
- isoperimetric_apply_eq_zero_of_disjoint_support is accepted (commit 3ccbe082) with exactly the reused frozen type.
- iwl_cr_radial_operator is decomposing and reserved by the sibling branch, so it cannot be reused. Hence the hypothesis (H) in cutoff_radial.
- No accepted declaration states locality or cut-off continuity. fiw_tb_ext_apply_eq_of_eqOn (decomposing, flat_iff_weak branch) has a different statement. The accepted fiw_ims_sc_* lemmas only give sup-norm continuity criteria.
- No iwl_cr_ce_* name exists anywhere.

Libraries: the snapshot Mathlib provides every input:
- norm_iteratedFDeriv_smul_le (ContDiff/Bounds.lean:250);
- ContDiffBump.tsupport_eq, one_of_mem_closedBall, hasCompactSupport and contDiff (BumpFunction/Basic.lean:157, 137, 166, 203);
- hasContDiffBump_of_innerProductSpace (InnerProduct.lean:57);
- support_iteratedFDeriv_subset and HasCompactSupport.iteratedFDeriv (FTaylorSeries.lean:868, 871);
- iteratedFDeriv_fun_zero (ContDiff/Basic.lean:80);
- Continuous.bounded_above_of_compact_support (Normed/Group/Bounded.lean:153);
- intervalIntegral.integral_add and integral_const_mul (IntervalIntegral/Basic.lean:774, 817).
SimonGMT supplies the definitions (TestFormOnConverges, GeometricCurrentOn.continuous', support = U ∖ zeroRegion) but no cut-off or locality lemma.

Lean (in /tmp scratch):
- All child challenge modules elaborate in the contract scope.
- The parent assembly compiles from exactly the four child types plus iwl_cr_radial_operator.
- Trial proofs of the three new children use only propext, Classical.choice and Quot.sound. The parent's only extra axiom is sorryAx, coming from the external radial operator.
- An independent reviewer agent reproduced these checks and accepted the split.

Source: Simon Ch. 6, 2.23 and 2.30 (local book copy).
