# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.restriction_limit-a1`
- Child DAG node: `root.integrality_weak_limits-a1.restriction_limit-a1.mass_iunion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- For V ⊆ ℝ^P, M_V(T) := T.massOn V = sup{ENNReal.ofReal(T(ω)) : ω ∈ massAdmissibleOn U k V} ∈ [0, ∞].
- massAdmissibleOn U k V is the set of ω ∈ D^k(U) = TestFormOn U k with tsupport ω ⊆ V and |ω(x)| ≤ 1 for all x, where |·| = covectorEuclideanNorm.
- M_V(T) is nondecreasing in V (GeometricCurrentOn.massOn_mono).
- ENNReal.ofReal(T(ω)) ≤ M_V(T) for every ω ∈ massAdmissibleOn U k V (GeometricCurrentOn.le_massOn).
- Every ω ∈ D^k(U) has compact tsupport (HasCompactSupport, the second component of the test-form property).

Source: the last sentence of step 5 of the parent proof (P6): 'For Y = X: μ(W ∩ B_η) → 0 as η ↓ 0, because these sets decrease to ∅ and μ(W) < ∞'. It is recast for the mass itself: the masses of the increasing open sets W ∩ {φ < s − 1/(i+1)} increase to the mass of W ∩ {φ < s}. No measure representation is needed.

Proof. Let V := ⋃_i O_i.
1. (≥.) For every i, O_i ⊆ V, so M_{O_i}(T) ≤ M_V(T) by monotonicity. Hence sup_i M_{O_i}(T) ≤ M_V(T).
2. (≤.) M_V(T) is a supremum, so it suffices to show ENNReal.ofReal(T(ω)) ≤ sup_i M_{O_i}(T) for every ω ∈ massAdmissibleOn U k V. Fix such an ω.
   - tsupport ω is compact, since ω is a test form, and it lies in V = ⋃_i O_i, a union of open sets.
   - The family (O_i) is directed under inclusion: O_i and O_{i′} both lie in O_{max(i,i′)} because the family is increasing (Monotone.directed_le).
   - By compactness (IsCompact.elim_directed_cover; ℕ is nonempty) there is an index i with tsupport ω ⊆ O_i. Equivalently, finitely many O_{i_1}, …, O_{i_m} cover tsupport ω, and all of them lie in O_{max_l i_l}.
   - Then ω ∈ massAdmissibleOn U k O_i, since the pointwise bound |ω(x)| ≤ 1 is unchanged.
   So ENNReal.ofReal(T(ω)) ≤ M_{O_i}(T) ≤ sup_i M_{O_i}(T).
3. Taking the supremum over all admissible ω in step 2 gives M_V(T) ≤ sup_i M_{O_i}(T). Together with step 1, M_V(T) = sup_i M_{O_i}(T). ∎

## Key steps

1. Monotonicity of massOn gives sup_i M_{O_i}(T) ≤ M_{⋃O}(T).
2. A form admissible for ⋃O has compact tsupport, which lies in a single O_i because the open O_i increase.
3. Hence ENNReal.ofReal(T(ω)) ≤ M_{O_i}(T) ≤ sup_i M_{O_i}(T); take the supremum over ω.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean (identical); cmp project/GMT/Ch06/Submission.lean project/GMT/Ch06/Contract.lean (identical)`
- `rg -n -i -l helly mathlib/Mathlib project (in the snapshot)`
- `rg -n 'massOn_iUnion|massOn_iSup|iwl_rl_' project mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare`
- `rg -n "theorem exists_contDiff_zero_iff_one_iff_of_isClosed|theorem normal_exists_closure_subset|theorem IsCompact.tendsto_subseq |theorem isCompact_univ_pi|theorem IsCompact.elim_directed_cover|theorem Monotone.countable_not_continuousAt|theorem tendsto_atTop_iSup|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem setIntegral_congr_fun |theorem ContinuousOn.preimage_isClosed_of_isClosed|theorem ContinuousOn.isOpen_inter_preimage|theorem tendsto_pi_nhds|theorem liminf_le_of_frequently_le'|theorem tsupport_smul_subset_right" mathlib/Mathlib (snapshot)`
- `grep -n '^variable' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean (smoothness order n : ℕ∞, so (n := ⊤) is C^∞)`
- `grep -n '^def |^theorem |^abbrev ' simongmt Chapter06/{Currents,Forms,Mass,FormsDuality}.lean (TestFormOn, GeometricCurrentOn, WeaklyConvergesOn, massAdmissibleOn, massOn, massOn_mono, le_massOn, massOn_le_liminf, covectorEuclideanNorm, NVector)`
- `python3 scan of dag.json (235 nodes): lean_name/lean_statement/status, accepted reuse candidates, foreign-child linking precedent`
- `grep -l <each new name> nodes/*/*.json dag.json DAG.md; git log --all -S iwl_rl_`
- `git show b9f9acdc41eaa29f36e54d7e570ae94d8ca8b4a6 / ba202ac0407b6e93210594416fcd0729874b2eff / c34586955a827a6731d9bc0ca8ae1ba1c0791948 :GMT/Ch06/Submission.lean`
- `grep -n 'selection argument|6.7(2)|4.5(1)' book/chapter-06.txt; sed -n 1512,1545p book/chapter-02.txt`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') + lean_contract.validate_lean_statement on the 6 child types`
- `lake build GMT.Ch06.Submission (scratch /tmp/iwl-rl-v3-LB0u7K, frozen sources, pinned lake-packages-25730c7c)`
- `lake env lean Scratch/Challenges/Challenge_<name>.lean (6 files)`
- `lake env lean Scratch/Assembly.lean`
- `lake env lean Scratch/CutoffTry.lean; lake env lean Scratch/Children.lean`
- `lake build GMT.Ch06.Submission (candidate = b9f9acd Submission + br_la_testForm_covectorNorm_bounded + 4 new children + parent); lake env lean Scratch/Solutions.lean (exact Submission.<name>; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convex/Radon.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/MonotoneConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-testform-bounded-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-testform-bounded-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/Challenges`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/Assembly.lean`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/CutoffTry.lean`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/Children.lean`
- `/tmp/iwl-rl-v3-LB0u7K/GMT/Ch06/Submission.lean`
- `/tmp/iwl-rl-v3-LB0u7K/Scratch/Solutions.lean`

Snapshot (project d8d46c95, Mathlib 25730c7c): the frozen Ch06 Contract is byte-identical to the workspace copy, and the snapshot Submission is byte-identical to the Contract.

Mathlib supplies every tool the children use:
- isCompact_univ_pi, IsCompact.tendsto_subseq and tendsto_pi_nhds;
- Monotone.countable_not_continuousAt and normal_exists_closure_subset;
- exists_contDiff_zero_iff_one_iff_of_isClosed (smooth Urysohn; n : ℕ∞, so ⊤ means C^∞);
- tsupport_smul_subset_right, IsCompact.elim_directed_cover and tendsto_atTop_iSup;
- setIntegral_eq_integral_of_forall_compl_eq_zero and setIntegral_congr_fun;
- ContinuousOn.isOpen_inter_preimage, ContinuousOn.preimage_isClosed_of_isClosed and liminf_le_of_frequently_le'.
SimonGMT supplies massOn, massOn_mono, le_massOn and WeaklyConvergesOn.massOn_le_liminf.

No match was found for:
- a Helly selection theorem (rg 'helly' finds only Analysis/Convex/Radon.lean, the convex Helly theorem);
- massOn_iUnion or massOn_iSup;
- any iwl_rl_* name in the project, Mathlib, SimonGMT, dag.json (235 nodes), other proposals or git history.

Accepted reuse: cmb_abs_apply_le_of_massOn_le (ba202ac) and br_la_testForm_covectorNorm_bounded (c345869) are accepted with comparator_passed=true, and their DAG types are string-identical to the proposed children.

Scratch verification:
- All 6 child types elaborate in the comparator child scope with only the intended sorry.
- The parent assembly compiles from stubs.
- The 4 new children are fully proved.
- With the accepted reuse proofs and the accepted iwl_restriction_theory (b9f9acd), the exact frozen parent Submission.iwl_restriction_weak_limit compiles.
- `exact Submission.<name>` checks pass, and #print axioms gives only propext, Classical.choice and Quot.sound for all 8 declarations.

The book's 8.2 proof and Remark 8.3(1) (chapter-06 lines 2313 and 2431) cite '4.5(1) and a selection argument as in 6.7(2) of Ch. 2'.

These checks do not replace the child acceptance gates.
