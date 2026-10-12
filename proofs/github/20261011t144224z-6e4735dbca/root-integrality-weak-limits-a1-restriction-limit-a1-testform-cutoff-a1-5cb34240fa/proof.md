# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.restriction_limit-a1`
- Child DAG node: `root.integrality_weak_limits-a1.restriction_limit-a1.testform_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- ℝ^P := Eucl P, with standard orthonormal basis e_1, …, e_P.
- For a k-covector α (a continuous alternating k-linear map), |α| := covectorEuclideanNorm α = (Σ_{I : Fin k → Fin P strictly increasing} α(e_{I(0)}, …, e_{I(k−1)})²)^{1/2}.
- D^k(U) := TestFormOn U k is the real submodule of k-forms ω : ℝ^P → Covector(ℝ^P, k) that are C^∞ (IsSmoothForm, i.e. ContDiff ℝ ∞ with ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)), have compact support (HasCompactSupport) and satisfy tsupport ω ⊆ U. Operations are pointwise.
- No hypothesis on U is needed.

Source: the cutoffs of the parent proof (P6).
- Step 4 uses χ = κ∘φ_η, with χω = ω on tsupport ω ∩ {φ ≤ s − η} and χω = 0 on tsupport ω ∩ {φ ≥ s}.
- Step 7 uses ζω, with ζ = 1 near K and tsupport ζ ⊆ W.
- Both are instances of this lemma: take C₀ = tsupport ω ∩ φ⁻¹[s, ∞) and C₁ = tsupport ω ∩ φ⁻¹(−∞, a], respectively C₀ = ℝ^P ∖ W and C₁ = K.
- The cutoff is built with the smooth Urysohn lemma instead of mollifying a Tietze extension.

Proof.
1. (Open neighbourhoods with disjoint closures.) ℝ^P is a metric space, hence normal.
   - Since C₀ ∩ C₁ = ∅, C₁ lies in ℝ^P ∖ C₀, which is open because C₀ is closed. By normality (normal_exists_closure_subset) there is an open N₁ with C₁ ⊆ N₁ and closure(N₁) ⊆ ℝ^P ∖ C₀.
   - Then C₀ ⊆ ℝ^P ∖ closure(N₁), which is open. By normality again there is an open N₀ with C₀ ⊆ N₀ and closure(N₀) ⊆ ℝ^P ∖ closure(N₁).
   Hence closure(N₀) and closure(N₁) are disjoint closed sets.
2. (Smooth Urysohn function.) ℝ^P is a finite-dimensional real normed space. Apply the smooth Urysohn lemma (exists_contDiff_zero_iff_one_iff_of_isClosed, with smoothness order ⊤ : ℕ∞, i.e. C^∞) to closure(N₀) and closure(N₁). It gives a C^∞ function χ : ℝ^P → ℝ with:
   - χ(ℝ^P) ⊆ [0, 1];
   - χ(x) = 0 for x ∈ closure(N₀);
   - χ(x) = 1 for x ∈ closure(N₁).
3. (Homogeneity of |·|.) For t ∈ ℝ and a k-covector α, |tα| = |t|·|α|. Every coefficient satisfies (tα)(e_I) = t·α(e_I), so the sum of squares is multiplied by t², and √(t²S) = |t|·√S.
4. (The form ω′.) Define ω′(x) := χ(x)·ω(x) for x ∈ ℝ^P.
   - ω′ is C^∞, as the product of the C^∞ scalar function χ and the C^∞ form ω (ContDiff.smul).
   - If ω′(x) ≠ 0 then ω(x) ≠ 0. So support ω′ ⊆ support ω, and therefore tsupport ω′ ⊆ tsupport ω (tsupport_smul_subset_right). This is (iii).
   - tsupport ω′ is closed and lies in the compact set tsupport ω, so it is compact (IsCompact.of_isClosed_subset), and ω′ has compact support.
   - tsupport ω′ ⊆ tsupport ω ⊆ U.
   Therefore ω′ ∈ D^k(U).
5. ((i) and (ii).) N₀ ⊇ C₀ and N₁ ⊇ C₁ are open by step 1.
   - If x ∈ N₀ ⊆ closure(N₀), then χ(x) = 0 and ω′(x) = 0·ω(x) = 0.
   - If x ∈ N₁ ⊆ closure(N₁), then χ(x) = 1 and ω′(x) = 1·ω(x) = ω(x).
6. ((iv).) For x ∈ ℝ^P:
   - ω(x) − ω′(x) = ω(x) − χ(x)·ω(x) = (1 − χ(x))·ω(x);
   - 0 ≤ 1 − χ(x) ≤ 1, because χ(x) ∈ [0, 1].
   By step 3, |ω(x) − ω′(x)| = (1 − χ(x))·|ω(x)| ≤ |ω(x)|, using |ω(x)| ≥ 0 (covectorEuclideanNorm_nonneg).
7. By steps 4–6, ω′ has properties (i)–(iv). ∎

Lean remarks, both verified in scratch:
- Build the form as `let f := fun x => χ x • ω x`, prove `f ∈ TestFormOn U k := ⟨⟨hχs.smul ω.2.1.1, hfc⟩, hfU⟩` with hfc obtained from ω.2.1.2.of_isClosed_subset, and then use ⟨f, hfmem⟩. A large inline anonymous constructor hit the heartbeat limit.
- `rw [sub_smul]` does not fire on covectors; use `((sub_smul (1 : ℝ) (χ x) (ω x)).trans (by rw [one_smul])).symm`.

## Key steps

1. Normality of ℝ^P gives open N₀ ⊇ C₀ and N₁ ⊇ C₁ with disjoint closures.
2. Smooth Urysohn lemma: a C^∞ χ : ℝ^P → [0,1] with χ = 0 on closure N₀ and χ = 1 on closure N₁.
3. ω′ := χω is a test form in U with tsupport ω′ ⊆ tsupport ω, ω′ = 0 on N₀ and ω′ = ω on N₁.
4. |ω − ω′| = (1 − χ)|ω| ≤ |ω| by homogeneity of the Euclidean coefficient norm.

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
