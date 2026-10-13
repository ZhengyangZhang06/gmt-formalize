# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1.fixed_support_dense-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–4 of the parent proof (the pieces X_i, the embedding ω ↦ (ω|_{K_i}, dω|_{K_i}) into a separable space of continuous maps on K_i, and the pulled-back countable dense subset), specialized to one compact set K. Two details are filled in:
 - (a) Mathlib cannot infer finite-dimensionality or second countability of Covector (Euclid P) k, so it is taken from the sibling covector_findim.
 - (b) Instead of the full isometry claim for the sum metric d_i, only two facts are used: pointwise distance ≤ uniform distance on K, and vanishing off K. This is exactly what step 6 of the parent proof needs.
Neither K ⊆ U nor openness of U is used.

Notation: Λ^k := Covector (Euclid P) k with its operator norm, so dist(a, b) = ‖a − b‖. d = exteriorDerivative. X := {ω ∈ 𝒟ⁿ(U) : tsupport ω ⊆ K}.

1. Regularity and vanishing. Let ω ∈ 𝒟ⁿ(U) (TestFormOn U n).
 - By definition ω is C^∞ with compact support and tsupport ω ⊆ U. In particular ω is continuous (Lean: ω.property.1.1.continuous).
 - dω is again a test form (SimonGMT Chapter06 exteriorDerivative_isTestForm ω.property.1), hence continuous.
 - If x ∉ tsupport ω then ω(x) = 0 (image_eq_zero_of_notMem_tsupport).
 - tsupport dω ⊆ tsupport ω (SimonGMT tsupport_exteriorDerivative_subset), so also dω(x) = 0.
 - Consequently, for ω ∈ X and x ∉ K: x ∉ tsupport ω, hence ω(x) = 0 and dω(x) = 0.

2. The target space.
 - By the sibling theorem covector_findim (with n and with n + 1), Λⁿ and Λ^{n+1} are finite-dimensional real normed spaces.
 - A finite-dimensional real normed space is proper (FiniteDimensional.proper), and a proper metric space is second countable (secondCountable_of_proper).
 - Let F := Λⁿ × Λ^{n+1} with the product metric dist((a, b), (a', b')) = max(dist(a, a'), dist(b, b')) (Prod.dist_eq). As a product of two second-countable spaces, F is second countable.

3. The function space. Give K the subspace topology.
 - K is compact (isCompact_iff_compactSpace) and Hausdorff, hence locally compact. It is second countable as a subspace of ℝ^P.
 - Therefore C(K, F), the continuous maps K → F with the compact-open topology, is second countable. This is ContinuousMap.instSecondCountableTopology in Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean; that module must be imported in Submission.lean.
 - Since K is compact, C(K, F) carries the uniform metric dist(f, g) = sup_{x ∈ K} dist(f(x), g(x)). Its topology is the compact-open topology: Mathlib's metric instance on C(K, F) is pulled back along the uniform embedding into bounded continuous functions.
 - For every x ∈ K, dist(f(x), g(x)) ≤ dist(f, g) (ContinuousMap.dist_apply_le_dist).

4. The map Φ. For ω ∈ 𝒟ⁿ(U), let Φ(ω) ∈ C(K, F) be the map K ∋ x ↦ (ω(x), dω(x)). It is continuous: x ↦ (ω(x), dω(x)) is continuous on ℝ^P by step 1 (Continuous.prodMk), and the inclusion K → ℝ^P is continuous.

5. A countable dense subset of Φ(X) and its pull-back.
 - The image Φ(X) is a subspace of the second-countable space C(K, F), hence second countable and separable. So there is a countable set T ⊆ Φ(X) that is dense in Φ(X) (TopologicalSpace.exists_countable_dense applied to the subtype Φ '' X).
 - Every t ∈ Φ(X) has the form Φ(ω) with ω ∈ X. By choice fix σ(t) ∈ X with Φ(σ(t)) = t.
 - Define D := σ(T) = {σ(t) : t ∈ T} ⊆ 𝒟ⁿ(U).

6. Properties of D. D is countable, as the image of the countable set T. Every η ∈ D equals σ(t) ∈ X for some t, so tsupport η ⊆ K.

7. Approximation. Let ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ K, i.e. ω ∈ X, and let ε > 0.
 - Φ(ω) ∈ Φ(X), and T is dense in the metric space Φ(X) with the restricted distance. So there is t ∈ T with dist(Φ(ω), t) < ε (Dense.exists_dist_lt).
 - Put η := σ(t) ∈ D. Then Φ(η) = t, so dist(Φ(ω), Φ(η)) < ε. Let x ∈ ℝ^P.
 - (a) If x ∈ K, steps 2 and 3 give max(dist(ω(x), η(x)), dist(dω(x), dη(x))) = dist(Φ(ω)(x), Φ(η)(x)) ≤ dist(Φ(ω), Φ(η)) < ε. So dist(ω(x), η(x)) < ε and dist(dω(x), dη(x)) < ε.
 - (b) If x ∉ K, then ω ∈ X and η ∈ X, so step 1 gives ω(x) = 0 = η(x) and dω(x) = 0 = dη(x). Both distances are 0 < ε.
 - Hence dist(ω(x), η(x)) < ε and dist(dω(x), dη(x)) < ε for every x ∈ ℝ^P.

8. Conclusion. D is countable and all its members are supported in K (step 6). Step 7 gives the required approximation for every ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ K and every ε > 0. ∎

## Key steps

1. Test forms and their exterior derivatives are continuous and vanish off tsupport ω; for ω supported in K, both vanish off K.
2. By the sibling covector_findim, F := Λⁿ × Λ^{n+1} is finite-dimensional, hence proper and second countable.
3. For compact K, C(K, F) is second countable and carries the sup metric, with dist(f x, g x) ≤ dist f g.
4. Map X = {ω : tsupport ω ⊆ K} by Φ(ω) := (ω, dω)|_K; take a countable dense T ⊆ Φ(X) and pull it back by choice to D ⊆ X.
5. For ω ∈ X and ε > 0, pick η ∈ D with dist(Φω, Φη) < ε. This bounds both pointwise distances on K; off K all values are 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git diff b4d606db 7d35af49 -- GMT/ (empty)`
- `grep -rn -i 'exhaust|SeparableSpace|SecondCountable|FiniteDimensional|countable dense|tendstoUniformly' local-references/123e8435b4a2469b/project/GMT --include=*.lean`
- `grep -rn 'instance instSecondCountableTopology|instance instSeparableSpace' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn 'exists_thickening_subset_open|dist_apply_le_dist|instPseudoMetricSpace : PseudoMetricSpace C(α, β)|Dense.exists_dist_lt|exists_countable_dense|Prod.dist_eq|image_eq_one_of_notMem_mulTSupport|isCompact_iff_compactSpace|exists_nat_one_div_lt|tendstoUniformly_iff {|ext_alternating|toAlternatingMap_injective|FiniteDimensional.proper|secondCountable_of_proper|theorem of_injective' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn 'FiniteDimensional' mathlib/Mathlib/{Topology/Algebra/Module,Analysis/Normed/Module}/{Alternating,Multilinear}`
- `lake env lean /tmp/tfd-decomp/Inst.lean (synthesize FiniteDimensional / SecondCountableTopology / ProperSpace for Covector (Euclid P) n)`
- `grep -n 'abbrev TestFormOn|theorem exteriorDerivative_isTestForm|theorem tsupport_exteriorDerivative_subset|abbrev exteriorDerivative|abbrev Covector' simongmt Chapter06/{Forms,Currents}.lean`
- `dag.json scans: regex 'exhaust|countable dense|separab|SeparableSpace|IsSeparable|FiniteDimensional|ProperSpace|SecondCountable|TendstoUniformly' over node statements; duplicate lean_name scan; collision check for dor_lmbs_tfa_*`
- `git grep -l dor_lmbs_tfa over every ref (no match); git show c9c005d1:GMT/Ch07/Submission.lean (accepted dor_ims_lusin_covector_finiteDimensional proof); git show 7d35af49:GMT/Ch07/Submission.lean | grep -c covector_finiteDimensional (0)`
- `python3 -I: verifier lean_contract.validate_lean_statement and gmt-compare.contract_scope/child_modules on the three child statements; lake env lean on the three generated challenge files, /tmp/tfd-decomp/Assembly.lean and /tmp/tfd-decomp/EndToEnd.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-t-9b84f5afc6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/tfd-decomp/Inst.lean`
- `/tmp/tfd-decomp/Assembly.lean`
- `/tmp/tfd-decomp/EndToEnd.lean`
- `/tmp/tfd-decomp/challenges/compact_exhaustion_Challenge.lean`
- `/tmp/tfd-decomp/challenges/covector_findim_Challenge.lean`
- `/tmp/tfd-decomp/challenges/fixed_support_dense_Challenge.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and to this node's proof base 7d35af49 (no diff under GMT/).

No-match results:
- The project snapshot has no exhaustion, separability, countable-dense or covector finite-dimensionality declaration. Its grep hits are only unrelated FiniteDimensional variables in the Ch01–Ch05 contracts.
- Mathlib has no FiniteDimensional instance for ContinuousAlternatingMap or ContinuousMultilinearMap.
- Lean fails to synthesize FiniteDimensional, ProperSpace and SecondCountableTopology for Covector (Euclid P) n (Inst.lean).

Mathlib supplies (cited in the child proofs):
- ContinuousMap.instSecondCountableTopology and instSeparableSpace (Topology/ContinuousMap/SecondCountableSpace.lean:84,108; needs an extra import);
- ContinuousMap.instPseudoMetricSpace (comap of a uniform embedding, so its topology is compact-open) and ContinuousMap.dist_apply_le_dist (Compact.lean:79,114);
- IsCompact.exists_thickening_subset_open (Thickening.lean:439);
- Dense.exists_dist_lt (Pseudo/Defs.lean:925);
- TopologicalSpace.exists_countable_dense (Bases.lean:349);
- Prod.dist_eq, image_eq_zero_of_notMem_tsupport (to_additive of Support.lean:111), isCompact_iff_compactSpace, exists_nat_one_div_lt;
- Metric.tendstoUniformly_iff (Pseudo/Basic.lean:157);
- Module.Basis.ext_alternating, ContinuousAlternatingMap.toAlternatingMap_injective, FiniteDimensional.of_injective, FiniteDimensional.proper, secondCountable_of_proper.

SimonGMT 2b36630 supplies TestFormOn (Currents.lean:123), exteriorDerivative_isTestForm (Currents.lean:164) and tsupport_exteriorDerivative_subset (Currents.lean:182).

DAG findings:
- Four accepted nodes have exactly ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n): dor_ims_lusin_, dor_ims_sua_, imsupp_ and lcn_covector_finiteDimensional. Their accepted proof is at commit c9c005d1.
- None of them is in proof base 7d35af49, and the DAG never duplicates a lean_name, so the fact becomes the fresh sibling dor_lmbs_tfa_covector_finiteDimensional.
- No exhaustion or fixed-support density node exists.
- The proposed names collide with nothing in the DAG or in any git ref.

Lean checks:
- The three child types validate and elaborate in the exact comparator scope.
- Assembly.lean derives the exact frozen parent type from the three stubs.
- EndToEnd.lean proves all three children and the parent with axioms [propext, Classical.choice, Quot.sound] only.
- An independent reviewer re-ran these checks and returned ACCEPT.

No web source was needed; the facts used (Heine–Borel, separability of C(K, F) for compact metric K) are standard.
