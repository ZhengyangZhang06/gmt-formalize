# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1.covector_findim-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the fact "Λⁿ, Λ^{n+1} are finite-dimensional", used without proof in step 3 of the parent proof. Mathlib has no FiniteDimensional, ProperSpace or SecondCountableTopology instance for Covector (Euclid P) n = (Euclid P) [⋀^Fin n]→L[ℝ] ℝ, and instance synthesis fails, so the fact must be proved. The frozen type and the argument below are those of the comparator-accepted DAG declaration dor_ims_lusin_covector_finiteDimensional. Three other accepted declarations have the identical type: dor_ims_sua_covector_finiteDimensional, imsupp_covector_finiteDimensional and lcn_covector_finiteDimensional. None of them is in this branch's proof base 7d35af49, so the fact is supplied as a sibling.

Let P, n ∈ ℕ.

1. Let e = (e_0, …, e_{P−1}) be the standard basis of ℝ^P = EuclideanSpace ℝ (Fin P). In Lean: e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis.

2. Define L : Covector (Euclid P) n → ((Fin n → Fin P) → ℝ) by L(α)(I) := α(e_{I(0)}, …, e_{I(n−1)}), i.e. L α I = α (fun k => e (I k)).
 - L is ℝ-linear, because covectors are added and scaled pointwise: (α + β)(v) = α(v) + β(v) and (c • α)(v) = c · α(v) for every n-tuple v.
 - So L(α + β) = L α + L β and L(c • α) = c • L α; both hold definitionally (rfl).

3. L is injective. Suppose L α = L β.
 - Then α and β agree on every n-tuple (e_{I(0)}, …, e_{I(n−1)}) of basis vectors.
 - An alternating multilinear map is determined by its values on tuples of basis vectors. Expanding each argument in the basis e and using multilinearity writes α(v_0, …, v_{n−1}) as a finite linear combination of the values α(e_{I(0)}, …, e_{I(n−1)}). In Lean: Module.Basis.ext_alternating e, applied to fun v _ => congrFun h v.
 - Hence α and β have the same underlying alternating map. A continuous alternating map is determined by its underlying alternating map (ContinuousAlternatingMap.toAlternatingMap_injective), so α = β.

4. Conclusion. The space (Fin n → Fin P) → ℝ of real functions on a finite set is finite-dimensional. A vector space with an injective linear map into a finite-dimensional space is finite-dimensional (FiniteDimensional.of_injective L hL). Hence Covector (Euclid P) n is finite-dimensional over ℝ. ∎

## Key steps

1. Take the standard basis e of ℝ^P.
2. Define the linear map L α := (α(e ∘ I))_{I : Fin n → Fin P} into the finite-dimensional space (Fin n → Fin P) → ℝ.
3. L is injective: an alternating map is determined by its values on basis tuples (Basis.ext_alternating), and toAlternatingMap is injective.
4. Conclude by FiniteDimensional.of_injective.

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
