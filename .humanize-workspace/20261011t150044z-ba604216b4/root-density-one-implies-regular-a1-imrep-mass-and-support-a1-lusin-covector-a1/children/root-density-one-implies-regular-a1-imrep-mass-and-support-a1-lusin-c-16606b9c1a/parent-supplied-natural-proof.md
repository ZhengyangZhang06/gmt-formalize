# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1`
- Child DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1.covector_finite_dimensional-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the "Notation" paragraph of the parent proof. It asserts that Λ := Covector (Euclid P) n is a finite-dimensional real normed space and uses this only to get a countable basis of open sets of Λ. The pinned Mathlib has no FiniteDimensional instance for continuous alternating maps, so the fact is proved here.
Notation: E := ℝ^P = EuclideanSpace ℝ (Fin P). Λ := Covector E n = E [⋀^Fin n]→L[ℝ] ℝ is the space of continuous alternating n-linear forms on E, with pointwise addition and scalar multiplication. For I : Fin n → Fin P, e ∘ I denotes the n-tuple (e_{I(i)})_{i ∈ Fin n}.
1. (Basis.) Let e = (e_i)_{i ∈ Fin P} be the standard basis of E: EuclideanSpace.basisFun (Fin P) ℝ, viewed as a Module.Basis (Fin P) ℝ E via .toBasis.
2. (Evaluation map.) Define L : Λ → ((Fin n → Fin P) → ℝ) by L(α)(I) := α(e ∘ I) for every index map I : Fin n → Fin P. For fixed I, the map α ↦ α(e ∘ I) is additive and ℝ-homogeneous, because (α + β)(v) = α(v) + β(v) and (c·α)(v) = c·α(v). Hence L is ℝ-linear.
3. (Injectivity.) Let α, β ∈ Λ with L(α) = L(β). Then α(e ∘ v) = β(e ∘ v) for every v : Fin n → Fin P, in particular for every injective v.
 An alternating n-linear map on a module with basis e is determined by its values on the tuples e ∘ v with v injective (Module.Basis.ext_alternating). [Directly: write each argument as x_j = Σ_i x_j^i e_i and expand by multilinearity. This gives α(x) = Σ_{I : Fin n → Fin P} (∏_{j ∈ Fin n} x_j^{I(j)}) α(e ∘ I), so α is determined by the numbers α(e ∘ I).]
 Hence the underlying alternating maps of α and β coincide. A continuous alternating map is determined by its underlying alternating map (ContinuousAlternatingMap.toAlternatingMap_injective), so α = β. Thus L is injective.
4. (Conclusion.) The codomain (Fin n → Fin P) → ℝ is a finite-dimensional real vector space, because the index type Fin n → Fin P is finite (it has P^n elements). A vector space with an injective linear map into a finite-dimensional space is finite-dimensional (FiniteDimensional.of_injective, applied to L and step 3). Therefore Covector (Euclid P) n is finite-dimensional over ℝ for all P and n. ∎

## Key steps

1. Fix the standard basis e of ℝ^P: (EuclideanSpace.basisFun (Fin P) ℝ).toBasis.
2. L(α) := (α(e ∘ I))_{I : Fin n → Fin P} is an ℝ-linear map from Covector (Euclid P) n to (Fin n → Fin P) → ℝ.
3. L is injective: Module.Basis.ext_alternating identifies the underlying alternating maps, and ContinuousAlternatingMap.toAlternatingMap_injective identifies the continuous ones.
4. (Fin n → Fin P) → ℝ is finite-dimensional, so FiniteDimensional.of_injective L gives FiniteDimensional ℝ (Covector (Euclid P) n).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp snapshot project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD`
- `grep -rn -i lusin <snapshot>/mathlib/Mathlib/{MeasureTheory,Topology,Analysis}`
- `grep -n 'theorem|lemma|instance' MeasureTheory/Measure/RegularityCompacts.lean; grep -n 'exists_isCompact_sdiff_lt|exists_isCompact_lt_add|exists_isCompact_isClosed_sdiff_lt|InnerRegularCompactLTTop' MeasureTheory/Measure/Regular.lean`
- `grep -rln 'ContinuousAlternatingMap|ContinuousMultilinearMap' <snapshot>/mathlib/Mathlib | xargs grep -ln 'FiniteDimensional|Module.Finite|SecondCountableTopology|SeparableSpace'`
- `grep -n of_injective LinearAlgebra/FiniteDimensional/Defs.lean; grep -n 'secondCountable_of_proper|proper_real' Topology/MetricSpace/ProperSpace.lean Analysis/Normed/Module/FiniteDimension.lean`
- `grep -rn 'SecondCountableTopology|FiniteDimensional|SeparableSpace' simongmt/Poincare/SimonGMT/Chapter06/; grep -n 'abbrev Covector' Chapter06/Forms.lean`
- `python3 -I scan of dag.json nodes: lean_name set, 'lusin', 'SecondCountableTopology', 'FiniteDimensional ℝ (Covector', status of dor_ims_sua_covector_finiteDimensional / imsupp_covector_finiteDimensional`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') and child_modules shape`
- `grep -n -i lusin book/chapter-01.txt; sed -n 300,400p book/chapter-01.txt (Simon 1.17)`
- `lake env lean /tmp/lusin-decomp/{Probe,Probe2,Assembly,C1,C2}.lean and /tmp/lusin-decomp/final/Final.lean (#synth probes, #print axioms)`
- `web (standard): Lusin's theorem second-countable topological space measurable function compact set continuous restriction proof countable basis`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-lusin-covector-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-8f5d9ea2e2/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/lusin-decomp/final/Final.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical.

Not available in the Submission scope (#synth / fail_if_success):
- Lusin's continuity theorem. Mathlib has only Lusin–Souslin and Lusin separation (Constructions/Polish/Basic.lean), which justifies child lusin_measurable.
- FiniteDimensional, SecondCountableTopology, ProperSpace and MeasurableSpace instances on Covector (Euclid P) n = E [⋀^Fin n]→L[ℝ] ℝ. No Mathlib file links continuous alternating or multilinear maps to finite-dimensionality, which justifies child covector_finite_dimensional.
- RegularityCompacts.lean is not imported, so an arbitrary μ is not InnerRegularCompactLTTop.

Available:
- μ.restrict A with μ A ≠ ∞ is IsFiniteMeasure, hence Regular (Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure), hence InnerRegularCompactLTTop. MeasurableSet.exists_isCompact_sdiff_lt then gives the compact approximations.
- ENNReal.exists_pos_sum_of_countable', TopologicalSpace.exists_countable_basis, IsTopologicalBasis.continuous_iff, continuousOn_iff_continuous_domRestrict.
- FiniteDimensional.of_injective, Module.Basis.ext_alternating, ContinuousAlternatingMap.toAlternatingMap_injective; FiniteDimensional.proper_real then secondCountable_of_proper.

DAG and naming:
- The same FiniteDimensional type is reserved as dor_ims_sua_covector_finiteDimensional (decomposing) and imsupp_covector_finiteDimensional (comparing). Neither is accepted, so the unique name dor_ims_lusin_covector_finiteDimensional is used.
- Neither proposed name occurs in dag.json, GMT/, simongmt or the run directory.
- The comparator child scope is the 7 replayed commands (open…, namespace GMT.Ch07, opens, noncomputable section, end).

Lean checks (/tmp/lusin-decomp/final/Final.lean):
- Both children are fully proved.
- The parent is assembled only from the two children.
- Comparator-shaped targets close by `exact Submission.X`.
- All axioms are [propext, Classical.choice, Quot.sound].
- An independent reviewer reproduced these results.

Sources: Simon 1.17 (book/chapter-01.txt lines 344–380) prints a level-set proof for a real-valued target and a closed C. The parent's countable-basis proof matches the second-countable form in https://math.univ-lyon1.fr/~santambrogio/Lusin.pdf and https://arxiv.org/pdf/math/0406370.
