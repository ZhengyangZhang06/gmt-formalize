# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child DAG node: `root.boundary_rectifiability-a1.local_to_global_im-a1.covector_separating-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (F4) of the parent proof: 'the space of k-covectors on ℝ^P is finite dimensional; fix a basis b₁,…,b_L; a k-vector w is determined by the numbers w(b_l)'. Here the finite-dimensionality is proved as well.

1. (Evaluation map.) Let e_1,…,e_P be the standard basis of ℝ^P. Define ev : Λᵏ(ℝ^P) → ℝ^(Fin k → Fin P) by ev(α)(I) := α(e_{I(1)},…,e_{I(k)}). It is ℝ-linear, since evaluation is linear in α.

2. (ev is injective.) Suppose ev(α) = ev(β). Then the k-linear maps underlying α and β agree on every k-tuple of basis vectors. Expand each argument as v_j = Σ_i v_j^i e_i. By multilinearity, α(v_1,…,v_k) = Σ_I (∏_j v_j^{I(j)})·α(e_{I(1)},…,e_{I(k)}), and likewise for β. So α = β as multilinear maps, hence as continuous alternating maps.

3. (Finite dimension.) The codomain ℝ^(Fin k → Fin P) is finite-dimensional. A vector space with an injective linear map into a finite-dimensional space is finite-dimensional, so Λᵏ(ℝ^P) is finite-dimensional. Let L be its dimension and b_1,…,b_L a basis.

4. (Separation.) Let w, w' be k-vectors with w(b_l) = w'(b_l) for all l. Every covector can be written α = Σ_l c_l b_l. By linearity, w(α) = Σ_l c_l w(b_l) = Σ_l c_l w'(b_l) = w'(α). Hence w = w', since continuous linear maps are determined by their values. ∎

Formalization notes (a complete Lean proof was checked in a scratch build):
- Define `ev` as a `LinearMap` with `map_add'` and `map_smul'` proved by `rfl`.
- Injectivity: `ContinuousAlternatingMap.toAlternatingMap_injective`, then `AlternatingMap.coe_multilinearMap_injective`, then `Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun (Fin P) ℝ).toBasis)`, finishing with `congrFun h v` and `simpa`.
- `FiniteDimensional ℝ (Covector (Eucl P) k)` is not an instance. Obtain it with `Module.Finite.of_injective ev hinj`, then take `Module.finBasis ℝ (Covector (Eucl P) k)`.
- Conclude with `ContinuousLinearMap.coe_injective` and `Basis.ext`.

## Key steps

1. Evaluation on basis k-tuples is an injective linear map from Λᵏ(ℝ^P) into ℝ^(Fin k → Fin P), because multilinear maps are determined by their values on basis vectors.
2. Hence Λᵏ(ℝ^P) is finite-dimensional; take a basis b_1,…,b_L.
3. Two linear functionals that agree on a basis are equal.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean workspace GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (both identical)`
- `sed -n 200,215p mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero: any measure, LocallyIntegrableOn only)`
- `grep -n "ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'" mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean (no sigma-finiteness needed)`
- `grep -n 'theorem locallyIntegrableOn_iff' mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `grep -rn 'integrableOn_indicator_iff|integrable_indicator_iff₀|integral_indicator₀|setIntegral_congr_set|setIntegral_eq_integral_of_forall_compl_eq_zero|ae_restrict_iff'₀|ae_restrict_mem₀|ae_restrict_iUnion_iff|integral_apply' mathlib/Mathlib`
- `grep -n 'theorem exists_isSubordinate|theorem sum_eq_one|def IsSubordinate' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `grep -n 'isOpen_biUnion_countable|Countable.exists_eq_range' mathlib/Mathlib/Topology/Bases.lean mathlib/Mathlib/Data/Set/Countable.lean`
- `grep -n 'Module.Basis.ext_multilinear' mathlib/Mathlib/LinearAlgebra/Multilinear/Basis.lean`
- `grep -n 'theorem Integrable.bdd_mul' mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean; grep -n 'theorem Continuous.clm_apply' mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `#synth probes in comparator scope: ContinuousENorm (NVector (Eucl P) k) FAILS; FiniteDimensional ℝ (Covector (Eucl P) k) FAILS; SecondCountableTopology (Covector ..) FAILS; ContinuousEval (NVector ..) (Covector ..) ℝ FAILS; @PseudoEMetricSpace.pseudoMetrizableSpace (NVector (Eucl P) k) _ SUCCEEDS (topologies defeq by rfl)`
- `inspect simongmt Chapter06/{Currents,CurrentLocalEquality,FormsDuality,Forms}.lean and Chapter03/Rectifiable.lean (TestFormOn, GeometricCurrentOn, NVector, simpleNVector, wedgeCovectors_apply_det, HasWeightedApproximateTangentSpaceAt, CountablyRectifiable, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero)`
- `grep -n 'integer multiplicity|6.3' book/chapter-06.txt (3.1 definition; 6.3 proof is one line)`
- `python3 gmt-compare.py child_modules (contract mode) for the 7 child statements and the parent statement; lean_contract.validate_lean_statement on each`
- `lake build GMT.Ch06.Submission (scratch /tmp/ltg-decomp = git archive d8d46c9, .lake/packages -> lake-packages-25730c7c), then with the 7 child proofs appended`
- `lake env lean gen/Challenge_*.lean (7 elaborate); lake env lean Scratch/Sol_*.lean + #print axioms (7 children: [propext, Classical.choice, Quot.sound]; parent: only sorryAx from sibling br_weightedTangent_congr)`
- `python3 scan of dag.json lean_name/theorems for 'ltg_' (no match); grep -rn 'ltg_' simongmt (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ltg-decomp/GMT/Ch06/Submission.lean`
- `/tmp/ltg-decomp/Scratch/Assembly.lean`
- `/tmp/ltg-decomp/Scratch/C0.lean`
- `/tmp/ltg-decomp/Scratch/C1.lean`
- `/tmp/ltg-decomp/Scratch/C2.lean`
- `/tmp/ltg-decomp/Scratch/C3.lean`
- `/tmp/ltg-decomp/Scratch/C4a.lean`
- `/tmp/ltg-decomp/Scratch/C4b.lean`
- `/tmp/ltg-decomp/Scratch/C5.lean`
- `/tmp/ltg-decomp/Scratch/Inst4.lean`
- `/tmp/ltg-decomp/Scratch/Sol_parent.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; the snapshot Contract, the workspace Contract and Submission are byte-identical. Mathlib supplies everything the children need:
- the open-set fundamental lemma `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, valid for any measure (no σ-finiteness) and locally integrable real functions;
- `locallyIntegrableOn_iff` for locally closed sets;
- null-measurable indicator integrability and integral lemmas;
- `setIntegral_congr_set` and `setIntegral_eq_integral_of_forall_compl_eq_zero`, which need no integrability;
- countable a.e. unions (`ae_all_iff`, `ae_restrict_iUnion_iff`, `aestronglyMeasurable_iUnion_iff`);
- `SmoothPartitionOfUnity.exists_isSubordinate`, `TopologicalSpace.isOpen_biUnion_countable`, `Module.Basis.ext_multilinear`, `Integrable.bdd_mul` and `Continuous.clm_apply`.

SimonGMT supplies `wedgeCovectors_apply_det`, `simpleNVector_apply`, `countablyRectifiable_iUnion`, `CountablyRectifiable.mono` and `countablyRectifiable_of_measure_zero`.

Instance probes in the comparator scope show that `ContinuousENorm`, `ContinuousEval` and `PseudoMetrizableSpace` for NVector, and `FiniteDimensional` for Covector, are not found by instance search. Hence:
- statements avoid NVector-valued integrability;
- finite-dimensionality is a child (covector_separating);
- `PseudoMetrizableSpace` is supplied manually inside proofs (topologies defeq by rfl).

In a scratch build at the frozen commit:
- all seven child types elaborate in the exact comparator child scope;
- all seven are fully proved with axioms [propext, Classical.choice, Quot.sound];
- the selected theorem's assembly typechecks from them plus the sibling `br_weightedTangent_congr` at its frozen type (the only sorry).

No `ltg_*` name exists in the DAG or in SimonGMT. The book's 6.3 proof is one line, so the child proofs come from the supplied parent proof.
