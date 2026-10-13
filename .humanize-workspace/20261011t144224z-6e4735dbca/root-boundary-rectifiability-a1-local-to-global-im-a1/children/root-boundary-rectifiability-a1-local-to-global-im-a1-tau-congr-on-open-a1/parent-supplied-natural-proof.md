# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child DAG node: `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_congr_on_open-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the locality argument inside step 7 of the parent proof ('the i-th integrand vanishes outside V_i, and on V_i the triples agree up to H-null sets, so ∫_{M_i}… = ∫_{M∩V_i}… = ∫_M …'), stated for arbitrary data.

Notation. H := μHE[k]. τ(M,θ,ξ)(ω) = ∫_M θ(x)·ξ(x)(ω(x)) dH(x) is a Bochner integral, equal to 0 when the integrand is not integrable. No integrability or measurability is assumed, and none is needed.

1. (Vanishing off V.) Let f(x) := θ(x)·ξ(x)(ω(x)) and f'(x) := θ'(x)·ξ'(x)(ω(x)). If x ∉ V, then x ∉ tsupport ω, so ω(x) = 0, and f(x) = f'(x) = 0 because ξ(x) and ξ'(x) are linear.

2. (Restricting to V.) For any A ⊆ ℝ^P and any function h vanishing off V: ∫_A h dH = ∫_{A∩V} h dH.
 - For the measure H⌞A, the integral of h over V equals its integral over the whole space, since h vanishes off V. This identity of Bochner integrals needs no integrability.
 - (H⌞A)⌞V = H⌞(V ∩ A), because V is open and hence measurable.

3. By steps 1–2: τ(M,θ,ξ)(ω) = ∫_{M∩V} f dH and τ(M',θ',ξ')(ω) = ∫_{M'∩V} f' dH.

4. (Sets.) (M ∩ V) Δ (M' ∩ V) = (M Δ M') ∩ V is H-null, so M ∩ V and M' ∩ V are H-a.e. equal sets. Integrals over a.e.-equal sets coincide, so ∫_{M'∩V} f' dH = ∫_{M∩V} f' dH.

5. (Integrands.) By hypothesis θ = θ' and ξ = ξ' H⌞(M ∩ V)-a.e., so f = f' H⌞(M ∩ V)-a.e., and ∫_{M∩V} f dH = ∫_{M∩V} f' dH.

6. (Conclusion.) By steps 3–5, τ(M,θ,ξ)(ω) = ∫_{M∩V} f dH = ∫_{M∩V} f' dH = ∫_{M'∩V} f' dH = τ(M',θ',ξ')(ω). ∎

Formalization notes (a complete Lean proof was checked in a scratch build):
- Step 1: `image_eq_zero_of_notMem_tsupport`.
- Step 2: `setIntegral_eq_integral_of_forall_compl_eq_zero` with (μ := H.restrict A), then `Measure.restrict_restrict hV.measurableSet` and `inter_comm`.
- Step 4: `ae_eq_set` with two applications of `measure_mono_null` to the null set, then `setIntegral_congr_set`.
- Step 5: `integral_congr_ae` with `filter_upwards`.

## Key steps

1. Both integrands vanish off V, since ω = 0 off tsupport ω ⊆ V.
2. Hence ∫_M = ∫_{M∩V} and ∫_{M'} = ∫_{M'∩V}, by restricting to the measurable set V.
3. M ∩ V and M' ∩ V are H-a.e. equal sets, and the integrands agree H⌞(M ∩ V)-a.e., so the integrals coincide.

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
