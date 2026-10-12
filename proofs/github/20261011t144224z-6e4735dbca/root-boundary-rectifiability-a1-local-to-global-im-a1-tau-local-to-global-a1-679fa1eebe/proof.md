# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child DAG node: `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_local_to_global-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof (the representation via a smooth partition of unity subordinate to finitely many neighbourhoods), with the local agreement taken as the hypothesis.

Notation. H := μHE[k] and τ := tauAction k M θ ξ, i.e. τ(η) = ∫_M θ(x)·ξ(x)(η(x)) dH(x). Uses child tau_integrable(b).

1. (Setup.) Let ω ∈ Dᵏ(U), let f := ω viewed as a form ℝ^P → Λᵏ, and let K := tsupport f. By the definition of Dᵏ(U), f is C^∞, K is compact, and K ⊆ U.

2. (Finite cover.) For every x ∈ U choose V_x as in the hypothesis. The open sets V_x with x ∈ K cover K, so by compactness K ⊆ ⋃_{y∈t} V_y for some finite set t ⊆ K.

3. (Partition of unity.) K is closed and covered by the finitely many open sets V_y (y ∈ t). So there are C^∞ functions χ_y : ℝ^P → ℝ (y ∈ t) with tsupport χ_y ⊆ V_y and Σ_{y∈t} χ_y(x) = 1 for all x ∈ K. This is a smooth partition of unity on K subordinate to (V_y)_{y∈t}; the index set is finite, so the sum is finite.

4. (Pieces.) For y ∈ t let g_y(x) := χ_y(x)·f(x).
 - g_y is C^∞.
 - supp g_y ⊆ supp f, so g_y has compact support and tsupport g_y ⊆ K ⊆ U. Hence g_y ∈ Dᵏ(U).
 - tsupport g_y ⊆ tsupport χ_y ⊆ V_y.

5. (Decomposition.) f = Σ_{y∈t} g_y:
 - for x ∈ K, Σ_y χ_y(x)·f(x) = (Σ_y χ_y(x))·f(x) = f(x);
 - for x ∉ K, f(x) = 0 and every term vanishes.
 Hence ω = Σ_y g_y in Dᵏ(U).

6. (Local agreement.) For each y ∈ t we have y ∈ U and tsupport g_y ⊆ V_y, so X(g_y) = τ(g_y) by the hypothesis.

7. (Linearity.) X is linear, so X(ω) = Σ_y X(g_y) = Σ_y τ(g_y). Each g_y is continuous with compact support and tsupport g_y ⊆ U, so by tau_integrable(b) the function x ↦ θ(x)·ξ(x)(g_y(x)) is H-integrable on M. Integrals of finitely many integrable functions add, and ξ(x) is linear, so
 Σ_y τ(g_y) = ∫_M Σ_y θ(x)·ξ(x)(g_y(x)) dH = ∫_M θ(x)·ξ(x)(Σ_y g_y(x)) dH = τ(ω).

8. (Conclusion.) X(ω) = τ(ω). ∎

Formalization notes (a complete Lean proof was checked in a scratch build):
- Step 2: hKc.elim_finite_subcover (fun x : K => V x).
- Step 3: SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Eucl P) (isClosed_tsupport f) (fun i : t => V i). Use `open scoped Manifold in`. Do NOT `open scoped ContDiff`: it makes ω a token.
- Step 4: put c i := (χ i : Eucl P → ℝ). Smoothness by contMDiff_iff_contDiff.mp (χ i).contMDiff, then `ContDiff.smul` after `unfold IsSmoothForm`. Compact support by `hfc.mono` with a support inclusion (HasCompactSupport.smul_left timed out). Prove the membership conjunction as a separate `have` before building the subtype.
- Step 5: `χ.sum_eq_one`, `finsum_eq_sum_of_fintype`, `Finset.sum_smul`.
- Step 7: map_sum X.toCurrent, `integral_finsetSum`, `Submodule.coe_sum`, `Finset.sum_apply`, `map_sum`, `Finset.mul_sum`.

## Key steps

1. Cover the compact set K = tsupport ω by finitely many of the neighbourhoods V_x.
2. Take a smooth partition of unity χ_y on K subordinate to them; g_y = χ_y·ω lies in Dᵏ(U) with tsupport g_y ⊆ V_y, and ω = Σ g_y.
3. X(ω) = Σ X(g_y) = Σ τ(g_y) = τ(ω), by linearity of X and of the integral (integrability from tau_integrable (b)).

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
