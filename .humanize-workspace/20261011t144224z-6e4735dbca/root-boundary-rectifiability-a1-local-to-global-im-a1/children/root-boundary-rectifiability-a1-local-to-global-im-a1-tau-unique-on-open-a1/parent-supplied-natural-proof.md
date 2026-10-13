# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1.local_to_global_im-a1`
- Child DAG node: `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_unique_on_open-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 (comparison on overlaps) of the parent proof, with O := V_i ∩ V_{i′}, written for two arbitrary triples. As in the parent, the fundamental lemma F3 is applied to scalar functions one covector at a time, and F4 (child covector_separating) recombines them. The measure used is H itself; since the functions vanish off M₁ ∪ M₂, this is the parent's ν = H⌞(M₁ ∪ M₂) argument.

Notation. H := μHE[k] and τ_i := tauAction k M_i θ_i ξ_i. For a k-covector b let
 f_i^b(x) := θ_i(x)·ξ_i(x)(b),
 g_i^b := 1_{M_i}·f_i^b (equal to 0 off M_i),
 G^b := g_1^b − g_2^b.

Tools.
- Child tau_integrable, parts (a) and (b).
- Child covector_separating.
- Child simple_unit_rigidity.
- Mathlib F3, `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`: let O be open, μ any measure on ℝ^P, and g : ℝ^P → ℝ locally μ-integrable on O. If ∫ φ·g dμ = 0 for every C^∞ compactly supported φ with tsupport φ ⊆ O, then g(x) = 0 for μ-a.e. x ∈ O.

1. (Local integrability.) Fix b and let K ⊆ O be compact; then K ⊆ U. By tau_integrable(a), f_i^b is H-integrable on M_i ∩ K. Since M_i is H-null-measurable, 1_{M_i}·f_i^b is H-integrable on K. So G^b is integrable on every compact subset of the open set O, i.e. G^b is locally H-integrable on O.

2. (Test forms φ·b.) Let φ : ℝ^P → ℝ be C^∞ with compact support and tsupport φ ⊆ O, and put ω_φ(x) := φ(x)·b. Then:
 - ω_φ is C^∞;
 - supp ω_φ ⊆ supp φ, so ω_φ has compact support and tsupport ω_φ ⊆ tsupport φ ⊆ O ⊆ U.
 Thus ω_φ ∈ Dᵏ(U) with tsupport ω_φ ⊆ O, and the hypothesis gives τ₁(ω_φ) = τ₂(ω_φ).

3. (Identification.)
 - Pointwise, φ(x)·g_i^b(x) = 1_{M_i}(x)·θ_i(x)·ξ_i(x)(ω_φ(x)), since ξ_i(x)(φ(x)·b) = φ(x)·ξ_i(x)(b).
 - ω_φ is continuous, compactly supported, with tsupport ⊆ U. By tau_integrable(b), x ↦ θ_i(x)·ξ_i(x)(ω_φ(x)) is H-integrable on M_i. So φ·g_i^b is H-integrable.
 - Because M_i is null-measurable, ∫ φ·g_i^b dH = ∫_{M_i} θ_i·ξ_i(ω_φ) dH = τ_i(ω_φ).
 Hence ∫ φ·G^b dH = τ₁(ω_φ) − τ₂(ω_φ) = 0.

4. (F3.) Steps 1 and 3 verify the hypotheses of F3. So for H-a.e. x: if x ∈ O then G^b(x) = 0.

5. (All covectors at once.) Let b_1,…,b_L come from covector_separating. Intersecting the finitely many a.e. sets of step 4 (b = b_l): for H-a.e. x, if x ∈ O then G^{b_l}(x) = 0 for all l. For such x set c_i := 1_{M_i}(x)·θ_i(x) and W_i := c_i·ξ_i(x), a k-vector. Then W_i(b) = g_i^b(x) for every b, so W_1(b_l) = W_2(b_l) for all l. By covector_separating, W_1 = W_2, i.e. (1_{M₁}θ₁)(x)·ξ₁(x) = (1_{M₂}θ₂)(x)·ξ₂(x).

6. (Orientation.) By `orients` and null-measurability of M_i: for H-a.e. x, if x ∈ M_i then ξ_i(x) = ±simpleNVector τ for some orthonormal τ : Fin k → ℝ^P (i = 1, 2).

7. (Pointwise analysis.) Let E be the H-null union of the exceptional sets of steps 5 and 6, and let x ∈ O \ E.
 (i) x ∈ M₁ \ M₂ is impossible. Otherwise step 5 gives θ₁(x)·ξ₁(x) = 0 = 0·ξ₁(x), with ξ₁(x) = ±simpleNVector τ. Apply simple_unit_rigidity with τ' := τ, w = w' := ξ₁(x), a := θ₁(x) ≥ 0 and a' := 0. It gives θ₁(x) = 0, contradicting θ₁(x) > 0 (`pos`).
 (ii) x ∈ M₂ \ M₁ is impossible, symmetrically.
 (iii) If x ∈ M₁, then x ∈ M₂ by (i), and θ₁(x)·ξ₁(x) = θ₂(x)·ξ₂(x). Here each ξ_i(x) is ±simpleNVector of an orthonormal frame and θ_i(x) > 0. simple_unit_rigidity gives θ₁(x) = θ₂(x), and, since θ₁(x) ≠ 0, ξ₁(x) = ξ₂(x).

8. (Conclusion.)
 - By (i) and (ii), (M₁ Δ M₂) ∩ O ⊆ E, so H((M₁ Δ M₂) ∩ O) = 0.
 - By (iii), for H-a.e. x: if x ∈ M₁ ∩ O then θ₁(x) = θ₂(x) and ξ₁(x) = ξ₂(x). Since M₁ ∩ O is null-measurable, this is exactly θ₁ = θ₂ and ξ₁ = ξ₂ H⌞(M₁ ∩ O)-a.e. ∎

Formalization notes (a complete Lean proof was checked in a scratch build):
- Use the real-valued G b x := M₁.indicator (fun y => θ₁ y * ξ₁ y b) x - M₂.indicator (fun y => θ₂ y * ξ₂ y b) x. Avoid NVector-valued integrals, because `ContinuousENorm (NVector ..)` fails to synthesize.
- Step 1: `locallyIntegrableOn_iff hO.isLocallyClosed`, `integrableOn_indicator_iff hT.nullMeasurableSet`, `IntegrableOn.sub`.
- Step 2: smoothness by `unfold IsSmoothForm; exact hφ.smul contDiff_const`. Compact support by `hφc.mono` with an explicit support inclusion. The test form is ⟨fun x => φ x • b, ⟨hsmooth, hcs⟩, hts.trans hOU⟩ : TestFormOn U k.
- Step 3: `integral_indicator₀`, `integrable_indicator_iff₀`, `integral_sub`, `map_smul`.
- Step 4: `hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
- Step 5: `ae_all_iff`, then the separating property with by_cases on membership and simp_all [indicator_of_mem, indicator_of_notMem].
- Step 6: `(ae_restrict_iff'₀ hT.nullMeasurableSet).1`.
- Step 8: `ae_iff`, `measure_mono_null`, and `ae_restrict_iff'₀ (hT₁.nullMeasurableSet.inter hO.measurableSet.nullMeasurableSet)`.

## Key steps

1. For each covector b, G^b := 1_{M₁}θ₁ξ₁(b) − 1_{M₂}θ₂ξ₂(b) is locally H-integrable on O (tau_integrable (a)).
2. Testing the hypothesis with ω = φ·b gives ∫ φ·G^b dH = τ₁(φb) − τ₂(φb) = 0 for every smooth φ supported in O (integrability from tau_integrable (b)).
3. By the fundamental lemma, G^b = 0 H-a.e. on O. With a finite separating family (covector_separating), 1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂ H-a.e. on O.
4. Pointwise rigidity (simple_unit_rigidity), with θ_i > 0 and ξ_i a unit simple k-vector up to sign, gives M₁ = M₂, θ₁ = θ₂ and ξ₁ = ξ₂ a.e. on O.

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
