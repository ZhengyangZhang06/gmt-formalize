# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.mass_representation-a1`
- Child DAG node: `root.slicing-a1.mass_representation-a1.continuous_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) with standard basis b_i = EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin P) ℝ i (i ∈ Fin P). A k-covector is α ∈ Covector (Eucl P) k (a continuous alternating k-linear map ℝ^P → ℝ) with operator norm ‖α‖; |α| := covectorEuclideanNorm α = (Σ_{I : Fin k → Fin P strictly increasing} α(b_{I(0)},…,b_{I(k−1)})²)^{1/2}. A k-vector is w ∈ NVector (Eucl P) k, a continuous linear functional on k-covectors. D^k(U) = TestFormOn U k (smooth, compactly supported forms with tsupport ⊆ U), D_k(U) = GeometricCurrentOn U k, M_W(T) = T.massOn W = sup{ENNReal.ofReal(T(ω)) : ω ∈ D^k(U), tsupport ω ⊆ W, |ω(x)| ≤ 1 ∀x} (massAdmissibleOn). CF(U) := {φ : ℝ^P → Covector (Eucl P) k : φ continuous, HasCompactSupport φ, tsupport φ ⊆ U}. All measures are Borel measures on ℝ^P; ∫_A f dμ means ∫ x in A, f x ∂μ (integral for μ.restrict A). Source: Simon, Introduction to GMT, Ch. 6, 2.7–2.9 (pp. 136–137), with Ch. 1, 4.14 (Riesz) and 1.17 (Lusin); this argument is extracted from the parent proof of slicing_mass_representation (its steps are cited as P1–P7).

This is step P6(v) of the parent proof (mollification of a continuous admissible form). By the sibling theorem smr_covector_coord_isometry, |α| = ‖Jα‖ for a linear J, so |·| satisfies the triangle inequality and |cα| = |c|·|α|.

1. (A compact neighbourhood.) tsupport φ is compact and contained in the open set W. Choose an open V with tsupport φ ⊆ V, closure V compact and closure V ⊆ W (exists_open_between_and_isCompact_closure). Put K′ := closure V; K′ is a compact subset of W ⊆ U, so μ(K′) < ∞. Also V ⊆ U.
2. (Approximants.) For j ∈ ℕ let δ_j := 1/(j+1). By the sibling theorem smr_exists_testForm_uniform_approx (open set V ⊆ U, ε := δ_j) there is η_j ∈ D^k(U) with tsupport η_j ⊆ V and |φ(x) − η_j(x)| ≤ δ_j for all x. Let ζ_j := (1 + δ_j)⁻¹·η_j ∈ D^k(U) (TestFormOn U k is a submodule).
3. (Admissibility.) tsupport ζ_j ⊆ tsupport η_j ⊆ V ⊆ W, and |ζ_j(x)| = (1 + δ_j)⁻¹|η_j(x)| ≤ (1 + δ_j)⁻¹(|φ(x)| + δ_j) ≤ 1. So ζ_j ∈ massAdmissibleOn U k W and ENNReal.ofReal(S(ζ_j)) ≤ M_W(S) (GeometricCurrentOn.le_massOn).
4. (Uniform closeness.) For all x: |ζ_j(x) − φ(x)| ≤ |ζ_j(x) − η_j(x)| + |η_j(x) − φ(x)| = (1 − (1 + δ_j)⁻¹)|η_j(x)| + |η_j(x) − φ(x)| ≤ (δ_j/(1 + δ_j))(1 + δ_j) + δ_j = 2δ_j (using |η_j(x)| ≤ 1 + δ_j). Moreover ζ_j and φ vanish off V ⊆ K′. Hence for every x, |v(x)(ζ_j(x)) − v(x)(φ(x))| = |v(x)(ζ_j(x) − φ(x))| ≤ |ζ_j(x) − φ(x)| ≤ 2δ_j·1_{K′}(x).
5. (Integrability of v(φ).) By step 4, v(x)(ζ_j(x)) → v(x)(φ(x)) for every x. Each x ↦ v(x)(ζ_j(x)) is μ-integrable (hypothesis), hence AE-strongly measurable for μ⌞A; therefore so is the pointwise limit x ↦ v(x)(φ(x)) (aestronglyMeasurable_of_tendsto_ae). It is bounded by |φ(x)| ≤ 1_{K′}(x) (φ = 0 off V) and μ(K′) < ∞, so it is μ⌞A-integrable; similarly each v(ζ_j) is μ⌞A-integrable.
6. (Convergence.) |S(ζ_j) − ∫_A v(φ) dμ| = |∫_A (v(x)(ζ_j(x)) − v(x)(φ(x))) dμ| ≤ ∫_A 2δ_j·1_{K′} dμ ≤ 2δ_j·μ(K′) → 0 (μ⌞A ≤ μ). Hence S(ζ_j) → ∫_A v(x)(φ(x)) dμ, and by continuity of ENNReal.ofReal, ENNReal.ofReal(S(ζ_j)) → ENNReal.ofReal(∫_A v(x)(φ(x)) dμ).
7. (Conclusion.) Every term of this sequence is ≤ M_W(S) (step 3), so its limit satisfies ENNReal.ofReal(∫_A v(x)(φ(x)) dμ) ≤ M_W(S) (le_of_tendsto'). ∎

## Key steps

1. Open V with tsupport φ ⊆ V, K′ := closure V compact ⊆ W, μ(K′) < ∞.
2. Smooth approximants η_j ∈ D^k(U) supported in V with |φ − η_j| ≤ δ_j; rescaled ζ_j := η_j/(1+δ_j) are admissible for M_W(S).
3. |v(ζ_j) − v(φ)| ≤ 2δ_j·1_{K′}; v(φ) is AE-strongly measurable as a pointwise limit and integrable.
4. S(ζ_j) → ∫_A v(φ) dμ; pass to the limit in ofReal(S(ζ_j)) ≤ M_W(S).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean vs GMT/Ch06/Submission.lean (identical, sha256 ea3ee0dd…); read Contract.lean: Eucl, CompactlyContainedOpen, IsMeasureRepresentation, IsRestriction`
- `read simongmt Chapter06/{Mass,Currents,Forms,FormsDuality,Representation,FormSupNorm}.lean: covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn, TestFormOn, TestFormOnConverges, GeometricCurrentOn, NVector, SimonMultiIndex, wedgeCovectors_apply_det, euclideanCovectorCoordinate`
- `grep -n simon_theorem_4_14 simongmt Chapter01/RadonPolarRepresentation.lean; IsLocallyBoundedCcFunctional (VectorFunctionalEnvelope.lean); IsRadonOuterMeasure, toCaratheodoryMeasure_apply_all, isOpenSigmaFinite_of_finite_compacts (RadonOuterMeasure.lean); toBorelMeasure_apply_all (Basic.lean); exists_borel_subset_mod_null (RegularityCompletion.lean)`
- `grep -n theorem simongmt Chapter01/Lusin.lean (exists_isClosed_continuousOn_of_measurable, simon_theorem_1_17)`
- `grep -rn TietzeExtension mathlib/Mathlib (ContinuousMap.exists_restrict_eq; Set.instTietzeExtensionUnitClosedBall in Analysis/Complex/Tietze.lean)`
- `grep mathlib for UniformContinuous.exists_contDiff_dist_le, exists_open_between_and_isCompact_closure, exists_contDiff_support_eq_eq_one_iff, exists_continuous_one_zero_of_isCompact, instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace, MeasurableSet.exists_lt_isCompact_of_ne_top, IsCompact.exists_cthickening_subset_open, tendsto_measure_iInter_atTop, integral_trim, MeasurableEmbedding.integral_map, NullMeasurable.aemeasurable, aestronglyMeasurable_of_tendsto_ae, enorm_integral_le_lintegral_enorm, norm_iteratedFDeriv_zero, abs_real_inner_le_norm`
- `python3 listing of dag.json lean_name/lean_statement for all nodes; grep -rl of the nine proposed smr_ names in dag.json, nodes/ and simongmt (no matches)`
- `git show 26d9d850:GMT/Ch06/Submission.lean (kernel-checked cmb_exists_testForm_uniform_approx); git show 6c6b4b27 (cmb_covector_eq_sum_coord_smul_wedge); git show 7cdd0aed (submission adding imports)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: namespace GMT.Ch06 + opens)`
- `lake build GMT.Ch06.Submission in scratch /tmp/smr-split-check (frozen d8d46c9, pinned shared packages)`
- `lake env lean Scratch/Challenge_*.lean (9 child types in comparator child scope, 0 errors); Scratch/Instances.lean; Scratch/Assembly.lean; Scratch/Glue5.lean; ReviewScratch/AssemblyAx.lean; ReviewScratch/UpperBound.lean (#print axioms); Scratch/Avail.lean and Scratch/Avail2.lean (which library lemmas need extra imports)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mollify-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RegularityCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/smr-split-check/Scratch/Assembly.lean`
- `/tmp/smr-split-check/Scratch/Glue5.lean`
- `/tmp/smr-split-check/ReviewScratch/UpperBound.lean`
- `/tmp/smr-split-check/ReviewScratch/AssemblyAx.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract and Submission, so child statements use only contract, SimonGMT and Mathlib names.

Available in SimonGMT:
- currents, massOn and covectorEuclideanNorm;
- wedgeCovectors_apply_det;
- Riesz on any locally compact Hausdorff space (simon_theorem_4_14: Radon outer measure, Carathéodory-measurable unit field);
- the Carathéodory-to-Borel tools (toBorelMeasure_apply_all, toCaratheodoryMeasure_apply_all, exists_borel_subset_mod_null, isOpenSigmaFinite_of_finite_compacts);
- Lusin's theorem (exists_isClosed_continuousOn_of_measurable).

Available in Mathlib: Tietze (including the closed unit ball of ℝ^N), Urysohn, smooth approximation and convolution, inner regularity of every Borel measure on ℝ^P, integral_trim and MeasurableEmbedding.integral_map. simon_theorem_4_14, Lusin and Tietze are not imported by GMT.Ch06.Submission; adding the corresponding imports compiles.

No existing declaration states the representation, the restriction current or the restriction mass formula. Kernel-checked templates exist in other branches for the approximation lemma (26d9d850) and the covector expansion (6c6b4b27); their names are reserved by active branches, so fresh smr_ names are used, none of which occur in the DAG, nodes/ or simongmt.

All nine child types elaborate in the comparator child scope. The parent's frozen type is kernel-checked from continuous_extension, riesz_forms, restriction_current and restriction_mass. riesz_forms is kernel-checked from covector_isometry and riesz_borel. The ≥ half of restriction_mass is kernel-checked from unit_form_density and continuous_mass_bound; its ≤ half is kernel-checked outright with axioms [propext, Classical.choice, Quot.sound]. These checks do not certify the analytic child proofs.
