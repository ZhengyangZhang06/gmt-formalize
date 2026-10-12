# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.mass_representation-a1`
- Child DAG node: `root.slicing-a1.mass_representation-a1.restriction_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) with standard basis b_i = EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin P) ℝ i (i ∈ Fin P). A k-covector is α ∈ Covector (Eucl P) k (a continuous alternating k-linear map ℝ^P → ℝ) with operator norm ‖α‖; |α| := covectorEuclideanNorm α = (Σ_{I : Fin k → Fin P strictly increasing} α(b_{I(0)},…,b_{I(k−1)})²)^{1/2}. A k-vector is w ∈ NVector (Eucl P) k, a continuous linear functional on k-covectors. D^k(U) = TestFormOn U k (smooth, compactly supported forms with tsupport ⊆ U), D_k(U) = GeometricCurrentOn U k, M_W(T) = T.massOn W = sup{ENNReal.ofReal(T(ω)) : ω ∈ D^k(U), tsupport ω ⊆ W, |ω(x)| ≤ 1 ∀x} (massAdmissibleOn). CF(U) := {φ : ℝ^P → Covector (Eucl P) k : φ continuous, HasCompactSupport φ, tsupport φ ⊆ U}. All measures are Borel measures on ℝ^P; ∫_A f dμ means ∫ x in A, f x ∂μ (integral for μ.restrict A). Source: Simon, Introduction to GMT, Ch. 6, 2.7–2.9 (pp. 136–137), with Ch. 1, 4.14 (Riesz) and 1.17 (Lusin); this argument is extracted from the parent proof of slicing_mass_representation (its steps are cited as P1–P7).

This is step P5 of the parent proof. Notation: M := #(Fin k → Fin P).

1. (Norm comparison.) For every covector α and I : Fin k → Fin P, |α(b_{I(0)},…,b_{I(k−1)})| ≤ ‖α‖ (ContinuousAlternatingMap.le_opNorm and ‖b_i‖ = 1), so |α|² ≤ M‖α‖², i.e. |α| ≤ √M·‖α‖.
2. (A linear functional.) For ω ∈ D^k(U) put S₀(ω) := ∫_A v(x)(ω(x)) dμ(x). The integrand is μ-integrable by hypothesis, hence μ⌞A-integrable (μ.restrict A ≤ μ). Since each v(x) is linear, v(x)((ω + η)(x)) = v(x)(ω(x)) + v(x)(η(x)) and v(x)((cω)(x)) = c·v(x)(ω(x)); by additivity of the integral of integrable functions and homogeneity of the integral, S₀ : TestFormOn U k → ℝ is ℝ-linear.
3. (Sequential continuity.) Let (ω_j) be a sequence in D^k(U) with TestFormOnConverges ω_j 0: there is a compact K ⊆ U with tsupport ω_j ⊆ K for all j such that, for every order m, iteratedFDeriv ℝ m ω_j → iteratedFDeriv ℝ m 0 = 0 uniformly on K. For m = 0, ‖iteratedFDeriv ℝ 0 ω_j x‖ = ‖ω_j(x)‖ (norm_iteratedFDeriv_zero), so for every ε > 0 there is j₀ with ‖ω_j(x)‖ ≤ ε for all x ∈ K and j ≥ j₀. For x ∉ K, ω_j(x) = 0 and v(x)(ω_j(x)) = 0; for x ∈ K, |v(x)(ω_j(x))| ≤ |ω_j(x)| ≤ √M·‖ω_j(x)‖. Hence, for j ≥ j₀, |S₀(ω_j)| ≤ ∫_A |v(x)(ω_j(x))| dμ ≤ ∫ √M·ε·1_K dμ = √M·ε·μ(K), and μ(K) < ∞ because K is a compact subset of U. As ε > 0 is arbitrary, S₀(ω_j) → 0.
4. (Conclusion.) S := ⟨S₀, step 3⟩ is an element of GeometricCurrentOn U k, and S(ω) = ∫_A v(x)(ω(x)) dμ(x) for all ω ∈ D^k(U). ∎

## Key steps

1. |α| ≤ √M‖α‖ for the operator norm.
2. S₀(ω) := ∫_A v(ω) dμ is linear because each integrand is integrable.
3. If ω_j → 0 in D^k(U), supports lie in a compact K ⊆ U and ω_j → 0 uniformly on K, so |S₀(ω_j)| ≤ √M μ(K) sup_K ‖ω_j‖ → 0.

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
