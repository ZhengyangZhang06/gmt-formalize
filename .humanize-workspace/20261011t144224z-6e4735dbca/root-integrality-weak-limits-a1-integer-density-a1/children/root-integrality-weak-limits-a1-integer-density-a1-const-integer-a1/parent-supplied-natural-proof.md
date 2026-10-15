# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the second half of Step 8 of the parent proof ("By iwl_top_dim_integrality, c[[B_1ⁿ(0)]] is i.m. … therefore c ∈ ℤ"), stated for an arbitrary nonempty open U ⊆ ℝⁿ. This is the final line of the printed Proof of 8.2: "θ ≡ θ(x) in B_1ⁿ(0); thus θ(x) ∈ ℤ".

Conventions.
- n := m + 1 and ℝⁿ := Eucl n with standard basis e = (e_1, …, e_n), e_i := EuclideanSpace.single i 1.
- Hⁿ := μHE[n] on ℝⁿ. It equals Lebesgue measure (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
- "i.m." means IsIntegerMultiplicity.

1. Representation. Since X is i.m., there are M″ ⊆ U, θ″ and ξ″ with:
 - IsRectifiableTriple U n M″ θ″ ξ″;
 - θ″(y) ∈ ℕ for y ∈ M″ (and θ″ > 0 there);
 - X(ω) = ∫_{M″} θ″(y)ξ″(y)(ω(y)) dy for every ω ∈ D^n(U).

2. The orientation is ±e_1∧⋯∧e_n. Let vol be the determinant of the standard basis e (Basis.det, an AlternatingMap), made a continuous alternating map (AlternatingMap.mkContinuous, or toContinuousAlternatingMap, in finite dimension). Then vol(e) = 1, and every n-covector α on ℝⁿ satisfies α = α(e)·vol (Mathlib AlternatingMap.eq_smul_basis_det, applied to α.toAlternatingMap). By the orients field there is an Hⁿ-null N₁ such that for y ∈ M″ ∖ N₁ we have ξ″(y) = ±simpleNVector τ_y for some orthonormal family τ_y of n vectors in ℝⁿ. For such y and every α,
  ξ″(y)(α) = ±α(τ_y) = ±α(e)·vol(τ_y) = σ″(y)·α(e), with σ″(y) := ±det_e(τ_y).
 det_e(τ_y)² = det(Gram matrix of τ_y) = det(I) = 1, so σ″(y) ∈ {1, −1}. Alternatively: the orthonormal family τ_y of n = dim ℝⁿ vectors is an orthonormal basis (basisOfOrthonormalOfCardEqFinrank), and Mathlib OrthonormalBasis.det_to_matrix_orthonormalBasis_real gives det_e(τ_y) = ±1. Moreover σ″(y) = ξ″(y)(vol) for y ∈ M″ ∖ N₁, so σ″ is AE-strongly measurable on M″, because ξ″ is.

3. Testing with a·vol. Let a ∈ C_c^∞(ℝⁿ) with tsupport a ⊆ U. Then ω := a·vol is in D^n(U), and ω(y)(e) = a(y).
 - By the hypothesis on X: X(ω) = c∫_U a(y) dy.
 - By steps 1 and 2: X(ω) = ∫_{M″} θ″(y)σ″(y)a(y) dy.
 Hence ∫_U g(y)a(y) dy = 0 with g := c·1_U − 1_{M″}θ″σ″, for every such a.

4. Fundamental lemma.
 - g is locally integrable on U: θ″ is integrable on M″ ∩ K for compact K ⊆ U (integrableOn), |σ″| = 1 a.e. on M″, and σ″ is AE-strongly measurable.
 - By the fundamental lemma of the calculus of variations on the open set U (Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero), g = 0 Lebesgue-a.e. on U.

5. Conclusion.
 - If c = 0, then c = (0 : ℤ).
 - Assume c ≠ 0. On U ∖ M″, g = c ≠ 0, so Lⁿ(U ∖ M″) = 0.
 - U is open and nonempty, so Lⁿ(U) > 0.
 - Hence the set of y ∈ U ∩ M″ ∖ N₁ with g(y) = 0 has positive measure, in particular it is nonempty. For such y, c = θ″(y)σ″(y) with θ″(y) ∈ ℕ and σ″(y) ∈ {±1}.
 - So c = ±θ″(y) ∈ ℤ, i.e. c = k for some k ∈ ℤ. ∎

Uses only Mathlib (EuclideanSpace.euclideanHausdorffMeasure_eq_volume, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero).

## Key steps

1. X = τ(M″,θ″,ξ″) with θ″ ∈ ℕ on M″.
2. For a.e. y ∈ M″, ξ″(y)(α) = σ″(y)α(e) with σ″(y) = ±det_e(τ_y) ∈ {±1}.
3. Testing with a·vol: ∫_U (c·1_U − 1_{M″}θ″σ″)·a = 0 for all a ∈ C_c^∞(U).
4. Fundamental lemma: c·1_U = 1_{M″}θ″σ″ a.e. on U.
5. If c ≠ 0, then Lⁿ(U ∖ M″) = 0 and some y ∈ M″ ∩ U has c = θ″(y)σ″(y) ∈ ℤ.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical; imports Densities, Rectifiable, Mass, FormsDuality, CurrentLocalEquality only)`
- `python3 scans of dag.json: lean_name/status/depends_on of all nodes (262 now); no ind_* names; statuses of iwl_*, br_weightedTangent_congr, br_restrictDomain_isIntegerMultiplicity, cmb_*, rectifiability_density_comparison, slicing_representation_unique, ltg_tau_integrable, lpf_wtc_blowup_setIntegral_image, fiw_ims_tt_unit_bound`
- `grep -n 'def \|theorem ' simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward,FormsDuality,FormSupNorm}.lean`
- `sed -n 1,130p; 270,370p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasWeightedApproximateTangentSpaceAt)`
- `grep dimensionalUpperDensity|dimensionalDensityQuotient|realUnitBallVolume|simon_theorem_4_16_compact_metrizable|finiteMeasure_tendsto_subseq_of_compact_metrizable|simon_theorem_3_3 simongmt/Poincare/SimonGMT/Chapter01`
- `grep -rn ae_tendsto_average_norm_sub|Besicovitch.tendsto_filterAt|vitaliFamily mathlib/Mathlib/MeasureTheory/Covering`
- `grep -n euclideanHausdorffMeasure_homothety_image|euclideanHausdorffMeasure_smul₀|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|Isometry.map_euclideanHausdorffMeasure mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn isCompact_setOfPred_finiteMeasure_le_of_isCompact|FiniteMeasure.limsup_measure_closed_le_of_tendsto|lintegral_liminf_le|IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|norm_fderiv_le_of_lipschitz|AlternatingMap.eq_smul_basis_det|exists_contDiff_zero_iff_one_iff_of_isClosed|IsCompact.exists_cthickening_subset_open|setIntegral_eq_of_subset_of_ae_sdiff_eq_zero|extraction_of_frequently_atTop|frequently_lt_of_liminf_lt|OrthonormalBasis.det_to_matrix_orthonormalBasis_real|MeasurableEmbedding.integrable_map_iff|aestronglyMeasurable_iUnion_iff|ae_restrict_iff'₀ mathlib/Mathlib`
- `sed -n 2400,2500p book/chapter-06.txt (printed Proof of 8.2, displays (7)-(10))`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') + lean_contract.validate_lean_statement on the 7 child statements`
- `lake env lean /tmp/ind-decomp-scratch/{Stmts,ScopeCheck,Assembly}.lean (#print axioms IndAssemblyCheck.parent)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ind-decomp-scratch/Stmts.lean`
- `/tmp/ind-decomp-scratch/ScopeCheck.lean`
- `/tmp/ind-decomp-scratch/Assembly_checked.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 Contract and a byte-identical Submission. Its imports are Mass, FormsDuality, CurrentLocalEquality, Densities and Rectifiable, but not AffineCurrentPushforward. So no child statement mentions affinePushforward; the child ind_rescaled_current states the push-forward through its action on pulled-back test forms.

Scratch Lean checks of the frozen project:
- All 7 child statements pass the comparator's validate_lean_statement and elaborate in the contract_scope replay at main_theorem.
- `exact Submission.<name>` resolves for each child.
- IndAssemblyCheck.parent derives the exact frozen iwl_integer_density type from the child types plus the frozen types of iwl_restriction_weak_limit, iwl_smooth_pushforward and iwl_top_dim_integrality. Its only axioms are propext, Classical.choice and Quot.sound.

SimonGMT supplies GeometricCurrentOn.affinePushforward (with boundary_affinePushforward, affinePullbackForm_isTestForm, TestFormOnConverges.affinePullback), restrictDomain, massOn_mono and le_massOn, blowUpMap, the definition of HasWeightedApproximateTangentSpaceAt, dimensionalUpperDensity with realUnitBallVolume, and finiteMeasure_tendsto_subseq_of_compact_metrizable / simon_theorem_4_16_compact_metrizable.

Mathlib supplies Besicovitch.vitaliFamily, VitaliFamily.ae_tendsto_average_norm_sub, Besicovitch.tendsto_filterAt, euclideanHausdorffMeasure_homothety_image, euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure, FiniteMeasure.limsup_measure_closed_le_of_tendsto, lintegral_liminf_le, IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, norm_fderiv_le_of_lipschitz, AlternatingMap.eq_smul_basis_det, exists_contDiff_zero_iff_one_iff_of_isClosed, IsCompact.exists_cthickening_subset_open, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero and extraction_of_frequently_atTop. Mathlib proves metrizability of the weak topology only for probability measures.

Accepted DAG declarations reused by the child proofs: iwl_restriction_theory, rectifiability_density_comparison, br_weightedTangent_congr, br_restrictDomain_isIntegerMultiplicity, cmb_exists_countable_dense_testForms, cmb_abs_apply_le_of_massOn_le, slicing_representation_unique, ltg_tau_integrable and lpf_wtc_blowup_setIntegral_image. iwl_restriction_weak_limit, iwl_smooth_pushforward and iwl_top_dim_integrality are unaccepted and enter only as hypotheses.

The printed Proof of 8.2 (book chapter-06 lines 2400–2500) matches the supplied Step 11. No ind_* names exist in the DAG or the libraries. These checks do not certify the analytic child proofs.
