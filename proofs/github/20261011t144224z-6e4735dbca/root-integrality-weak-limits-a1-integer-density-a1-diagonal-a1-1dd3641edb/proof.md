# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.diagonal-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the selection argument of Step 4 of the parent proof (the printed "(8) remains valid with T_{j′} instead of T", justified by a selection argument as in Simon Ch. 2, 6.7(2)). In the parent, X_{k,j} is the push-forward of T_j by the k-th dilation, Z_k(ω) its weak limit T(η_{λ_k}^#ω) as j → ∞, and L(ω) the blow-up limit. The diagonal sequence is the parent's Y_k := X_{k,j(k)}.

Conventions.
- ℝ^P := Eucl P, and M_W(·) := massOn W.
- |α| := covectorEuclideanNorm α for a covector α.
- "ω ∈ D_W" means ω ∈ TestFormOn U n with tsupport ω ⊆ W.
- C⁺ := max(C, 0), so ENNReal.ofReal C ≤ ENNReal.ofReal C⁺ and C⁺ ≥ 0.

1. Bound (F1) (comparator-accepted declaration Submission.cmb_abs_apply_le_of_massOn_le). Let Y be a current with M_W(Y) ≤ ENNReal.ofReal C, and let ω ∈ D_W with |ω(z)| ≤ ε for all z. Then |Y(ω)| ≤ C⁺ε. (Apply the declaration with B := C⁺ ≥ 0, using M_W(Y) ≤ ENNReal.ofReal C⁺.)

2. Countable dense family. By the comparator-accepted declaration Submission.cmb_exists_countable_dense_testForms (hypothesis: closure W compact), there is a countable set E ⊆ TestFormOn U n with the following properties:
 - tsupport η ⊆ W for every η ∈ E;
 - for every ω ∈ D_W and every ε > 0 some η ∈ E has |ω(z) − η(z)| ≤ ε for all z.
 E is nonempty, since 0 ∈ D_W must be approximated. Enumerate it as E = {ω_i : i ∈ ℕ}, with repetitions allowed.

3. Lipschitz bounds for Z_k and L. Let ω, ω′ ∈ D_W with |ω(z) − ω′(z)| ≤ ε for all z.
 (3a) ω − ω′ ∈ D_W, and X_{k,j}(ω) − X_{k,j}(ω′) = X_{k,j}(ω − ω′). For all large j, M_W(X_{k,j}) ≤ ENNReal.ofReal C by hypothesis, so |X_{k,j}(ω) − X_{k,j}(ω′)| ≤ C⁺ε by step 1.
 (3b) Letting j → ∞ (first hypothesis), |Z_k(ω) − Z_k(ω′)| ≤ C⁺ε.
 (3c) Letting k → ∞ (second hypothesis), |L(ω) − L(ω′)| ≤ C⁺ε.

4. Choice of φ. Fix k. Finitely many conditions hold for all sufficiently large j:
 (4a) M_W(X_{k,j}) ≤ ENNReal.ofReal C, by the hypothesis;
 (4b) |X_{k,j}(ω_i) − Z_k(ω_i)| < 1/(k+1) for each i ≤ k, by the first hypothesis.
 So there is J_k such that (4a) and (4b) hold for all j ≥ J_k. Define φ recursively by φ(0) := J_0 and φ(k) := max(J_k, φ(k−1) + 1). Then φ is strictly increasing, and (4a), (4b) hold at j = φ(k) for every k. In particular M_W(X_{k,φ(k)}) ≤ ENNReal.ofReal C for all k.

5. Convergence.
 (5a) Fix ω ∈ D_W and ε > 0. Choose i with |ω(z) − ω_i(z)| ≤ ε for all z (step 2).
 (5b) For k ≥ i:
  |X_{k,φ(k)}(ω) − L(ω)| ≤ |X_{k,φ(k)}(ω − ω_i)| + |X_{k,φ(k)}(ω_i) − Z_k(ω_i)| + |Z_k(ω_i) − L(ω_i)| + |L(ω_i) − L(ω)|
   ≤ C⁺ε + 1/(k+1) + |Z_k(ω_i) − L(ω_i)| + C⁺ε.
  The first bound is step 1 with (4a); the second is (4b), since i ≤ k; the last is (3c).
 (5c) As k → ∞, Z_k(ω_i) → L(ω_i) by the second hypothesis. So limsup_k |X_{k,φ(k)}(ω) − L(ω)| ≤ 2C⁺ε.
 (5d) Since ε > 0 is arbitrary, X_{k,φ(k)}(ω) → L(ω).

6. φ is strictly increasing (step 4), the mass bound holds for every k (step 4), and the convergence holds for every ω ∈ D_W (step 5). ∎

Accepted declarations used (reuse by name, identical frozen type): Submission.cmb_abs_apply_le_of_massOn_le, Submission.cmb_exists_countable_dense_testForms.

## Key steps

1. (F1): |Y(ω)| ≤ max(C,0)·sup|ω| when M_W(Y) ≤ ofReal C and tsupport ω ⊆ W (cmb_abs_apply_le_of_massOn_le).
2. A countable sup-norm-dense family {ω_i} of test forms supported in W (cmb_exists_countable_dense_testForms).
3. Z_k and L inherit the Lipschitz bound |·(ω) − ·(ω′)| ≤ C⁺·sup|ω − ω′|.
4. Choose φ(k) ≥ max(J_k, φ(k−1)+1) so that the mass bound holds and |X_{k,φ(k)}(ω_i) − Z_k(ω_i)| < 1/(k+1) for i ≤ k.
5. A four-term estimate gives limsup_k |X_{k,φ(k)}(ω) − L(ω)| ≤ 2C⁺ε for every ε > 0.

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
