# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.coordinate_covectors-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Notation paragraph: the coordinate covectors dx^I satisfy dx^I(e_J) = δ_{IJ}, and every covector is Σ_I α(e_I) dx^I.
Notation: e_i := EuclideanSpace.basisFun (Fin P) ℝ i = EuclideanSpace.single i 1, so e_i(l) = 1 if l = i and 0 otherwise; e_J := (fun j => e_{J j}); 𝓘 := the finset of strictly increasing J : Fin n → Fin P (classical decidability); |·| := covectorEuclideanNorm.
1. (Part (a).) Fix I. The map Θ : (Fin n → (Fin n → ℝ)) → ℝ, Θ(u) := det(Matrix.of fun k j => u j k), is multilinear and alternating in the family u. Indeed it is the determinant of the matrix whose j-th column is u j, i.e. of the transpose of the matrix with rows u j; since det Mᵀ = det M, Θ is Matrix.detRowAlternating, an alternating multilinear map. The coordinate map p_I : ℝ^P →ₗ[ℝ] (Fin n → ℝ), p_I x := (fun k => x (I k)), is linear. Hence θ⁰ := Θ.compLinearMap p_I is an alternating n-linear map ℝ^P → ℝ with θ⁰(v) = det(Matrix.of fun k j => v j (I k)). By the Leibniz formula and |x(l)| ≤ ‖x‖, |θ⁰(v)| ≤ Σ_σ Π_j |v_j(I(σ j))| ≤ n!·Π_j ‖v_j‖. So θ_I := AlternatingMap.mkContinuous θ⁰ (n!) (with this bound) is an n-covector with θ_I(v) = det(Matrix.of fun k j => v j (I k)) for all v.
2. (Kronecker property.) Let I, J be strictly increasing. Since (e_{J j})(I k) = if J j = I k then 1 else 0, θ_I(e_J) = det M with M k j := if J j = I k then 1 else 0.
 - If I = J, then M = 1, because J j = J k iff j = k by injectivity; so θ_I(e_J) = 1.
 - If I ≠ J, there is k₀ with I k₀ ∉ range J. Otherwise range I ⊆ range J; both ranges have exactly n elements (strictly increasing maps are injective), so range I = range J and hence I = J (two strictly increasing maps Fin n → Fin P with the same range are equal, StrictMono.range_inj_of_wellFoundedLT), a contradiction. Then row k₀ of M is zero, so θ_I(e_J) = 0 (Matrix.det_eq_zero_of_row_eq_zero).
 So θ_I(e_J) = δ_{IJ} for I, J ∈ 𝓘.
3. (Expansion.) Let α be an n-covector and α' := α − Σ_{I∈𝓘} α(e_I)•θ_I. For J ∈ 𝓘, α'(e_J) = α(e_J) − Σ_{I∈𝓘} α(e_I)·θ_I(e_J) = α(e_J) − α(e_J) = 0 by step 2. Every term of the sum defining |α'| therefore vanishes, so |α'| = 0. By the sibling covector_euclidean_equiv there are d and c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d) with |β| = ‖c β‖ for all β. Thus c α' = 0 and α' = 0, since c is injective. Therefore α = Σ_{I∈𝓘} α(e_I)•θ_I.
4. (Part (b).) Let ζ satisfy the hypothesis of (b). For each I ∈ 𝓘 the covector θ_I of step 1 satisfies the determinant identity, hence ζ θ_I = 0. By step 3 and linearity, ζ α = Σ_{I∈𝓘} α(e_I)·ζ θ_I = 0 for every n-covector α. So ζ = 0 (ContinuousLinearMap.ext).
5. (Degenerate cases.) For n = 0, 𝓘 consists of the empty map and θ_∅ is the constant 1 (the determinant of the empty matrix). For n > P, 𝓘 = ∅ and step 3 shows that every n-covector vanishes. The argument covers both cases without change.

## Key steps

1. θ_I := det of the coordinate rows (I k), made continuous by the bound n!·Π‖v_j‖.
2. θ_I(e_J) = δ_IJ for strictly increasing I, J (a zero row when I ≠ J).
3. α − Σ_I α(e_I)θ_I has covectorEuclideanNorm 0, hence vanishes by covector_euclidean_equiv.
4. ζ vanishes on every θ_I, hence on every covector.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `rg -n 'cmr_|massRepresentation' local-references/123e8435b4a2469b/project -g '*.lean' (no match); python3 scan of dag.json lean_name for prefix cmr (none) and of lean_statement for rieszMeasure|C_c|CompactlySupportedContinuousMap|rnDeriv|withDensity|cutoff|exteriorDerivative|LinearMap.trace|Matrix.det`
- `rg -n 'theorem eLpNorm_le_eLpNorm_fderiv_one|theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem integral_rieszMeasure|theorem haveLebesgueDecomposition_add|theorem singularPart_eq_zero_of_ac|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|def toRealPositiveLinear|theorem eq_toRealPositiveLinear_toReal|theorem tendsto_measure_cthickening_of_isCompact|theorem integral_withDensity_eq_integral_toReal_smul|theorem one_of_mem_closedBall|theorem exists_contDiff_tsupport_subset' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'; rg -n 'singularPart_eq_zero_of_ac|rnDeriv_lt_top' .../Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `grep -n 'theorem simon_theorem_4_14_caratheodory|theorem simon_theorem_4_14_positive_envelope|def IsLocallyBoundedCcFunctional|vectorFunctionalEnvelopeMeasure_isRadon|radonCaratheodoryMeasure_apply|integral_radonCaratheodoryMeasure' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/*.lean; grep -rn 'NullMeasurable|caratheodory' SimonGMT; sed -n 1,120p Chapter06/Representation.lean`
- `python3 scan of the public-import closure of the contract imports (module headers, public imports only); lake env lean /tmp/cmr-split/T1.lean T2.lean T3.lean T4.lean T5.lean T8.lean (#check availability after import GMT.Ch07.Submission)`
- `lake env lean /tmp/cmr-split/Stmts.lean (12 frozen child types + parent_check assembly); lake env lean /tmp/cmr-split/PI.lean and /tmp/cmr-split/PII.lean (interface skeletons); lake env lean /tmp/cmr-split/T6.lean T7.lean (#synth MeasurableSpace/BorelSpace/MeasureSpace on EuclideanSpace, toLp coordinate rfl, trace = sum of partials)`
- `read parent-child-handoff.json of dor_ims_sua_mollify_unit_field, rsd_mw_exists_testForm_approx, covectorEuclideanNorm_gram_bounds; check status accepted and candidate_commit in dag.json`
- `sed -n 75,110p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py; grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; sed -n 1800,1870p runtime.py; sed -n 555,640p verifier/gmt-compare.py; git show --stat 8abce3204fc05f00ae9a4047981f27a9f9a6ba3b`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/GeneralDifferentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-b62f226305/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-covector-gram-bounds-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cmr-split/Stmts.lean`
- `/tmp/cmr-split/PI.lean`
- `/tmp/cmr-split/PII.lean`
- `/tmp/cmr-split/T1.lean`
- `/tmp/cmr-split/T2.lean`
- `/tmp/cmr-split/T3.lean`
- `/tmp/cmr-split/T4.lean`
- `/tmp/cmr-split/T5.lean`
- `/tmp/cmr-split/T6.lean`
- `/tmp/cmr-split/T8.lean`
- `/tmp/cmr-split/closure_pub.txt`

Pinned sources. The snapshot contract (manifest: project b4d606db, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. SimonGMT is pinned at 2b366308.

Not reachable. The proof cites the vector Riesz development (SimonGMT Chapter01 RadonPolarRepresentation, VectorFunctionalEnvelope, RadonCaratheodoryIntegral), Mathlib's Sobolev inequality (SobolevInequality.lean:439) and ContDiffBump.normed. All exist in the pinned sources, but none is in the public import closure of GMT.Ch07.Submission: lake env lean reports unknown identifiers. Leaf candidates may not add imports. Chapter06/Representation.lean only packages conditional MassRepresentation data and says the existence theorem is pending.

In scope and used:
- RealRMK.integral_rieszMeasure (RieszMarkovKakutani/Real.lean:345), with its IsFiniteMeasureOnCompacts and Regular instances;
- toRealPositiveLinear (Topology/ContinuousMap/CompactlySupported.lean:799);
- haveLebesgueDecomposition_add (Decomposition/Lebesgue.lean:115) and singularPart_eq_zero_of_ac (:252);
- integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318);
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (Distribution/AEEqOfIntegralContDiff.lean:205);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
- tendsto_measure_cthickening_of_isCompact (BorelSpace/Metric.lean:185);
- ContDiffBump (BumpFunction/Basic.lean:137);
- Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure;
- SimonGMT exteriorDerivative_apply, GeometricCurrentOn.le_massOn and boundary_apply.

Reuse. Three accepted DAG theorems are reused with identical frozen types: dor_ims_sua_mollify_unit_field, rsd_mw_exists_testForm_approx and covectorEuclideanNorm_gram_bounds. No cmr_ declaration exists in dag.json or in the snapshot.

Lean checks. All 12 child types elaborate after `import GMT.Ch07.Submission` in the comparator child scope. The selected type follows in Lean from cmr_exists_massRepresentation_core and cmr_null_of_representation. Skeletons of both assemblies typecheck against the sibling interfaces.
