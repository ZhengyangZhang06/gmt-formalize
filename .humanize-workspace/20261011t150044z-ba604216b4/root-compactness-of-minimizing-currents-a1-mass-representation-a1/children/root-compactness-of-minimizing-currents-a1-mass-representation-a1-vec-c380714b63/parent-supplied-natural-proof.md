# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.vector_riesz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this replaces the citation of SimonGMT Chapter01 simon_theorem_4_14_caratheodory in step 3 of the parent proof, which is not in the import closure of GMT.Ch07.Submission. The argument uses only results that are in scope: Mathlib's scalar Riesz–Markov–Kakutani theorem (RealRMK.rieszMeasure, RealRMK.integral_rieszMeasure), CompactlySupportedContinuousMap.toRealPositiveLinear, and the Lebesgue decomposition.
Notation: H := EuclideanSpace ℝ (Fin d); e_i := EuclideanSpace.single i 1 for i ∈ Fin d, so ⟨x, y⟩ = Σ_i x_i y_i; ‖f‖_∞ := sup_x |f(x)| for f ∈ C_c(X, ℝ), which is finite. X is σ-compact, being locally compact with a countable basis.
1. (Scalar functionals and their bound.) For i ∈ Fin d and f ∈ C_c(X, ℝ), the map f•e_i : x ↦ f(x)•e_i is continuous with support equal to support f, so it belongs to C_c(X, H). Then Λ_i(f) := L(f•e_i) defines a linear functional Λ_i on C_c(X, ℝ). Let K be compact and M_K as in the hypothesis; applying the hypothesis to g = 0 shows M_K ≥ 0.
 Claim (B): if tsupport f ⊆ K then |Λ_i(f)| ≤ M_K‖f‖_∞. If s := ‖f‖_∞ = 0 then f = 0. Otherwise g := (s⁻¹f)•e_i satisfies ‖g(x)‖ = |f(x)|/s ≤ 1 and tsupport g ⊆ K, so |L g| ≤ M_K, i.e. |Λ_i(f)| ≤ s·M_K.
2. (Variation.) For f ∈ C_c(X, ℝ≥0) let A_f := {h ∈ C_c(X, ℝ) : |h(x)| ≤ f(x) for all x} and V_i(f) := sup Λ_i(A_f). A_f contains 0. Every h ∈ A_f has support h ⊆ support f, hence tsupport h ⊆ tsupport f (a compact set), and ‖h‖_∞ ≤ ‖f‖_∞. By (B), Λ_i(A_f) is bounded above by M_{tsupport f}·‖f‖_∞. Properties:
 (a) V_i(f) ≥ 0 (take h = 0), and |Λ_i(f)| ≤ V_i(f) (take h = ±f, with f regarded as a real function).
 (b) V_i(t f) = t·V_i(f) for t ∈ ℝ≥0. For t = 0 only h = 0 qualifies. For t > 0, h ↦ t h is a bijection A_f → A_{tf} and Λ_i(t h) = tΛ_i(h).
 (c) V_i(f₁ + f₂) = V_i(f₁) + V_i(f₂).
  '≥': if h_j ∈ A_{f_j} then h₁ + h₂ ∈ A_{f₁+f₂}, so Λ_i(h₁) + Λ_i(h₂) ≤ V_i(f₁ + f₂); take suprema.
  '≤': let h ∈ A_{f₁+f₂}, h₁ := max(−f₁, min(h, f₁)) and h₂ := h − h₁. h₁ is continuous and vanishes where h does (f₁ ≥ 0), so h₁, h₂ ∈ C_c(X, ℝ), and |h₁| ≤ f₁. Pointwise |h₂| ≤ f₂: if |h| ≤ f₁ then h₂ = 0; if h > f₁ then 0 < h₂ = h − f₁ ≤ f₂; if h < −f₁ then 0 > h₂ = h + f₁ ≥ −f₂. So Λ_i(h) = Λ_i(h₁) + Λ_i(h₂) ≤ V_i(f₁) + V_i(f₂).
 Thus f ↦ V_i(f) is an ℝ≥0-linear map C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0. Let V̂_i := toRealPositiveLinear V_i, a positive linear functional on C_c(X, ℝ) with V̂_i(f.toReal) = V_i(f) (eq_toRealPositiveLinear_toReal).
3. (Jordan decomposition.) P_i := V̂_i + Λ_i is linear. It is positive: if k ∈ C_c(X, ℝ) satisfies k ≥ 0 then k = (nnrealPart k).toReal, so P_i(k) = V_i(nnrealPart k) + Λ_i(k) ≥ |Λ_i(k)| + Λ_i(k) ≥ 0 by 2(a). Hence P_i is a positive linear functional (monotone by linearity), and Λ_i = P_i − V̂_i.
4. (Riesz–Markov–Kakutani.) a_i := RealRMK.rieszMeasure V̂_i and b_i := RealRMK.rieszMeasure P_i are Borel measures on X, finite on compact sets (IsFiniteMeasureOnCompacts instance). They satisfy ∫ f da_i = V̂_i(f) and ∫ f db_i = P_i(f) for f ∈ C_c(X, ℝ) (RealRMK.integral_rieszMeasure). Hence Λ_i(f) = ∫ f db_i − ∫ f da_i.
5. (Dominating measure.) μ₀ := Σ_i (a_i + b_i) is finite on compact sets, being a finite sum. Hence μ₀ is σ-finite on the σ-compact space X, and so are all a_i and b_i. Since a_i ≤ μ₀ and b_i ≤ μ₀, we have a_i ≪ μ₀ and b_i ≪ μ₀ (Measure.absolutelyContinuous_of_le).
6. (Densities.) By the Lebesgue decomposition for σ-finite measures (Measure.haveLebesgueDecomposition_add, with the σ-finite instance) and Measure.singularPart_eq_zero_of_ac, a_i = μ₀.withDensity α_i and b_i = μ₀.withDensity β_i. Here α_i := a_i.rnDeriv μ₀ and β_i := b_i.rnDeriv μ₀ are measurable [0, ∞]-valued functions, finite μ₀-a.e. (Measure.rnDeriv_lt_top). For compact K, ∫⁻_K α_i dμ₀ = a_i(K) < ∞ and ∫⁻_K β_i dμ₀ = b_i(K) < ∞.
7. (The field ν.) Put ν_i(x) := (β_i x).toReal − (α_i x).toReal and ν(x) := WithLp.toLp 2 (fun i => ν_i x) ∈ H. ν is measurable, since each coordinate is and WithLp.toLp is measurable. For compact K, ‖ν(x)‖ ≤ Σ_i ((α_i x).toReal + (β_i x).toReal), and ∫_K (α_i x).toReal dμ₀ ≤ a_i(K) < ∞ (likewise for β_i). So ν is integrable on K.
8. (Scalar representation.) For f ∈ C_c(X, ℝ), ∫ f da_i = ∫ (α_i x).toReal·f(x) dμ₀(x) (integral_withDensity_eq_integral_toReal_smul; α_i is measurable and finite a.e.), and likewise for b_i. So Λ_i(f) = ∫ f(x)·ν_i(x) dμ₀(x). All these integrals are finite, because f is bounded with compact support and α_i, β_i are integrable on compact sets.
9. (Vector representation.) Let g ∈ C_c(X, H) and g_i(x) := (g x) i. Then g_i ∈ C_c(X, ℝ), being a continuous linear coordinate of g that vanishes where g does. Pointwise g(x) = Σ_i g_i(x)•e_i, so g = Σ_i g_i•e_i in C_c(X, H). Hence L(g) = Σ_i Λ_i(g_i) = Σ_i ∫ g_i ν_i dμ₀ = ∫ Σ_i g_i(x)ν_i(x) dμ₀(x) = ∫ ⟨g(x), ν(x)⟩ dμ₀(x). Each g_i ν_i is integrable, and ⟨x, y⟩ = Σ_i x_i y_i in H.
10. Hence μ₀ and ν have all the required properties.

## Key steps

1. The coordinate functionals Λ_i(f) = L(f e_i) satisfy |Λ_i f| ≤ M_K‖f‖_∞ for f supported in K.
2. The total variation V_i(f) = sup{Λ_i h : |h| ≤ f} is additive (clamp h between ±f₁) and homogeneous; toRealPositiveLinear turns it into a positive functional V̂_i.
3. P_i = V̂_i + Λ_i is positive; RMK gives Radon measures a_i, b_i with Λ_i(f) = ∫ f db_i − ∫ f da_i.
4. μ₀ = Σ(a_i + b_i) dominates all of them; the Lebesgue decomposition gives densities α_i, β_i, and ν_i = β_i − α_i.
5. L(g) = Σ_i Λ_i(g_i) = ∫⟨g, ν⟩ dμ₀.

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
