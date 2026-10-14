# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Part I (steps 2–6). Two substitutions are forced by the import closure of GMT.Ch07.Submission, where SimonGMT Chapter01's vector Riesz theorem and its positive-envelope identity are unavailable. The Riesz representation is the sibling vector_riesz, and the lower mass bound uses the sibling testform_l1_approx instead of the positive-envelope identity (3a).
Notation: |α| := covectorEuclideanNorm α; M_W(T) := T.massOn W; val : ↥U → ℝ^P is the inclusion; H := EuclideanSpace ℝ (Fin d).
1. (Coordinates.) By the sibling covector_euclidean_equiv choose d and c : Covector (Euclid P) n ≃L[ℝ] H with |α| = ‖c α‖. Thus |·| is a norm on covectors, and c, c⁻¹ are continuous linear.
2. (Extension.) By the sibling testform_extension (with P, n, U, T, d, c and the hypotheses) there is a linear L : C_c(U, H) → ℝ with (i) L(g) = T(ω) whenever g(x) = c(ω(x)) for all x ∈ U, and (ii) local boundedness on compact subsets of ↥U.
3. (Representation.) ↥U is locally compact (IsOpen.locallyCompactSpace), Hausdorff and second countable, and carries its Borel σ-algebra (Subtype.borelSpace). Apply the sibling vector_riesz to X := ↥U, d and L; its hypothesis is (ii). This gives a measure μ₀ on ↥U, finite on compact sets, and a measurable ν : ↥U → H, integrable on compact sets, with L(g) = ∫ ⟨g(x), ν(x)⟩ dμ₀(x) for all g ∈ C_c(U, H).
4. (Normalization and definitions.)
 - ρ(x) := ‖ν(x)‖ and ν̂(x) := ρ(x)⁻¹•ν(x), with 0⁻¹ = 0. Both are measurable, ν(x) = ρ(x)•ν̂(x) for all x, ‖ν̂(x)‖ ≤ 1, and ‖ν̂(x)‖ = 1 when ρ(x) ≠ 0.
 - μ₁ := μ₀.withDensity (x ↦ ofReal ρ(x)) on ↥U, and μ := μ₁.map val. Since U is open, hence measurable, val is a measurable embedding. So μ(A) = μ₁(val⁻¹A) for measurable A, and ∫ F dμ = ∫ F(val x) dμ₁(x) (MeasurableEmbedding.integral_map).
 - ν̂_e : ℝ^P → H is ν̂(⟨y, h⟩) for y ∈ U and 0 for y ∉ U. It is measurable, being measurable on the measurable set U and constant on Uᶜ.
 - ξ(y) := (innerSL ℝ (ν̂_e y)).comp c, so ξ(y)(α) = ⟨ν̂_e(y), c α⟩ and ξ(y) = 0 for y ∉ U.
 - β(y) := c⁻¹(ν̂_e(y)).
5. (Property 1.) μ(Uᶜ) = μ₁(val⁻¹(Uᶜ)) = μ₁(∅) = 0.
6. (Property 2.) Let K ⊆ U be compact. val⁻¹(K) is compact in ↥U, because val is an embedding and K ⊆ range val (Topology.IsInducing.isCompact_preimage_iff). So μ(K) = μ₁(val⁻¹K) = ∫⁻_{val⁻¹K} ofReal ρ dμ₀ < ∞, since ν is integrable on val⁻¹K.
7. (Properties 4 and 5.) The map Φ : H → MultiVector P n, Φ(v) := (innerSL ℝ v).comp c, is continuous linear, and ξ = Φ ∘ ν̂_e. ν̂_e is measurable into the second-countable space H, hence strongly measurable. So ξ is strongly measurable, in particular AEStronglyMeasurable for μ. For every y and α, |ξ(y)(α)| = |⟨ν̂_e(y), c α⟩| ≤ ‖ν̂_e(y)‖·‖c α‖ ≤ |α| (Cauchy–Schwarz). Likewise β = c⁻¹ ∘ ν̂_e is strongly measurable, and |β(y)| = ‖ν̂_e(y)‖ ≤ 1.
8. (Property 6.) Let ω ∈ TestFormOn U n and g_ω : ↥U → H, g_ω(x) := c(ω(val x)). g_ω is continuous. Its support is contained in val⁻¹(tsupport ω), which is compact because tsupport ω is a compact subset of U = range val. Hence g_ω ∈ C_c(U, H), and by step 2(i), T(ω) = L(g_ω). By step 3:
 L(g_ω) = ∫ ⟨c(ω x), ν x⟩ dμ₀
 = ∫ ρ(x)⟨ν̂(x), c(ω x)⟩ dμ₀(x)   (ν = ρ•ν̂, and the inner product is symmetric)
 = ∫ ⟨ν̂(x), c(ω x)⟩ dμ₁(x)   (integral_withDensity_eq_integral_toReal_smul, with (ofReal ρ).toReal = ρ)
 = ∫ ξ(val x)(ω(val x)) dμ₁(x)
 = ∫ ξ(y)(ω y) dμ(y).
9. (μ-a.e. normalization.) The set Z := Uᶜ ∪ val''{x : ρ x = 0} is measurable, and μ(Z) ≤ μ(Uᶜ) + μ₁({ρ = 0}) = 0 + ∫⁻_{ρ=0} ofReal ρ dμ₀ = 0. For y = val x ∉ Z, ξ(y)(β y) = ⟨ν̂ x, c(c⁻¹(ν̂ x))⟩ = ‖ν̂ x‖² = 1. So ξ(y)(β(y)) = 1 for μ-a.e. y.
10. (Property 3, upper bound.) Let W be open and ω ∈ massAdmissibleOn U n W. If μ(W) = ∞ there is nothing to prove. Otherwise y ↦ ξ(y)(ω y) vanishes off W (ω(y) = 0 for y ∉ tsupport ω), and |ξ(y)(ω y)| ≤ |ω y| ≤ 1. By step 8, T(ω) = ∫_W ξ(ω) dμ ≤ (μ W).toReal, so ofReal(T ω) ≤ μ(W). Taking the supremum over ω, M_W(T) ≤ μ(W).
11. (Property 3, lower bound on relatively compact pieces.) Let W be open and W' an open set with W' ⊂⊂ U and W' ⊆ W.
 - ν' := μ.restrict W' is a finite measure (μ(W') ≤ μ(closure W') < ∞ by step 6) with ν'(W'ᶜ) = 0. β is integrable for ν', being strongly measurable and bounded, and |β| ≤ 1.
 - Let ε > 0. The sibling testform_l1_approx (with P, n, ν', V := W', β, ε) gives a test form ω₀ with tsupport ω₀ ⊆ W', |ω₀| ≤ 1 and ∫⁻ ofReal|ω₀ − β| dν' < ofReal ε. Since W' ⊆ U, ω₀ defines ω ∈ TestFormOn U n, and ω ∈ massAdmissibleOn U n W because W' ⊆ W.
 - By step 8, since ω vanishes off W', T(ω) = ∫_{W'} ξ(ω) dμ = ∫_{W'} ξ(β) dμ + ∫_{W'} ξ(ω − β) dμ; both integrands are bounded on the finite-measure set W'. By step 9 the first integral is μ.real(W'). The second has absolute value ≤ ∫_{W'} |ω − β| dμ < ε, since |ξ(y)(α)| ≤ |α|.
 - Hence M_W(T) ≥ ofReal(T ω) ≥ ofReal(μ.real(W') − ε). Letting ε ↓ 0, M_W(T) ≥ μ(W').
12. (Property 3, lower bound.) Let W be open and O := W ∩ U. Since μ(Uᶜ) = 0, μ(W) = μ(O). The open set O is the increasing union of the open sets W'_j (j ≥ 1), where W'_j := ball(0, j) if O = ℝ^P, and W'_j := {y : ‖y‖ < j and infDist(y, Oᶜ) > 1/j} otherwise. The closure of each W'_j lies in the compact set {‖y‖ ≤ j, infDist(y, Oᶜ) ≥ 1/j} ⊆ O (resp. closedBall(0, j)), so W'_j ⊂⊂ U and W'_j ⊆ W. By step 11 and continuity from below, μ(W) = sup_j μ(W'_j) ≤ M_W(T).
13. Steps 5–12 give all six properties for μ and ξ.

## Key steps

1. Get the coordinates c (covector_euclidean_equiv) and the extension L of T to C_c(U, ℝ^d) (testform_extension).
2. vector_riesz on X = U gives μ₀ and a locally integrable ν with L(g) = ∫⟨g, ν⟩ dμ₀.
3. Normalize polarly: μ := val_*(|ν|μ₀) and ξ(x)(α) := ⟨ν(x)/|ν(x)|, c α⟩; this gives properties (1), (2), (4), (5) and (6).
4. M_W(T) ≤ μ(W) because |ξ(ω)| ≤ |ω| ≤ 1.
5. M_W(T) ≥ μ(W') for open W' ⊂⊂ U with W' ⊆ W, via testform_l1_approx applied to β = c⁻¹(ν/|ν|); then exhaust W ∩ U.

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
