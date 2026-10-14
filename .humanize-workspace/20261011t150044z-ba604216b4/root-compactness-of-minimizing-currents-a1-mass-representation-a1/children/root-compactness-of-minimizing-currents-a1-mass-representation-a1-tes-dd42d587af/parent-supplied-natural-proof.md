# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.testform_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (extension of T to continuous forms by mollification). The coefficient space H := EuclideanSpace ℝ (Fin d) is given by c.
Notation: Λ := Covector (Euclid P) n; |α| := covectorEuclideanNorm α = ‖c α‖, so |·| is a norm on Λ (|α + β| ≤ |α| + |β|, |tα| = |t||α|); val : ↥U → ℝ^P is the inclusion, an embedding onto the open set U; 'W ⊂⊂ U' means CompactlyContained W U; M_W(T) := T.massOn W.
1. (Zero extension.) For g ∈ C_c(U, H) let S_g := val''(tsupport g), a compact subset of U. Define g̃ : ℝ^P → Λ by g̃(x) := c⁻¹(g⟨x, hx⟩) if x ∈ U and g̃(x) := 0 otherwise.
 - g̃ vanishes outside S_g: if x ∈ U ∖ S_g then ⟨x, hx⟩ ∉ tsupport g, so g̃(x) = c⁻¹(0) = 0.
 - g̃ is continuous. On the open set U it agrees with the continuous map c⁻¹ ∘ g ∘ (val restricted to U)⁻¹. On the open set ℝ^P ∖ S_g (S_g is compact, hence closed) it is 0. These two open sets cover ℝ^P.
 - Hence g̃ is continuous with compact support and tsupport g̃ ⊆ S_g ⊆ U.
 - |g̃(x)| = ‖g⟨x, hx⟩‖ for x ∈ U and 0 otherwise; (g₁ + g₂)~ = g̃₁ + g̃₂; (t g)~ = t g̃; S_{g₁+g₂} ⊆ S_{g₁} ∪ S_{g₂}; S_{tg} ⊆ S_g.
2. (Admissible open sets.) W is admissible for g if W is open, W ⊂⊂ U and S_g ⊆ W.
 - For every compact S ⊆ U there is an open W ⊂⊂ U with S ⊆ W. Choose δ > 0 with cthickening δ S ⊆ U (IsCompact.exists_cthickening_subset_open) and set W := thickening(δ/2) S. Then closure W ⊆ cthickening(δ/2) S, which is compact (a cthickening of a compact set in ℝ^P) and contained in U.
 - In particular admissible sets exist for every g, and for every compact K ⊆ ↥U there is an open W_K ⊂⊂ U with val''K ⊆ W_K.
 - If W₁, W₂ are open with W_i ⊂⊂ U, then W₁ ∪ W₂ is open and W₁ ∪ W₂ ⊂⊂ U, since the closure of a union of two sets is the union of the closures.
3. (Approximating sequences.) A sequence (ω_k) in TestFormOn U n approximates g on W with errors ε_k if tsupport ω_k ⊆ W and |ω_k(x) − g̃(x)| ≤ ε_k for all x and k, where ε_k → 0.
 - If W is admissible for g, such a sequence exists with ε_k = 1/(k+1). Let s := 1 + sup_x ‖g(x)‖, which is finite. The field s⁻¹g̃ is continuous with compact support, tsupport ⊆ S_g ⊆ W and |s⁻¹g̃| ≤ 1. The sibling mollify_unit_field (with V := W and ε := 1/(s(k+1))) gives a test form ω⁰_k with tsupport ω⁰_k ⊆ W, |ω⁰_k| ≤ 1 and |ω⁰_k − s⁻¹g̃| ≤ 1/(s(k+1)). Then ω_k := s•ω⁰_k is a test form with tsupport ⊆ W ⊆ U, so ω_k ∈ TestFormOn U n, and |ω_k − g̃| ≤ 1/(k+1).
 - If moreover ‖g(x)‖ ≤ 1 for all x, applying the sibling directly to g̃ gives such a sequence with, in addition, |ω_k(x)| ≤ 1 for all x and k.
4. (Cauchy estimate.) Let (ω_k) approximate g on W with errors ε_k and (ω'_k) approximate g on W' with errors ε'_k, where W and W' are admissible. W ∪ W' is open and ⊂⊂ U, so M := M_{W∪W'}(T) < ∞ by hypothesis. For all k, l, tsupport(ω_k − ω'_l) ⊆ W ∪ W' and |ω_k(x) − ω'_l(x)| ≤ ε_k + ε'_l. The sibling eval_mass_bound gives |T(ω_k) − T(ω'_l)| = |T(ω_k − ω'_l)| ≤ (ε_k + ε'_l)·M.toReal. Taking W' = W and ω' = ω shows that (T(ω_k))_k is a Cauchy sequence of reals, hence convergent. In general the estimate shows that the limits along (ω_k) and (ω'_k) coincide.
5. (Definition.) For each g choose an admissible W_g and an approximating sequence (ω^g_k) on W_g (steps 2–3), and set L(g) := lim_k T(ω^g_k). By step 4, L(g) = lim_k T(ω_k) for every sequence (ω_k) that approximates g on any admissible set.
6. (Linearity.) Let (ω_k) approximate g₁ on W₁ with errors ε_k, and (ω'_k) approximate g₂ on W₂ with errors ε'_k. Then (ω_k + ω'_k) approximates g₁ + g₂ on W₁ ∪ W₂ with errors ε_k + ε'_k; W₁ ∪ W₂ is admissible for g₁ + g₂ by steps 1–2. Also (t•ω_k) approximates t•g₁ on W₁ with errors |t|ε_k. By step 5 and linearity of T, L(g₁ + g₂) = lim_k T(ω_k + ω'_k) = L(g₁) + L(g₂) and L(t•g₁) = lim_k T(t•ω_k) = t·L(g₁). So L is a real linear map C_c(U, H) → ℝ.
7. (Property (i).) Let ω ∈ TestFormOn U n and g ∈ C_c(U, H) with g(x) = c(ω(x)) for all x ∈ ↥U.
 - g̃ = ω: for y ∈ U, g̃(y) = c⁻¹(c(ω(y))) = ω(y); for y ∉ U, ω(y) = 0 = g̃(y) because tsupport ω ⊆ U.
 - tsupport ω ⊆ S_g: support ω = val''(support g) ⊆ S_g because c is injective, and S_g is closed.
 - Hence for any admissible W the constant sequence ω_k := ω approximates g on W with errors 0, and L(g) = T(ω).
8. (Property (ii).) Let K ⊆ ↥U be compact, W_K as in step 2, and M := (M_{W_K}(T)).toReal, finite by hypothesis. Let g ∈ C_c(U, H) with tsupport g ⊆ K and ‖g‖ ≤ 1. Then S_g ⊆ val''K ⊆ W_K, so W_K is admissible for g. Step 3 gives an approximating sequence (ω_k) on W_K with |ω_k| ≤ 1. Both ω_k and −ω_k belong to massAdmissibleOn U n W_K. So ofReal(T ω_k) ≤ M_{W_K}(T) and ofReal(−T ω_k) ≤ M_{W_K}(T) (GeometricCurrentOn.le_massOn), i.e. |T(ω_k)| ≤ M. By step 5, |L(g)| = lim_k |T(ω_k)| ≤ M.

## Key steps

1. Extend g ∈ C_c(U, ℝ^d) by zero to the continuous compactly supported covector field g̃ = c⁻¹∘g, whose tsupport lies in the compact set S_g ⊆ U.
2. Admissible open sets W ⊂⊂ U containing S_g exist (thickenings) and are stable under finite unions.
3. mollify_unit_field gives test forms ω_k supported in W with |ω_k − g̃| ≤ 1/(k+1), and |ω_k| ≤ 1 when ‖g‖ ≤ 1.
4. eval_mass_bound on W ∪ W' makes T(ω_k) Cauchy with a limit independent of all choices; define L(g) as this limit.
5. Linearity follows from sums and scalings of approximating sequences; L(c∘ω) = T(ω) via the constant sequence; |L(g)| ≤ M_{W_K}(T) via the admissible forms ±ω_k.

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
