# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.vector_riesz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (Riesz representation of the locally bounded functional L of step 2). The parent cites SimonGMT Chapter01 simon_theorem_4_14_caratheodory, which is not in the import closure of GMT.Ch07.Submission (verified: unknown identifier after `import GMT.Ch07.Submission`); the representation is therefore proved here directly. The argument uses only results that are in scope: Mathlib's scalar Riesz–Markov–Kakutani theorem (RealRMK.rieszMeasure, RealRMK.integral_rieszMeasure), CompactlySupportedContinuousMap.toRealPositiveLinear, and the Lebesgue decomposition.
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
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean and Submission.lean against workspace GMT/Ch07/Contract.lean and Submission.lean  (identical)`
- `rg -n 'dimred_mbl_fnd' <snapshot>/project -g '*.lean'  (no match, rc=1)`
- `rg -n 'cmr_|cmc_imRep|rsd_mw_exists|dor_ims_sua' <snapshot>/project -g '*.lean'  (no match, rc=1)`
- `rg -n -i 'massRepresentation|vector_riesz|vectorRiesz' <snapshot>/project -g '*.lean'  (no match, rc=1)`
- `rg -n 'structure IMRep|def IsIntegerMultiplicity|def boundaryMassOn|def CompactlyContained|abbrev MultiVector' <snapshot>/project/GMT/Ch07/Contract.lean  (lines 61, 92, 120, 127, 48)`
- `rg -n 'def rieszMeasure|theorem integral_rieszMeasure|def toRealPositiveLinear|theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem tendsto_measure_cthickening_of_isCompact|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem integral_withDensity_eq_integral_toReal_smul|theorem exists_contDiff_tsupport_subset|theorem eLpNorm_le_eLpNorm_fderiv_one|theorem extDeriv_apply|theorem monotone_sort' <snapshot>/mathlib/Mathlib -g '*.lean'`
- `python3 walk of `import` lines from the contract's SimonGMT imports through lake-packages simongmt (closure: Chapter01.{Basic,Hausdorff,MetricCriterion}, Chapter02.Lipschitz, Chapter03.Rectifiable, Chapter04.Basic, Chapter06.{Forms,Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward})`
- `lake env lean /tmp/fnd-split/Probe2.lean and Probe3.lean  (#check of every cited name after `import GMT.Ch07.Submission`; unknown: simon_theorem_4_14_caratheodory, eLpNorm_le_eLpNorm_fderiv_one, ContDiffBump.normed, SignedMeasure.toJordanDecomposition, ContinuousAlternatingMap.map_perm, Measure.withDensity_rnDeriv_eq; all other cited names resolve)`
- `lake env lean /tmp/fnd-split/check/Final.lean  (12 child types + parent type in the replayed comparator scope; conditional assembly; #print axioms)`
- `python3 scans of dag.json: selected node, string identity parent = '(' + REP + ') ∧ (' + IMC + ')', statuses/candidate commits of reused nodes, dependency closures of reused nodes, lean_name collisions; lean_contract.validate_lean_statement on all 12 child types`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; contract_scope/child_modules in verifier/gmt-compare.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-foundations-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/isolated-comparator-result.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/fnd-split/check/Final.lean`

The snapshot pins match: project b4d606db and mathlib 25730c7c. The snapshot Contract.lean and Submission.lean are byte-identical to the workspace's. The snapshot contains no dimred_mbl_fnd_*, cmr_*, cmc_imRep*, rsd_mw_exists* or dor_ims_sua* declaration and no mass-representation or vector-Riesz theorem, so no snapshot declaration is reused and no fresh name collides. The snapshot mathlib has the in-scope replacement tools the children cite: RealRMK.rieszMeasure/integral_rieszMeasure, toRealPositiveLinear, IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, tendsto_measure_cthickening_of_isCompact, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, integral_withDensity_eq_integral_toReal_smul, extDeriv_apply and Tuple.monotone_sort. eLpNorm_le_eLpNorm_fderiv_one exists in the snapshot (SobolevInequality.lean:439) but is outside the import closure of GMT.Ch07.Submission, as are SimonGMT's simon_theorem_4_14_caratheodory and ContDiffBump.normed (Lean probe: unknown identifiers). Five DAG declarations are reused with byte-identical frozen types. All are accepted, with candidate commits and passed comparators, and their closures are fully accepted: cmc_imRep_locality_restrict_sub, cmr_abs_apply_le_massOn, cmr_covector_euclidean_equiv, dor_ims_sua_mollify_unit_field and rsd_mw_exists_testForm_approx. All 12 child types and the parent type elaborate in the replayed comparator scope. The conditional assembly proves the exact selected type with axioms propext, Classical.choice and Quot.sound.
