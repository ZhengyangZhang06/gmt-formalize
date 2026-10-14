# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (Hⁿ(M ∖ spt X) = 0), filled in and stated for an arbitrary representation of an arbitrary current. As in the parent, the vector measure θξHⁿ⌞M is tested against forms φ·b. Two technical substitutions shorten the parent's route:
- instead of (F2) (vanishing on all of U ∖ spt T via a partition of unity), the zero region is covered by countably many open sets W ⊂⊂ U on which T vanishes;
- instead of passing from C_c^∞ to C_c and then to Borel sets via Riesz uniqueness, Mathlib's fundamental lemma IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero is applied on each W. It accepts an arbitrary measure, so no local finiteness of Hⁿ⌞M is needed.
The coordinate covectors dx^I are replaced by an arbitrary finite basis of the covector space. All coefficients are handled as scalar functions; an NVector-valued Bochner integral is avoided on purpose, because at this Mathlib pin no ContinuousENorm instance is found for NVector.
The Lean statement is identical to that of the accepted DAG node root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1 (lpf_rectifiable_support_null). This child keeps a fresh name, as this run does for other identical types, so the branch has no cross-branch dependency; the proof below is self-contained.

Notation:
- μ := μHE[n] (= Hⁿ) and ν := μ⌞M = μ.restrict M;
- an n-covector b ∈ Covector (ℝ^P) n is a continuous alternating n-linear map; ‖b‖ is its operator norm, so |b(v₁, …, v_n)| ≤ ‖b‖·∏_i |v_i| (ContinuousAlternatingMap.le_opNorm);
- e_1, …, e_P is the standard orthonormal basis of ℝ^P (EuclideanSpace.basisFun);
- 𝒲 is the family of sets W ⊆ ℝ^P with W open, closure W compact, closure W ⊆ U and T.VanishesOn W, i.e. T(ψ) = 0 for every ψ ∈ Dⁿ(U) with tsupport ψ ⊆ W. By definition T.zeroRegion = ⋃𝒲 and spt T = T.support = U ∖ T.zeroRegion.

1. (Good points.) By the field orients, for ν-a.e. x there are an orthonormal τ : Fin n → ℝ^P and a sign s ∈ {1, −1} with ξ(x) = s·simpleNVector τ. By ae_restrict_mem₀ (M is μ-null-measurable), x ∈ M for ν-a.e. x, and then θ(x) > 0 (field pos). Call x good if both hold; ν-a.e. x is good. For a good x with τ and s as above:
   (a) for every n-covector b, |ξ(x)(b)| = |b(τ₁, …, τ_n)| ≤ ‖b‖·∏_i |τ_i| = ‖b‖, since |τ_i| = 1;
   (b) let b_τ := wedgeCovectors n (i ↦ innerSL ℝ τ_i). By wedgeCovectors_apply_det, b_τ(τ) = det(⟨τ_i, τ_j⟩)_{i,j} = det(Id) = 1, by orthonormality (for n = 0 this is the empty determinant 1). Hence ξ(x)(b_τ) = s ≠ 0, so ξ(x) ≠ 0.
2. (A finite separating family of covectors.) The map Φ : Covector (ℝ^P) n → ℝ^(Fin n → Fin P), Φ(α)(v) := α(e_{v(1)}, …, e_{v(n)}), is ℝ-linear.
   - Φ is injective. If Φ(α) = Φ(β), the alternating maps underlying α and β agree on every tuple of basis vectors, so they are equal (Module.Basis.ext_alternating with the basis e; a multilinear map is determined by its values on tuples of basis vectors). Hence α = β.
   - The codomain is finite-dimensional, so Covector (ℝ^P) n is finite-dimensional (Module.Finite.of_injective).
   Fix a basis b_1, …, b_N of Covector (ℝ^P) n (Module.finBasis). If w ∈ NVector (ℝ^P) n, a continuous linear functional on n-covectors, satisfies w(b_i) = 0 for all i, then w = 0, because a linear map vanishing on a basis is zero (Basis.ext).
3. (Fix W ∈ 𝒲.) K := closure W is compact and K ⊆ U, so θ is μ-integrable on M ∩ K (field integrableOn), hence on the subset M ∩ W. Since W is open, hence measurable, ν⌞W = μ⌞(W ∩ M) (Measure.restrict_restrict). Thus θ is ν-integrable on W.
4. (Integrable coefficients.) Fix an n-covector b and put g_b(x) := θ(x)·ξ(x)(b). Then g_b is ν-integrable on W:
   - x ↦ ξ(x)(b) is ν-a.e. strongly measurable, as the composition of ξ (a.e. strongly measurable for ν by the field aestronglyMeasurable) with the continuous linear evaluation w ↦ w(b) (ContinuousLinearMap.apply);
   - θ is a.e. strongly measurable for ν⌞W (step 3), so g_b is a.e. strongly measurable for ν⌞W;
   - |g_b(x)| ≤ ‖b‖·|θ(x)| for ν-a.e. x, by step 1(a);
   - ‖b‖·|θ| is ν-integrable on W, by step 3.
   Hence IntegrableOn g_b W ν (Integrable.mono'), and in particular LocallyIntegrableOn g_b W ν.
5. (Testing T.) Let φ : ℝ^P → ℝ be C^∞ with compact support and tsupport φ ⊆ W. The form ω_φ(x) := φ(x)·b is C^∞ with compact support, and tsupport ω_φ ⊆ tsupport φ ⊆ W ⊆ closure W ⊆ U. So ω_φ ∈ Dⁿ(U) with tsupport ω_φ ⊆ W, and T(ω_φ) = 0 because T vanishes on W. By the representation hypothesis and the linearity of ξ(x):
   0 = T(ω_φ) = ∫_M θ(x)·ξ(x)(φ(x)·b) dμ(x) = ∫ φ(x)·g_b(x) dν(x).
6. (Fundamental lemma.) Steps 4 and 5 are exactly the hypotheses of IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero for the open set W, the measure ν and the function g_b. Hence for ν-a.e. x: x ∈ W ⟹ θ(x)·ξ(x)(b) = 0. Since θ(x) > 0 at good points, for ν-a.e. x: x ∈ W ⟹ ξ(x)(b) = 0.
7. (ν(W) = 0.) Apply step 6 to b = b_1, …, b_N and intersect the finitely many full-measure sets with the set of good points (ae_all_iff). For ν-a.e. x, x is good and, if x ∈ W, then ξ(x)(b_i) = 0 for all i, whence ξ(x) = 0 by step 2. This contradicts step 1(b), so ν-a.e. x satisfies x ∉ W, i.e. ν(W) = 0 (ae_iff). Since W is measurable, μ(M ∩ W) = μ(W ∩ M) = ν(W) = 0 (Measure.restrict_apply).
8. (Countable union.) Every W ∈ 𝒲 is open and ℝ^P is second countable, so there is a countable subfamily 𝒲₀ ⊆ 𝒲 with ⋃𝒲₀ = ⋃𝒲 = T.zeroRegion (TopologicalSpace.isOpen_sUnion_countable). Let x ∈ M ∖ spt T. Then x ∈ U (field subset) and x ∉ U ∖ T.zeroRegion, so x ∈ T.zeroRegion, i.e. x ∈ W for some W ∈ 𝒲₀. Hence M ∖ spt T ⊆ ⋃_{W∈𝒲₀} (M ∩ W), a countable union of μ-null sets by step 7. Therefore μ(M ∖ spt T) = 0 (measure_mono_null, measure_biUnion_null_iff). ∎

## Key steps

1. At Hⁿ⌞M-a.e. x: θ(x) > 0, |ξ(x)(b)| ≤ ‖b‖ for every covector b, and ξ(x) ≠ 0, because ξ(x)(b_τ) = ±1 for b_τ = det⟨τ_i, ·⟩.
2. Covector (ℝ^P) n is finite-dimensional: the coordinate map α ↦ (α(e∘v))_v is injective by Module.Basis.ext_alternating. Hence a finite basis b_1, …, b_N separates n-vectors.
3. For each open W ⊂⊂ U on which T vanishes and each covector b, θ·ξ(b) is Hⁿ⌞M-integrable on W, and ∫ φ θ ξ(b) d(Hⁿ⌞M) = T(φ·b) = 0 for φ ∈ C_c^∞(W).
4. The fundamental lemma gives ξ(b_i) = 0 a.e. on W for all i, so ξ = 0 a.e. on W. This contradicts ξ ≠ 0, so Hⁿ(M ∩ W) = 0.
5. The zero region is a countable union of such W (second countability), so Hⁿ(M ∖ spt T) = 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical)`
- `python3 scan of dag.json lean_name/lean_statement (iwl_*, support_null, compContinuousLinearMap, nVectorPushforward, duplicates); status of root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem exists_contDiff_support_eq_eq_one_iff|theorem _root_.IsCompact.exists_cthickening_subset_open|theorem cthickening_subset_thickening'|theorem closure_thickening_subset_cthickening|lemma analyticOnNhd_compContinuousLinearMapCLM|theorem AnalyticOnNhd.contDiff |theorem ContDiff.fderiv_right|theorem extDeriv_pullback|theorem Filter.EventuallyEq.extDeriv_eq|lemma ContDiff.locallyLipschitz|lemma LocallyLipschitz.locallyLipschitzOn|theorem Module.Basis.ext_alternating|theorem isOpen_sUnion_countable|theorem HasCompactSupport.smul_right|theorem tsupport_smul_subset_left' mathlib/Mathlib`
- `rg -n 'FiniteDimensional ℝ \(.*ContinuousAlternatingMap|instance.*Module.Finite.*ContinuousAlternatingMap' mathlib/Mathlib (no match)`
- `rg -n 'def singularValues|normDet_eq_prod_singularValues|def svd' mathlib/Mathlib; rg -n '^theorem|^lemma' mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean; sed -n 1,40p mathlib/Mathlib/Analysis/InnerProductSpace/ExteriorPower.lean`
- `rg -n 'def finBasis|theorem map_coord_zero|theorem measure_biUnion_null_iff|theorem ae_restrict_mem₀|theorem measure_eq_zero_iff_ae_notMem' mathlib/Mathlib`
- `grep -n declarations in simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,FormsDuality,Forms}.lean (massOn, massAdmissibleOn, covectorEuclideanNorm, support/zeroRegion/VanishesOn, boundary_apply, nVectorPushforward_simple, simpleNVector, wedgeCovectors_apply_det, exteriorDerivativeTestOn)`
- `sed -n 385,470p and 800,870p book/chapter-06.txt (Simon 2.23–2.27, 3.6–3.10)`
- `verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement -> /tmp/iwl-sp-a3/gen/Challenge_*.lean, Solution_*.lean`
- `leanrun.sh (pinned lean-4.35.0-rc3, LEAN_PATH = workspace .lake/build + lake-packages-25730c7c) on gen/Challenge_*.lean, Assembly.lean, SimSubmission.lean, Probe1.lean (FiniteDimensional not inferable), Probe2.lean (ContinuousENorm on NVector not found), ProbeBF/ProbeCF/ProbeMB/ProbePF/ProbeSN2.lean, Final.lean with #print axioms`
- `python3 -I scripts/pullback_check.py (1500 random cases)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/ExteriorPower.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/iwl-sp-a3/Assembly.lean`
- `/tmp/iwl-sp-a3/SimSubmission.lean`
- `/tmp/iwl-sp-a3/Final.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 Contract and a byte-identical Submission with no Submission.* declarations.

Scratch Lean runs (pinned toolchain; workspace unmodified):
- All six child types elaborate in the comparator's child scope.
- Every `exact Submission.<name>` resolves.
- The frozen parent type follows sorry-free from the six child propositions.
- support_null, compatible_form and boundary_formula are proved outright.
- pushforward_formula is proved from support_null, and mass_bound from pullback_norm and compatible_form.
- The parent is proved from pullback_norm alone.
- All of these use only propext, Classical.choice and Quot.sound.

The cited lemmas exist with the stated hypotheses:
- the fundamental lemma takes an arbitrary measure, with no local finiteness;
- smooth Urysohn takes n : ℕ∞;
- extDeriv_pullback needs minSmoothness 2;
- compContinuousLinearMapCLM is analytic.

No FiniteDimensional instance exists for covectors; it is proved by injecting into coordinates. ContinuousENorm is not found for NVector, so the scalar route is used. Singular values exist, but there is no SVD factorization and no link to covectorEuclideanNorm, so the elementary tensor route is used for (F3), which was also checked numerically.

All six iwl_sp_* names are free in the 261-node DAG. lpf_rectifiable_support_null, which has the same type as support_null, is accepted, but this child is named freshly following the run's precedent.
