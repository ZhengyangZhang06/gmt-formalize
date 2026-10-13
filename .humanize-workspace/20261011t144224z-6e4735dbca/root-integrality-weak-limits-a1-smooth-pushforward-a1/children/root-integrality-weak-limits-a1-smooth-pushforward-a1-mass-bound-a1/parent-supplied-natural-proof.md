# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof. It is stated for an abstract pair (Y, Z) related through compatible pull-backs, so that it applies both to (S, X) in degree k + 1 and to (∂S, ∂X) in degree k, each with A = spt X.

Notation:
- p_ω(x) := Df(x)^#(ω(f(x))) = (ω(f x)).compContinuousLinearMap (fderiv ℝ f x);
- |·| := covectorEuclideanNorm;
- massAdmissibleOn V j W is the set of ω ∈ D^j(V) with tsupport ω ⊆ W and |ω(y)| ≤ 1 for all y;
- Y.massOn W = sup {ofReal(Y(ω)) : ω ∈ massAdmissibleOn V j W} in [0, ∞], and similarly for Z.

0. (Homogeneity.) For t ∈ ℝ and a j-covector β on ℝ^P, |t·β| = |t|·|β|. Indeed (tβ)(e∘I) = t·β(e∘I) for every coefficient, so Σ_I (t·β(e∘I))² = t²·Σ_I β(e∘I)², and √(t²·r) = |t|·√r for r ≥ 0 (Real.sqrt_mul, Real.sqrt_sq_eq_abs).
1. Fix W ⊆ ℝ^Q. Since Y.massOn W is a supremum (sSup_le), it suffices to show ofReal(Y(ω)) ≤ ofReal(c^j)·Z.massOn(f⁻¹(W) ∩ U) for every ω ∈ massAdmissibleOn V j W. Fix such an ω.
2. (Compatible form.) Apply the sibling lemma iwl_sp_exists_compatible_testForm to ω, using U open, A ⊆ U, f C^∞ and properness on A. It gives η ∈ D^j(U), ζ with 0 ≤ ζ ≤ 1, and an open N ⊇ A such that:
   - η(x) = ζ(x)·p_ω(x) for all x;
   - η = p_ω on N;
   - tsupport η ⊆ f⁻¹(tsupport ω).
   The compatibility hypothesis, applied to ω, η and N, gives Y(ω) = Z(η).
3. (Support.) tsupport η ⊆ f⁻¹(tsupport ω) ⊆ f⁻¹(W), because tsupport ω ⊆ W. Also tsupport η ⊆ U, because η ∈ D^j(U). Hence tsupport η ⊆ f⁻¹(W) ∩ U.
4. (Pointwise bound.) For every x,
   |η(x)| = |ζ(x)|·|p_ω(x)| ≤ |p_ω(x)| ≤ ‖Df(x)‖^j·|ω(f(x))| ≤ c^j·1 = c^j.
   This uses step 0 with |ζ(x)| ≤ 1, the sibling lemma iwl_sp_covectorEuclideanNorm_pullback_le, |ω(f(x))| ≤ 1, and ‖Df(x)‖^j ≤ c^j (from 0 ≤ ‖Df(x)‖ ≤ c; pow_le_pow_left₀).
5. (Case c^j = 0.) Then j ≠ 0, because c^0 = 1, and c = 0 (pow_eq_zero_iff). So ‖Df(x)‖ ≤ 0, i.e. Df(x) = 0, for every x. Then p_ω(x) = (ω(f x)).compContinuousLinearMap 0 = 0, because the j-linear map ω(f(x)) with j ≥ 1 vanishes when an argument is 0 (ContinuousAlternatingMap.map_coord_zero). So η(x) = ζ(x)·0 = 0 for all x, η = 0 in D^j(U), and Y(ω) = Z(0) = 0 by linearity. Therefore ofReal(Y(ω)) = 0 ≤ ofReal(c^j)·Z.massOn(f⁻¹(W) ∩ U).
6. (Case c^j > 0.) Put η₁ := (c^j)⁻¹·η ∈ D^j(U).
   - tsupport η₁ ⊆ tsupport η ⊆ f⁻¹(W) ∩ U (tsupport_smul_subset_right and step 3);
   - |η₁(x)| = (c^j)⁻¹·|η(x)| ≤ 1, by steps 0 and 4.
   So η₁ ∈ massAdmissibleOn U j (f⁻¹(W) ∩ U), and ofReal(Z(η₁)) ≤ Z.massOn(f⁻¹(W) ∩ U) (GeometricCurrentOn.le_massOn). Since η = c^j·η₁, linearity gives Z(η) = c^j·Z(η₁). Using ENNReal.ofReal_mul with c^j ≥ 0:
   ofReal(Y(ω)) = ofReal(c^j·Z(η₁)) = ofReal(c^j)·ofReal(Z(η₁)) ≤ ofReal(c^j)·Z.massOn(f⁻¹(W) ∩ U).
7. Steps 1, 5 and 6 give Y.massOn W ≤ ofReal(c^j)·Z.massOn(f⁻¹(W) ∩ U). This holds also when the right-hand mass is ∞. ∎

## Key steps

1. For each ω admissible for M_W(Y), the compatible-form sibling gives η = ζ·f^#ω ∈ D^j(U) with Y(ω) = Z(η) and tsupport η ⊆ f⁻¹(W) ∩ U.
2. The pull-back norm sibling and 0 ≤ ζ ≤ 1 give |η(x)| ≤ ‖Df(x)‖^j |ω(f x)| ≤ c^j.
3. If c^j = 0, then j ≥ 1 and Df ≡ 0, so η = 0 and Y(ω) = 0. Otherwise η/c^j is admissible for M_{f⁻¹(W)∩U}(Z), so ofReal(Y(ω)) ≤ ofReal(c^j)·M_{f⁻¹(W)∩U}(Z).
4. Take the supremum over ω.

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
