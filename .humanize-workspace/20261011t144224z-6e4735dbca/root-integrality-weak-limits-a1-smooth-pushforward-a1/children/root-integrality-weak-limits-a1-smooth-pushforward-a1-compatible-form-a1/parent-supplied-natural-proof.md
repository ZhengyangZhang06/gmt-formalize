# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (F5) of the parent proof (the cut-off function ζ of Simon 2.23, p. 139), filled in. It is stated for an arbitrary set A ⊆ U on which f is proper; the parent uses A = spt X. Neither MapsTo nor openness of V is needed.

Notation: p(x) := Df(x)^#(ω(f(x))) = (ω(f x)).compContinuousLinearMap (fderiv ℝ f x) is the pull-back form f^#ω. C^∞ means smoothness of order ((⊤ : ℕ∞) : WithTop ℕ∞), i.e. of every finite order.

1. (The compact set.) ω ∈ D^j(V) has compact support, so tsupport ω is compact (HasCompactSupport.isCompact), and tsupport ω ⊆ V. By the properness hypothesis, K := f⁻¹(tsupport ω) ∩ A is compact, and K ⊆ A ⊆ U.
2. (Thickenings.) K is compact, U is open and K ⊆ U, so there is δ₀ > 0 with cthickening δ₀ K ⊆ U (IsCompact.exists_cthickening_subset_open). Define:
   - O := thickening (δ₀/2) K, open, with K ⊆ O (self_subset_thickening, as δ₀/2 > 0);
   - C := cthickening (δ₀/2) K, closed, with O ⊆ C (thickening_subset_cthickening);
   - s := thickening δ₀ K, open, with C ⊆ s (cthickening_subset_thickening', since 0 < δ₀ and δ₀/2 < δ₀).
   If K = ∅, all these sets are empty and the argument below still applies.
3. (The cut-off.) Smooth Urysohn (exists_contDiff_support_eq_eq_one_iff with n = ⊤, applied to the open set s and the closed set C ⊆ s) gives a C^∞ function ζ : ℝ^P → ℝ with range ζ ⊆ [0, 1], support ζ = s, and ζ(x) = 1 ⟺ x ∈ C. Consequently:
   - 0 ≤ ζ ≤ 1 everywhere, and ζ = 1 on O;
   - tsupport ζ = closure s ⊆ cthickening δ₀ K ⊆ U (closure_thickening_subset_cthickening);
   - cthickening δ₀ K is compact (IsCompact.cthickening; ℝ^P is proper), so its closed subset tsupport ζ is compact, i.e. ζ has compact support.
4. (p is C^∞.)
   - x ↦ Df(x) is C^∞ because f is C^∞ (ContDiff.fderiv_right, using ∞ + 1 ≤ ∞).
   - x ↦ ω(f(x)) is C^∞ as the composition of the C^∞ maps ω (a test form) and f.
   - B ↦ compContinuousLinearMapCLM B is C^∞. It sends a continuous linear map B : ℝ^P → ℝ^Q to the continuous linear map α ↦ α.compContinuousLinearMap B on j-covectors, and it is analytic on the whole space (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM), hence C^∞ (AnalyticOnNhd.contDiff).
   - Since p(x) = (compContinuousLinearMapCLM (Df(x)))(ω(f(x))), p is C^∞ (ContDiff.comp, ContDiff.clm_apply).
5. (The test form.) Define η(x) := ζ(x)·p(x). η is C^∞ (ContDiff.smul). Also tsupport η ⊆ tsupport ζ (tsupport_smul_subset_left), so η has compact support (HasCompactSupport.smul_right) and tsupport η ⊆ U by step 3. Hence η ∈ D^j(U) = TestFormOn U j, and η(x) = ζ(x)·p(x) for all x by definition.
6. (Support.) If f(x) ∉ tsupport ω, then ω(f(x)) = 0 (image_eq_zero_of_notMem_tsupport). Hence p(x) = 0, the pull-back of the zero covector being zero, and η(x) = 0. So support η ⊆ f⁻¹(tsupport ω). This set is closed, since f is continuous and tsupport ω is closed, so tsupport η ⊆ f⁻¹(tsupport ω) (closure_minimal).
7. (The open set.) Put N := O ∪ f⁻¹(ℝ^Q ∖ tsupport ω), an open set. A ⊆ N: for x ∈ A, if f(x) ∈ tsupport ω then x ∈ K ⊆ O; otherwise x ∈ f⁻¹(ℝ^Q ∖ tsupport ω).
8. (η = p on N.) If x ∈ O ⊆ C, then ζ(x) = 1 and η(x) = p(x). If f(x) ∉ tsupport ω, then p(x) = 0 = η(x) by step 6.
9. Steps 3, 5, 6, 7 and 8 show that η, ζ and N have all the required properties. ∎

## Key steps

1. Properness makes K := f⁻¹(tsupport ω) ∩ A a compact subset of the open set U.
2. Smooth Urysohn on thickenings of K gives a C^∞ cut-off ζ with values in [0, 1], compact support in U and ζ = 1 on a neighbourhood O of K.
3. The pull-back p = f^#ω is C^∞ (B ↦ B^# is analytic), so η := ζ·p ∈ D^j(U) with tsupport η ⊆ f⁻¹(tsupport ω).
4. η = p on the open set N := O ∪ f⁻¹(ℝ^Q ∖ tsupport ω), which contains A.

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
