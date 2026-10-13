# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.boundary_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (Simon 2.24(1): ∂f_#T = f_#∂T), with the degree-(k+1) formula as hypothesis. The formula is applied directly to dω and dη on the same open set. This shortens the parent's step 5, which goes through an auxiliary η′ from (F5) and the support fact (F2); neither is needed.

Notation:
- p_ω(x) := Df(x)^#(ω(f(x))) = (ω(f x)).compContinuousLinearMap (fderiv ℝ f x);
- for ψ ∈ D^k(U) (resp. D^k(V)), dψ := exteriorDerivativeTestOn U k ψ ∈ D^{k+1}(U) (resp. with V); its underlying form is extDeriv ψ;
- by definition ∂S(ω) = S(dω) and ∂X(η) = X(dη) (GeometricCurrentOn.boundary_apply).

1. Fix ω ∈ D^k(V), η ∈ D^k(U) and an open N ⊇ spt X with η(x) = p_ω(x) for every x ∈ N. Then dω ∈ D^{k+1}(V) and dη ∈ D^{k+1}(U).
2. (Locality.) Let x ∈ N. Since N is open, η = p_ω on a neighbourhood of x, i.e. η =ᶠ[𝓝 x] p_ω (IsOpen.mem_nhds). Hence extDeriv η x = extDeriv p_ω x (Filter.EventuallyEq.extDeriv_eq): extDeriv ψ x is the alternatization of fderiv ℝ ψ x, which depends only on the germ of ψ at x.
3. (Naturality.) ω is C^∞, being a test form, so it is differentiable at f(x). f is C^∞, so ContDiffAt ℝ ∞ f x, and minSmoothness ℝ 2 = 2 ≤ ∞. Mathlib's extDeriv_pullback therefore gives
   extDeriv p_ω x = (extDeriv ω (f x)).compContinuousLinearMap (fderiv ℝ f x) = Df(x)^#((dω)(f(x))).
4. By steps 2–3, (dη)(x) = Df(x)^#((dω)(f(x))) for every x ∈ N. So dη agrees with the pull-back of dω on the open set N ⊇ spt X. The hypothesis, applied with ω′ := dω, η′ := dη and the same N, gives S(dω) = X(dη).
5. Hence ∂S(ω) = S(dω) = X(dη) = ∂X(η). ∎

## Key steps

1. ∂S(ω) = S(dω) and ∂X(η) = X(dη) by the definition of the boundary.
2. Locality of extDeriv on the open set N where η = f^#ω, together with Mathlib's extDeriv_pullback (naturality of d), gives dη = f^#(dω) on N.
3. Applying the degree-(k+1) formula to (dω, dη, N) gives ∂S(ω) = X(dη) = ∂X(η).

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
