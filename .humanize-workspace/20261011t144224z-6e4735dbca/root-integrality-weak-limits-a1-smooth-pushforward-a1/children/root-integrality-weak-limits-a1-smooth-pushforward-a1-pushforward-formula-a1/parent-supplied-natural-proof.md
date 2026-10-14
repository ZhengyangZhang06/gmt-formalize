# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.pushforward_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 2 and 4 of the parent proof, filled in. This is the identification, for differentiable f, of the Lipschitz push-forward of Simon 3.6 with the classical push-forward of 2.23 (Simon p. 148, remark after 3.10). The integrability remark in the parent's step 4 is not needed: integrals of a.e.-equal functions coincide without any integrability hypothesis (integral_congr_ae).

Notation:
- μ := μHE[n] and ν := μ⌞M;
- Df(x) := fderiv ℝ f x;
- for a continuous linear B : ℝ^P → ℝ^Q and an n-covector α on ℝ^Q, B^#α := α.compContinuousLinearMap B = covectorPullback n B α, so (B^#α)(v) = α(B ∘ v);
- for an n-vector w on ℝ^P, B_#w := nVectorPushforward n B w = w ∘ covectorPullback n B, so (B_#w)(α) = w(B^#α).

1. (Unfolding.) By IsLipschitzPushforward X f S there are M, θ, ξ and L with:
   (i) IsRectifiableTriple U n M θ ξ;
   (ii) X(ψ) = tauAction n M θ ξ ψ = ∫_M θ(x)·ξ(x)(ψ(x)) dμ for every ψ ∈ Dⁿ(U);
   (iii) for ν-a.e. x: for every subspace T_x with HasWeightedApproximateTangentSpaceAt n M θ x T_x and every v ∈ T_x, HasDerivAt (t ↦ f(x + t•v)) (L(x)v) 0;
   (iv) S(ω′) = ∫_M θ(x)·(L(x)_#ξ(x))(ω′(f(x))) dμ for every ω′ ∈ Dⁿ(V).
2. (ν-a.e. point of M lies in spt X.) The sibling lemma iwl_sp_rectifiable_support_null, applied to U, X, M, θ, ξ with (i) and (ii), gives μ(M ∖ spt X) = 0. Hence ν(M ∖ spt X) ≤ μ(M ∖ spt X) = 0 (Measure.restrict_le_self). Also x ∈ M for ν-a.e. x (ae_restrict_mem₀; M is μ-null-measurable by (i)). Every x ∈ M with x ∉ spt X lies in M ∖ spt X, so x ∈ spt X for ν-a.e. x.
3. Fix ω ∈ Dⁿ(V), η ∈ Dⁿ(U) and an open N ⊇ spt X with η(x) = Df(x)^#(ω(f(x))) for all x ∈ N. By step 2, (iii) and the field orients of (i), the following hold simultaneously for ν-a.e. x:
   - x ∈ spt X, hence x ∈ N;
   - (iii) holds at x;
   - there are an orthonormal τ : Fin n → ℝ^P and s ∈ {1, −1} with HasWeightedApproximateTangentSpaceAt n M θ x (span(range τ)) and ξ(x) = s·simpleNVector τ.
   Fix such x, τ and s.
4. (L(x) = Df(x) on the frame.) For each i, τ_i ∈ span(range τ) (Submodule.subset_span), so (iii) gives HasDerivAt (t ↦ f(x + t•τ_i)) (L(x)τ_i) 0. On the other hand, t ↦ x + t•τ_i has derivative τ_i and value x at t = 0, and f has Fréchet derivative Df(x) at x because f is differentiable. By the chain rule (HasFDerivAt.comp_hasDerivAt), HasDerivAt (t ↦ f(x + t•τ_i)) (Df(x)τ_i) 0. By uniqueness of derivatives (HasDerivAt.unique), L(x)τ_i = Df(x)τ_i for every i, i.e. L(x) ∘ τ = Df(x) ∘ τ.
5. (Pointwise identity.) Let α := ω(f(x)). Using ξ(x) = s·simpleNVector τ, simpleNVector_apply and step 4:
   (L(x)_#ξ(x))(α) = ξ(x)(L(x)^#α) = s·α(L(x) ∘ τ) = s·α(Df(x) ∘ τ) = s·(Df(x)^#α)(τ) = ξ(x)(Df(x)^#α) = ξ(x)(η(x)),
   the last equality because x ∈ N. Hence θ(x)·(L(x)_#ξ(x))(ω(f(x))) = θ(x)·ξ(x)(η(x)).
6. (Integration.) By steps 3–5, the integrand in (iv) (with ω′ = ω) and the integrand in (ii) (with ψ = η) agree ν-a.e. So their integrals over M coincide (integral_congr_ae for ν). Therefore S(ω) = ∫_M θ·ξ(η) dμ = tauAction n M θ ξ η = X(η). ∎

## Key steps

1. Unfold IsLipschitzPushforward: X = τ(M, θ, ξ), f has tangential directional derivatives L(x)v a.e., and S(ω) = ∫_M θ (L_#ξ)(ω∘f) dHⁿ.
2. By the sibling support-null lemma, Hⁿ⌞M-a.e. point of M lies in spt X ⊆ N.
3. At such points, uniqueness of the derivative of t ↦ f(x + tτ_i) gives L(x) ∘ τ = Df(x) ∘ τ on the orienting frame. Hence (L(x)_#ξ(x))(ω(f x)) = ξ(x)(Df(x)^#ω(f x)) = ξ(x)(η(x)).
4. The integrands of S(ω) and X(η) agree a.e. on M, so S(ω) = X(η) by integral_congr_ae.

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
