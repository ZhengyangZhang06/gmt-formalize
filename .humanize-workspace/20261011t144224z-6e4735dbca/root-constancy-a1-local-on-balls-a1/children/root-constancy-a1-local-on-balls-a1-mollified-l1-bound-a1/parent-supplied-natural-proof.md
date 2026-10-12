# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1.local_on_balls-a1`
- Child DAG node: `root.constancy-a1.local_on_balls-a1.mollified_l1_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to Geometric Measure Theory, Ch. 6, Theorem 2.34 (Constancy Theorem) and its printed proof, pp. 142–143, as expanded in the accepted proof of the parent node root.constancy-a1.local_on_balls-a1 (book n = m + 1; erratum applied there: the garbled printed display (1) reads T(a_ε dx¹∧⋯∧dxⁿ) = ∫ a θ_ε dLⁿ for a ∈ L¹(B_ρ(x₀)), with a_ε = ϕ_ε ∗ a). This child is the first half of Step 3 of that proof, the printed sentence “if a_j → a in L¹(B_ρ(x₀)) … then a_j^(ε) dx¹∧⋯∧dxⁿ → a^(ε) dx¹∧⋯∧dxⁿ in Dⁿ(U), and hence T(a_j^(ε) dx) → T(a^(ε) dx). Thus the functional F(a) = T(a^(ε) dx) is a bounded linear functional on L¹(B_ρ(x₀))”, with the scalar functional u in place of a ↦ T(a dx), and with the boundedness made explicit by the contradiction argument given in brackets in Step 3 of the parent proof.
Notation. ℝⁿ = Eucl n = EuclideanSpace ℝ (Fin n); e_j = EuclideanSpace.single j 1 is the j-th standard basis vector and e = (e_1,…,e_n); Lⁿ = Lebesgue measure (Lean: volume); spt g = tsupport g (closure of {g ≠ 0}); B_s(x) = ball x s, B̄_s(x) = closedBall x s; D^q g = iteratedFDeriv ℝ q g; D_j g(x) = Dg(x)(e_j) = fderiv ℝ g x (e_j); (f ∗ g)(x) = ∫ f(t) g(x − t) dLⁿ(t) is convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume; 1_B f = B.indicator f (f on B, 0 off B); “C^∞” means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞). A function a : ℝⁿ → ℝ is called admissible (for U) if a is C^∞, has compact support and spt a ⊆ U. (L1), (L2), (C) and (Bd) are the hypotheses of the statement, and F(f) := u(φ ∗ 1_B f).

Proof. Throughout, B := B_ρ(x₀) and K := B̄_{ρ+ε}(x₀); K is closed and bounded in ℝⁿ, hence compact, and K ⊆ U by hypothesis. A function g with spt g ⊆ K has compact support (a closed subset of a compact set).

1. (Mollified functions are admissible.) Let f be integrable on B and g := 1_B f. As B is measurable, g is integrable on ℝⁿ, in particular locally integrable. Then:
 (a) φ ∗ g is C^∞ (φ is C^∞ with compact support and g is locally integrable; differentiation under the integral sign);
 (b) {φ ∗ g ≠ 0} ⊆ {φ ≠ 0} + {g ≠ 0} ⊆ B̄_ε(0) + B_ρ(x₀) (spt φ ⊆ B̄_ε(0), and g = 0 off B); if ‖s‖ ≤ ε and ‖t − x₀‖ < ρ then ‖s + t − x₀‖ ≤ ‖s‖ + ‖t − x₀‖ < ρ + ε, so this set lies in K. As K is closed, spt(φ ∗ g) ⊆ K; hence φ ∗ g has compact support and is admissible with spt(φ ∗ g) ⊆ K;
 (c) the convolution integral defining φ ∗ g converges at every point (φ is continuous with compact support and g is locally integrable).

2. (Linearity of F.) Let f, h be integrable on B and c ∈ ℝ. Then 1_B(f + h) = 1_B f + 1_B h and 1_B(c·f) = c·1_B f. By 1(c) the convolution is additive, φ ∗ (1_B f + 1_B h) = φ ∗ 1_B f + φ ∗ 1_B h, and it is homogeneous, φ ∗ (c·1_B f) = c·(φ ∗ 1_B f). The functions φ ∗ 1_B f and φ ∗ 1_B h are admissible by Step 1, so (L1) and (L2) give F(f + h) = F(f) + F(h) and F(c·f) = c·F(f).

3. (u(0) = 0.) The zero function is admissible (C^∞, spt 0 = ∅), so (L2) with c = 0 and a = 0 gives u(0) = u(0·0) = 0·u(0) = 0.

4. (Boundedness, by contradiction.) Suppose that no C ∈ ℝ satisfies |F(f)| ≤ C ∫_B |f| dLⁿ for all f integrable on B. Then for every k ∈ ℕ (taking C = k + 1) there is f_k integrable on B with |F(f_k)| > (k + 1)·∫_B |f_k| dLⁿ. The right-hand side is ≥ 0, so F(f_k) ≠ 0. Put g_k := F(f_k)⁻¹·f_k. Then g_k is integrable on B, F(g_k) = F(f_k)⁻¹·F(f_k) = 1 by Step 2, and
 ∫_B |g_k| dLⁿ = |F(f_k)|⁻¹·∫_B |f_k| dLⁿ ≤ 1/(k + 1)   (because (k + 1)·∫_B |f_k| < |F(f_k)|).
 Let b_k := φ ∗ 1_B g_k. By Step 1 each b_k is C^∞ with spt b_k ⊆ K. Apply (Bd) to the integrable function 1_B g_k, for which ∫ |1_B g_k| dLⁿ = ∫_B |g_k| dLⁿ ≤ 1/(k + 1): for every q and x, ‖D^q b_k(x)‖ ≤ C_q·∫_B |g_k| ≤ max(C_q, 0)/(k + 1). Since max(C_q, 0)/(k + 1) → 0, for every q we get D^q b_k → 0 = D^q 0 uniformly on ℝⁿ, where 0 is the zero function (C^∞, spt 0 = ∅ ⊆ K). By (C), applied with this K, a_k := b_k and b := 0, u(b_k) → u(0) = 0 (Step 3). But u(b_k) = F(g_k) = 1 for every k, and the constant sequence 1 does not converge to 0: a contradiction.
 Hence there is C ∈ ℝ with |F(f)| ≤ C ∫_B |f| dLⁿ for every f integrable on B.
 [This is the bracketed argument of Step 3 of the parent proof — normalize counterexamples so that their L¹(B) norms tend to 0 while F stays away from 0, then contradict sequential continuity — with the normalization by F(f_k) instead of by ∫_B |f_k|, which makes a separate treatment of the case ∫_B |f_k| = 0 unnecessary.]

5. Steps 2 and 4 are the three assertions of the statement. ∎

Formalization notes (no new mathematics; no import beyond the frozen GMT.Ch06.Submission is needed). The convolution lemmas take the bilinear map L := ContinuousLinearMap.lsmul ℝ ℝ explicitly: HasCompactSupport.contDiff_convolution_left L hφ hg.locallyIntegrable (its order n : ℕ∞ matches ((⊤ : ℕ∞) : WithTop ℕ∞) directly), HasCompactSupport.convolutionExists_left L hφ.continuous hg.locallyIntegrable, ConvolutionExists.distrib_add, convolution_smul, support_convolution_subset L with Set.mem_add, Set.support_indicator_subset, subset_tsupport, mem_closedBall_zero_iff, norm_add_le, closure_minimal and isClosed_closedBall. Also: IntegrableOn.integrable_indicator with measurableSet_ball; Set.indicator_add'; Set.indicator_const_smul (ball x₀ ρ) c f (give the three arguments explicitly); ∫ |1_B h| = ∫_B |h| via integral_indicator after rewriting |1_B h| = 1_B |h| pointwise; contDiff_zero_fun, HasCompactSupport.zero, tsupport_zero and iteratedFDeriv_zero for b = 0; `push Not` (push_neg is deprecated in this Mathlib) and `choose` to extract f_k; Integrable.smul, integral_const_mul, inv_mul_le_iff₀, le_div_iff₀; Metric.tendstoUniformly_iff, tendsto_one_div_add_atTop_nhds_zero_nat, tendsto_order and tendsto_const_nhds_iff.

## Key steps

1. For f integrable on B, φ ∗ 1_B f is C^∞, the convolution exists everywhere, and spt(φ ∗ 1_B f) ⊆ K = B̄_{ρ+ε}(x₀), a compact subset of U: it is admissible.
2. F is additive and homogeneous: indicator and convolution are linear (ConvolutionExists.distrib_add, convolution_smul), then (L1), (L2).
3. u(0) = 0 by (L2) with c = 0.
4. If F were unbounded, f_k with |F(f_k)| > (k+1)∫_B|f_k| normalize to g_k = F(f_k)⁻¹f_k with F(g_k) = 1 and ∫_B|g_k| ≤ 1/(k+1).
5. By (Bd), D^q(φ ∗ 1_B g_k) → 0 uniformly with supports in K, so (C) forces 1 = F(g_k) → u(0) = 0: contradiction.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean with the workspace GMT/Ch06/Contract.lean and with project/GMT/Ch06/Submission.lean (all identical); grep -n 'ConstancyTheorem' -A 25 GMT/Ch06/Contract.lean`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right|hasFDerivAt_convolution_right' mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `rg -n 'convolutionExists_left|HasCompactSupport.convolution |theorem support_convolution_subset|theorem ConvolutionExists.distrib_add|theorem convolution_smul|theorem convolution_precompR_apply' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem (contDiff_normed|integral_normed|tsupport_normed_eq|hasCompactSupport_normed|nonneg_normed|continuous_normed)' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -n 'theorem AlternatingMap.eq_smul_basis_det|theorem det_self' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `rg -n 'iteratedFDeriv_comp_left|norm_compContinuousMultilinearMap_le|tsupport_fderiv_apply_subset|HasCompactSupport.fderiv_apply|setIntegral_eq_integral_of_forall_compl_eq_zero|ae_convolution_tendsto_right_of_locallyIntegrable' mathlib/Mathlib; rg -n '^def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `grep -n 'structure GeometricCurrentOn|def TestFormOnConverges|abbrev TestFormOn|abbrev DifferentialForm|def IsTestForm' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `grep -n 'def wedgeCovectors|theorem wedgeCovectors_apply_det' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean; grep -n 'theorem ae_eq_const_of_weak_coordinate_derivatives_zero' -A 8 simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean; grep -n 'exists_compact_derivative_bound' simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `#check after the frozen `import GMT.Ch06.Submission`: convolution API present; ContDiffBump.normed, Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero and GeometricCurrentOn.exists_compact_derivative_bound unknown`
- `lake build GMT.Ch06.Submission for the frozen commit (/tmp/lob2_check), for a variant adding only `import Poincare.SimonGMT.Chapter08.DistributionalConstancy` (/tmp/lob2_imp2: no new Lake warning; exposes ContDiffBump.normed and the SimonGMT lemma) and for a variant adding Mathlib imports (/tmp/lob2_imports: new Lake 'module system' warnings)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py child_modules (contract scope) on the 4 statements; lake env lean on the generated NodeChallenge modules against the frozen Submission and the variant`
- `lean Scratch/Child_{scalar_reduction,mollified_l1_bound,density_constancy,mollifier_limit}.lean (complete proofs, #print axioms) against the frozen Submission and with the single extra import; lean Scratch/Assembly.lean and Scratch/EndToEnd.lean (exact frozen parent type from the 4 children and the 3 dependency types; accepted mollifier proofs taken from commits d6285a3 and 933d7e8; Riesz stubbed)`
- `python3 -I scan of dag.json lean_name values (266 nodes) for the 4 proposed names and child ids; grep of simongmt/Poincare and the snapshot project for the names (no match)`
- `git show 56f7ba4 (speculative draft of root.constancy-a1 calling Submission.constancy_local_on_balls m U hU T (Submission.constancy_closed_kills_partial_derivatives m U T hT))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1/decomposition-v1.json`
- `/tmp/lob2_imp2/Scratch/Child_scalar_reduction.lean`
- `/tmp/lob2_imp2/Scratch/Child_mollified_l1_bound.lean`
- `/tmp/lob2_imp2/Scratch/Child_density_constancy.lean`
- `/tmp/lob2_imp2/Scratch/Child_mollifier_limit.lean`
- `/tmp/lob2_imp2/Scratch/Assembly.lean`
- `/tmp/lob2_imp2/Scratch/EndToEnd.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c; the frozen Contract.lean and Submission.lean are byte-identical. ConstancyTheorem quantifies over GeometricCurrentOn U (m+1): linear functionals on C^∞ compactly supported TestFormOn U (m+1) with T(ω_k) → 0 whenever TestFormOnConverges ω 0.

Available through the frozen import: Mathlib's first-derivative convolution API (HasCompactSupport.contDiff_convolution_left/right, hasFDerivAt_convolution_right, convolutionExists_left, ConvolutionExists.distrib_add, convolution_smul, support_convolution_subset, convolution_precompR_apply), AlternatingMap.eq_smul_basis_det, ContinuousLinearMap.iteratedFDeriv_comp_left, tsupport_fderiv_apply_subset, ContinuousAlternatingMap.apply, and SimonGMT wedgeCovectors/wedgeCovectors_apply_det (a ready-made continuous dx¹∧⋯∧dxⁿ).

Not available through the frozen import: ContDiffBump.normed, the SimonGMT weak-constancy lemma ae_eq_const_of_weak_coordinate_derivatives_zero and GeometricCurrentOn.exists_compact_derivative_bound. Adding `import Poincare.SimonGMT.Chapter08.DistributionalConstancy` to Submission.lean provides the first two, adds no new Lake warning, and leaves all 56 GMT.Ch06 declarations hash-identical; direct Mathlib imports add Lake 'module system' warnings.

Checks on the four children (constancy_topForm_scalar_reduction, constancy_mollified_functional_l1_bounded, constancy_mollified_density_const, constancy_local_of_mollified_const):
- Every statement passes the validator and elaborates in the exact comparator contract scope.
- Each has a complete Lean proof with axioms propext, Classical.choice, Quot.sound only. The first two need no new import; the last two need the single SimonGMT import above.
- An end-to-end file proves the parent's exact frozen type from the four children and the three dependencies; its only sorry is the still-decomposing Riesz dependency.
- An independent audit accepted all four children.
- The names collide with no DAG node or library declaration.
