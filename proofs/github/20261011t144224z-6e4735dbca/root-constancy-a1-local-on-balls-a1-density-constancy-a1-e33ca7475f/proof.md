# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1.local_on_balls-a1`
- Child DAG node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to Geometric Measure Theory, Ch. 6, Theorem 2.34 (Constancy Theorem) and its printed proof, pp. 142–143, as expanded in the accepted proof of the parent node root.constancy-a1.local_on_balls-a1 (book n = m + 1; erratum applied there: the garbled printed display (1) reads T(a_ε dx¹∧⋯∧dxⁿ) = ∫ a θ_ε dLⁿ for a ∈ L¹(B_ρ(x₀)), with a_ε = ϕ_ε ∗ a). This child is Step 4 of that proof: the printed display (2), “∫ D_j a θ_ε dLⁿ = T(dω_j) = ∂T(ω_j) = 0, j = 1,…,n”, and the following conclusion that θ_ε is constant on B_ρ(x₀); the hypothesis u(D_j a) = 0 plays the role of T(dω_j) = ∂T(ω_j) = 0, and a general kernel φ that of ϕ_ε.
Notation. ℝⁿ = Eucl n = EuclideanSpace ℝ (Fin n); e_j = EuclideanSpace.single j 1 is the j-th standard basis vector and e = (e_1,…,e_n); Lⁿ = Lebesgue measure (Lean: volume); spt g = tsupport g (closure of {g ≠ 0}); B_s(x) = ball x s, B̄_s(x) = closedBall x s; D^q g = iteratedFDeriv ℝ q g; D_j g(x) = Dg(x)(e_j) = fderiv ℝ g x (e_j); (f ∗ g)(x) = ∫ f(t) g(x − t) dLⁿ(t) is convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume; 1_B f = B.indicator f (f on B, 0 off B); “C^∞” means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞). A function a : ℝⁿ → ℝ is called admissible (for U) if a is C^∞, has compact support and spt a ⊆ U.

Proof. Put B := B_ρ(x₀).

1. (Test functions in B.) Let a : ℝⁿ → ℝ be C¹ with compact support and spt a ⊆ B, and let j ∈ {1,…,n}. Put d := D_j a, d(x) = Da(x)(e_j). Then d is continuous (Da is continuous), and spt d ⊆ spt a ⊆ B (the derivative vanishes on the open set where a vanishes identically). So d has compact support, d is integrable on ℝⁿ (continuous with compact support), in particular integrable on B, d = 0 outside B, and 1_B d = d.

2. (φ ∗ a is admissible.) φ ∗ a is C^∞ (φ is C^∞ with compact support; a is continuous, hence locally integrable). Moreover {φ ∗ a ≠ 0} ⊆ {φ ≠ 0} + {a ≠ 0} ⊆ B̄_ε(0) + B_ρ(x₀) ⊆ B̄_{ρ+ε}(x₀) (‖s + t − x₀‖ ≤ ‖s‖ + ‖t − x₀‖ ≤ ε + ρ). Hence spt(φ ∗ a) ⊆ B̄_{ρ+ε}(x₀) ⊆ U, and φ ∗ a has compact support (the convolution of two compactly supported functions). So φ ∗ a is C^∞ with compact support and spt(φ ∗ a) ⊆ U.

3. (The derivative falls on a; fact (M4) of the parent proof.) Since a is C¹ with compact support and φ is locally integrable, φ ∗ a is differentiable at every x with D(φ ∗ a)(x) = (φ ∗ Da)(x), the convolution of φ with the operator-valued function Da (differentiation under the integral sign). Evaluating at e_j (evaluation at a fixed vector commutes with the convolution integral, since Da is continuous with compact support) gives D_j(φ ∗ a)(x) = (φ ∗ d)(x) for every x. Hence the functions D_j(φ ∗ a) and φ ∗ d = φ ∗ (1_B d) coincide.

4. (Printed display (2).) By the hypothesis on u applied to the admissible function φ ∗ a of Step 2, u(D_j(φ ∗ a)) = 0. Using Step 3 and then hypothesis (1) with f := d (integrable on B by Step 1):
 ∫_B d θ dLⁿ = u(φ ∗ (1_B d)) = u(D_j(φ ∗ a)) = 0.
 Since d = 0 outside B, ∫_{ℝⁿ} θ(x)·Da(x)(e_j) dx = ∫_B θ d dLⁿ = ∫_B d θ dLⁿ = 0.
 [Printed form: with ω_j = (−1)^{j−1} a_ε dx¹∧⋯∧dx^{j−1}∧dx^{j+1}∧⋯∧dxⁿ one has dω_j = (D_j a)_ε dx¹∧⋯∧dxⁿ, and (2) reads ∫ D_j a θ_ε = T(dω_j) = ∂T(ω_j) = 0.]

5. (θ is a.e. constant on B.) θ is measurable and |θ| ≤ M, hence integrable on every compact set (compact sets have finite Lebesgue measure); so θ is locally integrable on ℝⁿ and therefore locally integrable on B. B is open and convex, hence preconnected. Step 4 shows ∫ θ(x)·Da(x)(e_j) dx = 0 for every C¹ compactly supported a with spt a ⊆ B and every j, where e_j = (EuclideanSpace.basisFun (Fin n) ℝ) j. These are exactly the hypotheses of the kernel-checked lemma Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero (module Poincare.SimonGMT.Chapter08.DistributionalConstancy of the pinned simongmt package; axioms propext, Classical.choice, Quot.sound only), applied with B in place of U and θ in place of f. It yields c ∈ ℝ with θ(x) = c for Lⁿ-a.e. x ∈ B. [This lemma is exactly the printed argument: for 0 < σ < ρ and a mollifier ϕ_σ (C^∞, ≥ 0, ∫ ϕ_σ = 1, spt ϕ_σ ⊆ B̄_σ(0)) the C^∞ function ϕ_σ ∗ (1_B θ) has zero first derivatives on B_{ρ−σ}(x₀) (apply (2) to a = ϕ_σ(x − ·)), hence is constant there, and letting σ ↓ 0 (Lebesgue differentiation) θ is a.e. constant on B.]

6. (Conclusion.) For every f integrable on B, by (1) and Step 5, u(φ ∗ (1_B f)) = ∫_B f θ dLⁿ = ∫_B f·c dLⁿ = c ∫_B f dLⁿ: the integrands f θ and f·c agree Lⁿ-a.e. on B, and the constant factor comes out of the integral. ∎

Formalization notes (no new mathematics). Required import: the SimonGMT lemma is not visible through the frozen `import GMT.Ch06.Submission`; add `import Poincare.SimonGMT.Chapter08.DistributionalConstancy` to the imports of GMT/Ch06/Submission.lean (a module of the pinned simongmt package; adding it keeps every frozen Ch06 statement elaborating unchanged and introduces no new Lake warning, unlike direct Mathlib imports). Poincare.SimonGMT.Chapter08.Euclidean n is definitionally Eucl n, so the lemma applies without casts: ae_eq_const_of_weak_coordinate_derivatives_zero (hθli.locallyIntegrableOn (ball x₀ ρ)) isOpen_ball (convex_ball x₀ ρ).isPreconnected hw, after rw [EuclideanSpace.basisFun_apply] inside hw. Checked call shapes, with L := ContinuousLinearMap.lsmul ℝ ℝ and hφli := hφ.continuous.locallyIntegrable: hφc.contDiff_convolution_left L hφ ha.continuous.locallyIntegrable; hφc.convolution L hac (compact support of φ ∗ a); support_convolution_subset L with Set.mem_add, closure_minimal, isClosed_closedBall; (hac.hasFDerivAt_convolution_right L hφli ha x).fderiv; convolution_precompR_apply L hφli (hac.fderiv ℝ) (ha.continuous_fderiv one_ne_zero) x v; (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const; tsupport_fderiv_apply_subset ℝ v; hac.fderiv_apply ℝ v; Continuous.integrable_of_hasCompactSupport; Set.indicator_eq_self; image_eq_zero_of_notMem_tsupport; setIntegral_eq_integral_of_forall_compl_eq_zero; locallyIntegrable_iff with Measure.integrableOn_of_bounded and IsCompact.measure_lt_top; LocallyIntegrable.locallyIntegrableOn; integral_congr_ae; integral_mul_const.

## Key steps

1. For a ∈ C¹ with compact support in B and each j, d = D_j a is continuous, compactly supported in B, integrable, and 1_B d = d.
2. φ ∗ a is C^∞ with compact support and spt(φ ∗ a) ⊆ B̄_{ρ+ε}(x₀) ⊆ U.
3. D_j(φ ∗ a) = φ ∗ D_j a (HasCompactSupport.hasFDerivAt_convolution_right, convolution_precompR_apply).
4. Printed (2): ∫_B (D_j a) θ = u(φ ∗ 1_B D_j a) = u(D_j(φ ∗ a)) = 0, hence ∫ θ·Da(·)(e_j) = 0.
5. SimonGMT ae_eq_const_of_weak_coordinate_derivatives_zero on the convex open ball B (θ bounded measurable, so locally integrable): θ = c a.e. on B.
6. u(φ ∗ 1_B f) = ∫_B f θ = c ∫_B f.

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
