# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1`
- Child DAG node: `root.constancy-a1.mollifier_derivative_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, proof of Theorem 2.34 (p. 142): “D^β a^{(σ)} = (D^β φ^{(σ)}) ∗ a for each multi-index β, so if a_j → a in L¹(B_ρ(x₀)) ... then a_j^{(σ)} dx¹∧⋯∧dxⁿ → a^{(σ)} dx¹∧⋯∧dxⁿ in Dⁿ(U)”, together with the mollifier facts of Ch. 2, §2. This lemma is the quantitative form of that remark (all derivatives of a mollification are controlled by the L¹ norm of the mollified function), with the standard proof (differentiation under the integral sign) filled in.

Statement. Let n ∈ ℕ, φ : ℝⁿ → ℝ be C^∞ with compact support, and q ∈ ℕ. Then there is C ∈ ℝ such that for every Lebesgue-integrable g : ℝⁿ → ℝ and every x ∈ ℝⁿ, ‖D^q(φ ∗ g)(x)‖ ≤ C ∫ |g| dLⁿ, where (φ ∗ g)(x) = ∫ φ(t) g(x − t) dLⁿ(t) (Lean: convolution φ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, see `convolution_def`) and D^q is the q-th Fréchet derivative (Lean: iteratedFDeriv ℝ q; ‖·‖ is the norm of q-multilinear maps).

Proof. We prove a more general claim by induction on q, in which the kernel may be vector-valued; this is needed because the derivative of a real kernel is vector-valued.

1. (General convolutions.) For real normed spaces E, F (F complete), a continuous bilinear map L : E × ℝ → F (Lean: L : E →L[ℝ] ℝ →L[ℝ] F), a function f : ℝⁿ → E and g ∈ L¹(ℝⁿ), put (f ∗_L g)(x) := ∫ L(f(t), g(x − t)) dt (Lean: convolution f g L volume). For E = F = ℝ and L = lsmul (L(s, t) = s t) this is φ ∗ g.

2. (Claim P(q).) For all E, F, L as in 1 and every B ≥ 0 with ‖L(u, t)‖ ≤ B ‖u‖ |t| for all u ∈ E, t ∈ ℝ; every C^∞ f : ℝⁿ → E with compact support; every S ∈ ℝ with ‖D^q f(t)‖ ≤ S for all t; every g ∈ L¹(ℝⁿ) and every x ∈ ℝⁿ:
 ‖D^q(f ∗_L g)(x)‖ ≤ B · S · ∫ |g| dLⁿ.
(The bound is phrased with an explicit constant B rather than the operator norm ‖L‖; this avoids norm-instance issues for the iterated bilinear maps of Step 4 and is mathematically equivalent.)

3. (P(0).) D^0 h(x) is h(x) (up to the isometry identifying E with 0-multilinear maps; `norm_iteratedFDeriv_zero`). By `convolution_def` and the norm bound for integrals (`norm_integral_le_of_norm_le`): ‖(f ∗_L g)(x)‖ ≤ ∫ ‖L(f(t), g(x − t))‖ dt ≤ ∫ B S |g(x − t)| dt = B S ∫ |g(x − t)| dt = B S ∫ |g| dLⁿ, since ‖f(t)‖ ≤ S and Lebesgue measure is invariant under t ↦ x − t (`integral_sub_left_eq_self`; t ↦ |g(x − t)| is integrable by `Integrable.comp_sub_left`).

4. (Derivative of a convolution.) If f is C^∞ with compact support and g ∈ L¹(ℝⁿ) (in particular locally integrable), then f ∗_L g is differentiable at every point with D(f ∗_L g)(y) = ((Df) ∗_{L'} g)(y) (differentiation under the integral sign; Mathlib `HasCompactSupport.hasFDerivAt_convolution_left`), where Df : ℝⁿ → (ℝⁿ →L E) is again C^∞ with compact support (`ContDiff.fderiv_right`, `HasCompactSupport.fderiv`) and L' := L.precompL : (ℝⁿ →L E) × ℝ → (ℝⁿ →L F), L'(u, t)(v) = L(u v, t). L' satisfies the same bound: ‖L'(u, t)(v)‖ = ‖L(u v, t)‖ ≤ B ‖u v‖ |t| ≤ B ‖u‖ ‖v‖ |t| for all v, hence ‖L'(u, t)‖ ≤ B ‖u‖ |t| (`ContinuousLinearMap.opNorm_le_bound`, `ContinuousLinearMap.precompL_apply`). Hence, as functions, D(f ∗_L g) = (Df) ∗_{L'} g.

5. (P(q) ⇒ P(q + 1).) Let f, S be as in P(q+1), i.e. ‖D^{q+1} f(t)‖ ≤ S for all t. The (q+1)-st derivative is the q-th derivative of the first derivative, with equal norms: ‖D^{q+1}h(x)‖ = ‖D^q(Dh)(x)‖ (Mathlib `norm_iteratedFDeriv_fderiv`). Hence ‖D^q(Df)(t)‖ = ‖D^{q+1}f(t)‖ ≤ S for every t, and, with h = f ∗_L g and Step 4,
 ‖D^{q+1}(f ∗_L g)(x)‖ = ‖D^q((Df) ∗_{L'} g)(x)‖ ≤ B · S · ∫|g| dLⁿ
by P(q) applied to the space ℝⁿ →L E, the kernel Df, the bilinear map L' (with the same B) and the same S. This proves P(q+1). (The induction is over q, with E, F, L, B, f, S, g, x universally quantified inside the claim.)

6. (Conclusion.) D^q φ is continuous with compact support, so S := sup_t ‖D^q φ(t)‖ is finite (`Continuous.bddAbove_range_of_hasCompactSupport`). Apply P(q) with E = F = ℝ, L = lsmul, B = 1 (|s t| = |s| |t|) and f = φ: the constant C := S does not depend on g or x, and ‖D^q(φ ∗ g)(x)‖ ≤ C ∫ |g| dLⁿ for every integrable g and every x. ∎

## Key steps

1. Generalize to vector-valued C_c^∞ kernels f and bilinear L with ‖L(u,t)‖ ≤ B‖u‖|t|: claim ‖D^q(f ∗_L g)(x)‖ ≤ B·S·∫|g| when ‖D^q f‖ ≤ S.
2. q = 0: norm of the integral ≤ B·sup‖f‖·∫|g(x − t)|dt = B·sup‖f‖·∫|g|.
3. D(f ∗_L g) = (Df) ∗_{L.precompL} g, and L.precompL satisfies the same bound B.
4. ‖D^{q+1}h‖ = ‖D^q(Dh)‖ closes the induction; specialize to φ, lsmul, B = 1, S = sup‖D^qφ‖.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean and vs project/GMT/Ch06/Submission.lean (byte-identical)`
- `grep -n 'ConstancyTheorem' -A 25 GMT/Ch06/Contract.lean`
- `rg -n 'theorem AlternatingMap.eq_smul_basis_det|theorem det_self' mathlib/Mathlib/LinearAlgebra`
- `rg -n 'theorem extDeriv_apply' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/`
- `rg -n 'curryLeft|removeNth' mathlib/Mathlib/Analysis/Normed/Module/Alternating/ ; rg -n 'theorem sign_cycleRange|cons_removeNth' mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `rg -n 'L1.*[Dd]ual|[Dd]ual.*L1|LpDual|Lp.dual|toDual|dualLp|Linfty' mathlib/Mathlib/MeasureTheory -l ; rg -n 'StrongDual|Dual' mathlib/Mathlib/MeasureTheory/Function/Holder.lean`
- `rg -n 'contDiff_convolution|hasFDerivAt_convolution|fderiv_convolution' mathlib/Mathlib/Analysis/ (first derivatives only; no iteratedFDeriv-of-convolution lemma)`
- `rg -n 'ae_convolution_tendsto_right_of_locallyIntegrable|integral_normed|tsupport_normed_eq|normed_neg|nonneg_normed|contDiff_normed' mathlib/Mathlib/Analysis/Calculus/BumpFunction/`
- `rg -n 'withDensityᵥ_rnDeriv_eq|def rnDeriv|integrable_rnDeriv' mathlib/Mathlib/MeasureTheory/Measure/Decomposition/ mathlib/Mathlib/MeasureTheory/VectorMeasure/`
- `rg -n 'theorem exists_isSubordinate' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `rg -n 'is_const_of_fderiv|IsPreconnected.constant|setIntegral_eq_integral_of_forall_compl_eq_zero' mathlib/Mathlib/Analysis/Calculus/MeanValue.lean mathlib/Mathlib/Topology/Connected/ mathlib/Mathlib/MeasureTheory/Integral/`
- `rg -n 'dist_convolution_le|norm_iteratedFDeriv_fderiv|iteratedFDeriv_succ_eq_comp_left|def precompL|norm_precompL_le' mathlib/Mathlib/Analysis`
- `rg -n -i 'constancy|mollif' simongmt/Poincare/SimonGMT ; rg -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean simongmt/Poincare/SimonGMT/Chapter01/FiniteL1Dual.lean`
- `#print axioms Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero ; #print axioms Poincare.SimonGMT.Chapter06.GeometricCurrentOn.exists_compact_derivative_bound`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the 6 child statements`
- `verifier/gmt-compare.py contract_scope + child_modules: generate and compile NodeChallenge/NodeSolution for all 6 children against stub Submission.<lean_name> (scratch /tmp/constancy_decomp_check, frozen commit d8d46c9, pinned packages)`
- `lean Scratch/ParentFromChildren.lean and Scratch/C2Usage.lean (parent assembly vs ConstancyTheorem; instantiation of the Riesz, bound and convergence siblings, normalized bumps, SimonGMT weak constancy)`
- `lean Scratch/ExtDerivCheck.lean, Scratch/DetForm.lean, Scratch/Review_C1.lean, Scratch/Review2_M1.lean, Scratch/Review2_M2.lean, Scratch/Review_API.lean (#print axioms)`
- `python3 listing of dag.json lean_name values (50 nodes; none equal to the 6 proposed names)`
- `grep -n 'Constancy' book/chapter-06.txt (printed proof of 2.34, p. 142-143)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Holder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Connected/TotallyDisconnected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentDistributionEquivalence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/FiniteL1Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/tmp/constancy_decomp_check/Scratch/ParentFromChildren.lean`
- `/tmp/constancy_decomp_check/Scratch/C2Usage.lean`
- `/tmp/constancy_decomp_check/Scratch/ExtDerivCheck.lean`
- `/tmp/constancy_decomp_check/Scratch/Review_C1.lean`
- `/tmp/constancy_decomp_check/Scratch/Review2_M1.lean`
- `/tmp/constancy_decomp_check/Scratch/Review2_M2.lean`
- `/tmp/constancy_decomp_check/Scratch/Review_API.lean`

Snapshot context: project d8d46c95 with Mathlib 25730c7c. The frozen Contract and Submission are byte-identical. `ConstancyTheorem` quantifies over `GeometricCurrentOn U (m+1)`, which consists of linear functionals on C^∞ (not analytic) compactly supported `TestFormOn` that are sequentially continuous in the `TestFormOnConverges` sense.

What Mathlib provides: `AlternatingMap.eq_smul_basis_det` (top-degree forms are multiples of det), `extDeriv_apply`, `ContinuousAlternatingMap.curryLeft`, `Fin.cons_removeNth_eq_comp_cycleRange_symm` and `Fin.sign_cycleRange`. These give C1's identity d(a·ι_{e_j}dx)(e) = D_j a, which was kernel-checked. Mathlib also has first-derivative convolution lemmas (`HasCompactSupport.hasFDerivAt_convolution_left/right`, `contDiff_convolution_left`), normalized bumps (`ContDiffBump.normed`), Lebesgue-differentiation a.e. convergence (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), `dist_convolution_le`, signed Radon–Nikodym (`SignedMeasure.withDensityᵥ_rnDeriv_eq`), `SmoothPartitionOfUnity.exists_isSubordinate` and `IsLocallyConstant.exists_eq_const`.

What Mathlib lacks: no iterated-derivative-of-convolution lemma, and no (L¹)* = L^∞ theorem (Holder.lean only has the pairing map). These motivate the three analytic siblings.

Reusable SimonGMT lemmas, all with only propext, Classical.choice and Quot.sound: `ae_eq_const_of_weak_coordinate_derivatives_zero` (Chapter08/DistributionalConstancy.lean: zero weak gradient with C¹ tests implies a.e. constant), `GeometricCurrentOn.exists_compact_derivative_bound` (the finite-order estimate) and `finiteL1DualField` (Chapter01/FiniteL1Dual.lean, an alternative route for the Riesz lemma).

Statement checks: all six child statements pass the comparator validator and compile as generated NodeChallenge/NodeSolution modules in the exact contract scope. `ContDiffBump.normed` is not importable through the frozen Submission, which is why it is avoided in the frozen statements. The parent assembly typechecks against `ConstancyTheorem`. Full proofs of C1, M1 and M2 compile against the verbatim statements with standard axioms.

Names: none of the six names collides with the 50 DAG nodes.
