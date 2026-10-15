# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1`
- Child DAG node: `root.constancy-a1.riesz_l1_dual-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, proof of Theorem 2.34 (p. 142), which invokes “the Riesz representation theorem for L¹(B_ρ(x₀))”: every bounded linear functional on L¹ of a finite measure is integration against a bounded measurable function ((L¹)* = L^∞). Simon cites this standard theorem without proof; the standard Radon–Nikodym proof is supplied below in the generality of an arbitrary finite measure (it is applied with μ = Lⁿ restricted to a ball).

Statement. Let (α, 𝔐) be a measurable space, μ a finite measure on α, F : (α → ℝ) → ℝ and C ∈ ℝ such that for all μ-integrable f, g and all c ∈ ℝ: (i) F(f + g) = F(f) + F(g); (ii) F(c f) = c F(f); (iii) |F(f)| ≤ C ∫|f| dμ. Then there is a measurable θ : α → ℝ with |θ(x)| ≤ M for all x (some M ∈ ℝ) such that F(f) = ∫ f θ dμ for every μ-integrable f.

Proof.

1. (Normalization.) Put C' := max(C, 0) ≥ 0; then |F(f)| ≤ C ∫|f| ≤ C' ∫|f| for integrable f, so (iii) holds with C' and we may assume C ≥ 0. By (ii) with c = 0, F(0) = 0. For integrable f, g we have f − g = f + (−1)·g, so F(f − g) = F(f) − F(g) by (i), (ii). Consequently, if f = g μ-a.e. (both integrable) then |F(f) − F(g)| = |F(f − g)| ≤ C ∫|f − g| dμ = 0, i.e. F(f) = F(g).

2. (The set function.) For measurable A ⊆ α the indicator 1_A is μ-integrable (μ(α) < ∞); put ν(A) := F(1_A). If A, B are disjoint measurable sets then 1_{A∪B} = 1_A + 1_B, so ν(A ∪ B) = ν(A) + ν(B) by (i); ν(∅) = F(0) = 0; and |ν(A)| ≤ C ∫ 1_A dμ = C μ(A) by (iii).

3. (Countable additivity.) Let (A_i)_{i∈ℕ} be pairwise disjoint measurable sets, A := ⋃_i A_i, S_N := ⋃_{i<N} A_i. By finite additivity, ν(A) − Σ_{i<N} ν(A_i) = ν(A \ S_N), and |ν(A \ S_N)| ≤ C μ(A \ S_N) → 0 as N → ∞, because A \ S_N decreases to ∅ and μ is finite (continuity from above). Moreover Σ_i |ν(A_i)| ≤ C Σ_i μ(A_i) = C μ(A) < ∞. Hence the series Σ_i ν(A_i) is absolutely, hence unconditionally, convergent with sum ν(A) (in Lean: HasSum, e.g. from summability of the norms and convergence of the partial sums). Setting ν(A) := 0 for non-measurable A, ν is a finite signed measure on (α, 𝔐) (Mathlib: `MeasureTheory.SignedMeasure`, i.e. `VectorMeasure α ℝ`). It is absolutely continuous with respect to μ: μ(A) = 0 implies |ν(A)| ≤ C μ(A) = 0.

4. (Radon–Nikodym.) μ is finite, hence σ-finite, and ν ≪ μ. By the Radon–Nikodym theorem for signed measures (Mathlib: `SignedMeasure.rnDeriv`, `SignedMeasure.integrable_rnDeriv`, `SignedMeasure.withDensityᵥ_rnDeriv_eq`) there is a measurable μ-integrable θ₀ : α → ℝ with ν(A) = ∫_A θ₀ dμ for every measurable A.

5. (Boundedness of the density.) Let A₊ := {x : θ₀(x) > C} (measurable). If μ(A₊) > 0, then ∫_{A₊} (θ₀ − C) dμ > 0, since the integrand is strictly positive on A₊ and A₊ has positive measure; that is, ν(A₊) = ∫_{A₊} θ₀ dμ > C μ(A₊), contradicting |ν(A₊)| ≤ C μ(A₊) from Step 2. So μ(A₊) = 0. Likewise A₋ := {θ₀ < −C} satisfies μ(A₋) = 0 (otherwise ν(A₋) < −C μ(A₋)). Define θ(x) := θ₀(x) if |θ₀(x)| ≤ C and θ(x) := 0 otherwise. Then θ is measurable, |θ(x)| ≤ C for every x (so M := C), θ = θ₀ μ-a.e., and therefore ν(A) = ∫_A θ dμ = ∫ 1_A θ dμ for every measurable A.

6. (Simple functions.) If s = Σ_{k=1}^{K} c_k 1_{A_k} with A_k measurable, then s is integrable and, by (i), (ii) and Step 5, F(s) = Σ_k c_k ν(A_k) = Σ_k c_k ∫ 1_{A_k} θ dμ = ∫ s θ dμ.

7. (All integrable functions.) For integrable f the product f θ is integrable (|f θ| ≤ C|f|, θ measurable). The property P(f): “F(f) = ∫ f θ dμ” holds for indicator functions c·1_A of measurable sets (Step 6), is preserved under sums of integrable functions (by (i) and linearity of the integral), is preserved under μ-a.e. equality (Step 1, and the integral only sees the a.e. class), and is closed in L¹: if ∫|f_k − f| dμ → 0 and P(f_k) for all k, then |F(f) − F(f_k)| = |F(f − f_k)| ≤ C ∫|f − f_k| → 0 and |∫ f θ − ∫ f_k θ| ≤ C ∫|f − f_k| → 0, so P(f). Since simple functions are dense in L¹(μ), P holds for every integrable f (in Mathlib this is exactly the induction principle `MeasureTheory.Integrable.induction`). Hence F(f) = ∫ f θ dμ for every μ-integrable f, with θ measurable and bounded. ∎

Remark (alternative route available in the pinned library). Steps 2–4 and the a.e. bound of Step 5 can be replaced by the Hilbert-space argument formalized in SimonGMT, module Poincare.SimonGMT.Chapter01.FiniteL1Dual (standard axioms only). By Step 1, F induces a bounded linear functional F̂ on the space Lp ℝ 1 μ of L¹ classes, F̂([f]) := F(f), with ‖F̂‖ ≤ C. If C = 0 then F = 0 on integrable functions and θ := 0 works. If C > 0, let ϑ := C·`finiteL1DualField μ (C⁻¹F̂)` (finiteL1DualField is ℝ-linear in its argument, being built from the linear map `InnerProductSpace.toDual.symm`); then F(f) = ∫ f ϑ dμ for every f ∈ L²(μ) (`finiteL1DualField_represents`, via the continuous inclusion L² ⊆ L¹ for finite μ), and |ϑ| ≤ C μ-a.e. (`finiteL1DualField_norm_le_one` applied to C⁻¹F̂, whose norm is ≤ 1). Indicators of measurable sets lie in L², so F(1_A) = ∫_A ϑ dμ for every measurable A. Truncating ϑ to an everywhere-bounded measurable representative θ as in Step 5 and concluding with Steps 6 and 7 gives the statement.

## Key steps

1. WLOG C ≥ 0; F(0) = 0, F is linear on integrable functions and respects μ-a.e. equality.
2. ν(A) := F(1_A) is finitely additive with |ν(A)| ≤ Cμ(A), hence countably additive: a finite signed measure with ν ≪ μ.
3. Radon–Nikodym gives θ₀ with ν(A) = ∫_A θ₀ dμ; |θ₀| ≤ C μ-a.e.; truncate to an everywhere-bounded measurable θ.
4. F(s) = ∫ sθ dμ for simple s; extend to all integrable f by L¹-density/closedness (Integrable.induction).

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
