# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1`
- Child DAG node: `root.constancy-a1.globalize-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Theorem 2.34, printed proof (p. 143), final clause “... on each ball B_ρ(x₀) with B̄_ρ(x₀) ⊆ U, and the result follows”, expanded as Steps 6 and 7 of the parent proof (overlapping balls, connectedness of U, partition of unity).

Setting and notation. m ∈ ℕ, n := m + 1, U ⊆ ℝⁿ open and connected, T ∈ D_n(U) (Lean: GeometricCurrentOn U (m+1)), e = (e_1,…,e_n) the standard basis (Lean: e_i = EuclideanSpace.single i 1), Lⁿ = Lebesgue measure (Lean: volume), spt = topological support (Lean: tsupport). Hypothesis:
(L) for every x₀ ∈ U there are r > 0 with B_r(x₀) ⊆ U and c ∈ ℝ such that T(ω) = c ∫ ω(x)(e) dLⁿ(x) for every ω ∈ Dⁿ(U) with spt ω ⊆ B_r(x₀).
Claim: there is c ∈ ℝ with T(ω) = c ∫_U ω(x)(e) dLⁿ(x) for every ω ∈ Dⁿ(U).

Proof.

1. (Choices.) Using (L), choose for every x₀ ∈ U a radius r(x₀) > 0 and a constant c(x₀) such that B(x₀) := B_{r(x₀)}(x₀) ⊆ U and T(ω) = c(x₀) ∫ ω(x)(e) dLⁿ(x) whenever ω ∈ Dⁿ(U), spt ω ⊆ B(x₀).

2. (The form b dx.) Let dx := dx¹∧⋯∧dxⁿ, the n-covector v ↦ det[v_1 … v_n] (Lean: continuous alternating map with underlying map (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det), so dx(e) = 1. For b ∈ C^∞(ℝⁿ) with compact support and spt b ⊆ U, the form [b] := (x ↦ b(x)·dx) lies in Dⁿ(U), spt [b] ⊆ spt b, and [b](x)(e) = b(x).

3. (Overlapping balls have equal constants — parent Step 6.) Let x₀, x₁ ∈ U with W := B(x₀) ∩ B(x₁) ≠ ∅. W is open; pick z ∈ W and δ > 0 with B_δ(z) ⊆ W. Let b be a normalized smooth bump: b ∈ C^∞, b ≥ 0, spt b = B̄_{δ/2}(z) ⊆ W, ∫ b dLⁿ = 1 (Lean: (ContDiffBump with centre z, rIn = δ/4, rOut = δ/2).normed volume; `integral_normed`, `tsupport_normed_eq`). Then [b] ∈ Dⁿ(U) and spt [b] ⊆ W ⊆ B(x₀) ∩ B(x₁). Applying Step 1 at x₀ and at x₁:
 c(x₀) = c(x₀) ∫ b = T([b]) = c(x₁) ∫ b = c(x₁).

4. (c is locally constant.) Let x₀ ∈ U and y ∈ B(x₀). Then y ∈ U, y ∈ B(y) (the centre of a ball of positive radius) and y ∈ B(x₀), so B(y) ∩ B(x₀) ≠ ∅ and c(y) = c(x₀) by Step 3. Thus the function c : U → ℝ is constant on the neighbourhood B(x₀) of each point x₀ of U, i.e. it is locally constant on U (with the subspace topology).

5. (Connectedness.) U is connected, so U ≠ ∅ and every locally constant function on U is constant (Mathlib: `IsLocallyConstant` on the subtype U together with `PreconnectedSpace U`, which follows from `IsConnected U`, gives `IsLocallyConstant.exists_eq_const`). Let c* be its value: c(x) = c* for all x ∈ U.

6. (Partition of unity — parent Step 7.) Let ω ∈ Dⁿ(U) and K := spt ω, a compact subset of U. The open balls B(x), x ∈ K, cover K, so K ⊆ B(x_1) ∪ ⋯ ∪ B(x_N) for finitely many x_1,…,x_N ∈ K (N may be 0 when K = ∅). Choose a smooth partition of unity on K subordinate to this finite open cover: χ_1,…,χ_N ∈ C^∞(ℝⁿ) with spt χ_k ⊆ B(x_k) and Σ_k χ_k(x) = 1 for every x ∈ K (Mathlib: `SmoothPartitionOfUnity.exists_isSubordinate` for the closed set K and the open cover (B(x_k))_k, with the model 𝓘(ℝ, ℝⁿ); smoothness of each χ_k as an ordinary C^∞ function follows from `contMDiff_iff_contDiff`). Each spt χ_k is closed and bounded, hence compact.

7. (Summation.) For each k let χ_kω be the form x ↦ χ_k(x)·ω(x). It is C^∞, spt χ_kω ⊆ spt χ_k ∩ spt ω, which is compact and contained in B(x_k) ⊆ U; so χ_kω ∈ Dⁿ(U) and spt χ_kω ⊆ B(x_k). Moreover ω = Σ_k χ_kω: for x ∈ K, Σ_k χ_k(x)ω(x) = ω(x); for x ∉ K, ω(x) = 0 and both sides vanish. By linearity of T, Step 1 at x_k and c(x_k) = c* (Step 5):
 T(ω) = Σ_k T(χ_kω) = Σ_k c* ∫ χ_k(x) ω(x)(e) dLⁿ(x) = c* ∫ Σ_k χ_k(x) ω(x)(e) dLⁿ(x) = c* ∫ ω(x)(e) dLⁿ(x),
 where the integrands are continuous with compact support (hence integrable), so the finite sum may be exchanged with the integral.

8. (Integral over U.) Since spt ω ⊆ U, ω(x) = 0 for x ∉ U, hence ∫ ω(x)(e) dLⁿ(x) = ∫_U ω(x)(e) dLⁿ(x) (Mathlib `setIntegral_eq_integral_of_forall_compl_eq_zero`). Therefore T(ω) = c* ∫_U ω(x)(e) dLⁿ(x) for every ω ∈ Dⁿ(U); take c := c*. ∎

## Key steps

1. Choose r(x₀), c(x₀) for each x₀ ∈ U.
2. Overlapping balls: a normalized bump b in the intersection gives c(x₀) = T(b dx) = c(x₁).
3. Hence c is locally constant on U, and constant (= c*) because U is connected.
4. A smooth partition of unity subordinate to finitely many balls covering spt ω gives T(ω) = Σ_k T(χ_kω) = c*∫ω(x)(e)dLⁿ.
5. ω vanishes off U, so the integral over ℝⁿ equals the integral over U.

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
