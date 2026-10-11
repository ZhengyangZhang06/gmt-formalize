# Parent-supplied natural-language proof

- Parent DAG node: `root.constancy-a1`
- Child DAG node: `root.constancy-a1.local_on_balls-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Theorem 2.34 and its printed proof (p. 142–143), the part ending with “T = c_{ρ,x₀}[[B_ρ(x₀)]] (c_{ρ,x₀} constant) on each ball B_ρ(x₀) with B̄_ρ(x₀) ⊂ U”; this is Steps 1, 3, 4 and 5 of the parent proof, with the conclusion of its Step 2 (u(D_j a) = 0, i.e. T(dω_j) = ∂T(ω_j) = 0) taken as the hypothesis (H). As in the printed proof, the ball B_ρ(x₀) is fixed, R > ρ with B_R(x₀) ⊂ U, and the mollification parameter satisfies ε < R − ρ. Book n = m + 1. Erratum applied: the printed display (1) is garbled; it must read T(a_ε dx¹∧⋯∧dxⁿ) = ∫ a θ_ε dLⁿ for a ∈ L¹(B_ρ(x₀)) (the left side involves the mollified function a_ε = ϕ_ε ∗ a, as the preceding sentence of the printed proof defines F(a) = T(a_ε dx¹∧⋯∧dxⁿ)).

Setting and notation. m ∈ ℕ, n := m + 1, U ⊆ ℝⁿ open, T ∈ D_n(U) (Lean: GeometricCurrentOn U (m+1)). e = (e_1,…,e_n) is the standard basis (Lean: e_i = EuclideanSpace.single i 1), Lⁿ = Lebesgue measure (Lean: volume), D_j a(x) := Da(x)(e_j) (Lean: fderiv ℝ a x (EuclideanSpace.single j 1)), D^q the q-th derivative (Lean: iteratedFDeriv ℝ q), B_s(x) the open ball, B̄_s(x) the closed ball, “spt” the topological support (closure of {≠ 0}; Lean: tsupport). C_c^∞ denotes C^∞ functions ℝⁿ → ℝ with compact support, C¹_c the C¹ functions with compact support. f ∗ g denotes the convolution (f ∗ g)(x) = ∫ f(t) g(x − t) dt (Lean: convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume). Hypothesis:
(H) T(ω) = 0 whenever ω ∈ Dⁿ(U), a ∈ C_c^∞ with spt a ⊆ U, j ∈ {1,…,n}, and ω(x)(e) = D_j a(x) for all x ∈ ℝⁿ.
Claim: for every x₀ ∈ U there are r > 0 with B_r(x₀) ⊆ U and c ∈ ℝ such that T(ω) = c ∫ ω(x)(e) dLⁿ(x) for every ω ∈ Dⁿ(U) with spt ω ⊆ B_r(x₀).
Sibling lemmas used: constancy_riesz_l1_dual_bounded_density (Riesz representation (L¹)* = L^∞ for a finite measure), constancy_mollifier_iteratedFDeriv_norm_le_integral (for φ ∈ C_c^∞ and each q there is C_q with |D^q(φ ∗ g)(x)| ≤ C_q ∫|g| for all integrable g and all x), constancy_approx_identity_iteratedFDeriv_tendstoUniformly (for b ∈ C_c^∞ and continuous ψ_k ≥ 0 with ∫ψ_k = 1, spt ψ_k ⊆ B̄_{r_k}(0), r_k → 0: D^q(ψ_k ∗ b) → D^q b uniformly on ℝⁿ for each q).

Proof.

0. (Radii.) Fix x₀ ∈ U. U is open, so B_{R₀}(x₀) ⊆ U for some R₀ > 0. Put R := R₀/2 and ρ := r := R/2. Then K := B̄_R(x₀) ⊆ B_{R₀}(x₀) ⊆ U is compact, r > 0, and B := B_ρ(x₀) = B_r(x₀) ⊆ U. For 0 < ε < R − ρ = R/2 we have ρ + ε < R.

1. (Reduction to a distribution — parent Step 1.)
 (1a) Let dx := dx¹∧⋯∧dxⁿ be the n-covector v ↦ det[v_1 … v_n] (Lean: the continuous alternating map whose underlying alternating map is (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det; continuity: the determinant of the coordinate matrix depends continuously on v, `Continuous.matrix_det`). dx(e) = 1 (`Module.Basis.det_self`), and every α ∈ Λⁿ(ℝⁿ) equals α(e)·dx, because the alternating n-linear forms on an n-dimensional space are the multiples of the determinant (`AlternatingMap.eq_smul_basis_det`).
 (1b) For a ∈ C_c^∞ with spt a ⊆ U let [a] := a·dx, the form x ↦ a(x)·dx; it is C^∞, spt [a] ⊆ spt a, so [a] ∈ Dⁿ(U), and [a](x)(e) = a(x). Put u(a) := T([a]). Since [a + b] = [a] + [b] and [ca] = c[a], u is linear.
 (1c) For ω ∈ Dⁿ(U) put a_ω(x) := ω(x)(e). Then a_ω is C^∞ (ω composed with the continuous linear evaluation at e), spt a_ω ⊆ spt ω (compact, ⊆ U), and ω = [a_ω] by (1a). Hence T(ω) = u(a_ω).
 (1d) (Derivatives of [a].) D^q[a](x) is the image of D^q a(x) under the fixed continuous linear map t ↦ t·dx (`ContinuousLinearMap.iteratedFDeriv_comp_left`), so ‖D^q[a](x)‖ ≤ ‖dx‖·‖D^q a(x)‖ and D^q[a_k] → D^q[a] uniformly whenever D^q a_k → D^q a uniformly.
 (1e) (Continuity of u.) If a_k, a ∈ C_c^∞ have spt ⊆ K' for one compact K' ⊆ U and D^q a_k → D^q a uniformly on ℝⁿ for every q ∈ ℕ, then u(a_k) → u(a): by (1d), [a_k − a] → 0 in the sense of `TestFormOnConverges` (all supports in K', every derivative uniformly), and the continuity axiom of T (`GeometricCurrentOn.continuous'`) gives u(a_k) − u(a) = T([a_k − a]) → 0.
 (1f) (Hypothesis (H) in terms of u.) If a ∈ C_c^∞ with spt a ⊆ U and j ∈ {1,…,n}, then D_j a ∈ C_c^∞, spt D_j a ⊆ spt a ⊆ U, and [D_j a](x)(e) = D_j a(x); so (H) gives u(D_j a) = T([D_j a]) = 0. [This is the printed identity T(dω_j) = ∂T(ω_j) = 0, encoded in (H).]
 (1g) It therefore suffices to find c with u(b) = c ∫ b dLⁿ for every b ∈ C_c^∞ with spt b ⊆ B: then for ω ∈ Dⁿ(U) with spt ω ⊆ B = B_r(x₀), a_ω ∈ C_c^∞ with spt a_ω ⊆ B, and T(ω) = u(a_ω) = c ∫ a_ω dLⁿ = c ∫ ω(x)(e) dLⁿ(x).

2. (Mollifiers, as in §2 of Ch. 2.) For ε > 0 let ϕ_ε ∈ C_c^∞ with ϕ_ε ≥ 0, ϕ_ε(−x) = ϕ_ε(x), ∫ ϕ_ε dLⁿ = 1 and spt ϕ_ε = B̄_ε(0) (e.g. ϕ_ε(x) = ε^{−n}ϕ(x/ε) for a fixed mollifier ϕ; Lean: the normalized `ContDiffBump` centred at 0 with rIn = ε/2, rOut = ε, from Mathlib.Analysis.Calculus.BumpFunction.Normed: `contDiff_normed`, `continuous_normed`, `nonneg_normed`, `normed_neg`, `integral_normed`, `tsupport_normed_eq`). For g ∈ L¹(ℝⁿ) let g_ε := ϕ_ε ∗ g. Facts:
 (M1) g_ε ∈ C^∞ (`HasCompactSupport.contDiff_convolution_left`, differentiation under the integral sign).
 (M2) If g = 0 outside a set S, then g_ε = 0 outside S + B̄_ε(0) (`MeasureTheory.support_convolution_subset`).
 (M3) For each q there is C_q(ε) ≥ 0 with |D^q g_ε(x)| ≤ C_q(ε) ∫|g| dLⁿ for all x and all g ∈ L¹(ℝⁿ) — sibling lemma constancy_mollifier_iteratedFDeriv_norm_le_integral with φ = ϕ_ε (replace C_q by max(C_q, 0)).
 (M4) If g ∈ C¹_c then D_j(g_ε) = (D_j g)_ε (the derivative falls on g: `HasCompactSupport.hasFDerivAt_convolution_right`, evaluated at e_j).
 (M5) If g ∈ C_c^∞ and ε_k ↓ 0 then D^q(g_{ε_k}) → D^q g uniformly on ℝⁿ for every q — sibling lemma constancy_approx_identity_iteratedFDeriv_tendstoUniformly with ψ_k = ϕ_{ε_k}, r_k = ε_k.

3. (Printed display (1), corrected.) Fix ε with 0 < ε < R/2. For a function a integrable on B put ã := 1_B·a ∈ L¹(ℝⁿ) (a extended by zero). By (M1), (M2), ã_ε ∈ C^∞ and ã_ε = 0 outside B + B̄_ε(0) ⊆ B_{ρ+ε}(x₀), so spt ã_ε ⊆ B̄_{ρ+ε}(x₀) ⊆ K ⊆ U and ã_ε ∈ C_c^∞. Define F(a) := u(ã_ε) for a integrable on B (and F(a) := 0 otherwise; these values play no role). Since a ↦ ã ↦ ã_ε and u are linear, F(a + b) = F(a) + F(b) and F(c a) = c F(a) for a, b integrable on B and c ∈ ℝ.
 F is bounded on L¹(B). The printed proof argues: if a_j → a in L¹(B) then, by (M3), every derivative of (ã_j)_ε converges uniformly to that of ã_ε with all supports in K, so T((ã_j)_ε dx) → T(ã_ε dx) by (1e); “thus the functional F is a bounded linear functional on L¹(B_ρ(x₀))”. Explicitly: by the finite-order estimate for currents (SimonGMT `GeometricCurrentOn.exists_compact_derivative_bound`, module Poincare.SimonGMT.Chapter06.FixedSupportCurrentTopology, applied to T and the compact K ⊆ U) there are N ∈ ℕ and C₀ > 0 with |T(ω)| ≤ C₀·D whenever ω ∈ Dⁿ(U), spt ω ⊆ K, D ≥ 0 and ‖D^q ω(x)‖ ≤ D for all q ≤ N and x ∈ K. For ω = [ã_ε], (1d) and (M3) give ‖D^q[ã_ε](x)‖ ≤ ‖dx‖·C_q(ε)·∫|ã| = ‖dx‖·C_q(ε)·∫_B|a|, so with C := C₀‖dx‖·max_{q≤N} C_q(ε):
 |F(a)| ≤ C ∫_B |a| dLⁿ for every a integrable on B.
 [Equivalently, without the finite-order estimate: if no such C existed, choose a_k with |F(a_k)| > k²∫_B|a_k|; then ∫_B|a_k| > 0 (otherwise ã_k = 0 a.e., (ã_k)_ε ≡ 0 and F(a_k) = 0) and b_k := a_k/(k∫_B|a_k|) has ∫_B|b_k| = 1/k → 0 but |F(b_k)| > k, contradicting the sequential continuity just shown.]
 Now apply the Riesz representation theorem for L¹(B_ρ(x₀)), i.e. the sibling lemma constancy_riesz_l1_dual_bounded_density, with the finite measure μ := Lⁿ⌞B (Lean: volume.restrict (ball x₀ ρ), finite by `measure_ball_lt_top`; “μ-integrable” = “integrable on B”) and this F and C. It yields a measurable θ_ε : ℝⁿ → ℝ, bounded by some M everywhere, with
 (1) u(ã_ε) = F(a) = ∫_B a θ_ε dLⁿ for every a integrable on B.
 This is the corrected printed display (1).

4. (Printed display (2); θ_ε is constant.) Let a ∈ C¹_c with spt a ⊆ B and j ∈ {1,…,n}. Then ã = a; D_j a is continuous with spt D_j a ⊆ spt a ⊆ B, hence integrable on B with (D_j a)~ = D_j a; a_ε ∈ C_c^∞ with spt a_ε ⊆ K ⊆ U (Step 3); and (D_j a)_ε = D_j(a_ε) by (M4). Using (1) for D_j a and (1f) for the C_c^∞ function a_ε:
 (2) ∫_B (D_j a) θ_ε dLⁿ = u((D_j a)_ε) = u(D_j(a_ε)) = 0, j = 1,…,n.
 [In the printed notation: with ω_j = (−1)^{j−1} a_ε dx¹∧⋯∧dx^{j−1}∧dx^{j+1}∧⋯∧dxⁿ one has dω_j = (D_j a)_ε dx, and (2) reads T(dω_j) = ∂T(ω_j) = 0.]
 Thus the bounded measurable (hence locally integrable on B) function θ_ε has vanishing weak partial derivatives in the ball B, tested against all C¹_c functions supported in B. As in the printed proof, θ_ε is Lⁿ-a.e. constant on B: for 0 < σ < ρ and x ∈ B_{ρ−σ}(x₀), the function y ↦ ϕ_σ(x − y) is C_c^∞ with spt ⊆ B̄_σ(x) ⊆ B and D_{y_j}[ϕ_σ(x − y)] = −(D_jϕ_σ)(x − y); so with θ̃_ε := 1_B θ_ε, differentiation under the integral sign and (2) give D_j(ϕ_σ ∗ θ̃_ε)(x) = ∫ (D_jϕ_σ)(x − y) θ_ε(y) dy = −∫_B D_j[ϕ_σ(x − ·)] θ_ε dLⁿ = 0. Hence the C^∞ function ϕ_σ ∗ θ̃_ε has zero derivative on the convex open ball B_{ρ−σ}(x₀) and is constant there, say = k_σ (`IsOpen.is_const_of_fderiv_eq_zero`). As σ ↓ 0 along a sequence, ϕ_σ ∗ θ̃_ε → θ̃_ε Lⁿ-a.e. (Lebesgue differentiation theorem for the approximate identity ϕ_σ; `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`). Pick x₁ ∈ B where this convergence holds (possible since Lⁿ(B) > 0); for small σ, x₁ ∈ B_{ρ−σ}(x₀), so k_σ = (ϕ_σ ∗ θ̃_ε)(x₁) → θ_ε(x₁) =: c_ε. Every x ∈ B lies in B_{ρ−σ}(x₀) for small σ, so θ_ε(x) = lim k_σ = c_ε for a.e. x ∈ B. Hence θ_ε = c_ε Lⁿ-a.e. on B. [This exact argument is available, kernel-checked with the standard axioms only, as `Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero` (module Poincare.SimonGMT.Chapter08.DistributionalConstancy). Its hypotheses are: θ_ε locally integrable on B, B open and preconnected (convex), and ∫ θ_ε(x)·Da(x)(e_j) dx = 0 for every C¹ compactly supported a with spt a ⊆ B and every j. This is (2), because D_j a vanishes outside B so the whole-space integral equals the integral over B.]
 Consequently, by (1): u(ã_ε) = c_ε ∫_B a dLⁿ for every a integrable on B.

5. (Letting ε ↓ 0.) Let ε_k := R/(k + 3), so 0 < ε_k < R/2 and ε_k → 0, and let c_k := c_{ε_k} be the constant of Step 4 for ε = ε_k.
 Let b ∈ C_c^∞ with spt b ⊆ B. Then b is integrable on B, b̃ = b and ∫_B b = ∫ b, so Step 4 gives u(b_{ε_k}) = c_k ∫ b dLⁿ. By Step 3, spt b_{ε_k} ⊆ K for all k, and by (M5) every derivative of b_{ε_k} converges uniformly to the corresponding derivative of b. By (1e), u(b_{ε_k}) → u(b).
 Fix b₀ ∈ C_c^∞ with spt b₀ ⊆ B and ∫ b₀ dLⁿ = 1 (e.g. the normalized `ContDiffBump` centred at x₀ with outer radius r/2). Then c_k = c_k ∫ b₀ = u((b₀)_{ε_k}) → u(b₀) =: c. Hence for every b ∈ C_c^∞ with spt b ⊆ B: u(b) = lim_k u(b_{ε_k}) = lim_k c_k ∫ b = c ∫ b dLⁿ.

6. (Conclusion.) By (1g), T(ω) = c ∫ ω(x)(e) dLⁿ(x) for every ω ∈ Dⁿ(U) with spt ω ⊆ B_r(x₀), where r > 0 and B_r(x₀) ⊆ U (Step 0). This is the printed conclusion “T = c_{ρ,x₀}[[B_ρ(x₀)]] on each ball B_ρ(x₀)” for ρ = r. ∎

Formalization note: besides `GMT.Ch06.Submission`, a Lean proof of this statement may import `Mathlib.Analysis.Calculus.BumpFunction.Normed`, `Mathlib.Analysis.Calculus.ContDiff.Convolution`, `Poincare.SimonGMT.Chapter06.FixedSupportCurrentTopology` and `Poincare.SimonGMT.Chapter08.DistributionalConstancy` (all in the pinned packages; the cited SimonGMT lemmas use only propext, Classical.choice, Quot.sound).

## Key steps

1. Fix x₀, R with B̄_R(x₀) ⊆ U and the ball B = B_ρ(x₀), ρ = r = R/2; write ω = a_ω dx and set u(a) := T(a dx), a continuous linear functional on C_c^∞(U) with u(D_j a) = 0 by the hypothesis.
2. For 0 < ε < R/2, F(a) := u(ϕ_ε ∗ (1_B a)) is linear and bounded on L¹(B) (finite-order estimate for T plus the mollifier derivative bound).
3. The sibling Riesz lemma gives a bounded measurable θ_ε with u((1_B a)_ε) = ∫_B a θ_ε (corrected printed display (1)).
4. For a ∈ C¹_c(B): ∫_B (D_j a)θ_ε = u(D_j(a_ε)) = 0 (printed (2)); hence θ_ε = c_ε a.e. on B (mollification argument = SimonGMT ae_eq_const_of_weak_coordinate_derivatives_zero).
5. Along ε_k = R/(k+3) ↓ 0: u(b_{ε_k}) = c_k∫b and b_{ε_k} → b in the test-function sense (sibling convergence lemma), so c_k → c := u(b₀) and u(b) = c∫b for spt b ⊆ B.
6. T(ω) = u(a_ω) = c∫ω(x)(e)dLⁿ for every ω with spt ω ⊆ B_r(x₀).

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
