# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: in the Lipschitz/L² setting of the frozen statements, this replaces one step of Simon's proof of Lemma 5.3.1 (parent proof A2): "∇f_{k'} ⇀ ∇w weakly in L², with ∫_B|∇w|² ≤ 1" (weak lower semicontinuity of the Dirichlet energy). The proof is by duality against compactly supported C¹ vector fields.

Notation.
- B := B̆_R(0), and e_i is the standard basis.
- For a vector field Φ = (Φ_1, …, Φ_n): divΦ := Σ_i ∂_iΦ_i and |Φ|² := Σ_i Φ_i².
- For u differentiable at y: ∇u·Φ(y) := Σ_i Du(y)(e_i)Φ_i(y). By Cauchy–Schwarz, |∇u·Φ| ≤ ‖Du(y)‖·|Φ(y)|, since the operator norm ‖Du(y)‖ is the Euclidean length of the gradient.
- 𝒱 is the set of Φ whose components are C¹ on ℝⁿ with compact support and tsupport Φ_i ⊆ B.

0. E ≥ 0, because E ≥ ∫_B ‖Du_0‖² ≥ 0.

1. (IBP for Lipschitz functions.) If u is Lipschitz and Φ ∈ 𝒱, then ∫_B ∇u·Φ = −∫_B u·divΦ and ∫_B divΦ = 0.
Proof: each Φ_i is C¹ with compact support, hence Lipschitz (ContDiff.lipschitzWith_of_hasCompactSupport). LipschitzWith.integral_lineDeriv_mul_eq with f := u, g := Φ_i, v := e_i gives
∫ lineDeriv ℝ u y e_i·Φ_i(y) dy = ∫ lineDeriv ℝ Φ_i y (−e_i)·u(y) dy = −∫ ∂_iΦ_i(y)·u(y) dy.
By Rademacher (LipschitzWith.ae_differentiableAt), for a.e. y, u is differentiable at y and lineDeriv ℝ u y e_i = Du(y)e_i. Sum over i. All integrands vanish outside ⋃_i tsupport Φ_i ⊆ B, so the integrals over ℝⁿ equal those over B. Taking u ≡ 1 (Du = 0) gives ∫_B divΦ = 0.

2. (IBP for h.) If Φ ∈ 𝒱 then ∫_B ∇h·Φ = −∫_B h·divΦ.
Proof:
- K := ⋃_i tsupport Φ_i is a compact subset of B, so K ⊆ closedBall(0, r₁) for some r₁ < R.
- Choose χ ∈ C^∞(ℝⁿ) with χ ≡ 1 on B̆_{r₂}(0) and tsupport χ ⊆ closedBall(0, r₃), where r₁ < r₂ < r₃ < R (a ContDiffBump).
- Put h̃ := χh on B and h̃ := 0 off B. Then h̃ is C² on ℝⁿ (C² on B, and zero on the open set ℝⁿ ∖ tsupport χ), has compact support, is Lipschitz, and is differentiable everywhere.
- The computation of step 1 with u := h̃ gives ∫ ∇h̃·Φ = −∫ h̃·divΦ. On the open set B̆_{r₂}(0) ⊇ K we have h̃ = h and Dh̃ = Dh, and both integrands vanish off K.

3. (Duality bound.) For Φ ∈ 𝒱: ∫_B ∇h·Φ ≤ √E·(∫_B |Φ|²)^{1/2}.
Proof:
- By step 2 and h = W a.e. on B, ∫_B ∇h·Φ = −∫_B W·divΦ.
- divΦ is bounded and supported in B, so by Cauchy–Schwarz |∫_B (u_j − c_j − W)·divΦ| ≤ (∫_B (u_j − c_j − W)²)^{1/2}(∫_B (divΦ)²)^{1/2} → 0.
- Hence −∫_B W·divΦ = lim_j −∫_B (u_j − c_j)·divΦ = lim_j −∫_B u_j·divΦ = lim_j ∫_B ∇u_j·Φ, using step 1 and ∫_B divΦ = 0.
- For every j, |∫_B ∇u_j·Φ| ≤ ∫_B ‖Du_j‖·|Φ| ≤ (∫_B ‖Du_j‖²)^{1/2}(∫_B |Φ|²)^{1/2} ≤ √E·(∫_B |Φ|²)^{1/2}. The bound passes to the limit.

4. (Energy on interior balls.) Let 0 < r < R.
- Choose χ_r ∈ C^∞(ℝⁿ) with 0 ≤ χ_r ≤ 1, χ_r ≡ 1 on B̆_r(0) and tsupport χ_r ⊆ closedBall(0, (r + R)/2) ⊆ B (a ContDiffBump centred at 0 with rIn = r, rOut = (r + R)/2).
- Put Φ_i := χ_r·∂_ih on B and Φ_i := 0 off B. Since h is C² on B, Φ_i is C¹ on B and vanishes on the open set ℝⁿ ∖ tsupport χ_r. So Φ ∈ 𝒱.
- ∇h·Φ = χ_r‖Dh‖² and |Φ|² = χ_r²‖Dh‖² ≤ χ_r‖Dh‖².
- Let X := ∫_B χ_r‖Dh‖². It is finite, because the integrand is continuous with compact support in B.
- Step 3 gives X ≤ √E·√X, hence X ≤ E (trivial if X = 0; otherwise divide by √X).
- Since χ_r = 1 on B̆_r(0) and the integrand is ≥ 0, ∫_{B̆_r(0)} ‖Dh‖² ≤ X ≤ E.

5. (Exhaustion.) ‖Dh‖² is continuous on B, hence a.e.-strongly measurable for volume.restrict B. Take r_k := R(1 − 1/(k + 1)) ↑ R. By monotone convergence for lower integrals, ∫⁻_B ‖Dh‖² = lim_k ∫⁻_{B̆_{r_k}(0)} ‖Dh‖² ≤ E < ∞. Hence ‖Dh‖² is integrable on B and ∫_B ‖Dh‖² ≤ E. ∎

## Key steps

1. Integration by parts against compactly supported C¹ vector fields Φ in B: for Lipschitz u via Mathlib's Lipschitz IBP and Rademacher, for h after a cutoff; also ∫_B divΦ = 0.
2. Duality: ∫_B ∇h·Φ = −∫_B W·divΦ = lim_j ∫_B ∇u_j·Φ ≤ √E·‖Φ‖_{L²(B)}.
3. Test with Φ = χ_r∇h, where 0 ≤ χ_r ≤ 1 and χ_r = 1 on B̆_r: X ≤ √E·√X, so ∫_{B̆_r} ‖Dh‖² ≤ E.
4. Monotone convergence as r ↑ R gives integrability and ∫_B ‖Dh‖² ≤ E.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (IDENTICAL)`
- `rg -l -i 'laplacian' <snapshot>/mathlib/Mathlib; rg -n '^(theorem|lemma|def)' Analysis/InnerProductSpace/Harmonic/*.lean; sed -n 110,200p Analysis/InnerProductSpace/Laplacian.lean`
- `grep -rn -E 'theorem .*(circleAverage|meanValue|mean_value)' Analysis/Complex/Harmonic/`
- `rg -n 'theorem|lemma' Analysis/Calculus/Rademacher.lean; sed -n 40,210p Analysis/Calculus/Rademacher.lean`
- `rg -l 'AbsolutelyContinuousOnInterval' <snapshot>/mathlib/Mathlib; sed -n 200,260p MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean; grep -n absolutelyContinuousOnInterval MeasureTheory/Function/AbsolutelyContinuous.lean`
- `rg -n 'theorem .*ae_tendsto_average|theorem .*tendsto_average|convolution_tendsto_right|ae_convolution_tendsto' <snapshot>/mathlib/Mathlib`
- `grep -rn -E 'theorem (_root_\.)?HasCompactSupport\.(contDiff|hasFDerivAt)_convolution_(left|right)' Analysis/`
- `rg -n 'theorem arzela_ascoli' Topology/ContinuousMap/Bounded/ArzelaAscoli.lean; grep -rn -E 'theorem (TotallyBounded\.isCompact|isCompact_iff_totallyBounded)' Topology/UniformSpace; grep -n 'exists_cthickening_subset_open' Topology/MetricSpace/Thickening.lean; grep -rn lipschitzWith_of_hasCompactSupport Analysis/Calculus/ContDiff/RCLike.lean; sed -n 125,160p MeasureTheory/Measure/Haar/NormedSpace.lean`
- `grep -rln 'rellich\|Rellich\|Kondrachov\|poincare_inequality\|PoincareInequality\|mean_value_property\|weyl_lemma\|WeylLemma' Analysis MeasureTheory  (no match)`
- `sed -n 1,50p Analysis/Distribution/Sobolev.lean  (Fourier-side Bessel potential spaces only)`
- `grep -rln -i -E 'harmonic|rellich|kondrachov|weyl|mean.value|poincar[eé].inequality' .lake/packages/simongmt/Poincare; grep -n -E '^(theorem|lemma|def)' Chapter05/HarmonicEnergy.lean Chapter04/Poincare.lean Chapter05/Basic.lean; grep -rn -i -E 'harmonic|poincar|rellich|weyl' <snapshot>/project/GMT`
- `python3 -I: lean_name scan of dag.json (212 nodes) and nodes/*/*.json (446 names) for the 7 proposed dorag_ha_* names (no collision)`
- `lean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = workspace .lake builds) /tmp/harmapprox-decomp/Children.lean, Assembly.lean, Assembly2.lean (#print axioms GMT.Ch07.Submission.dorag_harmonic_affine_approximation), Names.lean (#check of cited Mathlib lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/HarmonicEnergy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/tmp/harmapprox-decomp/Children.lean`
- `/tmp/harmapprox-decomp/Assembly.lean`
- `/tmp/harmapprox-decomp/Assembly2.lean`
- `/tmp/harmapprox-decomp/Names.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so the child types are checked in that scope.

What the pinned Mathlib lacks:
- no Rellich, Poincaré-on-a-ball, Weyl lemma or ℝⁿ mean value property (grep finds no match in Analysis or MeasureTheory);
- the only harmonic mean value result is HarmonicOnNhd.circleAverage_eq on ℂ (Analysis/Complex/Harmonic/MeanValue.lean);
- Sobolev.lean has only Fourier-side Bessel-potential spaces, so there is no W^{1,2} on domains.

What the pinned Mathlib supplies, and the child proofs cite:
- LipschitzWith.integral_lineDeriv_mul_eq (Rademacher.lean:169) and LipschitzWith.ae_differentiableAt (Rademacher.lean:385);
- AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (AbsolutelyContinuousFun.lean:225) and LipschitzOnWith.absolutelyContinuousOnInterval (AbsolutelyContinuous.lean:309);
- HasCompactSupport.contDiff_convolution_left / hasFDerivAt_convolution_left (ContDiff/Convolution.lean:91,427);
- VitaliFamily.ae_tendsto_average_norm_sub (Differentiation.lean:837) and tendsto_integral_smul_of_tendsto_average_norm_sub (Average.lean:835);
- BoundedContinuousFunction.arzela_ascoli (ArzelaAscoli.lean:109), TotallyBounded.isCompact_of_isClosed (Cauchy.lean:746), Measure.setIntegral_comp_smul_of_pos (Haar/NormedSpace.lean:148), ContDiff.lipschitzWith_of_hasCompactSupport, IsCompact.exists_cthickening_subset_open and ContDiffAt.isSymmSndFDerivAt.

The project and SimonGMT have nothing reusable. SimonGMT Chapter05/Basic.lean only re-exports HarmonicOnNhd vocabulary and says compactness and regularity are not formalized. Chapter04/Poincare.lean is the varifold (Michael–Simon type) inequality and Chapter05/HarmonicEnergy.lean the §1 energy estimate, neither the needed Euclidean results. The project's Ch05 HarmonicApproximationLemma is a Prop used only under main_theorem := by sorry. So no comparator-approved declaration can be reused.

Lean checks:
- all 7 child types elaborate in comparator scope;
- the exact frozen parent type compiles from dorag_ha_approximation and dorag_ha_interior_estimates alone, with axioms propext, Classical.choice and Quot.sound plus sorryAx from the stubbed children;
- the 7 dorag_ha_* names are unreserved.
