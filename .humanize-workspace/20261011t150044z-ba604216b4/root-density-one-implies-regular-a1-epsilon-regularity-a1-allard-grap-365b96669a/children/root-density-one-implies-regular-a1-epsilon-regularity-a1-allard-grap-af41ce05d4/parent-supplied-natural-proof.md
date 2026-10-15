# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Rellich's compactness theorem, as used in parent proof step A2 and in Simon's proof of Lemma 5.3.1 ("by Rellich's theorem (see [GT01])"; Gilbarg–Trudinger Thm 7.22, Evans §5.7 Thm 1). W^{1,2} is not available, so it is proved here directly for Lipschitz functions. The proof combines interior mollification and Arzelà–Ascoli with a boundary-layer estimate obtained from rays and dilations.

0. (Notation and tools.) B := B̆_1(0), B_r := B̆_r(0), A_s := B ∖ B_{1−s}, K_s := closedBall(0, 1 − s), ω := Lⁿ(B).
- M ≥ 0 automatically, since the integrals are ≥ 0.
- For a Lipschitz u, its non-differentiability set N_u is Borel and Lⁿ-null (measurableSet_of_differentiableAt, LipschitzWith.ae_differentiableAt). Du is Borel and bounded (measurable_fderiv, norm_fderiv_le_of_lipschitz).
- One-variable FTC: a Lipschitz φ : ℝ → ℝ satisfies φ(b) − φ(a) = ∫_a^b deriv φ (LipschitzOnWith.absolutelyContinuousOnInterval and AbsolutelyContinuousOnInterval.integral_deriv_eq_sub). If φ(τ) = u(p + τv) and u is differentiable at p + τv, then deriv φ(τ) = Du(p + τv)v.

1. (FTC along translations.) Let u be Lipschitz and z ∈ ℝⁿ. Then for a.e. p ∈ ℝⁿ, u(p + z) − u(p) = ∫_0^1 Du(p + τz)z dτ.
Proof: {(p, τ) ∈ ℝⁿ × [0, 1] : p + τz ∈ N_u} is Borel with null p-sections N_u − τz. By Tonelli, for a.e. p its τ-section is null, and the one-variable FTC applies to τ ↦ u(p + τz).

2. (Interior mollification.) Let ρ̂(z) := c₁(1 − |z|)₊ with c₁ := (∫(1 − |z|)₊ dz)^{−1}.
- ρ̂ ≥ 0, ρ̂ = 0 off B̆_1(0), ∫ρ̂ = 1, sup ρ̂ = c₁, and ρ̂ is c₁-Lipschitz.
- For ε > 0 put ρ̂_ε(w) := ε^{−n}ρ̂(w/ε). It vanishes off B̆_ε(0), has supremum ε^{−n}c₁ and Lipschitz constant ε^{−n−1}c₁.
- For a Lipschitz u let u_ε(x) := ∫ u(x − εz)ρ̂(z) dz = ∫ u(y)ρ̂_ε(x − y) dy.
(2a) If 0 < ε ≤ s ≤ 1/2 then ∫_{B_{1−s}} (u − u_ε)² ≤ ε²∫_B ‖Du‖².
- For x ∈ B_{1−s}, u(x) − u_ε(x) = ∫ (u(x) − u(x − εz))ρ̂(z) dz.
- By step 1 (vector εz, base point p = x − εz; translations preserve null sets) and Tonelli in (x, z), for a.e. x and a.e. z with |z| < 1:
  |u(x) − u(x − εz)| = |∫_0^1 Du(x − εz + τεz)(εz) dτ| ≤ ε∫_0^1 ‖Du(x − (1 − τ)εz)‖ dτ.
- ρ̂(z)dz ⊗ dτ is a probability measure on B̆_1(0) × [0, 1]. So by Jensen, for a.e. x ∈ B_{1−s}:
  (u(x) − u_ε(x))² ≤ ε²∫ρ̂(z)∫_0^1 ‖Du(x − (1 − τ)εz)‖² dτ dz.
- Integrate over x ∈ B_{1−s} and use Tonelli. For each (z, τ) the translation x ↦ x − (1 − τ)εz maps B_{1−s} into B, because |(1 − τ)εz| < ε ≤ s. So ∫_{B_{1−s}} ‖Du(x − (1 − τ)εz)‖² dx ≤ ∫_B ‖Du‖², and (2a) follows.
(2b) Let 0 < ε ≤ s/2 ≤ 1/4 and x, x' ∈ K_s. Then B̆_ε(x) ∪ B̆_ε(x') ⊆ B, since 1 − s + s/2 < 1, and
- |u_ε(x)| ≤ ε^{−n}c₁∫_B |u| ≤ ε^{−n}c₁(ω∫_B u²)^{1/2};
- |u_ε(x) − u_ε(x')| ≤ ε^{−n−1}c₁|x − x'|∫_B |u| ≤ ε^{−n−1}c₁(ω∫_B u²)^{1/2}|x − x'|.

3. (Boundary layer.) For 0 < s ≤ 1/2 and Lipschitz u: ∫_{A_s} u² ≤ 2^{n+3}s(∫_B u² + ∫_B ‖Du‖²).
(i) {(x, σ) ∈ ℝⁿ × [1/2, 1] : σx ∈ N_u} is Borel with null x-sections σ^{−1}N_u. So for a.e. x, u is differentiable at σx for a.e. σ ∈ [1/2, 1]. For such x and every t ∈ [1/2, 1], the one-variable FTC for σ ↦ u(σx) gives u(x) − u(tx) = ∫_t^1 Du(σx)x dσ.
(ii) For such x ∈ A_s (so |x| < 1): |u(x)| ≤ |u(tx)| + ∫_{1/2}^1 ‖Du(σx)‖ dσ. Hence, by Cauchy–Schwarz on an interval of length 1/2,
u(x)² ≤ 2u(tx)² + 2(∫_{1/2}^1 ‖Du(σx)‖ dσ)² ≤ 2u(tx)² + ∫_{1/2}^1 ‖Du(σx)‖² dσ.
Averaging over t ∈ [1/2, 1]: u(x)² ≤ 4∫_{1/2}^1 u(tx)² dt + ∫_{1/2}^1 ‖Du(σx)‖² dσ.
(iii) Integrate over x ∈ A_s (Tonelli): ∫_{A_s} u² ≤ 4∫_{1/2}^1∫_{A_s} u(tx)² dx dt + ∫_{1/2}^1∫_{A_s} ‖Du(σx)‖² dx dσ.
(iv) Let F ≥ 0 be measurable and t ∈ [1/2, 1]. Then ∫_{A_s} F(tx) dx = t^{−n}∫_{tA_s} F ≤ 2ⁿ∫_B F·1_{tA_s}, where tA_s = {y : t(1 − s) ≤ |y| < t} ⊆ B.
By Tonelli, ∫_{1/2}^1∫_{A_s} F(tx) dx dt ≤ 2ⁿ∫_B F(y)ℓ(y) dy, where ℓ(y) := L¹{t ∈ [1/2, 1] : |y| < t ≤ |y|/(1 − s)} ≤ |y|s/(1 − s) ≤ 2s.
Hence ∫_{1/2}^1∫_{A_s} F(tx) dx dt ≤ 2^{n+1}s∫_B F.
(v) Apply (iv) with F = u² and with F = ‖Du‖²: ∫_{A_s} u² ≤ 4·2^{n+1}s∫_B u² + 2^{n+1}s∫_B ‖Du‖² ≤ 2^{n+3}s(∫_B u² + ∫_B ‖Du‖²).

4. (Total boundedness.) Let 𝓛 := Lp ℝ 2 (volume.restrict B), a complete metric space. Let f_j ∈ 𝓛 be the class of u_j; it is in L² because u_j is continuous and bounded on B. Fix η > 0.
- Choose s ∈ (0, 1/2] with 2^{n+3}s·2M ≤ η²/16, and ε ∈ (0, s/2] with ε²M ≤ η²/16.
- By step 3, ‖u_j‖_{L²(A_s)} ≤ η/4 for all j. By (2a), ‖u_j − (u_j)_ε‖_{L²(B_{1−s})} ≤ η/4 for all j.
- By (2b), the restrictions v_j := (u_j)_ε|_{K_s} to the compact set K_s are uniformly bounded and uniformly Lipschitz, hence equicontinuous. By the Arzelà–Ascoli theorem (BoundedContinuousFunction.arzela_ascoli on the compact space K_s), {v_j} is relatively compact, hence totally bounded, for the sup distance.
- So there are indices j_1, …, j_m such that every j has some k with sup_{K_s}|v_j − v_{j_k}| ≤ η/(4√ω).
- Since B = B_{1−s} ∪ A_s and B_{1−s} ⊆ K_s:
  ‖f_j − f_{j_k}‖_𝓛 ≤ ‖u_j‖_{L²(A_s)} + ‖u_{j_k}‖_{L²(A_s)} + ‖u_j − v_j‖_{L²(B_{1−s})} + √ω·sup_{K_s}|v_j − v_{j_k}| + ‖v_{j_k} − u_{j_k}‖_{L²(B_{1−s})} ≤ 5η/4.
η > 0 was arbitrary, so {f_j : j ∈ ℕ} is totally bounded in 𝓛.

5. (Extraction.) In the complete space 𝓛, the closure of a totally bounded set is totally bounded and closed, hence compact (TotallyBounded.closure, TotallyBounded.isCompact_of_isClosed). By IsCompact.tendsto_subseq there are a strictly increasing φ : ℕ → ℕ and F ∈ 𝓛 with f_{φ(j)} → F in 𝓛. Let W : ℝⁿ → ℝ be a representative of F, so MemLp W 2 (volume.restrict B). Then ∫_B (u_{φ(j)} − W)² = ‖f_{φ(j)} − F‖²_𝓛 → 0. ∎

## Key steps

1. FTC along translations and along rays for Lipschitz functions, valid for a.e. base point by Rademacher and Tonelli.
2. Interior mollification: ‖u − u_ε‖_{L²(B̆_{1−s})} ≤ ε‖Du‖_{L²(B)}, and for ε ≤ s/2 the u_ε are uniformly bounded and uniformly Lipschitz on closedBall(0, 1−s).
3. Boundary layer: ∫_{B∖B̆_{1−s}} u² ≤ 2^{n+3}s(∫_B u² + ∫_B ‖Du‖²), from u(x) − u(tx) = ∫_t^1 Du(σx)x dσ and dilation.
4. Arzelà–Ascoli on closedBall(0, 1−s) together with the two estimates shows {u_j} is totally bounded in L²(B).
5. Completeness of L²(B) gives a convergent subsequence; W is a representative of the limit.

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
