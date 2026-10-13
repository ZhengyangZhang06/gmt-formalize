# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 5, estimates 3.2–3.4 ("standard estimates for harmonic functions (which follow directly from the mean-value property)"), as used in Part C (C1–C4) of the parent proof. Here they are derived from the ball mean value property, sibling dorag_ha_mean_value part (ii). The divergence-theorem step of the parent's C3 is replaced by comparing ball means over shifted balls.

Notation.
- B := B̆_R(0) (open), ω := Lⁿ(B̆_1(0)) ∈ (0, ∞), and Lⁿ(B̆_ρ(y)) = ωρⁿ (Measure.addHaar_ball, finrank ℝ (Euclid n) = n).
- ‖Dh(y)‖ = ‖fderiv ℝ h y‖ is the operator norm, equal to the Euclidean length of the gradient. D²h(y)(a, b) := iteratedFDeriv ℝ 2 h y ![a, b] = D(Dh)(y)(a)(b).
- K₁ := 2ⁿω^{−1/2} and C_H := 4n·K₁ = 4n·2ⁿω^{−1/2} > 0; C_H depends only on n, and 2^{n/2}ω^{−1/2} ≤ K₁ ≤ C_H.
Fix R > 0 and h satisfying the hypotheses.

1. (Directional derivatives are harmonic.) Fix e ∈ ℝⁿ and let u_e(y) := Dh(y)e. Since h is C^m on B for every m, u_e is C^∞ on B, in particular C².
- For y ∈ B, the third derivative D³h(y) is symmetric in its three arguments. Symmetry of second derivatives (ContDiffAt.isSymmSndFDerivAt), applied to the C² maps h and Dh, gives symmetry in the last two slots and in the first two slots.
- Hence D²u_e(y)(a, b) = D³h(y)(a, b, e), and Δu_e(y) = Σ_i D³h(y)(e_i, e_i, e) = Σ_i D³h(y)(e, e_i, e_i) = D(Δh)(y)e.
- The right side is the derivative in direction e of z ↦ Δh(z) = Σ_i D²h(z)(e_i, e_i), which vanishes identically on the open set B. So Δu_e = 0 on B.
Thus h and every u_e are C² on the open set U := B with zero Laplacian, and the mean value property (ii) applies to them on every closed ball contained in B.

2. (Mean value bounds.) Let y ∈ ℝⁿ and ρ > 0 with closedBall(y, ρ) ⊆ B.
(2a) h(y) = (ωρⁿ)^{−1}∫_{B̆_ρ(y)} h. By Cauchy–Schwarz, |h(y)| ≤ (ωρⁿ)^{−1}(ωρⁿ)^{1/2}(∫_{B̆_ρ(y)} h²)^{1/2} = (ωρⁿ)^{−1/2}(∫_{B̆_ρ(y)} h²)^{1/2}.
(2b) For a unit vector e, Dh(y)e = u_e(y) = (ωρⁿ)^{−1}∫_{B̆_ρ(y)} Dh(z)e dz ≤ (ωρⁿ)^{−1}∫_{B̆_ρ(y)} ‖Dh‖ ≤ (ωρⁿ)^{−1/2}(∫_{B̆_ρ(y)} ‖Dh‖²)^{1/2}. Replacing e by −e and taking the supremum over unit e gives ‖Dh(y)‖ ≤ (ωρⁿ)^{−1/2}(∫_B ‖Dh‖²)^{1/2} ≤ (ωρⁿ)^{−1/2}R^{n/2}.
The integrands are continuous on the compact set closedBall(y, ρ) ⊆ B. Since h² and ‖Dh‖² are integrable and nonnegative on B, their integrals over B̆_ρ(y) are at most those over B.

3. (Proof of (a) and (b).) closedBall(0, R/2) ⊆ B.
- (2a) with y = 0, ρ = R/2: |h(0)| ≤ (ω(R/2)ⁿ)^{−1/2}(∫_B h²)^{1/2} = 2^{n/2}ω^{−1/2}√((∫_B h²)/Rⁿ) ≤ C_H√((∫_B h²)/Rⁿ). This is (a).
- (2b) with y = 0, ρ = R/2: ‖Dh(0)‖ ≤ 2^{n/2}ω^{−1/2} ≤ C_H. This is (b).

4. (Gradient bound on closedBall(0, 5R/8).) If |y| ≤ 5R/8 then closedBall(y, R/4) ⊆ closedBall(0, 7R/8) ⊆ B. So (2b) with ρ = R/4 gives ‖Dh(y)‖ ≤ (ω(R/4)ⁿ)^{−1/2}R^{n/2} = 2ⁿω^{−1/2} = K₁.

5. (Second derivative bound on closedBall(0, R/4).) Let |x| ≤ R/4, let a and e be unit vectors, put ρ := R/4 and u := u_e, and let t ∈ ℝ with 0 < |t| ≤ R/8.
- closedBall(x, ρ) and closedBall(x + ta, ρ) lie in closedBall(0, 5R/8) ⊆ B. By the mean value property for u:
  u(x + ta) − u(x) = (ωρⁿ)^{−1}(∫_{B̆_ρ(x+ta)} u − ∫_{B̆_ρ(x)} u) = (ωρⁿ)^{−1}(∫_{S₁} u − ∫_{S₂} u),
  with S₁ := B̆_ρ(x+ta) ∖ B̆_ρ(x) and S₂ := B̆_ρ(x) ∖ B̆_ρ(x+ta).
- S₁ and S₂ are disjoint and contained in the annulus A_t := B̆_{ρ+|t|}(x) ∖ B̆_{ρ−|t|}(x). For z ∈ S₁: |z − x| ≥ ρ and |z − x| ≤ |z − x − ta| + |t| < ρ + |t|. For z ∈ S₂: |z − x| < ρ and |z − x| ≥ |z − x − ta| − |t| ≥ ρ − |t|.
- A_t ⊆ closedBall(0, 5R/8), where |u| ≤ ‖Dh‖ ≤ K₁ by step 4. Hence
  |u(x + ta) − u(x)| ≤ (ωρⁿ)^{−1}K₁·Lⁿ(A_t) = (ωρⁿ)^{−1}K₁ω((ρ + |t|)ⁿ − (ρ − |t|)ⁿ) ≤ K₁ρ^{−n}·2|t|·n(ρ + |t|)^{n−1},
  by the mean value theorem for τ ↦ τⁿ.
- Divide by |t| and let t → 0 (u is differentiable at x): |Du(x)a| ≤ 2nK₁/ρ = 8nK₁/R.
- Since Du(x)a = D(Dh)(x)(a)(e) = D²h(x)(a, e), we get |D²h(x)(a, e)| ≤ 8nK₁/R for all unit a, e. By bilinearity, |D²h(x)(v, v)| ≤ (8nK₁/R)|v|² for every v ∈ ℝⁿ whenever |x| ≤ R/4.

6. (Taylor expansion; proof of (c).) Let |v| ≤ R/4 and φ(τ) := h(τv) on the open interval J := {τ : |τ|·|v| < R} ⊇ [0, 1], on which τv ∈ B.
- φ is C² with φ'(τ) = Dh(τv)v and φ''(τ) = D²h(τv)(v, v).
- For τ ∈ [0, 1], |τv| ≤ R/4, so step 5 gives |φ''(τ)| ≤ S := 8nK₁|v|²/R.
- Let ψ(τ) := φ(τ) − φ(0) − τφ'(0). Then ψ(0) = 0 and, for τ ∈ [0, 1], |ψ'(τ)| = |φ'(τ) − φ'(0)| ≤ τS (mean value inequality for φ').
- Hence |ψ(1)| ≤ ∫_0^1 τS dτ = S/2 = 4nK₁|v|²/R = C_H|v|²/R.
Since ψ(1) = h(v) − h(0) − Dh(0)v, this is (c). ∎

## Key steps

1. Each directional derivative u_e = Dh(·)e is C² and harmonic on B̆_R(0), by symmetry of the third derivative.
2. Ball mean value property (sibling (ii)) plus Cauchy–Schwarz give |h(y)| ≤ (ωρⁿ)^{−1/2}‖h‖_{L²(B̆_ρ(y))} and ‖Dh(y)‖ ≤ (ωρⁿ)^{−1/2}‖Dh‖_{L²(B̆_R)} whenever closedBall(y, ρ) ⊆ B̆_R(0).
3. Take ρ = R/2 for (a) and (b); take ρ = R/4 to get ‖Dh‖ ≤ 2ⁿω^{−1/2} on closedBall(0, 5R/8).
4. Compare ball means of u_e over B̆_{R/4}(x+ta) and B̆_{R/4}(x), bounding the symmetric difference by an annulus: |D²h(x)(a, e)| ≤ 8n·2ⁿω^{−1/2}/R for |x| ≤ R/4.
5. Second-order Taylor expansion along τ ↦ h(τv) gives (c) with C_H = 4n·2ⁿω^{−1/2}.

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
