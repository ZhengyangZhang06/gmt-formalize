# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 5, Lemma 3.1 (Harmonic Approximation Lemma) and its printed proof, normalized to the unit ball as in parent proof Part A, followed by the scaling of parent proof Part B. W^{1,2} is unavailable in the frozen Lean setting, so the proof is adapted as follows:
- the f_k are Lipschitz;
- the harmonicity of the L² limit comes from the distributional identity ∫WΔζ = 0 and the sibling Weyl lemma, instead of from weak convergence of gradients;
- the energy bound for the limit comes from sibling dorag_ha_energy_lsc, instead of weak lower semicontinuity.
Siblings used: dorag_ha_poincare_ball (constant C_P), dorag_ha_rellich_ball, dorag_ha_weyl_lemma, dorag_ha_energy_lsc.

Notation.
- B_ρ := B̆_ρ(0) and ω := Lⁿ(B_1).
- For Lipschitz u and C¹ ζ, ∇u·∇ζ := Σ_i Du(e_i)·Dζ(e_i). This is exactly the Lean integrand Σ_i fderiv ℝ u v (e_i) * fderiv ℝ ζ v (e_i).
- Δζ := Σ_i D²ζ(e_i, e_i) with D²ζ(y)(a, b) = iteratedFDeriv ℝ 2 ζ y ![a, b].
- H(w, R₀, δ) is the hypothesis of the statement: for every C¹ compactly supported ζ with tsupport ζ ⊆ B_{R₀} and every G with ‖Dζ(v)‖ ≤ G for all v, |∫_{B_{R₀}} ∇w·∇ζ| ≤ δR₀ⁿG.
- "h is admissible for (w, R₀, ε)" means: h is C^m on B_{R₀} for every m ∈ ℕ; Δh = 0 on B_{R₀}; ‖Dh‖² is integrable on B_{R₀} with ∫_{B_{R₀}} ‖Dh‖² ≤ R₀ⁿ; and (h − w)² is integrable on B_{R₀} with ∫_{B_{R₀}} (h − w)² ≤ εR₀^{n+2}.

Step 0 (integration by parts). Let u be Lipschitz and ζ ∈ C²(ℝⁿ) with compact support and tsupport ζ ⊆ B_1. Then ∫_{B_1} ∇u·∇ζ = −∫_{B_1} u·Δζ and ∫_{B_1} Δζ = 0.
Proof:
- g_i := Dζ(·)e_i is C¹ with compact support, hence Lipschitz.
- LipschitzWith.integral_lineDeriv_mul_eq with f := u, g := g_i, v := e_i gives ∫ lineDeriv ℝ u y e_i·g_i(y) dy = ∫ lineDeriv ℝ g_i y (−e_i)·u(y) dy = −∫ Dg_i(y)(e_i)·u(y) dy, and Dg_i(y)(e_i) = D²ζ(y)(e_i, e_i) (iteratedFDeriv_two_apply).
- For a.e. y, u is differentiable at y (Rademacher) and lineDeriv ℝ u y e_i = Du(y)e_i.
- Summing over i gives the first identity on ℝⁿ, and both integrands vanish outside tsupport ζ ⊆ B_1. With u ≡ 1 we get ∫_{B_1} Δζ = 0.

Part A (R₀ = 1). Claim A: for every ε > 0 there is δ > 0 such that every Lipschitz w with ∫_{B_1} ‖Dw‖² ≤ 1 and H(w, 1, δ) has an admissible h for (w, 1, ε).
A1. Suppose Claim A fails for some ε > 0. Then for each j ∈ ℕ, taking δ := 1/(j + 1), there is a Lipschitz w_j with ∫_{B_1} ‖Dw_j‖² ≤ 1 and H(w_j, 1, 1/(j + 1)) for which no admissible h for (w_j, 1, ε) exists.
A2. Let λ_j := ω^{−1}∫_{B_1} w_j and u_j := w_j − λ_j. Then u_j is Lipschitz and Du_j = Dw_j.
- By the Poincaré inequality, ∫_{B_1} u_j² ≤ C_P∫_{B_1} ‖Dw_j‖² ≤ C_P.
- With M := max(C_P, 1), Rellich applies to (u_j). It gives a strictly increasing φ : ℕ → ℕ and W with MemLp W 2 on B_1 and ∫_{B_1} (u_{φ(j)} − W)² → 0.
A3. Let ζ ∈ C²(ℝⁿ) with compact support and tsupport ζ ⊆ B_1.
- ζ is C¹, and Dζ is continuous with compact support, so G_ζ := sup_v ‖Dζ(v)‖ < ∞.
- H(w_k, 1, 1/(k + 1)) with G = G_ζ gives |∫_{B_1} ∇w_k·∇ζ| ≤ G_ζ/(k + 1).
- By Step 0, ∫_{B_1} u_k·Δζ = ∫_{B_1} w_k·Δζ − λ_k∫_{B_1} Δζ = −∫_{B_1} ∇w_k·∇ζ. Hence |∫_{B_1} u_{φ(j)}·Δζ| ≤ G_ζ/(φ(j) + 1) → 0.
- Δζ is bounded, so by Cauchy–Schwarz |∫_{B_1} (u_{φ(j)} − W)·Δζ| ≤ (∫_{B_1} (u_{φ(j)} − W)²)^{1/2}(∫_{B_1} (Δζ)²)^{1/2} → 0.
- Therefore ∫_{B_1} W·Δζ = 0.
W is integrable on B_1 (it is L² on a set of finite measure). So Weyl's lemma with R = 1 gives h̃ that is C^m on B_1 for every m, with Δh̃ = 0 on B_1 and h̃ = W a.e. on B_1.
A4. Apply dorag_ha_energy_lsc with R = 1, E = 1, the Lipschitz functions w_{φ(j)}, the constants c_j := λ_{φ(j)}, the function W, and h := h̃ (C² on B_1). Its hypotheses hold: ∫_{B_1} ‖Dw_{φ(j)}‖² ≤ 1, and ∫_{B_1} (w_{φ(j)} − λ_{φ(j)} − W)² = ∫_{B_1} (u_{φ(j)} − W)² → 0. Hence ‖Dh̃‖² is integrable on B_1 and ∫_{B_1} ‖Dh̃‖² ≤ 1.
A5. Choose j with ∫_{B_1} (u_{φ(j)} − W)² ≤ ε, and put h := h̃ + λ_{φ(j)}.
- Adding a constant changes no derivative of order ≥ 1. So on B_1, h is C^m for every m, Dh = Dh̃, D²h = D²h̃, Δh = 0, and ‖Dh‖² is integrable with ∫_{B_1} ‖Dh‖² ≤ 1 = 1ⁿ.
- A.e. on B_1, h − w_{φ(j)} = h̃ − u_{φ(j)} = W − u_{φ(j)}. So (h − w_{φ(j)})² is integrable on B_1 (W ∈ L² and u_{φ(j)} is bounded on B_1), and ∫_{B_1} (h − w_{φ(j)})² ≤ ε = ε·1^{n+2}.
Thus h is admissible for (w_{φ(j)}, 1, ε), contradicting A1 for the index φ(j). This proves Claim A.

Part B (scaling). Given ε > 0, let δ be the constant of Claim A for this ε. Let R₀ > 0 and let w be Lipschitz with ∫_{B_{R₀}} ‖Dw‖² ≤ R₀ⁿ and H(w, R₀, δ).
B1. Put w₁(y) := R₀^{−1}w(R₀y). It is Lipschitz.
- Dw₁(y) = Dw(R₀y) for every y. If w is differentiable at R₀y this is the chain rule. Otherwise w₁ is not differentiable at y either, because w = R₀w₁(·/R₀), and both fderivs are 0.
- Change of variables x = R₀y: Measure.setIntegral_comp_smul_of_pos with finrank = n and R₀·B_1 = B_{R₀} (and Measure.map_addHaar_smul for lower integrals) give ∫_{B_1} F(R₀y) dy = R₀^{−n}∫_{B_{R₀}} F for F integrable on B_{R₀} or F ≥ 0 measurable. Integrability transfers in both directions.
- So ∫_{B_1} ‖Dw₁‖² = R₀^{−n}∫_{B_{R₀}} ‖Dw‖² ≤ 1.
B2. H(w₁, 1, δ) holds. Let ζ₁ be C¹ with compact support and tsupport ζ₁ ⊆ B_1, and let G satisfy ‖Dζ₁(v)‖ ≤ G for all v.
- Put ζ(x) := R₀ζ₁(x/R₀). ζ is C¹ with compact support, tsupport ζ = R₀·tsupport ζ₁ ⊆ B_{R₀}, and Dζ(x) = Dζ₁(x/R₀), so ‖Dζ(x)‖ ≤ G.
- By H(w, R₀, δ), |∫_{B_{R₀}} ∇w·∇ζ| ≤ δR₀ⁿG.
- By B1 and the change of variables, ∫_{B_{R₀}} ∇w·∇ζ = ∫_{B_{R₀}} Σ_i Dw(x)e_i·Dζ₁(x/R₀)e_i dx = R₀ⁿ∫_{B_1} Σ_i Dw(R₀y)e_i·Dζ₁(y)e_i dy = R₀ⁿ∫_{B_1} ∇w₁·∇ζ₁.
Hence |∫_{B_1} ∇w₁·∇ζ₁| ≤ δG.
B3. By Claim A there is h₁ admissible for (w₁, 1, ε). Put h(x) := R₀h₁(x/R₀).
- h is C^m on B_{R₀} for every m, since x ↦ x/R₀ is linear and maps B_{R₀} onto B_1.
- Dh(x) = Dh₁(x/R₀) and D²h(x)(a, b) = R₀^{−1}D²h₁(x/R₀)(a, b). So Δh(x) = R₀^{−1}Δh₁(x/R₀) = 0 on B_{R₀}.
- By the change of variables of B1, ‖Dh‖² is integrable on B_{R₀} and ∫_{B_{R₀}} ‖Dh‖² = R₀ⁿ∫_{B_1} ‖Dh₁‖² ≤ R₀ⁿ.
- Since h(x) − w(x) = R₀(h₁ − w₁)(x/R₀), (h − w)² is integrable on B_{R₀} and ∫_{B_{R₀}} (h − w)² = R₀²·R₀ⁿ∫_{B_1} (h₁ − w₁)² ≤ εR₀^{n+2}.
So h has every property required by the statement, with a δ that depends only on n and ε. ∎

## Key steps

1. Integration by parts: ∫_{B_1} ∇u·∇ζ = −∫_{B_1} u·Δζ and ∫_{B_1} Δζ = 0 for Lipschitz u and C² ζ compactly supported in B_1.
2. Case R₀ = 1 by contradiction (Simon 5.3.1): take w_j with δ = 1/(j+1) and λ_j their averages; Poincaré bounds ∫(w_j − λ_j)², and Rellich gives an L²(B_1) limit W of a subsequence.
3. ∫_{B_1} W·Δζ = 0 for C² test functions; Weyl gives a smooth harmonic h̃ = W a.e., and energy_lsc gives ∫_{B_1} ‖Dh̃‖² ≤ 1.
4. For large j, h̃ + λ_{φ(j)} is admissible for w_{φ(j)}: contradiction.
5. Scaling: w₁(y) = R₀^{−1}w(R₀y), ζ(x) = R₀ζ₁(x/R₀), h(x) = R₀h₁(x/R₀); change of variables transfers every hypothesis and conclusion.

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
