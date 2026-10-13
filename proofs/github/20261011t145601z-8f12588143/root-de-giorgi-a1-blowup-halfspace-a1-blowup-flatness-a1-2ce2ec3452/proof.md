# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.blowup_halfspace-a1`
- Child DAG node: `root.de_giorgi-a1.blowup_halfspace-a1.blowup_flatness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Selected-node proof, Step 2(b), (b1), (b2) and the closing remark of Step 2 ("The right-hand sides in (b1), (b2) tend to 0 as r ↓ 0, because rR ↓ 0"). This is Simon, Ch. 3, proof of Theorem 4.3, display (8) (chapter-03.txt lines 662-667: ∫_{ρ_k⁻¹E} D_iζ = ρ_k^{−n}∫_E D_iζ_k = −ρ_k^{−n}∫ζ_kν_i dμ_E → 0 by (2), i = 1, …, n) together with the display after (8) (lines 674-686) under erratum E1: for ζ ≥ 0 the correct sign is ∫_{ρ_k⁻¹E} D_{n+1}ζ = −ρ_k^{−n}∫ζ_kν_{n+1}dμ_E ≤ o(1). It is done at a general point x with a general unit vector e in place of x = 0, e = e_{n+1}. The blow-up identity (sibling blowup_identity, on balls) enters as hypothesis (I), and the excess decay (sibling density_estimates) as hypothesis (X). No sibling child of this split is used.

Notation. η_r := blowUpMap x r, η_r(y) = r⁻¹·(y − x); div := euclideanDivergence; D_wζ(z) := Dζ(z)w; ε(ρ) := (ρⁿ)⁻¹∫_{B_ρ(x)}|ν − e| dμ; "eventually" refers to the filter 𝓝[>]0 of right neighbourhoods of 0.

1. (Choice of R and M.) Fix ζ ∈ C¹_c(ℝ^N, ℝ). Its topological support is compact, hence bounded, so there is R > 0 with tsupport ζ ⊆ B_R(0). ζ is continuous with compact support, hence bounded: fix M ≥ 0 with |ζ(z)| ≤ M for all z.

2. (Window.) W := (0, ρ₁/R) belongs to 𝓝[>]0 because ρ₁/R > 0. For r ∈ W we have r > 0 and rR < ρ₁ (multiply r < ρ₁/R by R > 0).

3. (The field ζw.) For w ∈ ℝ^N let g_w(z) := ζ(z)·w. g_w is C¹ (a C¹ scalar function times a constant vector), has compact support, and tsupport g_w ⊆ tsupport ζ ⊆ B_R(0). As ζ is differentiable, Dg_w(z)u = (Dζ(z)u)·w for all u. This is a rank-one map with trace Dζ(z)w: in an orthonormal basis (b_i), Σ_i⟨b_i, (Dζ(z)b_i)w⟩ = Dζ(z)(Σ_i⟨b_i, w⟩b_i) = Dζ(z)w. Thus div g_w(z) = D_wζ(z) for every z. Also ⟨g_w(η_r(y)), ν(y)⟩ = ζ(η_r(y))⟨w, ν(y)⟩.

4. (Identity.) For r ∈ W, apply hypothesis (I) to (r, R, g_w) and rewrite both integrands pointwise by step 3:
 (★) ∫_{η_r(E)} D_wζ = −(rⁿ)⁻¹∫ζ(η_r(y))⟨w, ν(y)⟩ dμ(y).

5. (Localisation.) For r ∈ W put ρ := rR ∈ (0, ρ₁) and B := B_ρ(x). If y ∉ B then |η_r(y)| = r⁻¹|y − x| ≥ R, so η_r(y) ∉ tsupport ζ and ζ(η_r(y)) = 0. Hence |ζ(η_r(y))| ≤ M·1_B(y) for all y.

6. (Integrability.) μ(B) < ∞ by (F). The function y ↦ 1_B(y)|ν(y) − e| is μ-integrable: it is a.e. strongly measurable because ν is, it is bounded μ-a.e. by |ν| + |e| = 2, and it vanishes off B. Its integral is ∫_B|ν − e| dμ = ρⁿε(ρ), since ρ > 0. For every w, the function y ↦ ζ(η_r(y))⟨w, ν(y)⟩ is likewise integrable: ζ∘η_r is continuous, ν is a.e. strongly measurable, and the function is bounded μ-a.e. by M|w|·1_B (step 5 and |ν| = 1 a.e.).

7. ((H): horizontal directions.) Let ⟨v, e⟩ = 0. Then ⟨v, ν(y)⟩ = ⟨v, ν(y) − e⟩, so by Cauchy-Schwarz and step 5, |ζ(η_r(y))⟨v, ν(y)⟩| ≤ M|v|·1_B(y)|ν(y) − e| for all y. By (★) and step 6, for r ∈ W:
 |∫_{η_r(E)} D_vζ| ≤ (rⁿ)⁻¹M|v|∫_{B_{rR}(x)}|ν − e| dμ = M|v|Rⁿ·ε(rR),
 using (rⁿ)⁻¹ = Rⁿ·((rR)ⁿ)⁻¹.

8. (Limit of the bound.) The map r ↦ rR sends 𝓝[>]0 into 𝓝[>]0: it is continuous with value 0 at 0 and maps (0, ∞) into (0, ∞). So by (X), ε(rR) → 0 as r ↓ 0, and M|v|Rⁿε(rR) → 0. The bound of step 7 holds for all r ∈ W, i.e. eventually, so the squeeze theorem gives ∫_{η_r(E)} D_vζ → 0 as r ↓ 0. This proves (H).

9. ((M): the normal direction, corrected sign E1.) Let ζ ≥ 0 and take w = e. As |e| = 1, ⟨e, ν(y)⟩ = ⟨e, e⟩ + ⟨e, ν(y) − e⟩ ≥ 1 − |ν(y) − e|. Multiply by −ζ(η_r(y)) ≤ 0 and use ζ ≥ 0 and step 5:
 −ζ(η_r(y))⟨e, ν(y)⟩ ≤ −ζ(η_r(y)) + ζ(η_r(y))|ν(y) − e| ≤ M·1_B(y)|ν(y) − e| for all y.
 Integrate (both sides are integrable by step 6) and use (★): for r ∈ W,
 ∫_{η_r(E)} D_eζ = (rⁿ)⁻¹∫(−ζ(η_r(y))⟨e, ν(y)⟩) dμ(y) ≤ (rⁿ)⁻¹M∫_{B_{rR}(x)}|ν − e| dμ = MRⁿ·ε(rR).

10. Let δ > 0. By step 8 (with M in place of M|v|), MRⁿε(rR) → 0, so eventually MRⁿε(rR) < δ. Intersecting with W, which is also eventually, step 9 gives ∫_{η_r(E)} D_eζ ≤ δ eventually. This proves (M). ∎

## Key steps

1. Pick R > 0 with tsupport ζ ⊆ B_R(0), a bound M for |ζ|, and the window (0, ρ₁/R) ∈ 𝓝[>]0.
2. div(ζw) = D_wζ (trace of a rank-one map), so (I) gives ∫_{η_r(E)} D_wζ = −(rⁿ)⁻¹∫ζ(η_r)⟨w, ν⟩dμ.
3. ζ∘η_r vanishes off B_{rR}(x), whose μ-measure is finite; all integrands are integrable.
4. ⟨v, e⟩ = 0 gives ⟨v, ν⟩ = ⟨v, ν − e⟩ and |∫_{η_r(E)} D_vζ| ≤ M|v|Rⁿε(rR) → 0.
5. ζ ≥ 0 and |e| = 1 give ⟨e, ν⟩ ≥ 1 − |ν − e| and ∫_{η_r(E)} D_eζ ≤ MRⁿε(rR) → 0 (sign-corrected (8)), so the integral is eventually ≤ δ.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `rg -n "theorem tendsto_of_subseq_tendsto|theorem addHaar_image_homothety|theorem addHaar_smul|theorem addHaar_preimage_smul|theorem addHaar_image_continuousLinearEquiv|theorem integral_indicator₀|theorem setIntegral_union" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem HasCompactSupport.fderiv_apply" <snapshot>/mathlib/Mathlib; rg -n "mul_le_mul_left'|theorem mul_le_mul_right|zero_le" <snapshot>/mathlib/Mathlib/Algebra/Order`
- `rg -n "theorem trace_smulRight|trace_smulRight" <snapshot>/mathlib/Mathlib`
- `rg -n "symmDiff" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral; rg -n "theorem tendsto_measure_symmDiff|measure_symmDiff_le" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem [A-Za-z_']*blowUp|lemma [A-Za-z_']*blowUp" .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n "volume \(blowUpMap" .lake/packages/simongmt/Poincare/SimonGMT; rg -n "euclideanDivergence_smul|smulRight" .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `rg -n "^theorem|^lemma|^def" .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `python3 -I dag.json scan: lean_statements containing blowUpMap/symmDiff; lean_name collision check (152 nodes, also case-insensitive)`
- `python3 -I (importlib of verifier/gmt-compare.py) contract_scope + child_modules(contract mode) -> GMT/Scratch/BHS_Challenge_<key>.lean; lake env lean on BHS_Challenge_*.lean, BHS_Proof_*.lean, BHS_FullCheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-blowup-tangent-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_FullCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_image_volume.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_l1loc_transfer.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_perimeter_bound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_flatness.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). No Mathlib, SimonGMT or accepted-DAG declaration states any of the four children. Mathlib supplies only ingredients: addHaar_smul, NullMeasurableSet.const_smul, measure_preimage_add_right, integral_indicator₀, LinearMap.trace_smulRight (Trace.lean:272), HasCompactSupport.fderiv_apply (𝕜 explicit), measure_symmDiff_le, and tendsto_of_subseq_tendsto (CountablyGenerated.lean:125), which handles Step 6 directly. SimonGMT has blowUpMap (Rectifiable.lean) and euclideanDivergence/euclideanDivergence_eq_sum_inner (BV.lean). Its blow-up scaling lemmas are for μHE[n] and closed balls, in Chapter04 (not imported by Submission). FinitePerimeter.lean has definitions only. The rg searches for a Lebesgue-volume blow-up lemma, a divergence-of-ζv lemma and a set-integral/symmDiff transfer lemma found nothing. The accepted DAG nodes setIntegral_blowUpMap_image and chartTD_setIntegral_blowUpMap_image are μHE[n] identities with different types. All four child types elaborate in the exact NodeChallenge scope, and their full proofs compile with only propext, Classical.choice and Quot.sound. The selected-node assembly compiles against the frozen sibling types. No proposed lean_name collides with dag.json.
