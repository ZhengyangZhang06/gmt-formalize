# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.smoothed_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Sibling map (dependency key — frozen Lean declaration): cutoff_deriv — Submission.doragm_radial_cutoff_hasDerivAt (integrability and the derivative of σ ↦ ∫φ(r/σ)q dν); radial_variation — Submission.doragm_radial_first_variation (radial first-variation identity).
Source: parent proof, Steps 1–2 (Simon Ch. 4, 3.4–3.5 and 3.16 with |H| ≤ κ). The parent integrates τ^{−n}J'(τ) over [s, t] and applies Tonelli; here, exactly as in Simon's own derivation of 3.5 ("by integration in 3.4"), the same estimate is obtained by comparing derivatives with G(τ) := ∫φ(r/τ)q dμ, whose increment G(t) − G(s) = ∫(φ(r/t) − φ(r/s))q dμ is the integrated Tonelli expression; the truncation q = N/max(s, r)ⁿ keeps G finite and coincides with r^{−n}N wherever ∂_τφ(r/τ) ≠ 0, τ ≥ s. The pointwise factors r^{−n} ≤ τ^{−n} ≤ Aⁿr^{−n} are those of the parent (Simon's printed 3.5 has them in reversed order).
Notation: B̄_ρ := B̄_ρ(y); r(x) := |x − y|; N(x) := |(x − y) − p_x(x − y)|²/r(x)² (N(y) = 0); φ' := deriv φ; c := Aκ; 'measurable' means μ-a.e. strongly measurable.
1. (Preliminaries.) κ ≥ |H(y)| ≥ 0, so c ≥ 0 (A > 1). 0 ≤ N ≤ 1 since |v − p_x v| ≤ |v| (v − p_x v is the orthogonal projection of v onto (T_xM)^⊥); N is measurable (x ↦ p_x(x − y) is measurable, as in radial_variation, step 7). B̄_{At} is compact and contained in the open set W, so there is δ₀ > 0 with B̄_{R₀} ⊆ W, R₀ := δ₀ + At (IsCompact.exists_cthickening_subset_open and cthickening_closedBall). B̄_{R₀} is a compact subset of U, so μ(B̄_ρ) ≤ μ(B̄_{R₀}) < ∞ for every ρ ≤ R₀ (IMRep.locallyIntegrable_mult).
2. (Profile.) Let φ(u) := Ψ((A − u)/(A − 1)), Ψ := Real.smoothTransition (C^∞, nondecreasing, 0 ≤ Ψ ≤ 1, Ψ = 0 on (−∞, 0], Ψ = 1 on [1, ∞)). Then φ is C¹, 0 ≤ φ ≤ 1, φ is nonincreasing, φ(u) = 1 for u ≤ 1 and φ(u) = 0 for u ≥ A. Hence φ' ≤ 0 everywhere; every u ≤ 1 is a global maximum point and every u ≥ A a global minimum point of φ, so φ'(u) = 0 there (IsLocalMax.deriv_eq_zero, IsLocalMin.deriv_eq_zero). Thus φ'(u) ≠ 0 implies 1 < u < A.
3. (Truncated weight.) q(x) := N(x)/max(s, r(x))ⁿ. Then 0 ≤ q ≤ s^{−n} and q is measurable. If r(x) > s then max(s, r) = r and q(x) = N(x)r^{−n} = |(x − y) − p_x(x − y)|²/r^{n+2} = F_y(x).
4. (Functions of the scale.) For τ > 0 let d_τ(x) := −(r(x)/τ²)φ'(r(x)/τ) ≥ 0 and define I(τ) := ∫φ(r/τ)dμ, G(τ) := ∫φ(r/τ)q dμ, I'(τ) := ∫d_τ dμ, G'(τ) := ∫d_τq dμ, J'(τ) := ∫d_τN dμ, h(τ) := ∫φ(r/τ)⟨x − y, H(x)⟩dμ. For τ ∈ [s, t] we have Aτ ≤ At < R₀ and μ(B̄_{R₀}) < ∞, so cutoff_deriv (with ν = μ and R₀, applied to the weights 1 (B = 1), q (B = s^{−n}) and N (B = 1)) gives: φ(r/τ), φ(r/τ)q, d_τ, d_τq and d_τN are μ-integrable, I has derivative I'(τ) at τ, and G has derivative G'(τ) at τ.
5. (The identity (E).) For τ ∈ [s, t], B̄_{Aτ} ⊆ B̄_{At} ⊆ W and φ satisfies the hypotheses of radial_variation, which gives nI(τ) + ∫(r/τ)φ'(r/τ)(1 − N)dμ = −h(τ). Pointwise (r/τ)φ'(r/τ)(1 − N) = (−τ)·d_τ + τ·d_τN (because τ·(r/τ²) = r/τ), and both terms are integrable, so ∫(r/τ)φ'(r/τ)(1 − N)dμ = −τI'(τ) + τJ'(τ). Hence
   (E) nI(τ) − τI'(τ) + τJ'(τ) = −h(τ) for τ ∈ [s, t].
6. (Mean curvature term.) Fix τ ∈ [s, t]. If φ(r(x)/τ) ≠ 0 then r(x) < Aτ, so |φ(r/τ)⟨x − y, H(x)⟩| ≤ φ(r/τ)·r·κ ≤ cτ·φ(r/τ); if φ(r/τ) = 0 both sides vanish. Since cτφ(r/τ) is integrable, |h(τ)| ≤ cτI(τ) (norm_integral_le_of_norm_le). Equivalently −cI(τ) ≤ h(τ)/τ ≤ cI(τ).
7. (Comparison (C), Simon 3.5.) J'(τ) ≥ 0 because d_τ ≥ 0 and N ≥ 0. For τ ∈ [s, t] and every x: d_τq ≤ τ^{−n}d_τN ≤ Aⁿd_τq. Indeed, if φ'(r/τ) = 0 all three terms vanish; otherwise 1 < r/τ < A by step 2, so s ≤ τ < r < Aτ, max(s, r) = r, q = N r^{−n}, and τ ≤ r ≤ Aτ gives r^{−n} ≤ τ^{−n} ≤ Aⁿr^{−n}; multiply by d_τN ≥ 0. Integrating (all three functions are integrable):
   (C) G'(τ) ≤ τ^{−n}J'(τ) ≤ AⁿG'(τ) for τ ∈ [s, t].
8. (Exponentially weighted ratios, Simon 3.16.) For b ∈ {c, −c} put Φ_b(τ) := e^{bτ}·τ^{−n}·I(τ). For τ ∈ [s, t], the product rule, step 4 and (τ^{−n})' = −nτ^{−n−1} give that Φ_b has derivative Φ_b'(τ) = e^{bτ}(bτ^{−n}I + τ^{−n}I' − nτ^{−n−1}I). By (E), τ^{−n}I' − nτ^{−n−1}I = τ^{−n−1}(τI' − nI) = τ^{−n−1}(τJ' + h) = τ^{−n}J' + τ^{−n}(h/τ), so
   Φ_b'(τ) = e^{bτ}τ^{−n}J'(τ) + e^{bτ}τ^{−n}(bI(τ) + h(τ)/τ).
   (a) b = c: cI + h/τ ≥ 0 by step 6, e^{cτ} ≥ 1 (c ≥ 0, τ > 0) and τ^{−n}J' ≥ 0, so Φ_c'(τ) ≥ e^{cτ}τ^{−n}J'(τ) ≥ τ^{−n}J'(τ) ≥ G'(τ) by (C).
   (b) b = −c: −cI + h/τ ≤ 0 by step 6 and 0 < e^{−cτ} ≤ 1, so Φ_{−c}'(τ) ≤ e^{−cτ}τ^{−n}J'(τ) ≤ τ^{−n}J'(τ) ≤ AⁿG'(τ) by (C).
9. (Integration over [s, t].) If f, g are differentiable at every point of [s, t] with f' ≤ g' on [s, t], then g − f is nondecreasing on [s, t] (monotoneOn_of_deriv_nonneg), so f(t) − f(s) ≤ g(t) − g(s). With step 8: (a) G(t) − G(s) ≤ Φ_c(t) − Φ_c(s); (b) Φ_{−c}(t) − Φ_{−c}(s) ≤ AⁿG(t) − AⁿG(s).
10. (Cutoff comparisons.) (K1) For τ ∈ [s, t]: μ(B̄_τ) ≤ I(τ) ≤ μ(B̄_{Aτ}) as real numbers, because 1_{B̄_τ} ≤ φ(r/τ) ≤ 1_{B̄_{Aτ}} pointwise (φ(r/τ) = 1 for r ≤ τ, φ(r/τ) = 0 for r ≥ Aτ, 0 ≤ φ ≤ 1) and these balls have finite measure.
   (K2) 1_{B̄_t∖B̄_{As}}F_y ≤ (φ(r/t) − φ(r/s))q pointwise: on B̄_t∖B̄_{As}, r ≤ t gives φ(r/t) = 1, r > As gives r/s > A and φ(r/s) = 0, and r > As > s gives q = F_y (step 3); elsewhere the left side is 0 while φ(r/t) − φ(r/s) ≥ 0 (r/t ≤ r/s and φ nonincreasing) and q ≥ 0.
   (K3) (φ(r/t) − φ(r/s))q ≤ 1_{B̄_{At}∖B̄_s}F_y pointwise: if r ≤ s, both φ-values equal 1; if r > At, both vanish (then also r/s > A); otherwise x ∈ B̄_{At}∖B̄_s, q = F_y and φ(r/t) − φ(r/s) ≤ 1.
   F_y is measurable and 0 ≤ F_y ≤ s^{−n} on {r > s} (there F_y = q), and the annuli B̄_t∖B̄_{As}, B̄_{At}∖B̄_s are contained in {r > s} and have finite measure, so F_y is integrable on them. Since G(t) − G(s) = ∫(φ(r/t) − φ(r/s))q dμ (difference of integrals of integrable functions), (K2) and (K3) give
   X₁ := ∫_{B̄_t∖B̄_{As}}F_y dμ ≤ G(t) − G(s) ≤ Y₁ := ∫_{B̄_{At}∖B̄_s}F_y dμ.
11. (Real inequalities.) From X₁ ≤ G(t) − G(s), 9(a) and (K1) (multiplied by e^{cs}s^{−n} ≥ 0, resp. e^{ct}t^{−n} ≥ 0):
   X₁ + e^{cs}s^{−n}μ(B̄_s) ≤ X₁ + e^{cs}s^{−n}I(s) ≤ e^{ct}t^{−n}I(t) ≤ e^{ct}t^{−n}μ(B̄_{At}).
   From (K1), 9(b) and G(t) − G(s) ≤ Y₁ (multiplied by Aⁿ ≥ 0):
   e^{−ct}t^{−n}μ(B̄_t) ≤ e^{−ct}t^{−n}I(t) ≤ e^{−cs}s^{−n}I(s) + Aⁿ(G(t) − G(s)) ≤ e^{−cs}s^{−n}μ(B̄_{As}) + AⁿY₁.
12. (Passage to [0, ∞].) All quantities are finite and nonnegative. For the integrable nonnegative F_y on an annulus S, ∫⁻_S ofReal(F_y)dμ = ofReal(∫_S F_y dμ) (ofReal_integral_eq_lintegral_ofReal); μ(B̄_ρ) = ofReal(μ(B̄_ρ).toReal) for ρ ≤ R₀; ENNReal.ofReal is additive and multiplicative on [0, ∞) and monotone. Applying ofReal to the two inequalities of step 11 gives exactly (i') and (ii') as stated (e^{cs} = Real.exp (A * κ * s), e^{−ct} = Real.exp (−(A * κ * t)), and so on). ∎
Reference: a Lean proof of exactly this statement, compiled during the decomposition review against import GMT.Ch07.Submission (axioms propext, Classical.choice, Quot.sound only), is in /tmp/mono-review/Full2.lean, theorem GMT.Ch07.MonoC3Check.child3_from (there the two sibling statements are hypotheses h1, h2); it may be consulted if that file is available.

## Key steps

1. Choose R₀ > At with B̄_{R₀}(y) ⊆ W (finite μ-measure); profile φ(u) = smoothTransition((A − u)/(A − 1)); truncated weight q = N/max(s, r)ⁿ, equal to F_y where r > s.
2. cutoff_deriv: I(τ) = ∫φ(r/τ)dμ and G(τ) = ∫φ(r/τ)q dμ are differentiable on [s, t] with derivatives I', G'; the derivative integrands are integrable.
3. radial_variation plus splitting gives nI − τI' + τJ' = −h; the bound |H| ≤ κ gives |h| ≤ cτI.
4. Pointwise squeeze on the support of φ'(r/τ): G' ≤ τ^{−n}J' ≤ AⁿG'.
5. Φ_{±c}(τ) = e^{±cτ}τ^{−n}I(τ) satisfy Φ_c' ≥ G' and Φ_{−c}' ≤ AⁿG'; integrate over [s, t] by derivative comparison.
6. Cutoff comparisons μ(B̄_τ) ≤ I(τ) ≤ μ(B̄_{Aτ}) and ∫_{B̄_t∖B̄_{As}}F_y ≤ G(t) − G(s) ≤ ∫_{B̄_{At}∖B̄_s}F_y.
7. Combine into two real inequalities and transfer them to [0, ∞] with ENNReal.ofReal.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project; project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical)`
- `rg -n -i 'monoton|radial|cutoff|density' project/GMT/Ch04/Submission.lean; rg -c sorry project/GMT/Ch0{3,4,5}/Submission.lean; rg -n doragm project (no match)`
- `rg -n 'def approxTangentPlane|def tangentialDivergence|def IMRep.firstVariation|def unitBallVolume|def IMRep.measure' project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le' mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean; rg -n 'theorem integral_withDensity_eq_integral_toReal_smul' mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `rg -n 'theorem cthickening_closedBall|exists_cthickening_subset_open' mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean mathlib/Mathlib/Topology/MetricSpace/Thickening.lean; rg -n 'theorem tendsto_measure_iInter_atTop|theorem tendsto_measure_iUnion_atTop' mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `rg -n 'theorem starProjection_orthogonal_val|theorem norm_starProjection_apply_le' mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean; rg -n 'lemma mem_support_iff_forall' mathlib/Mathlib/MeasureTheory/Measure/Support.lean; rg -n 'one_of_one_le|zero_of_nonpos|protected theorem monotone|protected theorem contDiff' mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n 'le_lintegral_ofReal|ofReal_integral_le' mathlib/Mathlib (no match); rg -n 'theorem integral_eq_lintegral_of_nonneg_ae|theorem ofReal_toReal_le' mathlib/Mathlib; rg -n 'euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_image' mathlib/Mathlib`
- `rg -n 'exp_normalizedBallMass_monotoneOn|cutoffMass_deriv_identity|hasDerivAt_integral_scaledRadialCutoff_mul|IsStationaryIn.cutoff_squeeze|one_le_density_of_approximateTangent|planeMeasure_unit_closedBall|hausdorff_blowUp_ball|trace_starProjection' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/*.lean; rg -n -l IMRep lake-packages-25730c7c/simongmt/Poincare/SimonGMT (no match)`
- `lean (contract scope) #check Chapter04.hausdorff_blowUp_ball (unknown: Chapter04 not imported), integral_withDensity_eq_integral_toReal_smul, hasDerivAt_integral_of_dominated_loc_of_deriv_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_homothety_image (all in scope)`
- `python3 -I name-collision scan of the six doragm_* names over all workspaces' dag.json, ch07 node JSON files and GMT/**/*.lean (no hit)`
- `lean /tmp/mono-decomp-check/{Children,Comparator,Assembly,Child3,Child4,Child6}.lean and /tmp/mono-review/Full2.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/tmp/mono-decomp-check/Assembly.lean`
- `/tmp/mono-review/Full2.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c, and its GMT/Ch07/Contract.lean is byte-identical to the workspace Submission.lean, which is the compiler context of every child type.
Nothing in the snapshot proves any child:
- GMT/Ch04/Submission.lean only states StationaryMonotonicity and StationaryDensity as Props, for its own RectifiableVarifold type, behind a sorry-backed main theorem.
- No doragm_* declaration exists.
- The pinned SimonGMT Chapter04 library proves the analogous cutoff identity, exponential monotonicity, cutoff squeeze and density-one results only for its RectifiableVarifold structure; nothing in SimonGMT mentions IMRep. Chapter04 is not imported by the contract (#check fails in contract scope), so it served only as a template. Simon's chapter-04.txt 3.2–3.5 and 3.16–3.17 fixed the proof route.
The Mathlib lemmas the children's proofs cite exist at the pinned revision and are in contract scope:
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286);
- integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318);
- IsCompact.exists_cthickening_subset_open (Thickening.lean:426) and cthickening_closedBall (Ball/Pointwise.lean:318);
- tendsto_measure_iInter_atTop and tendsto_measure_iUnion_atTop (Continuity.lean:220, 198);
- Submodule.starProjection_orthogonal_val and norm_starProjection_apply_le (Projection/Basic.lean:203, 411);
- Measure.mem_support_iff_forall (Support.lean:75);
- the Real.smoothTransition lemmas;
- integral_eq_lintegral_of_nonneg_ae (Bochner/Basic.lean:515) and ENNReal.ofReal_toReal_le;
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume and Isometry.euclideanHausdorffMeasure_image (Volume/Measure.lean:187, 131).
There is no ofReal_integral_le_lintegral_ofReal (rg: no match), so tangent_lower_density uses integral_eq_lintegral_of_nonneg_ae with ofReal_toReal_le instead.
Lean checks: all six child types elaborate, and the exact parent type follows from them plus the uncle. An end-to-end file proves all six children and the parent assuming only the uncle, with axioms propext, Classical.choice and Quot.sound only. No identical comparator-approved declaration exists to reuse.
