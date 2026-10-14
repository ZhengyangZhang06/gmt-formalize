# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.cutoff_deriv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 1 ("by differentiation under the integral sign I and J are C¹"; Simon Ch. 4, 3.4 and 3.16, where I(ρ) = ∫φ(r/ρ)dμ and J(ρ) are differentiated in ρ). Here the statement is proved for an arbitrary measure ν and an arbitrary bounded weight q, so that it covers I (q ≡ 1), the normal-weighted mass (q = |D^⊥r|²) and truncated weights.
Notation: r(x) := |x − y|, φ' := deriv φ, K := B̄_{R₀}(y) (closed ball), so ν(K) < ∞.
1. (φ and φ' vanish on [A, ∞).) For u > A, φ vanishes on the open interval (A, ∞) ∋ u, so φ'(u) = 0. Hence φ(u) = 0 for all u ≥ A and φ'(u) = 0 for all u > A. (At u = A one also has φ'(A) = 0, since φ is differentiable at A and φ(A + h) = 0 = φ(A) for h ≥ 0; this is not needed below.)
2. (Bounds.) φ and φ' are continuous because φ ∈ C¹. Put K₀ := 2R₀/τ > 0 and let C₀ := max_{[0,K₀]}|φ|, C₁ := max_{[0,K₀]}|φ'| (finite by compactness of [0, K₀]). Also B ≥ 0, since B ≥ |q(x)| ≥ 0 at any point x of ℝ^P.
3. (A neighbourhood of τ.) As A > 0 and Aτ < R₀ we have τ < R₀/A and R₀ > 0. Put δ := min(τ/2, (R₀/A − τ)/2) > 0. For σ in the open interval (τ − δ, τ + δ): σ > τ/2 > 0 and σ < R₀/A, i.e. Aσ < R₀.
4. (The integrands and their domination.) For σ > 0 and x ∈ ℝ^P put F(σ, x) := φ(r(x)/σ)q(x) and F'(σ, x) := −(r(x)/σ²)φ'(r(x)/σ)q(x). Let σ ∈ (τ − δ, τ + δ).
   (i) If x ∉ K then r(x) > R₀ > Aσ, so r(x)/σ > A and, by step 1, F(σ, x) = F'(σ, x) = 0.
   (ii) If x ∈ K then 0 ≤ r(x)/σ ≤ R₀/(τ/2) = K₀, so |φ(r/σ)| ≤ C₀, |φ'(r/σ)| ≤ C₁, and r/σ² ≤ R₀/(τ/2)²; hence |F(σ, x)| ≤ C₀B and |F'(σ, x)| ≤ L := (R₀/(τ/2)²)·C₁·B.
   Therefore |F(σ, x)| ≤ C₀B·1_K(x) and |F'(σ, x)| ≤ L·1_K(x) for all x and all σ ∈ (τ − δ, τ + δ). The functions C₀B·1_K and L·1_K are ν-integrable because ν(K) < ∞.
5. (Measurability; parts (a), (b).) For fixed σ > 0 the maps x ↦ φ(r(x)/σ) and x ↦ −(r(x)/σ²)φ'(r(x)/σ) are continuous (compositions of x ↦ |x − y|, division by σ, φ, φ'), hence strongly measurable; multiplied by the ν-a.e. strongly measurable q they give ν-a.e. strongly measurable functions F(σ, ·), F'(σ, ·). By step 4 with σ = τ, F(τ, ·) and F'(τ, ·) are dominated by integrable functions, hence ν-integrable. These are (a) and (b).
6. (Pointwise derivative.) Fix x. For σ > 0, σ ↦ r(x)/σ has derivative −r(x)/σ², and φ is differentiable everywhere, so by the chain rule σ ↦ F(σ, x) = φ(r(x)/σ)q(x) has derivative φ'(r(x)/σ)·(−r(x)/σ²)·q(x) = F'(σ, x) at every σ > 0, in particular at every σ ∈ (τ − δ, τ + δ).
7. (Differentiation under the integral sign; part (c).) Apply the dominated differentiation theorem (Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le) with the neighbourhood (τ − δ, τ + δ) of τ: F(σ, ·) is a.e. strongly measurable for every σ (step 5); F(τ, ·) is integrable (step 5); F'(τ, ·) is a.e. strongly measurable (step 5); |F'(σ, x)| ≤ L·1_K(x) for all x and all σ in the neighbourhood, with L·1_K integrable (step 4); and σ ↦ F(σ, x) has derivative F'(σ, x) at each σ of the neighbourhood, for every x (step 6). The theorem yields that σ ↦ ∫F(σ, x)dν(x) has derivative ∫F'(τ, x)dν(x) at τ, which is (c). ∎
Reference: a Lean proof of exactly this statement, compiled during the decomposition review against import GMT.Ch07.Submission (axioms propext, Classical.choice, Quot.sound only), is in /tmp/mono-review/Full2.lean, theorem GMT.Ch07.Review1.leaf1; it may be consulted if that file is available.

## Key steps

1. φ = 0 on [A, ∞) and φ' = 0 on (A, ∞); φ, φ' are bounded on [0, 2R₀/τ] by continuity.
2. For σ in (τ − δ, τ + δ), δ = min(τ/2, (R₀/A − τ)/2), one has σ > τ/2 and Aσ < R₀, so F(σ,·) = φ(r/σ)q and F'(σ,·) = −(r/σ²)φ'(r/σ)q vanish off K = B̄_{R₀}(y).
3. On K both are bounded uniformly in σ; constant·1_K is ν-integrable since ν(K) < ∞, giving integrability (a), (b) and the domination.
4. Chain rule: ∂_σ φ(r/σ) = −(r/σ²)φ'(r/σ).
5. hasDerivAt_integral_of_dominated_loc_of_deriv_le gives (c).

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
