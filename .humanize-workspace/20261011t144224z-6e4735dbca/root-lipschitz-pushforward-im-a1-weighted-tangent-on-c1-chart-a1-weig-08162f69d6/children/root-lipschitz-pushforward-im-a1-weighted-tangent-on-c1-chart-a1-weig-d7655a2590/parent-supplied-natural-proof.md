# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1.continuity_error_vanishes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- ℝ^Q = Eucl Q = EuclideanSpace ℝ (Fin Q), with Euclidean norm |·|.
- μ := μHE[n] is Mathlib's Euclidean-normalized n-dimensional Hausdorff measure on ℝ^Q. It is a Borel measure, so closed balls are μ-measurable.
- B̄_ρ(y) = closedBall y ρ and B_ρ(0) = ball 0 ρ.
- For t ∈ ℝ, η_t(x) := Poincare.SimonGMT.Chapter03.blowUpMap y t x = t⁻¹ • (x − y).
- ∫_S f dμ is the Bochner integral of f against μ restricted to S (0 when f is not integrable on S); ∫⁻ is the [0, ∞]-valued lintegral.
- ofReal : ℝ → [0, ∞] is a ↦ max(a, 0). toReal : [0, ∞] → ℝ is the identity on [0, ∞) and sends ∞ to 0.
- 'For all sufficiently small t > 0' means 'eventually in the filter 𝓝[>] 0'.

Let K ∈ ℝ≥0 be as in the hypothesis, so μ(C ∩ B̄_ρ(y)) ≤ K · ofReal(ρⁿ) for all sufficiently small ρ > 0.

1. (Constants attached to φ.) tsupport φ is compact, hence bounded, so there is R > 0 with tsupport φ ⊆ B_R(0) (Bornology.IsBounded.subset_ball_lt). φ is continuous with compact support, so there is A with |φ(z)| ≤ A for all z (Continuous.bounded_above_of_compact_support). In particular A ≥ |φ(0)| ≥ 0.

2. (Localization.) Let t > 0 and x ∉ B̄_{tR}(y); then φ(η_t(x)) = 0. Otherwise η_t(x) ∈ support φ ⊆ tsupport φ ⊆ B_R(0), so t⁻¹|x − y| < R, i.e. |x − y| < tR, contradicting x ∉ B̄_{tR}(y).

3. (Composition with t ↦ tR.) The map t ↦ tR is continuous, vanishes at 0, and maps (0, ∞) into (0, ∞) because R > 0. So tR → 0 within (0, ∞) as t → 0+ (tendsto_nhdsWithin_iff). Hence the density bound holds at ρ = tR for all sufficiently small t > 0:
 μ(C ∩ B̄_{tR}(y)) ≤ K · ofReal((tR)ⁿ).   (∗)
Also, for every δ > 0, tR < δ for all sufficiently small t > 0.

4. (ε-formulation.) We verify the metric definition of convergence to 0 (Metric.tendsto_nhds). Let ε > 0. Put c := A · K · Rⁿ ≥ 0 and ε₁ := ε / (2(c + 1)) > 0. By ContinuousWithinAt θ C y (Metric.continuousWithinAt_iff) there is δ > 0 such that |θ(x) − θ(y)| < ε₁ for every x ∈ C with |x − y| < δ. By step 3, all sufficiently small t > 0 satisfy both (∗) and tR < δ; fix such a t > 0. It suffices to show
 |(tⁿ)⁻¹ ∫_C φ(η_t(x)) (θ(x) − θ(y)) dμ(x)| < ε.

5. (Pointwise bound.) C is null-measurable, so μ⌞C-almost every x lies in C (ae_restrict_mem₀). Let x ∈ C.
- If x ∈ B̄_{tR}(y), then |x − y| ≤ tR < δ, so |θ(x) − θ(y)| < ε₁ and |φ(η_t(x))(θ(x) − θ(y))| = |φ(η_t(x))| · |θ(x) − θ(y)| ≤ A ε₁.
- If x ∉ B̄_{tR}(y), then φ(η_t(x)) = 0 by step 2.
Hence, μ⌞C-a.e.,
 ofReal|φ(η_t(x)) (θ(x) − θ(y))| ≤ 1_{B̄_{tR}(y)}(x) · ofReal(A ε₁).

6. (Lintegral bound.) Integrate step 5 over C (lintegral_mono_ae). The closed ball B := B̄_{tR}(y) is measurable, so ∫⁻_C 1_B · ofReal(A ε₁) dμ = ofReal(A ε₁) · (μ⌞C)(B) = ofReal(A ε₁) · μ(B ∩ C) = ofReal(A ε₁) · μ(C ∩ B) (lintegral_indicator_const, Measure.restrict_apply, Set.inter_comm). Multiplying (∗) by the constant ofReal(A ε₁) then gives
 ∫⁻_C ofReal|φ(η_t(x)) (θ(x) − θ(y))| dμ ≤ ofReal(A ε₁) · μ(C ∩ B̄_{tR}(y)) ≤ ofReal(A ε₁) · K · ofReal((tR)ⁿ).
The right-hand side is finite, being a product of finite elements of [0, ∞].

7. (Bochner bound.) For every function f and set S, |∫_S f dμ| ≤ toReal(∫⁻_S ofReal|f| dμ) (norm_integral_le_lintegral_norm; no integrability is needed). toReal is monotone below a finite value (ENNReal.toReal_mono), so step 6 gives
 |∫_C φ(η_t(x)) (θ(x) − θ(y)) dμ| ≤ toReal(ofReal(A ε₁) · K · ofReal((tR)ⁿ)) = A ε₁ · K · (tR)ⁿ.
The equality uses ENNReal.toReal_mul, ENNReal.toReal_ofReal (with A ε₁ ≥ 0 and (tR)ⁿ ≥ 0), and the fact that toReal of the coercion of K is K.

8. (Rescaling.) Since t > 0, tⁿ > 0 and (tR)ⁿ = tⁿ Rⁿ, so
 |(tⁿ)⁻¹ ∫_C …| = (tⁿ)⁻¹ |∫_C …| ≤ (tⁿ)⁻¹ · A ε₁ K tⁿ Rⁿ = A K Rⁿ · ε₁ = c ε₁ = ε · c / (2(c + 1)).
Since 0 ≤ c < 2(c + 1), we have c / (2(c + 1)) < 1, so c ε₁ < ε (as ε > 0).

9. (Conclusion.) Since ε > 0 was arbitrary, (tⁿ)⁻¹ ∫_C φ(η_t(x)) (θ(x) − θ(y)) dHⁿ(x) → 0 as t → 0+. ∎

## Key steps

1. Choose R > 0 with tsupport φ ⊆ B_R(0) and A ≥ 0 with |φ| ≤ A. For t > 0, φ(η_t(x)) = 0 off B̄_{tR}(y). Composing with t ↦ tR (which tends to 0 within (0,∞)), the density bound holds at ρ = tR for all small t > 0.
2. Given ε > 0, put c = A K Rⁿ and ε₁ = ε/(2(c+1)). ContinuousWithinAt gives δ > 0 with |θ(x) − θ(y)| < ε₁ for x ∈ C, |x − y| < δ. For small t, also tR < δ.
3. μ⌞C-a.e. (C is null-measurable), ofReal|φ(η_t x)(θ(x) − θ(y))| ≤ 1_{B̄_{tR}(y)}(x)·ofReal(Aε₁). So the lintegral over C is ≤ ofReal(Aε₁)·Hⁿ(C ∩ B̄_{tR}(y)) ≤ ofReal(Aε₁)·K·ofReal((tR)ⁿ) < ∞.
4. norm_integral_le_lintegral_norm and ENNReal.toReal_mono give |∫_C …| ≤ Aε₁K(tR)ⁿ.
5. Rescaling: |(tⁿ)⁻¹∫_C …| ≤ cε₁ = εc/(2(c+1)) < ε. Since ε is arbitrary, the term tends to 0.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'weighted_tangent|tangent_transfer|blowup_integral|continuity_error|remainder_vanishes|lpf_wtc' <snapshot>/project --glob '*.lean' (no match)`
- `rg -n 'HasWeightedApproximateTangentSpaceAt|blowUpMap' <snapshot>/project --glob '*.lean' (only frozen Ch04/Ch05/Ch06/Ch08 Contract/Submission uses of the predicate; blowUpMap absent)`
- `rg -n 'theorem norm_integral_le_lintegral_norm|theorem setIntegral_union₀|theorem integral_add |theorem integral_const_mul ' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `rg -n 'of_ae_sdiff_eq_zero|of_ae_diff_eq_zero|integrableOn_of_bounded' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `grep -n 'blowUpMap|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; read lines 1-150 and 300-380`
- `sed -n 270,330p book/chapter-03.txt (Definition 1.7, Remark 1.8(1))`
- `python3 scan of dag.json lean_name values for lpf_wtc_wtt_* (no match among 207 nodes); git log --all --oneline -S lpf_wtc_wtt (no match)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') loaded from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the 3 child statements`
- `lake build GMT.Ch06.Submission in /tmp/wtt2_scratch_Eaxecg (.lake/packages symlinked to lake-packages-25730c7c); lake env lean Scratch/Chal_*.lean, Scratch/Assembly.lean, Scratch/Checks.lean (#check of every cited lemma); persistent lean --server checks of Scratch/Prove_*.lean and Scratch/Full.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-08162f69d6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-08162f69d6/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Chal_blowup_integral_split.lean`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Chal_continuity_error_vanishes.lean`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Chal_remainder_vanishes.lean`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Assembly.lean`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Checks.lean`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Prove_blowup_integral_split.lean`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Prove_continuity_error_vanishes.lean`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Prove_remainder_vanishes.lean`
- `/tmp/wtt2_scratch_Eaxecg/Scratch/Full.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The workspace Contract.lean and Submission.lean are byte-identical.

No existing declaration states the three-term split, the I₂ estimate or the I₃ estimate. rg over the project snapshot for weighted_tangent|tangent_transfer|blowup_integral|continuity_error|remainder_vanishes|lpf_wtc finds nothing. HasWeightedApproximateTangentSpaceAt occurs there only in the frozen Ch04/Ch05/Ch06/Ch08 contracts.

The shapes the children use are fixed by SimonGMT Chapter03 Rectifiable.lean:
- l.96 blowUpMap x r y = r⁻¹•(y−x);
- l.102 HasApproximateTangentSpaceAt (Def. 1.4);
- l.330 HasWeightedApproximateTangentSpaceAt (Def. 1.7), with integrand f y * θ (x + r • y) and limit θ x * ∫_P f.

The snapshot Mathlib has the cited lemmas:
- norm_integral_le_lintegral_norm (Bochner/Basic.lean:328, no hypotheses);
- integral_add (:239) and integral_const_mul (:290);
- setIntegral_union₀ (Bochner/Set.lean:80);
- IntegrableOn.of_ae_sdiff_eq_zero (IntegrableOn.lean:408) and Measure.integrableOn_of_bounded (IntegrableOn.lean:716).
A Lean #check confirmed the signatures of these and of Integrable.bdd_mul, Bornology.IsBounded.subset_ball_lt, Continuous.bounded_above_of_compact_support, Metric.continuousWithinAt_iff, ae_restrict_mem₀, lintegral_indicator(_const), lintegral_const_mul', ENNReal.toReal_mono, ENNReal.tendsto_toReal, ENNReal.top_div_of_ne_top, ENNReal.toReal_div and squeeze_zero_norm'.

Book Remark 1.8(1) only says the transfer is 'straightforward to check', so the child proofs are extracted from parent Steps 4, 6 and 7 with the details filled in.

The names lpf_wtc_wtt_* are unreserved in dag.json and absent from git history.

Lean checks in the exact comparator scope:
- The three statements validate and elaborate.
- The frozen parent is proved sorry-free from the two sibling contracts and the three child contracts.
- Each child is fully proved with axioms {propext, Classical.choice, Quot.sound} only.
