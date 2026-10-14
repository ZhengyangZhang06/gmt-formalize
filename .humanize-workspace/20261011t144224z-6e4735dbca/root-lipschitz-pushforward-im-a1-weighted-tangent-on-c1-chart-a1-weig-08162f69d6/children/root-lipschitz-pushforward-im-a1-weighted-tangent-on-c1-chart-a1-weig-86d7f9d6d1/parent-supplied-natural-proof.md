# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1.remainder_vanishes-a1`
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

Put L(ρ) := ∫⁻_{D ∩ B̄_ρ(y)} ofReal(θ(x)) dμ(x) and q(ρ) := L(ρ) / ofReal(ρⁿ). The hypothesis is q(ρ) → 0 in [0, ∞] as ρ → 0+.

1. (Constants attached to φ.) tsupport φ is compact (φ has compact support), hence bounded, so there is R > 0 with tsupport φ ⊆ B_R(0) (Bornology.IsBounded.subset_ball_lt with lower bound 0 and centre 0). φ is continuous with compact support, hence bounded: there is A ∈ ℝ with |φ(z)| ≤ A for all z (Continuous.bounded_above_of_compact_support). In particular A ≥ |φ(0)| ≥ 0.

2. (Localization.) Let t > 0 and x ∉ B̄_{tR}(y); then φ(η_t(x)) = 0. Indeed, if φ(η_t(x)) ≠ 0, then η_t(x) ∈ support φ ⊆ tsupport φ ⊆ B_R(0). That is, |t⁻¹ • (x − y)| = t⁻¹|x − y| < R, so |x − y| < tR and x ∈ B̄_{tR}(y), a contradiction.

3. (Composition with t ↦ tR.) The map t ↦ tR is continuous with value 0 at t = 0, and it maps (0, ∞) into (0, ∞) because R > 0. Hence tR → 0 within (0, ∞) as t → 0+ (tendsto_nhdsWithin_iff). Composing with the hypothesis, q(tR) → 0 in [0, ∞] as t → 0+. Consequently:
 (a) since 0 < ∞, q(tR) < ∞ for all sufficiently small t > 0;
 (b) toReal is continuous at 0 ≠ ∞ (ENNReal.tendsto_toReal), so toReal(q(tR)) → 0, and therefore b(t) := A · Rⁿ · toReal(q(tR)) → A · Rⁿ · 0 = 0 as t → 0+.

4. (Reduction.) By the squeeze theorem for norms (squeeze_zero_norm'), it suffices to show that for all sufficiently small t > 0
 |(tⁿ)⁻¹ ∫_D φ(η_t(x)) θ(x) dμ(x)| ≤ b(t).
By 3(a), we may fix t > 0 with q(tR) < ∞.

5. (L(tR) is finite.) Since tR > 0, (tR)ⁿ > 0, so c := ofReal((tR)ⁿ) satisfies 0 < c < ∞. If L(tR) = ∞, then q(tR) = ∞ / c = ∞ (ENNReal.top_div_of_ne_top), contradicting q(tR) < ∞. Hence L(tR) < ∞.

6. (Pointwise bound.) D is null-measurable, so μ⌞D-almost every x belongs to D (ae_restrict_mem₀). Let x ∈ D.
- If x ∈ B̄_{tR}(y): θ(x) ≥ 0 and |φ(η_t(x))| ≤ A give |φ(η_t(x)) θ(x)| = |φ(η_t(x))| θ(x) ≤ A θ(x). So ofReal|φ(η_t(x)) θ(x)| ≤ ofReal(A θ(x)) = ofReal(A) · ofReal(θ(x)) (ENNReal.ofReal_mul, using A ≥ 0).
- If x ∉ B̄_{tR}(y): φ(η_t(x)) = 0 by step 2, so the left side is 0.
Hence, μ⌞D-a.e.,
 ofReal|φ(η_t(x)) θ(x)| ≤ ofReal(A) · 1_{B̄_{tR}(y)}(x) · ofReal(θ(x)).

7. (Lintegral bound.) Integrate step 6 over D (lintegral_mono_ae) and pull out the finite constant ofReal(A) (lintegral_const_mul'). The set B := B̄_{tR}(y) is closed, hence measurable, so ∫⁻_D 1_B · g dμ = ∫⁻ g d((μ⌞D)⌞B) = ∫⁻_{B ∩ D} g dμ = ∫⁻_{D ∩ B} g dμ (lintegral_indicator, Measure.restrict_restrict, Set.inter_comm). Therefore
 ∫⁻_D ofReal|φ(η_t(x)) θ(x)| dμ(x) ≤ ofReal(A) · L(tR).

8. (Bochner bound.) For every function f and set S, |∫_S f dμ| ≤ toReal(∫⁻_S ofReal|f| dμ) (norm_integral_le_lintegral_norm). No integrability is needed: if f is not integrable on S, the left side is 0. Since ofReal(A) · L(tR) < ∞ (step 5), toReal is monotone up to that value (ENNReal.toReal_mono), so step 7 gives
 |∫_D φ(η_t(x)) θ(x) dμ(x)| ≤ toReal(ofReal(A) · L(tR)) = A · toReal(L(tR))
(ENNReal.toReal_mul, and ENNReal.toReal_ofReal with A ≥ 0).

9. (Rescaling.) Since t > 0,
 |(tⁿ)⁻¹ ∫_D …| = (tⁿ)⁻¹ |∫_D …| ≤ (tⁿ)⁻¹ · A · toReal(L(tR)).
Moreover toReal(q(tR)) = toReal(L(tR)) / toReal(ofReal((tR)ⁿ)) = toReal(L(tR)) / (tR)ⁿ (ENNReal.toReal_div, and ENNReal.toReal_ofReal since (tR)ⁿ ≥ 0). Also (tR)ⁿ = tⁿ Rⁿ with tⁿ > 0 and Rⁿ > 0. Therefore
 (tⁿ)⁻¹ · A · toReal(L(tR)) = A · Rⁿ · toReal(L(tR)) / (tⁿ Rⁿ) = A · Rⁿ · toReal(q(tR)) = b(t).

10. (Conclusion.) Steps 4–9 show |(tⁿ)⁻¹ ∫_D φ(η_t(x)) θ(x) dμ(x)| ≤ b(t) for all sufficiently small t > 0, and b(t) → 0 by step 3(b). By the squeeze theorem, (tⁿ)⁻¹ ∫_D φ(η_t(x)) θ(x) dHⁿ(x) → 0 as t → 0+. ∎

## Key steps

1. Choose R > 0 with tsupport φ ⊆ B_R(0) and A ≥ 0 with |φ| ≤ A. For t > 0, φ(η_t(x)) = 0 whenever x ∉ B̄_{tR}(y).
2. Compose the density hypothesis with t ↦ tR, which tends to 0 within (0,∞): q(tR) → 0. Hence eventually q(tR) < ∞ (so L(tR) < ∞), and b(t) := A Rⁿ toReal q(tR) → 0.
3. Using θ ≥ 0 μ⌞D-a.e. on D (D null-measurable) and measurability of B̄_{tR}(y): ∫⁻_D ofReal|φ(η_t x)θ(x)| ≤ ofReal(A)·L(tR).
4. norm_integral_le_lintegral_norm and ENNReal.toReal_mono give |∫_D φ(η_t x)θ(x)| ≤ A·toReal L(tR), with no integrability needed.
5. (tⁿ)⁻¹ A toReal L(tR) = A Rⁿ toReal q(tR) = b(t), and the squeeze theorem gives convergence to 0.

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
