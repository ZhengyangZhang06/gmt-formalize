# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1`
- Child DAG node: `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1.weighted_diff_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the second half of step 4 and steps 5–6 of the parent-supplied proof of fiw_tl_transfer, specialized so that the test weight f∘η_r is replaced by an arbitrary continuous φ and the radius R·r by an arbitrary s ≤ ρ (no blow-up change of variables occurs here). Notation: H := μHE[n], B_t := B̄_t(x) = closedBall x t, h := 1_{M₂}θ₂ − c·1_{M₁}θ₁, t⁺ := ENNReal.ofReal t.

1. φ vanishes off B_ρ. Since s ≤ ρ, B_s ⊆ B_ρ (closedBall_subset_closedBall). Hence if z ∉ B_ρ then z ∉ B_s, so φ(z) = 0 by hypothesis.

2. Indicator form. Let i ∈ {1, 2}. Because M_i is H-null-measurable, integral_indicator₀ gives ∫_{M_i} φθ_i dH = ∫ 1_{M_i}(φθ_i) dH, and 1_{M_i}(φθ_i)(z) = φ(z)·(1_{M_i}θ_i)(z) for every z (indicator_mul_right). Put G_i(z) := φ(z)·(1_{M_i}θ_i)(z). Thus ∫_{M_i} φθ_i dH = ∫ G_i dH.

3. Integrability of G_i. The set M_i ∩ B_ρ is H-null-measurable (M_i is, and closed balls are measurable: NullMeasurableSet.inter with measurableSet_closedBall). So the hypothesis that θ_i is H-integrable on M_i ∩ B_ρ gives that 1_{M_i∩B_ρ}θ_i is H-integrable (IntegrableOn.integrable_indicator₀). φ is continuous, hence AE-strongly measurable, and ‖φ(z)‖ ≤ K for all z. Therefore z ↦ φ(z)·(1_{M_i∩B_ρ}θ_i)(z) is H-integrable (Integrable.bdd_mul). This function equals G_i at every z: if z ∈ B_ρ, then (1_{M_i∩B_ρ}θ_i)(z) = (1_{M_i}θ_i)(z), both being θ_i(z) when z ∈ M_i and 0 otherwise; if z ∉ B_ρ, then φ(z) = 0 by step 1 and both products are 0. Hence G_i is H-integrable (Integrable.congr).

4. Linearity. By step 2, ∫_{M₂} φθ₂ dH − c·∫_{M₁} φθ₁ dH = ∫ G₂ dH − c·∫ G₁ dH. By integral_const_mul, c·∫ G₁ dH = ∫ c·G₁ dH. By step 3 (G₂ and c·G₁ are integrable) and integral_sub, ∫ G₂ dH − ∫ c·G₁ dH = ∫ (G₂ − c·G₁) dH. Pointwise, G₂(z) − c·G₁(z) = φ(z)·h(z) by ring arithmetic. Hence ∫_{M₂} φθ₂ dH − c·∫_{M₁} φθ₁ dH = ∫ φ·h dH.

5. Pointwise bound. For every z, ‖φ(z)h(z)‖ₑ ≤ 1_{B_s}(z)·K⁺·‖h(z)‖ₑ. If z ∈ B_s, then ‖φ(z)h(z)‖ₑ = ‖φ(z)‖ₑ·‖h(z)‖ₑ (enorm_mul) and ‖φ(z)‖ₑ = ‖φ(z)‖⁺ ≤ K⁺ (ofReal_norm and ENNReal.ofReal_le_ofReal applied to ‖φ(z)‖ ≤ K). If z ∉ B_s, then φ(z) = 0, so the left side is 0.

6. Conclusion. By step 4 and enorm_integral_le_lintegral_enorm,
‖∫_{M₂} φθ₂ dH − c·∫_{M₁} φθ₁ dH‖ₑ = ‖∫ φ·h dH‖ₑ ≤ ∫⁻ ‖φ·h‖ₑ dH.
By step 5 and lintegral_mono this is at most ∫⁻ 1_{B_s}·(K⁺‖h‖ₑ) dH. That equals ∫⁻_{B_s} K⁺‖h‖ₑ dH by lintegral_indicator, since B_s is measurable. Finally it equals K⁺·∫⁻_{B_s} ‖h‖ₑ dH by lintegral_const_mul', since K⁺ ≠ ∞. This is the claimed inequality. ∎

## Key steps

1. s ≤ ρ gives B̄_s(x) ⊆ B̄_ρ(x), so φ = 0 off B̄_ρ(x).
2. integral_indicator₀ and indicator_mul_right give ∫_{M_i} φθ_i dH = ∫ φ·1_{M_i}θ_i dH.
3. φ·1_{M_i}θ_i = φ·1_{M_i∩B̄_ρ(x)}θ_i is H-integrable by IntegrableOn.integrable_indicator₀ and Integrable.bdd_mul.
4. integral_const_mul and integral_sub give ∫_{M₂}φθ₂ − c∫_{M₁}φθ₁ = ∫ φ·(1_{M₂}θ₂ − c·1_{M₁}θ₁) dH.
5. ‖φh‖ₑ ≤ 1_{B̄_s(x)}·ofReal(K)·‖h‖ₑ pointwise.
6. enorm_integral_le_lintegral_enorm, lintegral_indicator and lintegral_const_mul' give the bound ofReal(K)·∫⁻_{B̄_s(x)} ‖h‖ₑ dH.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch06/{Contract,Submission}.lean in workspace and in local-references/197bdd4b88278494/project (all ea3ee0ddd08be5db…)`
- `grep -n 'blowUpMap\|HasWeightedApproximateTangentSpaceAt\|^namespace\|^open' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rln blowUpMap simongmt/Poincare; grep -n '^theorem\|^import' Chapter04/WeightedBlowUp.lean; lean #eval env.header.moduleNames after import GMT.Ch06.Submission (5050 modules; only Poincare.SimonGMT.Chapter04.Basic from Ch04/Ch08)`
- `grep -n in snapshot mathlib: 'theorem integral_indicator₀' Bochner/Set.lean; 'theorem Integrable.bdd_mul' L1Space/Integrable.lean; 'theorem IntegrableOn.integrable_indicator₀' Integral/IntegrableOn.lean; 'theorem enorm_integral_le_lintegral_enorm' Bochner/Basic.lean; 'theorem lintegral_indicator' Lebesgue/Basic.lean; 'theorem lintegral_const_mul'' Lebesgue/Add.lean; 'Continuous.bounded_above_of_compact_support|exists_pos_le_norm' Normed/Group/Bounded.lean; 'lemma indicator_mul_right' GroupWithZero/Indicator.lean`
- `grep ofReal_norm Mathlib/Analysis/Normed/Group/Basic.lean; grep indicator_of_notMem Mathlib/Algebra/Notation/Indicator.lean; grep 'notation\|^theorem' Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `python3 -I scan of dag.json for tangent/transfer/blowup/growth nodes (lean_name, status, lean_statement of lpf_wtc_* accepted lemmas)`
- `python3 -I scan of dag.json (360 nodes), nodes/*/decomposition-v*.json (334 files), all node files (4731) for fiw_tl_tr_weighted_diff_bound|fiw_tl_tr_scaling_limit|fiw_tl_tr_`
- `for r in $(git for-each-ref): git grep -E 'fiw_tl_tr_(weighted_diff_bound|scaling_limit)' $r -- '*.lean' (1147 refs, no match)`
- `git archive d8d46c9587747dee0751a1f780fcafdba16a3886 | tar -x -C /tmp/fiw_tl_tr_split_CA4Dkj; LEAN_PATH=… lean -o .lake/build/lib/lean/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean (exit 0)`
- `python3 -I /tmp/fiw_tl_tr_split_scripts/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare.child_modules(mode='contract')); lean Cmp/*_Challenge.lean (3 files, exit 0)`
- `lean Audit/ChildA.lean, Audit/ChildB.lean, Audit/Assembly.lean (#print axioms: [propext, Classical.choice, Quot.sound])`
- `python3 -I /tmp/fiw_tl_tr_split_scripts/sim.py; lean simulated GMT/Ch06/Submission.lean, Cmp/*_Solution.lean, Cmp/Axioms.lean (exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/GroupWithZero/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Algebra/Notation/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/fiw_tl_tr_split_CA4Dkj/Audit/ChildA.lean`
- `/tmp/fiw_tl_tr_split_CA4Dkj/Audit/ChildB.lean`
- `/tmp/fiw_tl_tr_split_CA4Dkj/Audit/Assembly.lean`
- `/tmp/fiw_tl_tr_split_CA4Dkj/Audit/Closure.lean`
- `/tmp/fiw_tl_tr_split_CA4Dkj/Cmp/fiw_tl_tr_weighted_diff_bound_Challenge.lean`
- `/tmp/fiw_tl_tr_split_CA4Dkj/Cmp/fiw_tl_tr_scaling_limit_Challenge.lean`
- `/tmp/fiw_tl_tr_split_CA4Dkj/Cmp/fiw_tl_transfer_Challenge.lean`
- `/tmp/fiw_tl_tr_sim_XsLkVq/GMT/Ch06/Submission.lean`

Snapshot pins project d8d46c9587747dee0751a1f780fcafdba16a3886 and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace and snapshot Contract.lean/Submission.lean are byte-identical (sha256 ea3ee0dd…).

Definitions. SimonGMT Chapter03 defines blowUpMap x r y = r⁻¹ • (y − x). HasWeightedApproximateTangentSpaceAt is finrank Q = n together with ∀ f : C_c, Tendsto (∫_{blowUpMap x r '' M} f(y)·θ(x + r•y) dμHE[n]) (𝓝[>] 0) (𝓝 (θ x·∫_Q f)). Both match the supplied proof. SimonGMT's Chapter04 WeightedBlowUp lemmas lie outside the frozen import closure (only Chapter04.Basic is imported), and neither child needs them.

Mathlib lemmas. Every lemma used by the children exists with the used signature:
- integral_indicator₀, indicator_mul_right, IntegrableOn.integrable_indicator₀;
- Integrable.bdd_mul (ae bound form), integral_sub, integral_const_mul;
- enorm_integral_le_lintegral_enorm, enorm_mul, lintegral_indicator, lintegral_const_mul';
- ofReal_norm (ofReal_norm_eq_enorm is now a deprecated alias), ENNReal.ofReal_mul, ENNReal.ofReal_le_ofReal_iff;
- tendsto_nhdsWithin_iff, Metric.tendsto_nhds.
For the glue: HasCompactSupport.exists_pos_le_norm, Continuous.bounded_above_of_compact_support, Real.enorm_eq_ofReal.

Reuse. No accepted declaration has a type identical to either child. lpf_wtc_wtt_remainder_vanishes is related but needs θ ≥ 0 and a density hypothesis, so it is not reusable. The two new names occur nowhere in the DAG, in decomposition proposals, in node files or in git refs.

Lean checks. In a fresh build of the frozen commit:
- both child types and the parent type elaborate in the comparator's challenge layout;
- full proofs of both children compile using only propext, Classical.choice and Quot.sound;
- FiwTlTrAudit.assembly_exact derives the byte-exact frozen parent type from the byte-exact child types plus the dag.json types of fiw_tl_blowup_setIntegral and fiw_tl_growth_bound, with the same axioms;
- a simulated Submission passes all generated NodeSolution checks.
An independent reviewer replayed all of this and accepted.
