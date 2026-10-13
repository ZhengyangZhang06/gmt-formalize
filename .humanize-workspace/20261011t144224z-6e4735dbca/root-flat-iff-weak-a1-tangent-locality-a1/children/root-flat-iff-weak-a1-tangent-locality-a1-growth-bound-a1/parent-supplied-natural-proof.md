# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.tangent_locality-a1`
- Child DAG node: `root.flat_iff_weak-a1.tangent_locality-a1.growth_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4(i) of the parent-supplied proof (growth of ν₁ from the tangent hypothesis), stated for a single pair (M, θ). Notation: H := μHE[n], η_s := blowUpMap x s, and t⁺ := ENNReal.ofReal t. Note ‖η_s(z)‖ = ‖z − x‖/s for s > 0.

1. Test function. Let φ(y) := max(0, min(1, 2 − ‖y‖)). Then φ is continuous and 0 ≤ φ ≤ 1. Also φ(y) = 1 if ‖y‖ ≤ 1 and φ(y) = 0 if ‖y‖ ≥ 2. So φ vanishes outside the compact ball B̄_2(0) and defines f₀ ∈ C_c(ℝ^P, ℝ). In Lean write CompactlySupportedContinuousMap (Eucl P) ℝ, since the C_c notation needs `open scoped CompactlySupported`, and build it with HasCompactSupport.intro (isCompact_closedBall 0 2).

2. Use of the hypothesis. Let I(s) := ∫_{η_s(M)} f₀(y)·θ(x + s•y) dH(y). The second component of HasWeightedApproximateTangentSpaceAt, applied to f₀, gives I(s) → L := θ(x)·∫_Q f₀ dH as s → 0⁺. Put C := |L| + 1 > L. Then there is s₁ > 0 with I(s) < C for all s ∈ (0, s₁) (Tendsto.eventually with gt_mem_nhds).

3. Fix s with 0 < s < min(s₁, ρ/2). Apply the sibling lemma fiw_tl_blowup_setIntegral with S = M, r = s and g(y) = f₀(y)θ(x + s•y). Since x + s•η_s(z) = z, this gives I(s) = s^{−n}·∫_M F dH, where F(z) := f₀(η_s(z))·θ(z).

4. Properties of F:
(a) If ‖z − x‖ > ρ, then ‖η_s(z)‖ > ρ/s > 2, so F(z) = 0.
(b) If z ∈ B̄_s(x), then ‖η_s(z)‖ ≤ 1, so F(z) = θ(z).
(c) F ≥ 0 on M, because f₀ ≥ 0 and θ ≥ 0 on M.
(d) f₀∘η_s is continuous with |f₀∘η_s| ≤ 1.

5. Integrability of F on M. F is integrable on M ∩ B̄_ρ(x): it is a bounded continuous factor times the integrable θ (Integrable.bdd_mul). By 4(a), F = 0 on M ∖ B̄_ρ(x). Since M is null-measurable, F is integrable on M (IntegrableOn.of_ae_sdiff_eq_zero).

6. Comparison:
∫_{M∩B̄_s(x)} θ dH = ∫_{M∩B̄_s(x)} F dH, by 4(b) and setIntegral_congr_fun₀ on the null-measurable set M ∩ B̄_s(x);
≤ ∫_M F dH, by setIntegral_mono_set (F is integrable on M, F ≥ 0 a.e. for H⌞M by 4(c) and ae_restrict_mem₀, and M ∩ B̄_s(x) ⊆ M);
= sⁿ·I(s), by step 3;
≤ C·sⁿ, by step 2 and sⁿ > 0.

7. θ is integrable on M ∩ B̄_s(x) ⊆ M ∩ B̄_ρ(x) (IntegrableOn.mono_set), and θ ≥ 0 a.e. there. So ∫⁻_{M∩B̄_s(x)} θ⁺ dH = (∫_{M∩B̄_s(x)} θ dH)⁺ by ofReal_integral_eq_lintegral_ofReal. This is ≤ (C·sⁿ)⁺ by step 6 and monotonicity of ENNReal.ofReal.

8. Steps 3–7 hold for every s ∈ (0, min(s₁, ρ/2)). Combining the eventual statement of step 2 with Ioo_mem_nhdsGT (half_pos hρ), the bound holds for all sufficiently small s > 0, with the constant C of step 2. ∎

## Key steps

1. Choose f₀(y) = max(0, min(1, 2 − ‖y‖)) ∈ C_c, with 1_{B̄_1(0)} ≤ f₀ ≤ 1 and support in B̄_2(0).
2. The tangent hypothesis gives I(s) → θ(x)∫_Q f₀ dH, so I(s) < C := |L| + 1 for small s.
3. By the change of variables, I(s) = s^{−n}∫_M f₀(η_s z)θ(z) dH(z).
4. F = (f₀∘η_s)θ is integrable on M, nonnegative on M, and equals θ on B̄_s(x), so ∫_{M∩B̄_s(x)} θ ≤ ∫_M F = sⁿI(s) ≤ C sⁿ.
5. Convert to a lintegral with ofReal_integral_eq_lintegral_ofReal.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `grep -n 'blowUpMap\|HasWeightedApproximateTangentSpaceAt\|^import\|^namespace\|^open' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'μHE\|theorem\|lemma\|def \|notation' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image, IsometryEquiv.measurePreserving_euclideanHausdorffMeasure)`
- `grep -n -A6 'theorem ae_tendsto_measure_inter_div\b\|theorem tendsto_filterAt\|protected def vitaliFamily' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div\b' mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `grep -rn 'theorem ae_restrict_biUnion_iff\|theorem isOpen_iUnion_countable\|withDensity_apply'\|withDensity_absolutelyContinuous'\|setLIntegral_withDensity_eq_lintegral_mul₀\|lintegral_withDensity_eq_lintegral_mul₀\|of_ae_diff_eq_zero\|theorem integral_smul_measure\|theorem integral_map' mathlib/Mathlib`
- `python3 -I scan of dag.json (220 nodes) and nodes/*/decomposition-v*.json (223 files) for fiw_tl_blowup_setIntegral|fiw_tl_growth_bound|fiw_tl_transfer|fiw_tl_ae_l1_density and for related blow/tangent/growth/transfer/density lean_names`
- `for r in $(git for-each-ref): git grep -E 'fiw_tl_(blowup_setIntegral|growth_bound|transfer|ae_l1_density)' $r -- '*.lean' (626 refs, no match)`
- `git archive d8d46c9587747dee0751a1f780fcafdba16a3886 | tar -x -C /tmp/fiw_tl_a3_wb2ctk; LEAN_PATH=... lean -o .lake/build/lib/lean/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean (exit 0)`
- `python3 -I /tmp/fiw_tl_a3_scripts/gen.py: lean_contract.validate_lean_statement + gmt-compare.py child_modules(mode='contract') for the 4 child types and the frozen parent; lean Cmp/*_Challenge.lean (5 files, exit 0)`
- `lean Audit/Assembly.lean (#print axioms FiwTlAudit.assembly_exact: [propext, Classical.choice, Quot.sound])`
- `lean Audit/Names.lean, Audit/Names2.lean, Audit/Names3.lean (#check of every lemma cited in the child proofs; 0 errors)`
- `read nodes/root-flat-iff-weak-a1-tangent-locality-a1/{parent-child-handoff,decomposition-v1,decomposition-v2,decomposition-audit-v1,decomposition-audit-v2,decomposition-review-receipt-v2}.json and issue-workers.json entries for issue 809`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1/decomposition-audit-v2.json`
- `/tmp/fiw_tl_a3_wb2ctk/Cmp/fiw_tangent_locality_Challenge.lean`
- `/tmp/fiw_tl_a3_wb2ctk/Cmp/fiw_tl_transfer_Challenge.lean`
- `/tmp/fiw_tl_a3_wb2ctk/Cmp/fiw_tl_ae_l1_density_Challenge.lean`
- `/tmp/fiw_tl_a3_wb2ctk/Audit/Assembly.lean`
- `/tmp/fiw_tl_a3_wb2ctk/Audit/Names.lean`
- `/tmp/fiw_tl_a3_wb2ctk/Audit/Names3.lean`

The snapshot is project d8d46c9587747dee0751a1f780fcafdba16a3886 with Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Contract.lean and Submission.lean are byte-identical at that commit.

SimonGMT Chapter03 defines blowUpMap x r y = r⁻¹ • (y − x) and HasWeightedApproximateTangentSpaceAt as finrank Q = n together with convergence, for every f ∈ C_c, of ∫_{blowUpMap x r '' M} f(y)·θ(x + r•y) dμHE[n] to θ(x)·∫_Q f dμHE[n] as r → 0⁺. These definitions match the supplied proof.

Mathlib supplies every tool the children use:
- euclideanHausdorffMeasure_smul₀ (arbitrary sets) and Isometry.euclideanHausdorffMeasure_image;
- MeasurableEmbedding.integral_map and integral_smul_measure;
- Besicovitch.ae_tendsto_measure_inter_div, Besicovitch.vitaliFamily and Besicovitch.tendsto_filterAt;
- VitaliFamily.ae_tendsto_lintegral_enorm_sub_div (LocallyIntegrable);
- withDensity_absolutelyContinuous', withDensity_apply₀ and setLIntegral_withDensity_eq_lintegral_mul₀;
- ae_restrict_biUnion_iff and TopologicalSpace.isOpen_iUnion_countable;
- ENNReal.div_lt_iff and ENNReal.lt_div_iff_mul_lt, with the side conditions used.

There is no reusable accepted declaration. SimonGMT's Chapter04 blow-up lemmas are outside the frozen import closure. lpf_wtc_blowup_setIntegral_image is only alpha-equivalent to fiw_tl_blowup_setIntegral, belongs to another branch and is not accepted (rlcr-lean).

The fiw_tl_* names are reserved nowhere else: not in the DAG, not in other decompositions, not in any of the 626 git refs.

In a fresh build of the frozen commit, all four child types and the parent type elaborate in the comparator's exact challenge layout. FiwTlAudit.assembly_exact derives the byte-exact frozen parent type from the verbatim fiw_tl_transfer and fiw_tl_ae_l1_density types, using only propext, Classical.choice and Quot.sound.
