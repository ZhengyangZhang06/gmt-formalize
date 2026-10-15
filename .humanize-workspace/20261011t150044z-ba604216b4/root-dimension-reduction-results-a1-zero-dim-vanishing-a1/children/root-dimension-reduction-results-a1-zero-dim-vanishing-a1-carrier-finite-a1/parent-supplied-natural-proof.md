# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.zero_dim_vanishing-a1`
- Child DAG node: `root.dimension_reduction_results-a1.zero_dim_vanishing-a1.carrier_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: H⁰ := μHE[0] on ℝ^P, M := R.carrier, θ := R.mult.
1. (H⁰ of a point.) By Mathlib, μHE[0] = μH[0] (MeasureTheory.Measure.euclideanHausdorffMeasure_zero) and μH[0]{x} = 1 (MeasureTheory.Measure.hausdorffMeasure_zero_singleton). Hence H⁰{x} = 1 for every x ∈ ℝ^P.
2. Put I := ∫⁻_{M∩K} θ dH⁰ ∈ [0, ∞]. Since K is compact and K ⊆ U, the field R.locallyIntegrable_mult gives I ≠ ∞.
3. Suppose, for a contradiction, that M ∩ K is infinite. We show that N ≤ I for every N ∈ ℕ.
4. Fix N ∈ ℕ. Because M ∩ K is infinite, there is a finite set t ⊆ M ∩ K with exactly N elements (Set.Infinite.exists_subset_card_eq).
5. Every x ∈ t lies in M, so θ(x) > 0 by the field R.mult_pos. Since θ(x) is a natural number, θ(x) ≥ 1, and by step 1, 1 ≤ θ(x)·H⁰{x}. Summing over t gives N = Σ_{x∈t} 1 ≤ Σ_{x∈t} θ(x)·H⁰{x}.
6. Singletons are measurable in ℝ^P, so the lower integral over the finite set t is the weighted sum: ∫⁻_t θ dH⁰ = Σ_{x∈t} θ(x)·H⁰{x} (lintegral_finset).
7. Since t ⊆ M ∩ K, the lower integral is monotone in the domain of integration (lintegral_mono_set): ∫⁻_t θ dH⁰ ≤ ∫⁻_{M∩K} θ dH⁰ = I. Combining steps 5–7 gives N ≤ I.
8. So N ≤ I for every N ∈ ℕ. Since N → ∞ in [0, ∞] (ENNReal.tendsto_nat_nhds_top), I = ∞, which contradicts step 2. Hence M ∩ K is finite.

## Key steps

1. μHE[0] = μH[0] gives H⁰{x} = 1 for every point x.
2. If M ∩ K were infinite, then for every N there is an N-element subset t ⊆ M ∩ K.
3. θ ≥ 1 on M gives N ≤ Σ_{x∈t} θ(x)H⁰{x} = ∫⁻_t θ dH⁰ ≤ ∫⁻_{M∩K} θ dH⁰.
4. So the lower integral is ∞, contradicting locallyIntegrable_mult; hence M ∩ K is finite.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `grep -n 'euclideanHausdorffMeasure_zero' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 620,665p local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem setIntegral_union |theorem integral_singleton |theorem lintegral_finset|theorem integrableOn_finite_biUnion|theorem IntegrableOn.of_forall_sdiff_eq_zero|theorem integrableOn_singleton |theorem Infinite.exists_subset_card_eq|theorem hausdorffMeasure_zero_singleton' (snapshot mathlib)`
- `grep -rn -i 'dirac\|pointCurrent\|pointGeometricCurrentOn\|TestFormOnConverges\.' .lake/packages/simongmt/Poincare/SimonGMT; sed -n 1,70p Chapter06/GeometricPointProduct.lean`
- `grep -n 'def HasApproximateTangentSpaceAt\|def CountablyRectifiable\|def blowUpMap\|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 1,200p simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, support); sed -n 1,320p Chapter06/Currents.lean (TestFormOnConverges, GeometricCurrentOn, ext, Zero); sed -n 1,140p Chapter06/Mass.lean (massOn)`
- `lake env lean /tmp/zdv-check/Probe.lean: env.contains of Poincare.SimonGMT.Chapter06.pointGeometricCurrentOn, Poincare.SimonGMT.Chapter06.TestFormOnConverges.tendsto_eval and GMT.Ch07.Submission.dimred_im_mass_measure after import GMT.Ch07.Submission`
- `python3 inspection of dag.json: dtc_dim_zero_eq_zero, dtc_dim_zero_carrier_finite, dtc_dim_zero_erase_point, dtc_point_current, dtc_approxTangent_sdiff_singleton, dor_zero_dim_minimizing_support_disjoint, regcomp_rim_sub_imrep, rsd_cmr_imrep_restrict (statements and statuses)`
- `grep -c dimred_zdv dag.json; for d in .swarm-worktrees/*/gmt-ch07/GMT; do grep -rl dimred_zdv $d; done`
- `lake env lean /tmp/zdv-check/Assembly.lean; lake env lean /tmp/zdv-check/Children.lean; lake env lean /tmp/zdv-check/Full.lean with #print axioms; string comparison of the tested parent and sibling types with the handoff lean_statement fields`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-zero-dim-vanishing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/tmp/zdv-check/Probe.lean`
- `/tmp/zdv-check/Assembly.lean`
- `/tmp/zdv-check/Children.lean`
- `/tmp/zdv-check/Full.lean`

Pins match. The snapshot is project b4d606d, equal to workspace HEAD, with mathlib 25730c7c and simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Mathlib facts used:
- μHE[0] = μH[0] (Measure.lean:82) and μH[0]{x} = 1 (Hausdorff.lean:628), so H⁰{x} = 1.
- Set-integral and integrability lemmas: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), setIntegral_union (:87), integral_singleton (Bochner/Basic.lean:1254), lintegral_finset (Lebesgue/Countable.lean:149), integrableOn_singleton / integrableOn_finite_biUnion / IntegrableOn.of_forall_sdiff_eq_zero (IntegrableOn.lean:221/226/435), Set.Infinite.exists_subset_card_eq (Data/Set/Finite/Basic.lean:862).

SimonGMT facts used:
- HasApproximateTangentSpaceAt integrates f over blowUpMap x r '' M against μHE[n] as r → 0⁺ (Rectifiable.lean:96–111). CountablyRectifiable.mono exists.
- support = U \ zeroRegion, where zeroRegion is the union of open W with compact closure ⊆ U on which the current vanishes (CurrentLocalEquality.lean).
- GeometricCurrentOn continuity is defined via TestFormOnConverges to 0; GeometricCurrentOn.ext and Zero are in Currents.lean.
- pointGeometricCurrentOn and TestFormOnConverges.tendsto_eval exist only in Chapter06/GeometricPointProduct.lean, which the contract does not import. The probe confirmed both are absent after import GMT.Ch07.Submission, so point_current must be proved as a child.

Related nodes. dtc_dim_zero_* and dtc_point_current, dor_zero_dim_minimizing_support_disjoint, regcomp_rim_sub_imrep and rsd_cmr_imrep_restrict are all status decomposing, none accepted. So no exact accepted declaration can be reused, and the names chosen here use the unused prefix dimred_zdv_; grep found no match in dag.json, the workspace GMT tree or any of the 544 swarm worktrees.

Lean check (scratch files only, workspace untouched):
- All four child types elaborate in GMT.Ch07 with the contract opens.
- All four children were fully proved (axioms propext, Classical.choice, Quot.sound).
- The frozen parent type was proved from them plus a stub of the frozen sibling dimred_im_mass_measure; the parent depends on sorryAx only through that stub.
