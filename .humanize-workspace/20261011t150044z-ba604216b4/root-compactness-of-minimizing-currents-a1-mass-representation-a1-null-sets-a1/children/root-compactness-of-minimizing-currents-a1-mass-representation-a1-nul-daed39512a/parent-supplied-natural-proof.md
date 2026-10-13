# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1.orient_zero_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 8, for an arbitrary measurable W of finite μ-measure and measurable C ⊆ W.
Notation: |α| := covectorEuclideanNorm α. M_W(T) := T.massOn W is the supremum of ofReal(T(ω)) over ω ∈ massAdmissibleOn U n W, i.e. over ω ∈ TestFormOn U n with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x. μ.real s := (μ s).toReal. Hypotheses: (S) W and C are measurable, C ⊆ W, μ(W) < ∞; (M) M_W(T) = μ(W); (5) |ξ(x)(α)| ≤ |α|; (6) T(ω) = ∫ ξ(x)(ω(x)) dμ(x); (Z) for μ-a.e. x, x ∈ C → ξ(x) = 0.
1. (The bound G.) μ(W∖C) ≤ μ(W) < ∞. G := (W∖C).indicator 1 is real-valued, G ≥ 0, and G is μ-integrable because W∖C is measurable of finite measure (integrable_indicator_iff, integrableOn_const). Also ∫ G dμ = μ.real(W∖C) (integral_indicator_one).
2. (Pointwise domination.) Fix ω ∈ massAdmissibleOn U n W and let F(x) := ξ(x)(ω(x)). Claim: ‖F(x)‖ ≤ G(x) for μ-a.e. x. Take any x for which the implication in (Z) holds.
 - If x ∈ C (so x ∈ W): ξ(x) = 0, so F(x) = 0 ≤ G(x).
 - If x ∈ W∖C: |F(x)| ≤ |ω(x)| ≤ 1 = G(x), by (5) and admissibility.
 - If x ∉ W: x ∉ tsupport ω because tsupport ω ⊆ W. So ω(x) = 0 (image_eq_zero_of_notMem_tsupport) and F(x) = ξ(x)(0) = 0 ≤ G(x).
3. (Each admissible value.) By (6), T(ω) = ∫ F dμ. norm_integral_le_of_norm_le needs only G to be integrable, and gives T(ω) ≤ ‖∫ F dμ‖ ≤ ∫ G dμ = μ.real(W∖C). Hence ofReal(T(ω)) ≤ ofReal(μ.real(W∖C)) = μ(W∖C), the equality because μ(W∖C) ≠ ∞ (ENNReal.ofReal_toReal).
4. (Supremum.) ω was an arbitrary admissible form, so sSup_le gives M_W(T) ≤ μ(W∖C). By (M), μ(W) ≤ μ(W∖C).
5. (Conclusion.) C is measurable and C ⊆ W, so μ(W∖C) + μ(C) = μ(W∖C) + μ(W ∩ C) = μ(W) (measure_sdiff_add_inter). With step 4, μ(W∖C) + μ(C) ≤ μ(W∖C) + 0. Since μ(W∖C) < ∞, it may be cancelled (ENNReal.add_le_add_iff_left), so μ(C) ≤ 0, i.e. μ(C) = 0.

## Key steps

1. For admissible ω, |ξ(x)(ω(x))| ≤ 1_{W∖C}(x) μ-a.e.: it vanishes off W (ω = 0) and a.e. on C (ξ = 0), and is ≤ |ω| ≤ 1 on W∖C.
2. Hence T(ω) ≤ μ(W∖C), so μ(W) = M_W(T) ≤ μ(W∖C).
3. μ(W∖C) + μ(C) = μ(W) < ∞ forces μ(C) = 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/{Contract,Submission}.lean against workspace GMT/Ch07/{Contract,Submission}.lean (both identical); git rev-parse HEAD (b4d606db = manifest project_commit)`
- `rg -n 'euclideanHausdorffMeasure' mathlib/Mathlib -g '*.lean'; sed -n 55,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem exists_open_between_and_isCompact_closure|theorem LipschitzOnWith.hausdorffMeasure_image_le|theorem exists_measurable_superset_of_null|theorem MeasurableSet.exists_lt_isCompact_of_ne_top|theorem IsOpen.exists_iUnion_isCompact_eq_set|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem norm_integral_le_of_norm_le|theorem Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|theorem integral_indicator_one|theorem hausdorffMeasure_zero_singleton' mathlib/Mathlib -g '*.lean'`
- `rg -n 'hausdorffMeasure_image_le|exists_lt_isCompact_of_ne_top|of_sigmaCompactSpace_of_isLocallyFiniteMeasure|exists_iUnion_isCompact|IsOpen.isSigmaCompact|exists_iUnion_isClosed|compactCovering|InnerRegularCompactLTTop' mathlib/Mathlib -g '*.lean'`
- `rg -n 'Integrable.of_bound|bounded_above_of_compact_support|measure_sdiff_add_inter|EuclideanSpace.dist_eq|of_dist_le_mul|theorem integral_indicator' mathlib/Mathlib -g '*.lean'`
- `grep -n 'def massOn|def massAdmissibleOn|def covectorEuclideanNorm|def exteriorDerivativeTestOn|abbrev TestFormOn|def IsTestForm|structure GeometricCurrentOn|boundary_apply|le_massOn' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `python3 scan of dag.json: lean_name prefix cmr (no collision with the five proposed names) and lean_statement patterns 'μHE[n] C = 0 → volume', 'ν C = 0 → μ C = 0', 'massAdmissibleOn', 'toLp 2 (fun k => x (I k))', 'x ∈ C → ξ x = 0' (no accepted equivalent declaration)`
- `lake env lean /tmp/null-sets-split/T0.lean and T1.lean (#check / inferInstance availability after import GMT.Ch07.Submission)`
- `python3 -I gen.py using verifier/gmt-compare.py child_modules to generate comparator challenges; lake env lean /tmp/null-sets-split/challenges/*.lean`
- `lake env lean /tmp/null-sets-split/Assembly.lean (parent assembly from 5 child + 4 sibling frozen types); lake env lean /tmp/null-sets-split/AllChildren.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-null-sets-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-coo-17702f4d24/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-top-9a560aab97/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-div-abe89aabd1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/tmp/null-sets-split/Assembly.lean`
- `/tmp/null-sets-split/AllChildren.lean`
- `/tmp/null-sets-split/challenges/cmr_volume_coordProj_image_null.lean`
- `/tmp/null-sets-split/challenges/cmr_abs_integral_div_le_mass.lean`
- `/tmp/null-sets-split/challenges/cmr_ae_zero_of_div_bounds.lean`
- `/tmp/null-sets-split/challenges/cmr_measure_null_of_orient_ae_zero.lean`
- `/tmp/null-sets-split/challenges/cmr_null_of_compact_null.lean`

Snapshot. The manifest pins project b4d606db and mathlib 25730c7c. The snapshot Contract.lean and Submission.lean are byte-identical to the workspace files at HEAD b4d606db.

Lemmas found in the snapshot, all reachable from import GMT.Ch07.Submission:
- euclideanHausdorffMeasure_def and the scalar-factor-nonzero lemma (Geometry/Euclidean/Volume/Measure.lean:74, :96)
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (same file, :187)
- LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:745)
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean:205)
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486)
- integral_indicator and integral_indicator_one (Bochner/Set.lean:185, :533)
- norm_integral_le_of_norm_le (Bochner/Basic.lean:985)
- MeasurableSet.exists_lt_isCompact_of_ne_top (Regular.lean:874)
- Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (Regular.lean:1183)
- IsOpen.exists_iUnion_isClosed (HausdorffDistance.lean:207)
- exists_measurable_superset_of_null (MeasureSpaceDef.lean:219)
- exists_open_between_and_isCompact_closure (Separation/Regular.lean:364)
- Integrable.of_bound (IntegrableOn.lean:171)
- measure_sdiff_add_inter (Measure/Basic.lean:88)
- SimonGMT massOn, massAdmissibleOn, le_massOn, boundary_apply (rfl) and exteriorDerivativeTestOn

Not reachable. The general instance instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace (RegularityCompacts.lean:186) is outside the import closure, so the step 9 child uses finite restrictions; that route was confirmed by instance search. No IsOpen.exists_iUnion_isCompact_eq_set exists; F_i ∩ closedBall(0, j) is used instead.

Names and reuse. No accepted DAG declaration is equivalent to any proposed child, and the five names are globally fresh. The four siblings are not accepted. The runtime's _existing_lean_name_problem and _overlay_accepted_children therefore forbid reusing or overlaying them in children, so their content enters as hypotheses.

Lean checks.
- All five child types elaborate in the exact comparator challenge scope.
- The parent assembly of the selected frozen type compiles from the five child types plus the four sibling frozen types.
- All five children are fully proved in scratch with only propext, Classical.choice and Quot.sound.
