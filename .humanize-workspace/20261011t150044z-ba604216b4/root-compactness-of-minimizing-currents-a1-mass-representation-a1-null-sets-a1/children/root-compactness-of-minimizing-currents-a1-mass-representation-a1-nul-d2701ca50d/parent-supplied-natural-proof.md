# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.null_sets-a1.div_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 4 (second to fourth bullets), with the divergence factor div g(q x) replaced by an arbitrary function D(x) and the evaluation bound eval_mass_bound taken as the hypothesis (EB).
Notation: |α| := covectorEuclideanNorm α; M_W(S) := S.massOn W; ∂T := T.boundary ∈ 𝒟_m(U); μ⌞W := μ.restrict W. Hypotheses: (W) W ⊆ U; (M) M_W(T) ≠ ∞ and M_W(∂T) ≠ ∞; (R) T(ω) = ∫ ξ(x)(ω(x)) dμ(x) for ω ∈ TestFormOn U (m+1); (EB) as in the statement; (b) tsupport b ⊆ W; (F) η, ζ are test forms with tsupport η ⊆ tsupport b, tsupport ζ ⊆ tsupport b, |η(x)| ≤ K and |ζ(x)| ≤ K for all x; (d) exteriorDerivative η x = (b(x)·D(x))•θ + ζ(x) for all x.
1. (Test forms in U.) By (F), (b) and (W), tsupport η ⊆ tsupport b ⊆ W ⊆ U and tsupport ζ ⊆ tsupport b ⊆ W ⊆ U. Since η and ζ are test forms, η' := ⟨η, ⟨IsTestForm η, tsupport η ⊆ U⟩⟩ ∈ TestFormOn U m and ζ' := ⟨ζ, ⟨IsTestForm ζ, tsupport ζ ⊆ U⟩⟩ ∈ TestFormOn U (m+1). Put ω := exteriorDerivativeTestOn U m η' − ζ' ∈ TestFormOn U (m+1).
2. (The form ω.) By the definition of exteriorDerivativeTestOn, the underlying form of exteriorDerivativeTestOn U m η' is exteriorDerivative η, and the coercion TestFormOn U (m+1) → DifferentialForm commutes with subtraction. Hence for every x, using (d): ω(x) = exteriorDerivative η x − ζ(x) = (b(x)·D(x))•θ.
3. (T(ω) through ∂T.) T.toCurrent is ℝ-linear, so T(ω) = T(exteriorDerivativeTestOn U m η') − T(ζ'). (In Lean use map_sub for (T.toCurrent : TestFormOn U (m+1) →ₗ[ℝ] ℝ); dot notation through the abbreviation CurrentOn may not resolve.) By GeometricCurrentOn.boundary_apply, which holds by rfl, T(exteriorDerivativeTestOn U m η') = ∂T(η'). Thus T(ω) = ∂T(η') − T(ζ').
4. (Mass bounds.) Apply (EB) with k = m, S = ∂T, the form η' and r = K. Its hypotheses hold: M_W(∂T) ≠ ∞ by (M), tsupport η ⊆ W by step 1, and |η(x)| ≤ K by (F). So |∂T(η')| ≤ K·M_W(∂T).toReal. Apply (EB) with k = m+1, S = T, the form ζ' and r = K to get |T(ζ')| ≤ K·M_W(T).toReal. By |a − c| ≤ |a| + |c| and step 3, |T(ω)| ≤ K·M_W(∂T).toReal + K·M_W(T).toReal = K·(M_W(∂T).toReal + M_W(T).toReal).
5. (The integral equals T(ω).) Let F(x) := b(x)·ξ(x)(θ)·D(x).
 - By (R) and step 2, T(ω) = ∫ ξ(x)((b(x)·D(x))•θ) dμ(x). Since ξ(x) is linear, ξ(x)((b(x)D(x))•θ) = (b(x)D(x))·ξ(x)(θ) = F(x) (map_smul, smul_eq_mul, ring). So T(ω) = ∫ F dμ.
 - If x ∉ W then x ∉ tsupport b by (b), so b(x) = 0 (image_eq_zero_of_notMem_tsupport) and F(x) = 0.
 - Hence setIntegral_eq_integral_of_forall_compl_eq_zero, which needs no measurability, gives ∫ F d(μ⌞W) = ∫_W F dμ = ∫ F dμ = T(ω).
6. (Conclusion.) By steps 4 and 5, |∫ b(x)·ξ(x)(θ)·D(x) d(μ⌞W)(x)| = |T(ω)| ≤ K·((T.boundary.massOn W).toReal + (T.massOn W).toReal).

## Key steps

1. η, ζ are test forms supported in tsupport b ⊆ W ⊆ U, so ω := dη' − ζ' ∈ 𝒟^{m+1}(U) has ω(x) = (b(x)D(x))•θ.
2. Linearity and boundary_apply give T(ω) = ∂T(η') − T(ζ').
3. (EB) bounds |∂T(η')| ≤ K M_W(∂T) and |T(ζ')| ≤ K M_W(T).
4. The representation turns T(ω) into ∫ b ξ(θ) D dμ, which equals the μ⌞W integral because b = 0 off W.

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
