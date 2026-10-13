# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1.testform_restrict_cc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 8, first sentence (g_ω(x) := c(ω(val x)) is continuous, with support in the compact set val⁻¹(tsupport ω)). It is stated here for any continuous f with f(0) = 0; the parent uses f := c.
Notation: val : ↥U → ℝ^P is the inclusion and K := tsupport ω.
1. Membership ω ∈ TestFormOn U n means IsTestForm ω and K ⊆ U, where IsTestForm ω means that ω is C^∞ and HasCompactSupport ω. So ω is continuous (ContDiff.continuous) and K is compact.
2. Define G : ↥U → ℝ^d by G(x) := f(ω(val x)). G is continuous, being the composition of the continuous maps val (continuous_subtype_val), ω and f.
3. K_U := val⁻¹(K) is compact in ↥U. The map val is inducing (Topology.IsInducing.subtypeVal) and K ⊆ U = range val (Subtype.range_coe). So by Topology.IsInducing.isCompact_preimage_iff, val⁻¹(K) is compact iff K is, and K is compact by step 1.
4. If x ∈ ↥U and x ∉ K_U, then val x ∉ tsupport ω, so ω(val x) = 0 (image_eq_zero_of_notMem_tsupport). Hence G(x) = f(0) = 0.
5. ↥U is Hausdorff, as a subspace of the metric space ℝ^P. By steps 3–4 and HasCompactSupport.intro, G has compact support.
6. Let g ∈ C_c(U, ℝ^d) be the element with underlying continuous map G (steps 2 and 5). For every x ∈ U, g(x) = G(x) = f(ω(x)) by definition (rfl). ∎

## Key steps

1. G := f ∘ ω ∘ val is continuous.
2. val⁻¹(tsupport ω) is compact, because val is inducing and tsupport ω ⊆ U = range val.
3. G vanishes off val⁻¹(tsupport ω) since f(0) = 0, so G has compact support (HasCompactSupport.intro); package it as g ∈ C_c(U, ℝ^d).

## Reference use

### local-project

Queries:
- `rg -n 'cmrc_|polar_pushforward|massOn_le_of_repr|measure_le_massOn_of_norming|measure_le_of_compactlyContained|testForm_restrict_cc' project mathlib -g '*.lean'  (exit 1: no match)`
- `rg -n 'rsd_mw_exists_testForm_approx|cmr_vector_riesz_representation|cmr_testForm_extension_functional|cmr_covector_euclidean_equiv' project -g '*.lean'  (exit 1: no match; these exist only as DAG declarations)`
- `rg -n 'def CompactlyContained|abbrev MultiVector|def boundaryMassOn' project/GMT/Ch07/Contract.lean; cmp project/GMT/Ch07/Contract.lean <workspace>/GMT/Ch07/Submission.lean (identical)`
- `rg -n 'theorem integral_withDensity_eq_integral_toReal_smul |theorem withDensity_apply_eq_zero |theorem measurable_extend |theorem subtype_coe|theorem continuous_infEDist|theorem mem_closure_iff_infEDist_zero|theorem enorm_integral_le_lintegral_enorm|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem integral_eq_lintegral_of_nonneg_ae|lemma Integrable.of_bound|theorem lintegral_indicator_one |theorem exists_inv_nat_lt|theorem le_of_forall_pos_le_add' mathlib/Mathlib -g '*.lean'`
- `rg -n 'isCompact_preimage_iff' mathlib/Mathlib/Topology; rg -n 'Monotone.measure_iUnion' mathlib/Mathlib/MeasureTheory/Measure; rg -n 'integral_map' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean; rg -n 'theorem intro' mathlib/Mathlib/Topology/Algebra/Support.lean; rg -n 'Continuous.clm_comp' mathlib/Mathlib/Analysis/Normed/Operator`
- `grep -n 'def massOn|def massAdmissibleOn|theorem le_massOn|abbrev TestFormOn|def IsTestForm|def covectorEuclideanNorm' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass}.lean`
- `lake env lean /tmp/rc-core-split/Api.lean Api2.lean Api3.lean (#check of every lemma cited in the child proofs after import GMT.Ch07.Submission; instance checks BorelSpace/SecondCountableTopology/T2Space on ↥U, ProperSpace and BorelSpace on EuclideanSpace)`
- `lake env lean /tmp/rc-core-split/Stmts.lean, Assembly.lean, ProofsBDE.lean, ProofC.lean, ProofA.lean, Combined.lean (exact child types; full proofs of the five new children; parent_check assembly; #print axioms)`
- `python3 scan of dag.json: no lean_name containing cmrc_/polar_pushforward/massOn_le_of_repr/...; uncle and selected lean_statement strings equal to dag.json; status of root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1 = accepted (candidate bc8485e); grep runtime.py _existing_lean_name_problem and prerequisite list (children + depends_on)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-rep-42d2392225/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/tmp/rc-core-split/Combined.lean`
- `/tmp/rc-core-split/Assembly.lean`
- `/tmp/rc-core-split/ProofA.lean`
- `/tmp/rc-core-split/ProofC.lean`
- `/tmp/rc-core-split/ProofsBDE.lean`
- `/tmp/rc-core-split/Api.lean`
- `/tmp/rc-core-split/Api2.lean`
- `/tmp/rc-core-split/Api3.lean`

Pinned sources:
- The snapshot contract (manifest: project b4d606db, mathlib 25730c7c) is byte-identical to the workspace GMT/Ch07/Submission.lean. CompactlyContained is at Contract.lean:127 and MultiVector at :48.
- The SimonGMT definitions used are TestFormOn, massAdmissibleOn, GeometricCurrentOn.massOn and le_massOn (Chapter06/Mass.lean:57–92).
- None of the proposed cmrc_ names occurs in the snapshot or in dag.json, so there is no collision.

All cited Mathlib facts are in the public import closure (#check), with their snapshot locations:
- integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318); withDensity_apply (Measure/WithDensity.lean:44) and withDensity_apply_eq_zero (:287);
- MeasurableEmbedding.subtype_coe and measurable_extend (MeasurableSpace/Embedding.lean:86, 105); MeasurableEmbedding.map_apply (Measure/Map.lean:271) and MeasurableEmbedding.integral_map (Bochner/Basic.lean:1093);
- Topology.IsInducing.isCompact_preimage_iff (Compactness/Compact.lean:1006);
- enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333) and integral_eq_lintegral_of_nonneg_ae (:515); lintegral_indicator_one (Lebesgue/Basic.lean:572);
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486); Integrable.of_bound (IntegrableOn.lean:171);
- Monotone.measure_iUnion (Measure/Continuity.lean:71); continuous_infEDist and mem_closure_iff_infEDist_zero (HausdorffDistance.lean:140, 161);
- ENNReal.exists_inv_nat_lt (ENNReal/Inv.lean:650) and ENNReal.le_of_forall_pos_le_add (ENNReal/Basic.lean:613); Continuous.clm_comp (BoundedLinearMaps.lean:448); HasCompactSupport.intro (Algebra/Support.lean).

Infinite-distance names. They are infEDist and continuous_infEDist in namespace Metric; the EMetric.infEdist spellings are unknown identifiers.

Reuse. The only reused external theorem is the accepted rsd_mw_exists_testForm_approx, with its identical frozen type.

Lean checks.
- The selected node's three unaccepted uncles stay with its own assembly. The runtime grants a node its children plus its depends_on, and an unaccepted declaration under another parent cannot be reused.
- Combined.lean compiles. The five new children are fully proved; four of them use only propext, Classical.choice and Quot.sound. cmrc_measure_le_massOn_of_norming is proved given R.
- parent_check derives the exact selected frozen type from the children and the uncle types.
