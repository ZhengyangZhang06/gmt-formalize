# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.antipodal-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.antipodal-a1.ray_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 8 ("By ray_current_rep, C has a representation R_C with R_C.measure(A) = Σ_{e∈F} |m(e)|·ℒ¹({t > 0 : te ∈ A}); by im_mass_measure (a) (with U = ℝ^P), M_W(C) = R_C.measure(W) ≥ Σ_{e∈F} |m(e)|·ℒ¹((0, 2)) = 2Σ_{e∈F}|m(e)|, since |te| = t < 2 for 0 < t < 2"); here the representation R is given and the same computation is carried out exactly for an arbitrary radius r.
1. (Mass equals representing measure.) ℝ^P is open and R represents C, so im_mass_measure (a) (dimred_im_mass_measure with U = ℝ^P, T = C) gives C.massOn(W) = R.measure(W) for every open W ⊆ ℝ^P. The open ball B_r(0) is open (also when r ≤ 0, where it is empty), hence C.massOn(B_r(0)) = R.measure(B_r(0)).
2. (Formula.) B_r(0) is Borel (measurableSet_ball), so by hypothesis R.measure(B_r(0)) = Σ_{e∈F} ofReal|m(e)| · ℒ¹((0,∞) ∩ {t : te ∈ B_r(0)}).
3. (The parameter set.) Let e ∈ F, so |e| = 1, and t ∈ ℝ. Then te ∈ B_r(0) ⟺ |te| < r ⟺ |t|·|e| < r ⟺ |t| < r. If t > 0 then |t| = t, so t ∈ (0,∞) ∩ {t : te ∈ B_r(0)} ⟺ 0 < t < r. Hence (0,∞) ∩ {t : te ∈ B_r(0)} = (0, r) (the empty set when r ≤ 0).
4. (Length.) ℒ¹((0, r)) = ofReal(r − 0) = ofReal(r) (Real.volume_Ioo; this equals 0 when r ≤ 0).
5. (Summation.) By steps 2–4, R.measure(B_r(0)) = Σ_{e∈F} ofReal|m(e)| · ofReal(r) = (Σ_{e∈F} ofReal|m(e)|) · ofReal(r) (Finset.sum_mul) = ofReal(Σ_{e∈F}|m(e)|) · ofReal(r) (ENNReal.ofReal_sum_of_nonneg, each |m(e)| ≥ 0) = ofReal((Σ_{e∈F}|m(e)|)·r) (ENNReal.ofReal_mul, valid because Σ_{e∈F}|m(e)| ≥ 0). With step 1, C.massOn(B_r(0)) = ofReal((Σ_{e∈F}|m(e)|)·r). ∎

## Key steps

1. im_mass_measure (a): C.massOn(B_r(0)) = R.measure(B_r(0)).
2. For a unit vector e, (0,∞) ∩ {t : te ∈ B_r(0)} = (0, r).
3. ℒ¹((0, r)) = ofReal r, and Σ_{e∈F} ofReal|m(e)|·ofReal r = ofReal((Σ_{e∈F}|m(e)|)·r).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 -I scans of dag.json: nodes with id prefix root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1 (status, lean_name, lean_statement, depends_on); accepted lean_statements containing exteriorDerivative / HasDerivAt / 'support ⊆' / '= 0) →'; lean_name lookups for 'antipodal', cbr_cc_seg_zero_form_ftc, rsd_cmr_support_subset_of_vanish, dimred_im_mass_measure and idtp_fons_odc_antipodal_{chord,ray_split,ray_mass,competitor}`
- `python3 -I reads of parent-child-handoff.json / isolated-comparator-result.json / accepted-candidate.json for nodes root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a0328cc6d3, root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81, root-dimension-reduction-results-a1-im-mass-measure-a1, and nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c6dd52ac2a/parent-child-handoff.json`
- `git show 75f499358:GMT/Ch07/Submission.lean (speculative draft: Submission.odc_antipodal lines 2435–2577 and odc_antipodal_* helpers lines 2159–2434)`
- `grep -n '_decompose|_existing_lean_name_problem|_accepted_checkpoint|_solve_children|_install_parent_supplied_child_handoff' /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py; sed -n 60,110p leaf_verification.py (check_source_delta); grep -n 'def ensure' store.py; git show 242e219d7:.humanize-workspace/.../controller-contract.json (max_depth, max_children)`
- `rg -n 'theorem nullSingletonClass_hausdorff|theorem euclideanHausdorffMeasure_def|theorem parallelogram_law_with_norm|theorem setIntegral_union |theorem Ioc_union_Ioi_eq_Ioi|theorem integral_Ioc_eq_integral_Ioo |theorem closure_Ioo |theorem closure_Ioi |theorem volume_Ioo|theorem ofReal_sum_of_nonneg|theorem setIntegral_eq_zero_of_forall_eq_zero|theorem smul_mem_iff|theorem mem_span_singleton ' <snapshot>/mathlib/Mathlib`
- `rg -n 'isClosedEmbedding|closure_image_eq|comp_isClosedEmbedding|euclideanHausdorffMeasure_def' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean Topology/Maps/Basic.lean Topology/Algebra/Support.lean Geometry/Euclidean/Volume/Measure.lean; grep -n integrable_of_hasCompactSupport <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `rg -n 'boundary_apply|isOpen_zeroRegion|def exteriorDerivativeTestOn' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06; rg -n 'idtp_fons_odc_antipodal_|cbr_cc_seg_zero_form_ftc|rsd_cmr_support_subset_of_vanish' <snapshot>/project .lake/packages/simongmt/Poincare (no match)`
- `grep -n '1-dimensional minimizing cone|necessarily has the form|S0 D m\[\[' book/chapter-07.txt`
- `lake env lean /tmp/antipodal_decomp/check/T1.lean (child and sibling types), T2.lean (selected type from child stubs, #print axioms), T3.lean (chord, ray_split), T4.lean (ray_mass), T5.lean (competitor), T6.lean (all four new children proven + selected type assembled, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c6dd52ac2a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a0328cc6d3/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a0328cc6d3/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a0328cc6d3/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/isolated-comparator-result.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Interval/Set/LinearOrder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/DenselyOrdered.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/antipodal_decomp/draft.lean`
- `/tmp/antipodal_decomp/check/T1.lean`
- `/tmp/antipodal_decomp/check/T2.lean`
- `/tmp/antipodal_decomp/check/T3.lean`
- `/tmp/antipodal_decomp/check/T4.lean`
- `/tmp/antipodal_decomp/check/T5.lean`
- `/tmp/antipodal_decomp/check/T6.lean`

Pins match: the snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to the workspace HEAD and .lake/packages/mathlib HEAD. The snapshot Contract.lean is byte-identical to GMT/Ch07/Contract.lean and Submission.lean. The selected node has depth 5, with max_depth 6 and max_children 12 (controller-contract.json), so its children will be machine leaves (one theorem each, no helpers; leaf_verification.check_source_delta). Reuse: cbr_cc_seg_zero_form_ftc (accepted, candidate 9e35a3d5), rsd_cmr_support_subset_of_vanish (accepted, 02c6122c) and dimred_im_mass_measure (accepted, 01ae2c59) all passed the isolated comparator. Their lean_statements are byte-identical to dag.json. runtime._existing_lean_name_problem and _accepted_checkpoint permit this reuse, and _install_parent_supplied_child_handoff skips accepted children. The siblings idtp_fons_odc_polygonal_current and idtp_fons_odc_ray_current_rep are still 'decomposing' (unaccepted, reserved under the grandparent). They therefore enter only as an explicit hypothesis of competitor, or via the representation passed to ray_mass. The four new names idtp_fons_odc_antipodal_{chord,ray_split,ray_mass,competitor} occur nowhere in dag.json, the node directories, the snapshot project or SimonGMT (no match). The library facts used by the child proofs exist in the snapshot: Measure.nullSingletonClass_hausdorff (MeasureTheory/Measure/Hausdorff.lean:615), Measure.euclideanHausdorffMeasure_def (Geometry/Euclidean/Volume/Measure.lean:74), Isometry.isClosedEmbedding (Topology/MetricSpace/Isometry.lean:209), IsClosedEmbedding.closure_image_eq (Topology/Maps/Basic.lean:880), HasCompactSupport.comp_isClosedEmbedding (Topology/Algebra/Support.lean:290), Continuous.integrable_of_hasCompactSupport (MeasureTheory/Function/LocallyIntegrable.lean:622), setIntegral_union / setIntegral_eq_zero_of_forall_eq_zero / integral_Ioc_eq_integral_Ioo (MeasureTheory/Integral/Bochner/Set.lean:87, :357, :709), Ioc_union_Ioi_eq_Ioi (Order/Interval/Set/LinearOrder.lean:190), closure_Ioi / closure_Ioo (Topology/Order/DenselyOrdered.lean:39, :74), Real.volume_Ioo (MeasureTheory/Measure/Lebesgue/Basic.lean:96), ENNReal.ofReal_sum_of_nonneg (Basic/ENNReal/BigOperators.lean:122), Submodule.smul_mem_iff (Algebra/Module/Submodule/Basic.lean:172), Submodule.mem_span_singleton (LinearAlgebra/Span/Defs.lean:447) and parallelogram_law_with_norm (Analysis/InnerProductSpace/Basic.lean:496). SimonGMT supplies GeometricCurrentOn.boundary_apply (Chapter06/Currents.lean:333), exteriorDerivativeTestOn (:193) and GeometricCurrentOn.isOpen_zeroRegion (Chapter06/CurrentLocalEquality.lean:119). The draft 75f499358 (Submission.odc_antipodal and its helpers) was adapted to the frozen sibling interfaces. The book source is chapter-07.txt lines 563–566 (S0 = m[[ℓ]]). Lean checks: T1 shows that all child and sibling types elaborate. T2 proves the selected frozen type from the child stubs. T3–T5 prove chord, ray_split, ray_mass and competitor as single theorems. T6 checks everything together: the selected theorem's axioms are propext, Classical.choice and Quot.sound, plus sorryAx only from the stubbed sibling and reused declarations.
