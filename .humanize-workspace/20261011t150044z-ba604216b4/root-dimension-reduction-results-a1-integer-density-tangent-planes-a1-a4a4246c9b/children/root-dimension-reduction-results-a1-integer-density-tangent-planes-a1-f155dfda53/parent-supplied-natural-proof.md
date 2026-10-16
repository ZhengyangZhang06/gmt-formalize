# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1.ray_isolation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the parent proof of the selected theorem idtp_fons_odc_ray_orientation, i.e. the isolation of ray(e) at x = t₀e and the geometric half of the local inclusion M ∩ B_δ(x) ⊆ (x + L) ∪ N. Here it is extracted for an arbitrary finite set F of unit vectors and an arbitrary unit vector e; membership e ∈ F is not needed.

Notation: x := t₀e; ray(w) := {t·w : t > 0}; for w ∈ ℝ^P, γ_w(s) := s·w (s ∈ ℝ) and C(w) := γ_w([0, ∞)) = {s·w : s ≥ 0}; B_δ(x) is the open ball of radius δ about x.

1. (Closed rays are closed.) Let e' ∈ F. For s, s' ∈ ℝ, ‖γ_{e'}(s) − γ_{e'}(s')‖ = ‖(s − s')·e'‖ = |s − s'|·‖e'‖ = |s − s'|, so γ_{e'} : ℝ → ℝ^P is an isometry. An isometry defined on the complete space ℝ is a closed embedding (Mathlib Isometry.isClosedEmbedding), so it maps the closed set [0, ∞) onto a closed set. Hence C(e') is closed.
2. (The closed rays of the other directions.) Let K := ⋃_{e' ∈ F, e' ≠ e} C(e'). Since F is finite, K is a finite union of closed sets, hence closed.
3. (x ∉ K.) Suppose x ∈ K, i.e. t₀·e = s·e' for some e' ∈ F with e' ≠ e and some s ≥ 0. Take norms, using t₀ > 0, s ≥ 0 and ‖e‖ = ‖e'‖ = 1: t₀ = |t₀|·‖e‖ = ‖t₀·e‖ = ‖s·e'‖ = |s|·‖e'‖ = s. Hence t₀·e = t₀·e'. Multiplying by t₀⁻¹ (t₀ ≠ 0) gives e = e', contradicting e' ≠ e. So x ∉ K.
4. (Choice of δ.) The complement ℝ^P ∖ K is open (step 2) and contains x (step 3), so there is δ > 0 with B_δ(x) ⊆ ℝ^P ∖ K.
5. (Conclusion.) Let y ∈ B_δ(x) ∩ ⋃_{e'∈F} ray(e'). Then y = t·e'' for some e'' ∈ F and some t > 0. If e'' ≠ e, then, since t ≥ 0, y ∈ C(e'') ⊆ K, contradicting y ∈ B_δ(x) ⊆ ℝ^P ∖ K. Hence e'' = e and y = t·e with t > 0, i.e. y ∈ ray(e). Thus this δ > 0 satisfies B_δ(t₀e) ∩ ⋃_{e'∈F} ray(e') ⊆ ray(e). ∎

## Key steps

1. For each e' ∈ F, s ↦ s·e' is an isometry of ℝ into ℝ^P, so the closed ray {s·e' : s ≥ 0} is closed, and K := ⋃_{e'∈F, e'≠e} {s·e' : s ≥ 0} is closed.
2. t₀e ∉ K: t₀·e = s·e' with s ≥ 0 forces s = t₀ by comparing norms, and then e' = e.
3. Openness of ℝ^P ∖ K gives δ > 0 with B_δ(t₀e) ∩ K = ∅.
4. A point t·e'' (t > 0, e'' ∈ F) of that ball cannot have e'' ≠ e, so it lies on ray(e).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; python3 -I read of <snapshot>/project/lake-manifest.json package revs; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean`
- `python3 -I reads of nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a4a4246c9b/parent-child-handoff.json, parent-supplied-plan.md, parent-supplied-natural-proof.json`
- `python3 -I scans of dag.json: selected node record (depth 5, depends_on line_param-a1, children []); the 12 children of ...one_dim_cones-a1 with status/lean_name/lean_statement; regex scans of every lean_name/lean_statement for 'IsUnitOrientationOf', 'unitOrientation|orient', 'eq_or_eq_neg', 'HasApproximateTangentSpaceAt 1 .*Submodule\.span ℝ \{', 'IsUnitOrientationOf \S+ \(Submodule\.span ℝ \{', '0 < ∫ y in \(Submodule\.span', 'ball \(t₀ • e\)', "⋃ e' ∈ F, \(fun t : ℝ => t • e'\)"; grep -c idtp_fons_odc_ro_ / idtp_fons_odc_ro_line_orientation / idtp_fons_odc_ro_line_integral_pos / idtp_fons_odc_ro_tangent_line / idtp_fons_odc_ro_ray_isolation dag.json (all 0)`
- `git show bdf34f91edfa2642928ed59a139dd914ab9326d5:GMT/Ch07/Submission.lean | grep -n '^theorem' (proof base = contract only); git show 75f499358:GMT/Ch07/Submission.lean | sed -n 1060,1210p; sed -n 1395,1475p; sed -n 1960,2010p (odc_tangent_blowUp_image_eq, odc_tangent_blowUp_null, odc_tangent_mem_range_iff, odc_approxTangent_eq_of_subset, odc_orient_on_ray, odc_rays_orient)`
- `grep -n 'depth|max_depth|_machine_leaf|_leaf_author_task|_existing_lean_name_problem|_inherited_prerequisites|max_nodes|awaiting accepted inherited' /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py; sed -n 90,110p leaf_verification.py; sed -n 1,50p inherited.py; python3 -I read of max_nodes/max_depth/max_children/leaf_lean_agent_review in .humanize/swarm-configs/*.json`
- `rg -n 'theorem Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero|theorem setIntegral_eq_zero_of_ae_eq_zero|theorem map_smul_univ|lemma apply_apply|theorem eq_of_le_of_finrank_eq|theorem finrank_span_singleton|notMem_iff_infDist_pos|theorem infDist_le_dist_of_mem|theorem comp_isClosedEmbedding|theorem _root_.MeasurableEmbedding.integral_map|theorem mem_span_singleton|theorem isClosedEmbedding' <snapshot>/mathlib/Mathlib`
- `sed -n 50,140p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 205,235p .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean; sed -n 25,45p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean; rg -n 'def IsUnitOrientationOf|structure IMRep|orients :|abbrev MultiVector' <snapshot>/project/GMT/Ch07/Contract.lean`
- `grep -n 'approximate tangent space' book/chapter-03.txt; sed -n 70,108p book/chapter-03.txt`
- `lake env lean /tmp/ro_split_check/Statements.lean; lake env lean /tmp/ro_split_check/ChildA.lean; lake env lean /tmp/ro_split_check/ChildBCD.lean (#count_heartbeats in); lake env lean /tmp/ro_split_check/All.lean; lake env lean /tmp/ro_split_check/AllAx.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a4a4246c9b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a4a4246c9b/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a4a4246c9b/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/000ebfcde04a4ddbbf0d2b498fa7b64f.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `git object 75f499358:GMT/Ch07/Submission.lean`
- `/tmp/ro_split_check/Statements.lean`
- `/tmp/ro_split_check/ChildA.lean`
- `/tmp/ro_split_check/ChildBCD.lean`
- `/tmp/ro_split_check/All.lean`
- `/tmp/ro_split_check/AllAx.lean`

Pins and contract: the snapshot manifest records project b4d606db and Mathlib 25730c7c, matching the workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest pins SimonGMT 2b366308, matching .lake/packages/simongmt. The snapshot Contract.lean is byte-identical to the workspace one. The proof base bdf34f91 contains only the contract.

Runtime: the selected node is at depth 5 < max_depth 6. Swarm configs set max_depth 6, max_children 12, max_nodes 5000 and leaf_lean_agent_review false, and the DAG has 2102 nodes. Its children will therefore be machine leaves, each limited to one helper-free theorem with no set_option. runtime.py _inherited_prerequisites, with inherited.py cited_inherited, waits for and merges an ancestor dependency whose exact Lean name a child's proof cites. line_integral_pos therefore cites Submission.idtp_fons_odc_line_hausdorff.

Reuse: no accepted or active DAG statement matches any child. The closest are:
- cbr_cc_seg_open_segment_tangent, the converse statement that a segment has its line as approximate tangent space;
- rsdic_unitOrientation_eq_or_eq_neg, dgcr_unitOrientation_eq_or_neg and dor_lmbsf_io_orientation_frame_sign, which are general-n sign lemmas from other branches and are not in the proof base. Reusing one would bring in a heavier general proof than the n = 1 fact needed.
No idtp_fons_odc_ro_ name occurs in dag.json. The speculative draft 75f499358 uses the same cut points: odc_approxTangent_eq_of_subset for the tangent line, and odc_orient_on_ray for isolation plus assembly.

Library facts used, with snapshot locations:
- Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero, MeasureTheory/Integral/Bochner/Set.lean:1031
- setIntegral_eq_zero_of_ae_eq_zero, same file :341
- MeasurableEmbedding.integral_map, MeasureTheory/Integral/Bochner/Basic.lean:1093
- ContinuousAlternatingMap.map_smul_univ, Topology/Algebra/Module/Alternating/Basic.lean:518
- ContinuousAlternatingMap.apply_apply, Topology/Algebra/Module/Alternating/Topology.lean:302
- Submodule.eq_of_le_of_finrank_eq and finrank_span_singleton, LinearAlgebra/FiniteDimensional/Basic.lean:257 and :535
- IsClosed.notMem_iff_infDist_pos and infDist_le_dist_of_mem, Topology/MetricSpace/HausdorffDistance.lean:584 and :500
- HasCompactSupport.comp_isClosedEmbedding, Topology/Algebra/Support.lean:290
- Isometry.isClosedEmbedding, Topology/MetricSpace/Isometry.lean:209
- Submodule.mem_span_singleton, LinearAlgebra/Span/Defs.lean:447
- the μHE notation, Geometry/Euclidean/Volume/Measure.lean:72
- SimonGMT blowUpMap and HasApproximateTangentSpaceAt, Chapter03/Rectifiable.lean:96 and :102
- SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn, Chapter02/Lipschitz.lean:216
- Simon Ch. 3 Definition 1.4 and Remark 1.5(1), book/chapter-03.txt:77–90.

Lean results:
- All four child types elaborate verbatim in the contract context.
- Each child has a complete single-theorem proof with no helpers. count_heartbeats gives 1707, 2377 and 12451 out of 200000 for ray_isolation, line_integral_pos and tangent_line.
- The selected theorem, with its byte-identical frozen type, compiles from the four child types plus line_param's frozen type.
- #print axioms gives propext, Classical.choice and Quot.sound, plus only the line_param stub.
