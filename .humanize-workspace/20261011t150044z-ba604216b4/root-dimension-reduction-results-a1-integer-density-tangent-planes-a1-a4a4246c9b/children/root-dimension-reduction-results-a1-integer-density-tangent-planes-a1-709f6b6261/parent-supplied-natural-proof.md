# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_orientation-a1.tangent_line-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof of the selected theorem idtp_fons_odc_ray_orientation (“The approximate tangent line at x is L”). It is extracted here for an arbitrary set M, an arbitrary H¹-null set N and an arbitrary nonzero direction v, with the line written as {x + s·v : s ∈ ℝ}. In the parent it is applied with x = t₀e, v = e and N = R.carrier ∖ ⋃_{e'∈F} ray(e'). Step 4a of the parent is the sibling line_integral_pos (Lean name Submission.idtp_fons_odc_ro_line_integral_pos).

Notation: H¹ := μHE[1]; L := span{v} = {a·v : a ∈ ℝ}; ℓ := {x + s·v : s ∈ ℝ}; η_r := blowUpMap x r, so η_r(y) = r⁻¹(y − x); B_δ(x) is the open ball.

1. (Three elementary facts.)
 (a) For r ≠ 0 and any S ⊆ ℝ^P: η_r(S) = {y : x + r·y ∈ S}, because y = r⁻¹(z − x) iff z = x + r·y.
 (b) For r > 0, η_r is Lipschitz with constant |r⁻¹|, since ‖η_r(a) − η_r(b)‖ = |r⁻¹|·‖a − b‖. By the Lipschitz image bound for the normalized Hausdorff measure (SimonGMT Chapter02 euclideanHausdorffMeasure_image_le_of_lipschitzOn with n = 1), H¹(η_r(N)) ≤ |r⁻¹|·H¹(N) = 0.
 (c) For ρ ≠ 0 and y ∈ ℝ^P: x + ρ·y ∈ ℓ iff y ∈ L. If x + ρ·y = x + s·v, then y = (ρ⁻¹s)·v ∈ L. If y = a·v, then x + ρ·y = x + (ρa)·v ∈ ℓ.
2. (Reduction.) finrank Q = 1 by the first component of HasApproximateTangentSpaceAt 1 M x Q, and finrank L = 1 because v ≠ 0. A subspace contained in a finite-dimensional subspace of the same dimension equals it (Submodule.eq_of_le_of_finrank_eq). So it suffices to prove Q ≤ L. Suppose, for a contradiction, that Q ⊄ L.
3. (A unit vector u ∈ Q ∖ L.) Choose w ∈ Q with w ∉ L; w ≠ 0 because 0 ∈ L. Put u := ‖w‖⁻¹·w. Then u ∈ Q, ‖u‖ = 1, and u ∉ L (otherwise w = ‖w‖·u ∈ L). Since u ≠ 0, span{u} is a 1-dimensional subspace of Q, and finrank Q = 1, so span{u} = Q.
4. (The bump function.) Let d := dist(u, L) = inf_{a∈ℝ} ‖u − a·v‖. L is finite-dimensional, hence closed, and nonempty, and u ∉ L, so d > 0. Define f(y) := max(0, d/2 − ‖y − u‖). f is continuous and f ≥ 0. Also f(y) = 0 whenever ‖y − u‖ > d/2, so f vanishes outside the compact closed ball B̄(u, d/2) and has compact support. Thus f ∈ C_c(ℝ^P, ℝ), and f(u) = max(0, d/2) = d/2 > 0.
5. (The limit is positive.) Apply the sibling line_integral_pos (Submission.idtp_fons_odc_ro_line_integral_pos) to u (‖u‖ = 1) and f (continuous, compactly supported, f ≥ 0, f(u) > 0). It gives ∫_{span{u}} f dH¹ > 0, which by step 3 says ∫_Q f dH¹ > 0.
6. (The blown-up integrals vanish.) Let 0 < ρ < δ/(1 + d); the bound is positive since δ > 0 and d > 0, and ρ(1 + d) < δ.
 Claim: every y ∈ η_ρ(M) with f(y) ≠ 0 lies in η_ρ(N). By 1(a), z := x + ρ·y ∈ M. As f(y) ≠ 0, ‖y − u‖ < d/2 (if ‖y − u‖ ≥ d/2 then d/2 − ‖y − u‖ ≤ 0 and f(y) = 0). Hence ‖y‖ ≤ ‖u‖ + ‖y − u‖ < 1 + d/2 < 1 + d, and ‖z − x‖ = ρ·‖y‖ < ρ(1 + d) < δ. So z ∈ M ∩ B_δ(x) ⊆ ℓ ∪ N. If z ∈ ℓ, then y ∈ L by 1(c), whence d = dist(u, L) ≤ ‖u − y‖ < d/2, impossible because d > 0. Therefore z = x + ρ·y ∈ N, i.e. y ∈ η_ρ(N) by 1(a).
 By 1(b), η_ρ(N) is H¹-null, so f(y) = 0 for H¹-almost every y ∈ η_ρ(M). Hence ∫_{η_ρ(M)} f dH¹ = 0, because an integrand vanishing almost everywhere on the domain of integration has integral 0 (Mathlib setIntegral_eq_zero_of_ae_eq_zero; this needs no measurability of η_ρ(M), M or N).
7. (Contradiction.) By step 6, the function r ↦ ∫_{η_r(M)} f dH¹ is 0 on (0, δ/(1 + d)), which belongs to the right-neighbourhood filter 𝓝[>] 0; so it tends to 0 as r ↓ 0. By the second component of HasApproximateTangentSpaceAt 1 M x Q, applied to f ∈ C_c(ℝ^P, ℝ), the same function tends to ∫_Q f dH¹ as r ↓ 0. Limits in ℝ along the non-trivial filter 𝓝[>] 0 are unique, so ∫_Q f dH¹ = 0, contradicting step 5. Hence Q ≤ L, and by step 2, Q = L = span{v}. ∎

## Key steps

1. η_{x,r}(S) = {y : x + r·y ∈ S} for r ≠ 0; η_{x,r} is |r⁻¹|-Lipschitz, so η_{x,r}(N) is H¹-null; x + ρ·y lies on x + ℝv iff y ∈ ℝv.
2. Since finrank Q = 1 = finrank ℝv, it suffices to rule out Q ⊄ ℝv. In that case pick a unit u ∈ Q ∖ ℝv; then Q = ℝu and d = dist(u, ℝv) > 0.
3. For f(y) = max(0, d/2 − ‖y − u‖) ∈ C_c, line_integral_pos gives ∫_Q f dH¹ > 0.
4. For 0 < ρ < δ/(1+d), every y ∈ η_{x,ρ}(M) with f(y) ≠ 0 has x + ρ·y ∈ B_δ(x) and off the line, hence in N. So ∫_{η_{x,ρ}(M)} f dH¹ = 0.
5. Uniqueness of limits as r ↓ 0 forces ∫_Q f dH¹ = 0, a contradiction; hence Q = ℝv.

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
