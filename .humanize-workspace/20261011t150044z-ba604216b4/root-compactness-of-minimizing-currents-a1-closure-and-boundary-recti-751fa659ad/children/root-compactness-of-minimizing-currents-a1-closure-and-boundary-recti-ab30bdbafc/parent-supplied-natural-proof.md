# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.atoms-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.atoms-a1.carried-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 ("σ lives on Z") of the parent proof, for an arbitrary Borel set Z. In the parent, Z = {w ∈ V^⊥ : ofReal c ≤ σ({w})}, which is countable and hence Borel, and q x = x − p_V x. Uses the sibling subspace_ball (accepted idtp_tdc_subspace_ball_measure).
Notation: (D) is the hypothesis ν(A) = ∫⁻_{t∈V}σ({y : t + y ∈ A}) dHⁿ(t) for Borel A, and q(y) := y − p_V y. The map q is continuous because p_V is a continuous linear map.
1. (The set E.) Let E := q⁻¹(ℝ^P∖Z) = {y : y − p_V y ∉ Z}. As Z is Borel and q is continuous (hence Borel measurable), E is Borel.
2. (ν(E) = 0.) The hypothesis states that q(x) ∈ Z for ν-a.e. x, i.e. ν({x : q(x) ∉ Z}) = 0 (ae_iff), and this set is E.
3. (Invariance under V.) Let t ∈ V and y ∈ ℝ^P. By linearity p_V(t + y) = p_V t + p_V y, and p_V t = t because t ∈ V (Submodule.starProjection_eq_self_iff). Hence q(t + y) = (t + y) − (t + p_V y) = y − p_V y = q(y), so t + y ∈ E ⟺ y ∈ E. That is, {y : t + y ∈ E} = E for every t ∈ V.
4. (Product formula.) V is finite-dimensional, hence closed, hence Borel. Apply (D) to A = E (Borel by step 1) and use step 3: ν(E) = ∫⁻_{t∈V}σ({y : t + y ∈ E}) dHⁿ(t) = ∫⁻_{t∈V}σ(E) dHⁿ(t), since the integrands agree at every t ∈ V (setLIntegral_congr_fun). The last integral equals σ(E)·Hⁿ(V) (setLIntegral_const).
5. (Hⁿ(V) > 0.) Since 0 ∈ V, dim V = n and 1 > 0, subspace_ball (Q = V, y = 0, ρ = 1) gives Hⁿ(V ∩ B_1(0)) = ω_n·ofReal(1ⁿ) = ω_n. Here ω_n = unitBallVolume n is the Lebesgue measure of the open unit ball of ℝⁿ = Euclid n. It is positive because Lebesgue measure on Euclid n is an additive Haar measure, positive on nonempty open sets (measure_ball_pos). This includes n = 0, where Euclid 0 is a single point of measure 1. As V ∩ B_1(0) ⊆ V, Hⁿ(V) ≥ ω_n > 0.
6. (σ(E) = 0.) By steps 2 and 4, σ(E)·Hⁿ(V) = 0. A product in [0, ∞] is 0 only if a factor is 0 (mul_eq_zero), and Hⁿ(V) ≠ 0 by step 5, so σ(E) = 0.
7. (Conclusion.) We show ℝ^P∖Z ⊆ E ∪ (ℝ^P∖V^⊥). Let w ∉ Z. If w ∈ V^⊥, then p_V w = 0 (Submodule.starProjection_apply_eq_zero_iff), so q(w) = w ∉ Z and w ∈ E. Otherwise w ∈ ℝ^P∖V^⊥. By monotonicity and subadditivity of σ, σ(ℝ^P∖Z) ≤ σ(E) + σ(ℝ^P∖V^⊥) = 0 + 0 = 0, using step 6 and the hypothesis σ(ℝ^P∖V^⊥) = 0 (measure_union_null, measure_mono_null). ∎

## Key steps

1. E := {y : y − p_Vy ∉ Z} is Borel, and ν(E) = 0 by the a.e. hypothesis.
2. p_V(t + y) = t + p_Vy for t ∈ V, so E is invariant under translations by V, and the product formula gives ν(E) = σ(E)·Hⁿ(V).
3. Hⁿ(V) ≥ Hⁿ(V ∩ B_1(0)) = ω_n > 0 (subspace_ball, measure_ball_pos), hence σ(E) = 0.
4. ℝ^P∖Z ⊆ E ∪ (ℝ^P∖V^⊥) because p_Vw = 0 for w ∈ V^⊥, so σ(ℝ^P∖Z) = 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn 'cbr_ci_cp_atm\|liminf_density_le_atom\|transversal_carried\|sum_planes_of_carried\|ball_le_transversal_ball' <snapshot>/project (no match)`
- `python3 -I /tmp/atoms-decomp-scripts/check.py on fresh copies of dag.json (1538, then 1552 nodes): the four cbr_ci_cp_atm_* names are unused; idtp_tdc_subspace_ball_measure is accepted (candidate a029156d) with byte-identical lean_statement; validate_lean_statement passes on all five strings; key/name regexes; acyclic order`
- `git show a029156d2b71053da5c6d27b9abcc46011c9cfac:GMT/Ch07/Submission.lean | grep -n idtp_tdc_subspace_ball_measure (theorem Submission.idtp_tdc_subspace_ball_measure with the identical type, inside namespace GMT.Ch07 after the closed noncomputable section)`
- `grep in <snapshot>/mathlib/Mathlib for measure_inter_conull, measure_iUnion, tsum_measure_preimage_singleton, countable_meas_level_set_pos, isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts, sigmaFinite_of_locallyFinite, setLIntegral_mono', lintegral_indicator_const, lintegral_indicator_one, setLIntegral_congr_fun, setLIntegral_const, lintegral_tsum, lintegral_const_mul, tendsto_measure_biInter_gt, Filter.Tendsto.liminf_eq, liminf_le_liminf, ENNReal div_le_of_le_mul, Isometry.euclideanHausdorffMeasure_image, isometry_mul_right (to_additive isometry_add_right), measure_ball_pos, starProjection_apply_mem, sub_starProjection_mem_orthogonal, starProjection_eq_self_iff, starProjection_apply_eq_zero_iff, starProjection_orthogonal_val, inner_right_of_mem_orthogonal, norm_add_sq_eq_norm_sq_add_norm_sq_real, Measure.sum_apply, Measure.smul_apply, Measure.restrict_apply, Measure.ext, ae_iff, measure_union_null, measure_mono_null (all found)`
- `lake env lean /tmp/atoms-decomp/Probe.lean (#check of the cited Mathlib lemmas after import GMT.Ch07.Submission: all reachable)`
- `lake env lean /tmp/atoms-decomp/Stmts.lean: five child lean_statements elaborate; hypothesis-only theorem atoms_assembly (hypotheses = four new child types verbatim, conclusion = frozen parent type) compiles; #print axioms: propext, Classical.choice, Quot.sound`
- `lake env lean /tmp/atoms-decomp/Children.lean, Children2.lean, EndToEnd.lean: real proofs of the four children and of Submission.cbr_ci_cp_atomic_transversal from them compile without errors or warnings; #print axioms of all five declarations: propext, Classical.choice, Quot.sound`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose max_depth check, _existing_lean_name_problem, _accepted_checkpoint, cross-branch accepted children linked rather than re-provisioned), leaf_verification.py check_source_delta, prompts.py DECOMPOSE/DECOMPOSITION_AUDIT`
- `read this node's parent-child-handoff.json and parent-supplied-natural-proof.md; parent decomposition-v1.json (node dir ...-6c861e5511) for the subspace_ball reuse convention; accepted subspace_ball node's parent-supplied-natural-proof.json (node dir ...-661fba5cee)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Sum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-751fa659ad/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-751fa659ad/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6c861e5511/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-661fba5cee/parent-supplied-natural-proof.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/atoms-decomp/Stmts.lean`
- `/tmp/atoms-decomp/EndToEnd.lean`
- `/tmp/atoms-decomp-scripts/check.py`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). The comparator-accepted idtp_tdc_subspace_ball_measure (candidate a029156d) is reused with a byte-identical type. The four new cbr_ci_cp_atm_* names are fresh in the DAG and absent from the snapshot project. No accepted DAG lemma or Mathlib declaration already provides the transversal ball estimate, the null-set transfer through the product formula or the plane decomposition, so these are new children. Every Mathlib lemma cited in the child proofs exists in the snapshot and is reachable from import GMT.Ch07.Submission, as confirmed by compilation. All five child types elaborate and pass validate_lean_statement. In Lean, the four new child types imply the exact frozen parent type, and real proofs of all four children plus the parent assembly compile end-to-end using only propext, Classical.choice and Quot.sound.
