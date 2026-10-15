# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_closed-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the selected node's supplied proof (class_reduction), which follows Simon 7.3.3, Remark 3.4 and the proof of 3.3(2) (chapter-07.txt lines 380–398 and 512–583) and Appendix A, A.1–A.4 (chapter-A.txt lines 18–45). This child is step 9 of that proof (A.3, closedness): R is relatively open in S, so the non-flat set is closed. Simon's flatness quantity h(spt S, L, ρ, x) = sup_{y ∈ spt S ∩ B_ρ(x)} |q(y − x)| is the one of display (3) in the proof of 3.3(2), lines 524–530.
Notation in the proof: q_Q(v) := v − p_Q(v). q_Q is linear because p_Q is. |q_Q(v)| ≤ |v|: q_Q(v) ∈ Q^⊥ and p_Q(v) ∈ Q, so |v|² = |p_Q v|² + |q_Q v|² by Pythagoras. In Mathlib, v − Q.starProjection v = Qᗮ.starProjection v (Submodule.starProjection_orthogonal_val), and ‖Qᗮ.starProjection v‖ ≤ ‖v‖ (Submodule.norm_starProjection_apply_le). q_Q is also continuous, being a continuous linear map.
1. Let N := N(S, D) and R := R(S, D). We show that ℝ^P ∖ N is open. Let w ∉ N. Then w ∈ D, because w ∉ ℝ^P ∖ D, and w ∉ (S ∩ D) ∖ R. Hence w ∉ S or w ∈ R.
2. (Case w ∉ S.) V := D ∩ (ℝ^P ∖ S) is open (D open, S closed) and contains w. Every w' ∈ V lies in D and not in S, so w' ∉ (S ∩ D) ∖ R and w' ∉ ℝ^P ∖ D, i.e. w' ∉ N. So V is a neighbourhood of w disjoint from N.
3. (Case w ∈ S.) Then w ∈ R. Take witnesses ρ > 0 with B_ρ(w) ⊆ D, Q with dim Q = n, and s < βρ with |q_Q(y − w)| ≤ s for all y ∈ S ∩ B_ρ(w). Taking y = w ∈ S ∩ B_ρ(w) gives s ≥ |q_Q(0)| = 0. Put r := (βρ − s)/(1 + β) > 0 (βρ − s > 0, 1 + β > 0).
4. Let w' ∈ B_r(w) and t := |w' − w|, so 0 ≤ t < r. Then (1 + β)t < βρ − s ≤ βρ, hence t < βρ/(1 + β) < ρ (β > 0). Thus w' ∈ B_ρ(w) ⊆ D and w' ∉ ℝ^P ∖ D.
5. If w' ∉ S, then w' ∉ (S ∩ D) ∖ R. If w' ∈ S, then (ρ − t, Q, s + t) witnesses w' ∈ R: (i) ρ − t > 0 by step 4. (ii) B_{ρ−t}(w') ⊆ B_ρ(w) ⊆ D, since |z − w| ≤ |z − w'| + t < ρ. (iii) s + t < β(ρ − t) ⟺ (1 + β)t < βρ − s, which holds. (iv) For y ∈ S ∩ B_{ρ−t}(w'), y ∈ S ∩ B_ρ(w) by (ii), and by linearity |q_Q(y − w')| = |q_Q(y − w) + q_Q(w − w')| ≤ |q_Q(y − w)| + |w − w'| ≤ s + t. Hence w' ∈ R and again w' ∉ (S ∩ D) ∖ R.
6. By steps 4–5, B_r(w) ∩ N = ∅. Together with step 2, every point outside N has a neighbourhood disjoint from N. So ℝ^P ∖ N is open (Metric.isOpen_iff / isOpen_iff_forall_mem_open) and N is closed. ∎

## Key steps

1. A point outside N lies in D and is either outside the closed set S or β-flat.
2. Outside S: the open set D ∖ S misses N.
3. β-flat with witness (ρ, Q, s), s ≥ 0: for |w' − w| = t < (βρ − s)/(1 + β), (ρ − t, Q, s + t) witnesses flatness of w' since |q_Q| ≤ |·| and q_Q is linear.

## Reference use

### local-project

Queries:
- `python3 -I json.load of nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ff027afbd6/parent-child-handoff.json (subproblem, audit, resolved_dependencies)`
- `python3 -I scan of dag.json: selected node, parent root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1 and its children, root.abstract_dimension_reduction-a1 (status, candidate_commit, lean_statement)`
- `grep -iE 'measurab|semicont|lsc|rescal|support.*(closed|limit|semicont)|spt|vague|limsup|flat|bump|urysohn' over accepted DAG lean_name | title list`
- `grep -c 'idtp_fons_cr_' dag.json; grep -rl 'idtp_fons_cr_' nodes; grep -l 'idtp_fons_cr_' .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `grep -rn 'theorem HasBasis.limsup_eq_iInf_iSup|def support|theorem LowerSemicontinuous.measurable|theorem lowerSemicontinuous_iSup|theorem lowerSemicontinuous_biSup' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `sed -n 1,150p local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero)`
- `sed -n 1,140p local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean (HasBasis.mem_measureSupport, isClosed_support)`
- `sed -n 380,600p book/chapter-07.txt; sed -n 1,80p book/chapter-A.txt`
- `lake env lean /tmp/cr_split/check/Probe.lean; lake env lean /tmp/cr_split/check/Types.lean; lake env lean /tmp/cr_split/check/TypesPP.lean; lake env lean /tmp/cr_split/check/Assembly.lean; lake env lean /tmp/cr_split/check/Full.lean`
- `python3 byte comparison of the frozen abstract_dimension_reduction type with 'theorem Submission.abstract_dimension_reduction' in .swarm-worktrees/388d25a471022ad57489/gmt-ch07/GMT/Ch07/Submission.lean (HEAD 9ab8e5d6)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ff027afbd6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ff027afbd6/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ff027afbd6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/388d25a471022ad57489/gmt-ch07/GMT/Ch07/Submission.lean`
- `/tmp/cr_split/check/Types.lean`
- `/tmp/cr_split/check/TypesPP.lean`
- `/tmp/cr_split/check/Assembly.lean`
- `/tmp/cr_split/check/Full.lean`

Pins match: the snapshot manifest records project b4d606d (= workspace HEAD) and Mathlib 25730c7c; simongmt is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The only declaration reused is the registered dependency abstract_dimension_reduction (root.abstract_dimension_reduction-a1, accepted). Its frozen type is byte-identical to Submission.abstract_dimension_reduction in the accepted worktree (9ab8e5d6). No accepted DAG declaration has the type of any proposed child; there are related but different facts, e.g. dtc_density_usc, dimred_mono_density_usc_of_monotone, cmcdt_dil_support_eq. Hence all children get fresh names. The prefix idtp_fons_cr_ has zero occurrences in dag.json, nodes/ and every .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean. Library facts the children use, found in the snapshot Mathlib:
- euclideanHausdorffMeasure_def (μHE[d] = addHaarScalarFactor(volume_{ℝ^d}, μH[d])•μH[d]) and addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Geometry/Euclidean/Volume/Measure.lean);
- Filter.HasBasis.limsup_eq_iInf_iSup (Order/LiminfLimsup.lean:308);
- Measure.support with HasBasis.mem_measureSupport and isClosed_support (MeasureTheory/Measure/Support.lean);
- LowerSemicontinuous.measurable (BorelSpace/Order.lean:686);
- lowerSemicontinuous_iSup/biSup (Topology/Semicontinuity/Basic.lean:688–692).
There is no library lemma for lower semicontinuity of x ↦ μ(B_ρ(x)); density_measurable proves it. The cited book passages are Simon 7.3.3 proof of 3.3(2) (chapter-07.txt lines 512–583, with R_β at 524–530 and the A.3(3) claim at 539–541), Remark 3.4 (380–398) and Appendix A.1–A.4 (chapter-A.txt lines 18–45). Lean results:
- all 7 child types elaborate (Types.lean, exit 0), and TypesPP confirms their parse;
- the frozen parent type is kernel-checked from the child types plus the frozen dependency type taken as axioms (Assembly.lean, exit 0);
- the parent is also kernel-checked from scratch Lean proofs of all 7 children, each using only propext, Classical.choice and Quot.sound (Full.lean, exit 0, 0 errors).
