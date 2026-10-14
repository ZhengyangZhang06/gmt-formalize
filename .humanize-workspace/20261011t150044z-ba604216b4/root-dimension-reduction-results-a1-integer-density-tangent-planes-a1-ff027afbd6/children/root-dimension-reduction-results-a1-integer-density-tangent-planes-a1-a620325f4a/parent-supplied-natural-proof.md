# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_affine_preimage-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the selected node's supplied proof (class_reduction), which follows Simon 7.3.3, Remark 3.4 and the proof of 3.3(2) (chapter-07.txt lines 380–398 and 512–583) and Appendix A, A.1–A.4 (chapter-A.txt lines 18–45). This child is the set-theoretic core of step 11 of that proof (A.3(2)) and of display (5) of Simon's proof of 3.3(2) (line 537, η_{x,λ}R_β(S) = R_β(η_{x,λ#}S)): (ρ, Q, s) witnesses flatness of w for the pulled-back data iff (λρ, Q, λs) witnesses flatness of g(w).
Notation in the proof: q_Q(v) := v − p_Q(v). q_Q is linear because p_Q = Q.starProjection is a linear map, so q_Q(λv) = λq_Q(v) and |q_Q(λv)| = λ|q_Q(v)| for λ > 0.
1. (The affine map.) g(a) − g(b) = λ(a − b), so |g(a) − g(b)| = λ|a − b|. g is bijective with inverse g⁻¹(z) = λ⁻¹(z − y₀). For r > 0, g maps B_r(x) onto B_{λr}(g(x)): if |z − g(x)| < λr then z = g(g⁻¹z) with |g⁻¹z − x| = λ⁻¹|z − g(x)| < r.
2. (Reduction to R.) Preimages commute with ∩, ∖, ∪ and complement. So if R(g⁻¹S, g⁻¹D) = g⁻¹(R(S, D)), then N(g⁻¹S, g⁻¹D) = ((g⁻¹S ∩ g⁻¹D) ∖ g⁻¹R(S, D)) ∪ (ℝ^P ∖ g⁻¹D) = g⁻¹(((S ∩ D) ∖ R(S, D)) ∪ (ℝ^P ∖ D)) = g⁻¹(N(S, D)). It remains to show: w ∈ R(g⁻¹S, g⁻¹D) ⟺ g(w) ∈ R(S, D).
3. (⇒) Let ρ > 0, Q with dim Q = n, and s < βρ satisfy B_ρ(w) ⊆ g⁻¹D and |q_Q(y − w)| ≤ s for all y ∈ g⁻¹S ∩ B_ρ(w). Then (λρ, Q, λs) witnesses g(w) ∈ R(S, D): (i) λρ > 0. (ii) B_{λρ}(g(w)) = g(B_ρ(w)) ⊆ D by step 1. (iii) λs < β(λρ), multiplying s < βρ by λ > 0. (iv) For z ∈ S ∩ B_{λρ}(g(w)), y := g⁻¹(z) lies in g⁻¹S ∩ B_ρ(w) (step 1) and z − g(w) = λ(y − w). By linearity |q_Q(z − g(w))| = λ|q_Q(y − w)| ≤ λs.
4. (⇐) Let ρ₀ > 0, Q with dim Q = n, and s₀ < βρ₀ satisfy B_{ρ₀}(g(w)) ⊆ D and |q_Q(z − g(w))| ≤ s₀ for z ∈ S ∩ B_{ρ₀}(g(w)). Then (ρ₀/λ, Q, s₀/λ) witnesses w ∈ R(g⁻¹S, g⁻¹D): (i) ρ₀/λ > 0. (ii) If |x − w| < ρ₀/λ then |g(x) − g(w)| = λ|x − w| < ρ₀, so g(x) ∈ D, i.e. B_{ρ₀/λ}(w) ⊆ g⁻¹D. (iii) s₀/λ < β(ρ₀/λ), dividing by λ > 0. (iv) For y ∈ g⁻¹S ∩ B_{ρ₀/λ}(w), g(y) ∈ S ∩ B_{ρ₀}(g(w)), so λ|q_Q(y − w)| = |q_Q(g(y) − g(w))| ≤ s₀, i.e. |q_Q(y − w)| ≤ s₀/λ.
5. Steps 3–4 give R(g⁻¹S, g⁻¹D) = g⁻¹(R(S, D)), and step 2 concludes. ∎

## Key steps

1. g(x) = y₀ + λx scales distances by λ and maps B_r(x) onto B_{λr}(g(x)).
2. (ρ, Q, s) witnesses flatness of w for (g⁻¹S, g⁻¹D) iff (λρ, Q, λs) witnesses flatness of g(w) for (S, D), because q_Q(g(y) − g(w)) = λq_Q(y − w).
3. Preimages commute with the Boolean operations defining N.

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
