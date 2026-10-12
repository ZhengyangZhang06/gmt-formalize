# Parent-supplied natural-language proof

- Parent DAG node: `root.density_semicontinuity-a1.lower_density_ae-a1`
- Child DAG node: `root.density_semicontinuity-a1.lower_density_ae-a1.relcompact_exhaustion_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 (exhaustion) of the parent proof, which is the covering part of STEP 4 of the grandparent proof (root.density_semicontinuity-a1): "Cover U by countably many W ⊂⊂ U". Simon's printed proof of 3.7 leaves this step implicit: it proves the density bound for points of one W ⊂⊂ U off a μ-null set (p. 213, (4)–(5)) and ends with "the theorem is established (by (4))". This lemma passes from all such W to μ-a.e. point. Here μ of an arbitrary set is its outer measure.

1. Radii. Let x ∈ U. As U is open there is ε > 0 with B°_ε(x) ⊆ U (Metric.isOpen_iff). Put r_x := ε/2 > 0. Then B_{r_x}(x) ⊆ B°_ε(x) ⊆ U (closedBall_subset_ball, as ε/2 < ε). Choose such r_x for every x ∈ U.
2. The balls are ⊂⊂ U. Let x ∈ U and W_x := B°_{r_x}(x). W_x is open, and closure W_x ⊆ B_{r_x}(x) (closure_ball_subset_closedBall). Closed balls of ℝ^N are compact (proper space, isCompact_closedBall), so closure W_x, a closed subset of B_{r_x}(x), is compact. Finally closure W_x ⊆ B_{r_x}(x) ⊆ U by step 1. Hence IsRelCompactOpenIn W_x U.
3. Countable subcover. ℝ^N is second countable. So for the family (W_x)_{x∈U} of open sets, indexed by the subtype U, there is a countable set T ⊆ U of indices with ⋃_{x∈T} W_x = ⋃_{x∈U} W_x (TopologicalSpace.isOpen_iUnion_countable). Every y ∈ U lies in W_y because r_y > 0, so U ⊆ ⋃_{x∈U} W_x = ⋃_{x∈T} W_x.
4. Local exceptional sets. For each x ∈ U apply the hypothesis to W_x (allowed by step 2). Choose E_x ⊆ ℝ^N with μ(E_x) = 0 and P(y) for every y ∈ W_x ∖ E_x.
5. The exceptional set. Let F := {y : ¬P(y)}. Claim: F ⊆ Uᶜ ∪ ⋃_{x∈T} E_x. Let y ∈ F. If y ∉ U, then y ∈ Uᶜ. If y ∈ U, by step 3 there is x ∈ T with y ∈ W_x. If y ∉ E_x, step 4 would give P(y), contradicting y ∈ F. Hence y ∈ E_x ⊆ ⋃_{x∈T} E_x.
6. Null. μ(Uᶜ) = 0 by hypothesis. T is countable and μ(E_x) = 0 for all x ∈ T, so μ(⋃_{x∈T} E_x) = 0 by countable subadditivity of the outer measure (measure_biUnion_null_iff). Hence μ(Uᶜ ∪ ⋃_{x∈T} E_x) ≤ μ(Uᶜ) + μ(⋃_{x∈T} E_x) = 0 (measure_union_null). By step 5 and monotonicity, μ(F) = 0 (measure_mono_null).
7. μ({y : ¬P(y)}) = 0 is exactly ∀ᵐ y ∂μ, P y (ae_iff). ∎

## Key steps

1. For x ∈ U choose r_x > 0 with B_{r_x}(x) ⊆ U; W_x := B°_{r_x}(x) is open with compact closure ⊆ B_{r_x}(x) ⊆ U, so W_x ⊂⊂ U.
2. Second countability (TopologicalSpace.isOpen_iUnion_countable): a countable T ⊆ U with U ⊆ ⋃_{x∈T} W_x.
3. The hypothesis on each W_x gives a μ-null E_x with P on W_x ∖ E_x.
4. {¬P} ⊆ Uᶜ ∪ ⋃_{x∈T} E_x, which is μ-null; hence ∀ᵐ y ∂μ, P y.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean vs workspace GMT/Ch08/Contract.lean and Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'exists_cthickening_subset_open|IsCompact.cthickening' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'theorem IsCompact.exists_cthickening_subset_open|theorem closure_thickening_subset_cthickening|theorem cthickening_closure|theorem ball_subset_thickening|theorem thickening_subset_of_subset' mathlib/Mathlib`
- `rg -n 'theorem isOpen_iUnion_countable' mathlib/Mathlib`
- `rg -n 'theorem liminf_const_mul_of_ne_top|theorem liminf_add_of_right_tendsto_zero|theorem tendsto_inv_nat_nhds_zero' mathlib/Mathlib`
- `rg -n 'theorem Monotone.measure_iUnion|theorem measure_biUnion_null_iff|theorem measure_le_inter_add_sdiff' mathlib/Mathlib; rg -n 'Monotone.measure_iUnion' mathlib/Mathlib/MeasureTheory`
- `rg -n 'theorem interior_maximal|theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem tendsto_iff_dist_tendsto_zero' mathlib/Mathlib`
- `rg -n 'theorem ae_of_forall_measure_lt_top_ae_restrict|theorem ae_restrict_iUnion_iff|theorem ae_of_ae_restrict_of_ae_restrict_compl' mathlib/Mathlib (existing a.e.-exhaustion lemmas)`
- `rg -n 'IsRelCompactOpenIn' project (only the contract definition and statements)`
- `rg -n -g '*.lean' 'interior \(⋂ ℓ|interior \(⋂ q|⋂ k, ⋃ i, interior' simongmt/Poincare (no match); rg -n -g '*.lean' 'isOpen_iUnion_countable' simongmt/Poincare (no match); rg -n 'exists_cthickening_subset_open' simongmt/Poincare`
- `sed -n 330,422p book/sources/chapter-08-source.txt (printed proof of 3.7)`
- `python3 -I: gmt-compare.contract_scope replay + lean_contract.validate_lean_statement on the 4 lean_statements; dag.json lean_name collision check (161 nodes)`
- `lake env lean Scratch/T0.lean (#check of all cited Mathlib/SimonGMT lemmas); Scratch/C1.lean (4 children, full proofs); Scratch/C2.lean and C3.lean (parent assembly; siblings as exact-type axioms; #print axioms)`
- `lake build GMT.Ch08.Submission on the scratch copy with children inserted; lake env lean Scratch/Challenge0..3.lean and Scratch/Solution0..4.lean (exact comparator file format, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Closure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LogarithmicError.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-08-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-lower-density-ae-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1/parent-supplied-natural-proof.md`

Snapshot 5a882a57: project 63436ae6, Mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 2e5cd5b3…).
- Mathlib supplies every tool the four children need. In Topology/MetricSpace/Thickening.lean: IsCompact.exists_cthickening_subset_open (l.426), IsCompact.cthickening (l.283), closure_thickening_subset_cthickening (l.293), cthickening_closure (l.380), ball_subset_thickening (l.153) and thickening_subset_of_subset (l.94).
- Further tools: Topology/Bases.lean:932 isOpen_iUnion_countable; Order/Filter/ENNReal.lean:190 ENNReal.liminf_const_mul_of_ne_top, so a liminf constant-multiplication lemma does exist, contrary to the handoff's note; Topology/Instances/ENNReal/Lemmas.lean:888 liminf_add_of_right_tendsto_zero and :486 tendsto_inv_nat_nhds_zero; MeasureTheory/OuterMeasure/Basic.lean:94 measure_le_inter_add_sdiff and :107 measure_biUnion_null_iff; Measure/Continuity.lean:71 Monotone.measure_iUnion; Topology/Closure.lean:49 interior_maximal; Analysis/SpecificLimits/Basic.lean:70 tendsto_one_div_add_atTop_nhds_zero_nat.
- No existing declaration states any child. Mathlib's a.e.-exhaustion lemmas (Restrict.lean:565 ae_restrict_iUnion_iff, SFinite.lean:697 ae_of_forall_measure_lt_top_ae_restrict) are not indexed by IsRelCompactOpenIn, which appears only in the frozen contract.
- SimonGMT has no diagonal, interior-of-bad-sets or open-cover exhaustion lemma: both rg searches returned no match. Its only exists_cthickening_subset_open use is Chapter04/LogarithmicError.lean:288. Chapter08/VarifoldConvergence.lean states that it does not prove the lower-density part of 3.7.
- The four children are therefore new nodes, each provable from Mathlib alone. All four were proved in Lean in a scratch copy and pass the comparator-format checks. The parent assembly from these children and the four frozen siblings compiles with only the standard axioms plus the sibling declarations.
