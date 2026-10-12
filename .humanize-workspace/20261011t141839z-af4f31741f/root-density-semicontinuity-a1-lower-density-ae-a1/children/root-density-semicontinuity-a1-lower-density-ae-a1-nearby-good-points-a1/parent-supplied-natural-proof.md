# Parent-supplied natural-language proof

- Parent DAG node: `root.density_semicontinuity-a1.lower_density_ae-a1`
- Child DAG node: `root.density_semicontinuity-a1.lower_density_ae-a1.nearby_good_points-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 8, printed proof of 3.7, p. 212, the sentences before display (4): "consider the possibility that there is a point x ∈ W such that x ∈ W ∖ interior ⋂_{q≥i} B_{q,j} for each i. Then we could select, for each i, y_i ∈ W ∖ ⋂_{q≥i} B_{q,j} with |y_i − x| < 1/i. Thus there are sequences y_i → x and q_i → ∞ such that y_i ∉ B_{q_i,j}." This is the "Choice of y_i, q_i" in step 1f of the parent proof, with Bad_ℓ = Bad_{ℓ,k} for the fixed k. The radius is 1/(i+1) because i starts at 0.

1. Fix i ∈ ℕ and let G_i := W ∩ B°_{1/(i+1)}(x). G_i is open, as the intersection of the open set W and an open ball. And x ∈ G_i, because x ∈ W and dist(x, x) = 0 < 1/(i+1).
2. Claim: there are ℓ ∈ ℕ and z ∈ ℝ^N with i ≤ ℓ, z ∈ W, dist(z, x) < 1/(i+1) and z ∉ Bad_ℓ. Suppose not. Then every z ∈ G_i satisfies z ∈ Bad_ℓ for all ℓ ≥ i, i.e. G_i ⊆ ⋂_{ℓ≥i} Bad_ℓ. Since G_i is open, G_i ⊆ interior(⋂_{ℓ≥i} Bad_ℓ) (interior_maximal). So x ∈ interior(⋂_{ℓ≥i} Bad_ℓ) by step 1, contradicting the hypothesis for this i.
3. By step 2 and the axiom of choice there are q : ℕ → ℕ and y : ℕ → ℝ^N such that, for every i: i ≤ q_i, y_i ∈ W, dist(y_i, x) < 1/(i+1) and y_i ∉ Bad_{q_i}.
4. q_i → ∞: q_i ≥ i for every i, and i → ∞ (tendsto_atTop_mono with the identity).
5. y_i → x: 0 ≤ dist(y_i, x) ≤ 1/(i+1), and 1/(i+1) → 0 (tendsto_one_div_add_atTop_nhds_zero_nat). So dist(y_i, x) → 0 by the squeeze theorem (squeeze_zero), which means y_i → x (tendsto_iff_dist_tendsto_zero).
6. Steps 3–5 give q and y with all the required properties. ∎

## Key steps

1. G_i := W ∩ B°_{1/(i+1)}(x) is an open neighbourhood of x.
2. If G_i ⊆ ⋂_{ℓ≥i} Bad_ℓ then x ∈ interior ⋂_{ℓ≥i} Bad_ℓ (interior_maximal), a contradiction; so there are y_i ∈ G_i and q_i ≥ i with y_i ∉ Bad_{q_i}.
3. Choose y_i, q_i for every i; q_i ≥ i gives q_i → ∞.
4. dist(y_i, x) < 1/(i+1) → 0 gives y_i → x.

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
