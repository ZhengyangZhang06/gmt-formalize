# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.distribution_regularity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 2(a) (G is nondecreasing) and Step 2(d) (G is right-continuous, by continuity of ν from above). Here they are stated for an arbitrary Borel measure ν on ℝ and reals a, b with ν((a,b)) < ∞. The parent applies this to its distribution function G(s) = ν((a,b) ∩ (−∞, s]) in the case Q = ν((a,b)) < ∞. The conclusion supplies the hypotheses of the sibling lemma dini_measurable.

Setting. ν is a measure on the Borel σ-algebra of ℝ, a, b ∈ ℝ and Q := ν((a,b)) < ∞. For r ∈ ℝ put A_r := (a,b) ∩ (−∞, r] and G(r) := (ν(A_r)).toReal.

1. (Finiteness.) For every r we have A_r ⊆ (a,b), hence ν(A_r) ≤ Q < ∞ (`measure_mono`, `ne_top_of_le_ne_top`). So ν(A_r) ≠ ∞ for every r.

2. (G is nondecreasing; Step 2(a).) Let r ≤ r′. If x ∈ A_r, then x ∈ (a,b) and x ≤ r ≤ r′, so x ∈ A_{r′}. Thus A_r ⊆ A_{r′} and ν(A_r) ≤ ν(A_{r′}). Since ν(A_{r′}) ≠ ∞ by step 1, toReal preserves this inequality (`ENNReal.toReal_mono`), so G(r) ≤ G(r′).

3. (Reduction to the open half-line.) Fix s ∈ ℝ. Continuity of G at s within [s, ∞) is equivalent to continuity of G at s within (s, ∞) (`continuousWithinAt_Ioi_iff_Ici`). That is, it is equivalent to G(r) → G(s) as r → s along the filter 𝓝[>] s. We prove the latter.

4. (Continuity from above.) Consider the family (A_r) for r > s.
 (i) Each A_r is a Borel set (an open interval intersected with a closed half-line), in particular ν-null-measurable.
 (ii) The family is monotone: if s < i ≤ j then A_i ⊆ A_j (step 2).
 (iii) Some member has finite measure: s + 1 > s and ν(A_{s+1}) < ∞ by step 1.
 Continuity of measures from above, for a family decreasing as r ↓ s, gives ν(A_r) → ν(⋂_{r>s} A_r) as r → s along 𝓝[>] s (`tendsto_measure_biInter_gt`; the index type ℝ is linearly ordered, order-topological and first countable).

5. (The intersection equals A_s.) Suppose x ∈ A_r for every r > s. Taking r = s + 1 gives x ∈ (a,b). Also x ≤ r for every r > s. Hence x ≤ s: otherwise any r with s < r < x would give x > r (formally `le_of_forall_gt_imp_ge_of_dense`). So x ∈ A_s. Conversely, if x ∈ A_s and r > s, then x ≤ s < r, so x ∈ A_r. Hence ⋂_{r>s} A_r = A_s, and step 4 reads: ν(A_r) → ν(A_s) as r → s along 𝓝[>] s.

6. (Passing to real values.) Since ν(A_s) ≠ ∞ (step 1), toReal is continuous at ν(A_s) (`ENNReal.tendsto_toReal`). Composing with step 5 gives G(r) = (ν(A_r)).toReal → (ν(A_s)).toReal = G(s) as r → s along 𝓝[>] s. This is continuity of G within (s, ∞) at s. By step 3 it is continuity within [s, ∞) at s.

7. (Conclusion.) By step 2, G is monotone. By step 6, for every s ∈ ℝ, G is continuous at s within [s, ∞) (ContinuousWithinAt G (Ici s) s). ∎

## Key steps

1. For A_r := (a,b) ∩ (−∞, r], ν(A_r) ≤ ν((a,b)) < ∞, so G(r) = ν(A_r).toReal is a faithful real value.
2. r ≤ r′ ⇒ A_r ⊆ A_{r′} ⇒ G(r) ≤ G(r′) (measure_mono, ENNReal.toReal_mono).
3. Right-continuity within Ici s is equivalent to continuity within Ioi s (continuousWithinAt_Ioi_iff_Ici).
4. Continuity from above (tendsto_measure_biInter_gt) for the decreasing Borel family A_r, r ↓ s, using ν(A_{s+1}) < ∞, gives ν(A_r) → ν(⋂_{r>s} A_r) = ν(A_s).
5. ENNReal.tendsto_toReal at the finite value ν(A_s) gives G(r) → G(s) as r → s+.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical)`
- `grep -n 'theorem\|lemma' mathlib/Mathlib/Analysis/Calculus/Monotone.lean mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean (Monotone.ae_differentiableAt l.209; MonotoneOn.intervalIntegrable_deriv l.86; MonotoneOn.intervalIntegral_deriv_mem_uIcc l.100)`
- `grep -rln -i dini mathlib/Mathlib/{Analysis,MeasureTheory,Order,Topology} (only Topology/UniformSpace/Dini.lean = Dini's uniform-convergence theorem; no Dini-derivative API)`
- `grep -rn 'theorem Measurable.liminf' mathlib/Mathlib/MeasureTheory (Constructions/BorelSpace/Order.lean:998, 1058)`
- `grep for liminf_const_mul_of_ne_top (Order/Filter/ENNReal.lean:190), tendsto_measure_biInter_gt (MeasureTheory/Measure/Continuity.lean:266), ofReal_integral_eq_lintegral_ofReal (MeasureTheory/Integral/Bochner/Basic.lean:739), Monotone.deriv_nonneg (Analysis/Calculus/Deriv/Slope.lean:191), lintegral_liminf_le (MeasureTheory/Integral/Lebesgue/Add.lean:233), nhdsGT_basis (Topology/Order/LeftRightNhds.lean:80), liminf_eq_iSup_iInf / liminf_le_liminf_comp (Order/LiminfLimsup.lean)`
- `grep -rn -E 'slicing_mb_dm_|lowerLeftDini|LowerDini|lowerDini|dini' --include=*.lean lake-packages-25730c7c/simongmt/Poincare workspaces/gmt-ch06/GMT local-references/197bdd4b88278494/project (no match)`
- `python3 scan of dag.json (226 nodes): the four proposed lean_names are unreserved; reserved slicing_mb_* names are cutoff, cutoff_defect_bound, density_majorant, leibniz_bound, pointwise, smooth_approx, wedge_norm_le`
- `lake env printenv LEAN_PATH; lean -o /tmp/dm_split_Cu6Gop/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean /tmp/dm_split_Cu6Gop/check/Closure.lean (only import GMT.Ch06.Submission: Monotone.ae_differentiableAt, Monotone.ae_hasDerivAt, lintegral_liminf_le, tendsto_measure_biInter_gt, ENNReal.liminf_const_mul_of_ne_top, Tendsto.liminf_le_liminf_comp, HasBasis.liminf_eq_iSup_iInf, Monotone.deriv_nonneg available; MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc unknown)`
- `lean /tmp/dm_split_Cu6Gop/check/Names.lean (#check of every lemma cited in the child proofs, with the DerivIntegrable import)`
- `contract_scope() of verifier/gmt-compare.py on GMT/Ch06/Contract.lean (replayed child scope) and validate_lean_statement() of verifier/lean_contract.py on the four child types and the parent type (all pass)`
- `lean /tmp/dm_split_Cu6Gop/check/Ch_*.lean (each child type as a NodeChallenge in the comparator scope: 0 errors)`
- `lean /tmp/dm_split_Cu6Gop/check/Assembly.lean (exact parent type from the four sorry'd children) and lean /tmp/dm_split_Cu6Gop/check/TrialFull.lean (trial proofs of all four children + parent; #print axioms [propext, Classical.choice, Quot.sound])`
- `lean -o of /tmp/dm_split_Cu6Gop/cand/GMT/Ch06/Submission.lean (frozen Submission + import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable + the five theorems), then NodeSolution-style `exact Submission.X` files for each child and the parent (axioms [propext, Classical.choice, Quot.sound])`
- `git log --all -p -- GMT/Ch06/Submission.lean | grep '^+import' (accepted 'Prove' commits b4c070e, b9f9acd, 2f36576 add imports); read verifier/gmt-compare.py frozen_inputs/candidate_inputs (only the contract and build inputs are byte-checked)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/Dini.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-density-majorant-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/tmp/dm_split_Cu6Gop/check/Closure.lean`
- `/tmp/dm_split_Cu6Gop/check/Names.lean`
- `/tmp/dm_split_Cu6Gop/check/Assembly.lean`
- `/tmp/dm_split_Cu6Gop/check/TrialFull.lean`
- `/tmp/dm_split_Cu6Gop/cand/GMT/Ch06/Submission.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and it is byte-identical to the workspace Submission. Neither Mathlib, SimonGMT nor the project has a Dini-derivative API. The only Dini file is Topology/UniformSpace/Dini.lean, which is Dini's uniform-convergence theorem. The four children therefore state the needed facts inline about liminf along 𝓝[>] 0. The frozen import closure provides Lebesgue's theorem Monotone.ae_differentiableAt, continuity from above tendsto_measure_biInter_gt, ENNReal.liminf_const_mul_of_ne_top, Filter.Tendsto.liminf_le_liminf_comp, HasBasis.liminf_eq_iSup_iInf with nhdsGT_basis, Monotone.measurable, Monotone.deriv_nonneg, Measurable.iInf_Prop/iInf/iSup and ofReal_integral_eq_lintegral_ofReal. Two lemmas need import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable: MonotoneOn.intervalIntegrable_deriv and MonotoneOn.intervalIntegral_deriv_mem_uIcc. The comparator permits adding this import, and accepted Ch06 children have added imports. All four child types and the parent type elaborate in the exact comparator child scope and pass validate_lean_statement. Trial proofs of all four children compile. The exact frozen parent type follows from them, and comparator-style `exact Submission.X` checks pass in a simulated candidate with axioms [propext, Classical.choice, Quot.sound]. No proposed name is reserved among the 226 DAG nodes or present in the snapshot, SimonGMT or Mathlib.
