# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.dini_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 5 ((5b): Borel measurability of D by a rational infimum), parts (a)–(d). Here it is stated for an arbitrary nondecreasing right-continuous G : ℝ → ℝ. The parent applies it to its distribution function G, which is nondecreasing and right-continuous by its Step 2(a),(d) (sibling lemma distribution_regularity). Step 2(e) (a monotone function is Borel) is used in step 5 below.

Setting. G : ℝ → ℝ is nondecreasing, and for every s ∈ ℝ, G(r) → G(s) as r → s within [s, ∞). For t, k ∈ ℝ put F_t(k) := ofReal((G(t) − G(t − k))/k) ∈ [0, ∞). Put D(t) := liminf_{k→0+} F_t(k) ∈ [0, ∞], the liminf in the complete lattice [0, ∞] along the filter 𝓝[>] 0.

1. (A countable basis of 𝓝[>] 0.) The intervals (0, δ), δ > 0, form a basis of 𝓝[>] 0 (`nhdsGT_basis`). For every δ > 0 there is j ∈ ℕ with 1/(j+1) < δ (`exists_nat_one_div_lt`), and then (0, 1/(j+1)) ⊆ (0, δ). Conversely, each (0, 1/(j+1)) is a basic set (0, δ) with δ = 1/(j+1) > 0. Hence the intervals (0, 1/(j+1)), j ∈ ℕ, also form a basis of 𝓝[>] 0 (`Filter.HasBasis.to_hasBasis`). In a complete lattice, the liminf along a filter with a basis is the supremum over the basic sets of the infimum over the set (`Filter.HasBasis.liminf_eq_iSup_iInf`). Therefore, for every t,
 D(t) = sup_{j∈ℕ} inf_{k∈(0,1/(j+1))} F_t(k).

2. (Left-continuity of k ↦ F_t(k); Step 5(a).) Fix t ∈ ℝ, k > 0 and real numbers q_n with q_n < k for all n and q_n → k. Then t − q_n > t − k for all n and t − q_n → t − k. So t − q_n → t − k within (t − k, ∞) (`tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`). By hypothesis G is continuous at t − k within [t − k, ∞), equivalently within (t − k, ∞) (`continuousWithinAt_Ioi_iff_Ici`). Hence G(t − q_n) → G(t − k). Since q_n → k ≠ 0, the quotients (G(t) − G(t − q_n))/q_n converge to (G(t) − G(t − k))/k. Since ofReal is continuous, F_t(q_n) → F_t(k).

3. (Rational infimum; Step 5(b).) For every t ∈ ℝ and δ > 0,
 inf_{k∈(0,δ)} F_t(k) = inf_{q∈ℚ, q∈(0,δ)} F_t(q).
 “≤”: every rational q ∈ (0, δ) is a real number in (0, δ), so the left side is ≤ F_t(q) for each such q.
 “≥”: let I be the right side and fix k ∈ (0, δ); we show I ≤ F_t(k).
 (i) For each n ∈ ℕ, max(0, k − 1/(n+1)) < k, because k > 0 and 1/(n+1) > 0. So there is a rational q_n with max(0, k − 1/(n+1)) < q_n < k (`exists_rat_btwn`).
 (ii) Then 0 < q_n < k < δ, so q_n ∈ (0, δ) and I ≤ F_t(q_n).
 (iii) Moreover k − 1/(n+1) < q_n < k and k − 1/(n+1) → k (`tendsto_one_div_add_atTop_nhds_zero_nat`). So q_n → k by the squeeze theorem (`tendsto_of_tendsto_of_tendsto_of_le_of_le`), and by step 2, F_t(q_n) → F_t(k).
 (iv) Every F_t(q_n) is ≥ I, so the limit is ≥ I as well (`ge_of_tendsto`): I ≤ F_t(k).
 Taking the infimum over k ∈ (0, δ) gives “≥”.

4. (Countable formula; Step 5(c).) Combining steps 1 and 3 (with δ = 1/(j+1) > 0), for every t ∈ ℝ,
 D(t) = sup_{j∈ℕ} inf_{q∈ℚ} inf_{[q∈(0,1/(j+1))]} F_t(q).
 The innermost infimum is over proofs of the proposition q ∈ (0, 1/(j+1)). It equals F_t(q) if the proposition holds and ∞ otherwise.

5. (Measurability; Step 5(d).) G is nondecreasing, hence Borel measurable (`Monotone.measurable`). Fix q ∈ ℚ. The map t ↦ t − q is measurable, so t ↦ G(t − q) is measurable. Hence t ↦ (G(t) − G(t − q))/q is measurable (difference of measurable functions, division by a constant), and so is t ↦ F_t(q) (`ENNReal.measurable_ofReal`). For fixed j and q, the infimum of this function over the t-independent proposition q ∈ (0, 1/(j+1)) is measurable (`Measurable.iInf_Prop`). A countable infimum over q ∈ ℚ (`Measurable.iInf`) and a countable supremum over j ∈ ℕ (`Measurable.iSup`) of measurable [0, ∞]-valued functions are measurable. By the formula of step 4, D is Borel measurable. ∎

## Key steps

1. The intervals (0, 1/(j+1)), j ∈ ℕ, form a basis of 𝓝[>] 0, so D(t) = sup_j inf_{k∈(0,1/(j+1))} F_t(k) (Filter.HasBasis.liminf_eq_iSup_iInf).
2. Right-continuity of G makes k ↦ F_t(k) = ofReal((G(t) − G(t−k))/k) left-continuous at each k > 0.
3. The infimum over real k ∈ (0,δ) equals the infimum over rational q ∈ (0,δ): approximate k from the left by rationals q_n ∈ (max(0, k − 1/(n+1)), k) and apply ge_of_tendsto.
4. D(t) = sup_j inf_{q∈ℚ} inf_{[q∈(0,1/(j+1))]} F_t(q). Each t ↦ F_t(q) is measurable because G is monotone, hence measurable. So D is measurable by Measurable.iInf_Prop, Measurable.iInf and Measurable.iSup.

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
