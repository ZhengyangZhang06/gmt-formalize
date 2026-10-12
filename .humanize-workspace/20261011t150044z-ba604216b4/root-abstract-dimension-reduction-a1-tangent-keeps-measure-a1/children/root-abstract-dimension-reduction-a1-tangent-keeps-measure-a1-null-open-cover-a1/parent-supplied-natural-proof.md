# Parent-supplied natural-language proof

- Parent DAG node: `root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1`
- Child DAG node: `root.abstract_dimension_reduction-a1.tangent_keeps_measure-a1.null_open_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent-supplied proof ("by the definition of Hausdorff measure there are sets D_j (j ∈ ℕ) covering E with Σ_j (diam D_j)^ℓ < … The U_j are open, E ⊆ U := ∪_j U_j, and Σ_j (diam U_j)^ℓ < ε'"). This is Simon's "for any ε > 0 we could find open balls B_{ρ_j}(x_j) such that sing ψ ⊆ ∪_j B_{ρ_j}(x_j) and Σ_j ω_ℓ ρ_j^ℓ < ε (by definition of H^ℓ_∞)" (chapter-A.txt lines 88–96).
The enlargement is the one the parent cites, the library lemma Poincare.SimonGMT.Chapter01.exists_isOpen_superset_ediam_rpow_lt, which uses an r-thickening rather than a ball. That lemma is not in the import closure of GMT.Ch07.Submission, so the argument is given in full. It uses only Mathlib facts about thickenings. All sums and powers are in [0, ∞].
1. Reduction to finite ε. Put ε₁ := min(ε, 1). Then 0 < ε₁ ≤ 1 < ∞ and ε₁ ≤ ε. So it suffices to find open U_j covering E with Σ_j (diam U_j)^ℓ < ε₁.
2. A cheap cover. Mathlib's formula for the Hausdorff measure (Measure.hausdorffMeasure_apply) reads
μH[ℓ](E) = sup_{r>0} inf { Σ_n c(t_n) : E ⊆ ∪_n t_n, diam t_n ≤ r for all n },
where c(t) := (diam t)^ℓ if t is nonempty and c(∅) := 0. The term of the supremum at r = 1 is at most μH[ℓ](E) = 0 < ε₁/2. Hence there are sets t_n (n ∈ ℕ) such that:
(a) E ⊆ ∪_n t_n;
(b) diam t_n ≤ 1 for all n;
(c) Σ_n c(t_n) < ε₁/2.
3. Slack. Since ε₁/2 > 0, there are reals δ_n > 0 (n ∈ ℕ) with Σ_n δ_n < ε₁/2, e.g. δ_n := ε₁ 2^{−n−3}. In Mathlib this is ENNReal.exists_pos_sum_of_countable'.
4. Open enlargement. For each n we construct an open set V_n ⊇ t_n with (diam V_n)^ℓ ≤ c(t_n) + δ_n.
(a) If t_n = ∅, let V_n := ∅. It is open and contains t_n, and (diam V_n)^ℓ = 0^ℓ = 0 ≤ c(t_n) + δ_n.
(b) If t_n ≠ ∅, let d := diam t_n. Then d ≤ 1 < ∞, so c(t_n) = d^ℓ is finite, and d^ℓ < d^ℓ + δ_n since δ_n > 0. The map r ↦ (d + 2r)^ℓ, r ∈ [0, ∞), is continuous with value d^ℓ at r = 0. So there is r > 0 with (d + 2r)^ℓ < d^ℓ + δ_n.
(c) For this r, let V_n := {w : |w − y| < r for some y ∈ t_n} be the open r-thickening of t_n. It is open, being a union of open balls, and it contains t_n because r > 0.
(d) diam V_n ≤ d + 2r. Let w, w' ∈ V_n with |w − y| < r and |w' − y'| < r for some y, y' ∈ t_n. Then |w − w'| ≤ |w − y| + |y − y'| + |y' − w'| < 2r + d. In Mathlib this is ediam_thickening_le.
(e) Since t ↦ t^ℓ is monotone on [0, ∞] for ℓ > 0, (diam V_n)^ℓ ≤ (d + 2r)^ℓ < d^ℓ + δ_n = c(t_n) + δ_n.
5. Conclusion. Let U_n := V_n.
(a) Every U_n is open.
(b) E ⊆ ∪_n t_n ⊆ ∪_n U_n.
(c) Σ_n (diam U_n)^ℓ ≤ Σ_n (c(t_n) + δ_n) = Σ_n c(t_n) + Σ_n δ_n < ε₁/2 + ε₁/2 = ε₁ ≤ ε. The sum inequality is strict because each summand is strictly below the finite number ε₁/2. ∎

## Key steps

1. replace ε by the finite ε₁ = min(ε, 1)
2. since μH[ℓ](E) = 0, the defining formula at scale 1 gives a cover {t_n} with Σ_n c(t_n) < ε₁/2, where c(t) = (diam t)^ℓ for t ≠ ∅ and c(∅) = 0
3. choose δ_n > 0 with Σ_n δ_n < ε₁/2
4. replace each nonempty t_n by an r_n-thickening with (diam t_n + 2r_n)^ℓ < (diam t_n)^ℓ + δ_n (r_n exists by continuity), and each empty t_n by ∅
5. sum the bounds: Σ_n (diam U_n)^ℓ ≤ Σ_n c(t_n) + Σ_n δ_n < ε₁ ≤ ε

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `cmp snapshot mathlib/Mathlib/{MeasureTheory/Measure/Hausdorff.lean,Topology/MetricSpace/Thickening.lean,Topology/EMetricSpace/Diam.lean,Analysis/Normed/Module/Ball/Pointwise.lean,Analysis/SpecificLimits/Basic.lean,Order/Monotone/Basic.lean,Basic/ENNReal/Operations.lean} against .lake/packages/mathlib`
- `rg -n 'theorem hausdorffMeasure_apply|theorem hausdorffMeasure_mono' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'exists_thickening_subset_open \(|theorem ediam_thickening_le|theorem self_subset_thickening|theorem isOpen_thickening|theorem mem_thickening_iff ' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'theorem ediam_smul₀' mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean; rg -n 'theorem isometry_mul_left' mathlib/Mathlib; rg -n 'theorem ediam_image' mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `rg -n "theorem exists_pos_sum_of_countable'|theorem tendsto_one_div_add_atTop_nhds_zero_nat" mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean; rg -n 'theorem strictAnti_nat_of_succ_lt' mathlib/Mathlib/Order/Monotone/Basic.lean`
- `rg -n 'protected theorem mul_lt_mul_right' mathlib/Mathlib/Basic/ENNReal/Operations.lean; rg -n 'theorem div_le_of_le_mul ' mathlib/Mathlib/Basic/ENNReal/Inv.lean; rg -n 'protected theorem tsum_add|protected theorem tsum_le_tsum|protected theorem tsum_mul_left' mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `rg -n 'adr_exists_strictAnti_radii|adr_null_open_cover|adr_eventually_subset_small_cover|adr_rescaled_content_lower_bound' project mathlib -g '*.lean' (no match)`
- `rg -n 'HausdorffOpenCovers|exists_isOpen_superset_ediam_rpow_lt' project -g '*.lean' (no match); rg -n '^import' project/GMT/Ch07/Contract.lean`
- `grep -rn 'exists_isOpen_superset_ediam_rpow_lt|simon_theorem_3_26_ii_of_totallyBounded' lake-packages-25730c7c/simongmt/Poincare; #check Poincare.SimonGMT.Chapter01.exists_isOpen_superset_ediam_rpow_lt after import GMT.Ch07.Submission (Unknown identifier)`
- `sed -n 58,112p book/chapter-A.txt (Simon, proof of A.4 implication (1))`
- `python3 scan of dag.json lean_name values (111 nodes); git grep over all 98 refs for the four proposed names (no match)`
- `python3 verifier/lean_contract.py validate_lean_statement on the four child types`
- `lake env lean /tmp/tkm-decomp/Check.lean (verbatim parent type proved from sorry-stubs of the four children and of the sibling adr_content_density)`
- `lake env lean /tmp/tkm-decomp/Child1.lean, Child2.lean, Child3.lean, Child4.lean (full child proofs, #print axioms)`
- `lake env lean /tmp/tkm-decomp/All.lean (real child proofs + comparator-style wrappers + parent assembly, #print axioms)`
- `lake env lean /tmp/tkm-decomp/Inst.lean (set_option pp.explicit true: instances of smul, norm, ball, μH[ℓ], ENNReal rpow)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-tangent-keeps-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-tangent-keeps-measure-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-content-density-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-finite-of-dim-zero-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffOpenCovers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tkm-decomp/Check.lean`
- `/tmp/tkm-decomp/Child1.lean`
- `/tmp/tkm-decomp/Child2.lean`
- `/tmp/tkm-decomp/Child3.lean`
- `/tmp/tkm-decomp/Child4.lean`
- `/tmp/tkm-decomp/All.lean`
- `/tmp/tkm-decomp/Inst.lean`

The snapshot Contract.lean (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. The cited snapshot Mathlib files are byte-identical to .lake/packages/mathlib.

Mathlib supplies everything the four children need:
- Hausdorff.lean:546 hausdorffMeasure_apply (cover formula for μH);
- Thickening.lean:74 isOpen_thickening, :143 mem_thickening_iff, :309 self_subset_thickening, :354 ediam_thickening_le, :439 IsCompact.exists_thickening_subset_open;
- Ball/Pointwise.lean:41 ediam_smul₀, plus isometry_add_left (to_additive of IsometricSMul.lean:83 isometry_mul_left) with Isometry.lean:162 Isometry.ediam_image;
- SpecificLimits/Basic.lean:649 ENNReal.exists_pos_sum_of_countable' and :70 tendsto_one_div_add_atTop_nhds_zero_nat;
- Order/Monotone/Basic.lean:572 strictAnti_nat_of_succ_lt;
- ENNReal Operations.lean:58 mul_lt_mul_right, Inv.lean:392 div_le_of_le_mul, and InfiniteSum/ENNReal.lean:108/116/180 tsum_add, tsum_le_tsum, tsum_mul_left.

The simongmt open-enlargement lemma Poincare.SimonGMT.Chapter01.exists_isOpen_superset_ediam_rpow_lt (HausdorffOpenCovers.lean:29), cited in the supplied step 5, is NOT in the import closure of GMT.Ch07.Submission: #check reports Unknown identifier. So null_open_cover reproves it inline from Mathlib's thickening lemmas. No snapshot file defines any of the four proposed names; rg finds no match.

Compiled in the verifier's exact child scope (import GMT.Ch07.Submission, then the replayed opens and namespace at GMT.Ch07.main_theorem):
- the verbatim parent type compiles from stubs of the four children and of the sibling adr_content_density, whose stub uses the verbatim DAG type;
- all four children are fully proved using only propext, Classical.choice and Quot.sound;
- the comparator-style wrappers `exact Submission.X` elaborate;
- the parent's only sorryAx comes from the adr_content_density stub, which belongs to another branch;
- pp.explicit shows the same instances as the parent type: PiLp.instNorm, WithLp.instSMul, PiLp.instDist and PiLp.instEMetricSpace, WithLp.measurableSpace, and ENNReal.instPowReal.

lean_contract.validate_lean_statement accepts all four types. The four names are absent from dag.json (111 nodes) and from all 98 git refs. The nearest existing node, regcomp_null_compact_ball_cover, has a different type (compact Z, integer dimension, finite ball covers), so nothing can be reused.
