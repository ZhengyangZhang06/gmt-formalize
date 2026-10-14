# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.minimality_localizes-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.minimality_localizes-a1.measure_agree_on_borel-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the supplied proof of the parent node root.compactness_of_minimizing_currents-a1.minimality_localizes-a1 (cmc_massOn_le_of_le_near_support), stated for general measures; there μ = μ_S, ν = μ_T and O = U ∖ K, and the finiteness of ν on the exhausting sets, which the parent takes from local integrability, follows here from μ(O_i) = ν(O_i). Write d(x) := inf{|x − y| : y ∈ ℝ^P ∖ O} ∈ [0, ∞] for the distance from x to ℝ^P ∖ O, with d(x) := +∞ for every x when O = ℝ^P (the infimum over the empty set). d is continuous as a map to [0, ∞] (it is 1-Lipschitz when ℝ^P ∖ O ≠ ∅ and constant otherwise), and d(x) = 0 for every x ∈ ℝ^P ∖ O.
1. (Exhaustion.) For i ∈ ℕ put O_i := {x ∈ ℝ^P : |x| < i and d(x) > 1/(i+1)}. (a) Each O_i is open: it is the intersection of the sets {|x| < i} and {d(x) > 1/(i+1)}, which are open by continuity of |·| and of d. (b) The set F_i := {x : |x| ≤ i and d(x) ≥ 1/(i+1)} is closed and contains O_i, so closure(O_i) ⊆ F_i. If x ∉ O, then d(x) = 0 < 1/(i+1), so x ∉ F_i; hence closure(O_i) ⊆ F_i ⊆ O. (c) closure(O_i) is closed and contained in the closed ball of radius i about 0, hence compact (Heine–Borel). (d) O_i ⊆ O_j whenever i ≤ j, since then |x| < i ≤ j and 1/(j+1) ≤ 1/(i+1). (e) ⋃_i O_i = O. Indeed O_i ⊆ closure(O_i) ⊆ O for every i. Conversely let x ∈ O. The set ℝ^P ∖ O is closed and does not contain x, so x is not in its closure and d(x) > 0. Choose an integer m ≥ 1 with 1/m < d(x) and an integer k > |x|, and put i := max(m, k). Then |x| < k ≤ i and 1/(i+1) < 1/m < d(x), so x ∈ O_i.
2. (Finiteness.) For each i, μ(O_i) ≤ μ(closure(O_i)) < ∞ by hypothesis, because closure(O_i) is a compact subset of O by step 1(b),(c). Since O_i is an open subset of O, ν(O_i) = μ(O_i) < ∞.
3. (Uniqueness on O_i.) Fix i and let μ_i := μ⌞O_i and ν_i := ν⌞O_i be the restricted measures, μ_i(B) = μ(B ∩ O_i) and ν_i(B) = ν(B ∩ O_i) for Borel B. By step 2 they are finite measures. For every open G ⊆ ℝ^P, the set G ∩ O_i is open and contained in O, so μ_i(G) = μ(G ∩ O_i) = ν(G ∩ O_i) = ν_i(G); in particular μ_i(ℝ^P) = ν_i(ℝ^P) (take G = ℝ^P). The family of open subsets of ℝ^P is closed under finite intersections (a π-system) and generates the Borel σ-algebra of ℝ^P. Two finite measures that have the same total mass and agree on a π-system generating the σ-algebra are equal (Dynkin's π–λ uniqueness theorem; Mathlib MeasureTheory.ext_of_generate_finite with isPiSystem_isOpen). Hence μ_i = ν_i.
4. (Continuity from below.) Let A ⊆ O be a Borel set. The sets A ∩ O_i increase with i by step 1(d), and ⋃_i (A ∩ O_i) = A ∩ ⋃_i O_i = A ∩ O = A by step 1(e). By continuity of measures from below, μ(A) = sup_i μ(A ∩ O_i) = sup_i μ_i(A) and ν(A) = sup_i ν(A ∩ O_i) = sup_i ν_i(A). By step 3, μ_i(A) = ν_i(A) for every i; therefore μ(A) = ν(A). ∎

## Key steps

1. Exhaust O by open sets O_i = {|x| < i, dist(x, ℝ^P ∖ O) > 1/(i+1)} increasing to O, whose closures are compact subsets of O.
2. μ(O_i) ≤ μ(closure O_i) < ∞ and ν(O_i) = μ(O_i), so μ⌞O_i and ν⌞O_i are finite measures.
3. μ⌞O_i and ν⌞O_i agree on every open G (G ∩ O_i is an open subset of O), including ℝ^P; open sets form a π-system generating the Borel σ-algebra, so μ⌞O_i = ν⌞O_i.
4. For Borel A ⊆ O, continuity from below along A ∩ O_i ↑ A gives μ(A) = sup_i μ(A ∩ O_i) = sup_i ν(A ∩ O_i) = ν(A).

## Reference use

### local-project

Queries:
- `cat nodes/root-compactness-of-minimizing-currents-a1-minimality-localizes-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean (all identical; manifest project b4d606db, mathlib 25730c7c)`
- `grep -rn 'GeometricCurrentOn.support|def GeometricCurrentOn.zeroRegion|GeometricCurrentOn.VanishesOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean; cat Chapter06/Mass.lean (massAdmissibleOn, GeometricCurrentOn.massOn); grep 'instance' Chapter06/*.lean (only a Zero instance, no Sub)`
- `python3 scan of dag.json lean_statement for massOn with support/Disjoint, measure equality on open sets, R.measure finiteness; lean_name inventory (cmc_ prefix; cmc_ml_massOn_eq_of_disjoint_sub_support and cmc_ml_measure_eq_of_eq_on_open_subsets: no match); status/candidate_commit of dtc_vanish_off_support, rsd_imrep_compact_measure_ne_top, dor_imrep_massOn_eq_measure_and_support, dtc_massOn_eq_of_agreeOn`
- `rg -n 'massOn_eq|measure_eq_of|ext_of_generate|isPiSystem_isOpen|VanishesOn|support ⊆' local-references/123e8435b4a2469b/project/GMT -g '*.lean' (no relevant match)`
- `rg -n 'theorem ext_of_generate_finite|theorem isPiSystem_isOpen|theorem Monotone.measure_iUnion|theorem restrict_apply|lemma isFiniteMeasure_restrict|theorem withDensity_apply|measure_add_sdiff|theorem continuous_infEDist|theorem infEDist_zero_of_mem|theorem infEDist_pos_iff_notMem_closure|exists_inv_nat_lt' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'theorem ext_of_isOpen|restrict_eq_of_isOpen|ext_of_forall_isOpen|theorem ext_of_generateFrom_of_cover' local-references/123e8435b4a2469b/mathlib/Mathlib (only the general ext_of_generateFrom_of_cover)`
- `rg -n 'massOn_eq|measure_eq_of_eq|ext_of_generate' lake-packages-25730c7c/simongmt/Poincare (only the unrelated Chapter08 Varifold.massOn_eq)`
- `sed -n 1655,1760p, 1800,1930p and 6532,6572p runtime.py; grep -n 'def ensure' -A 35 store.py; grep -n 'def _accepted_checkpoint' -A 5 runtime.py`
- `git show 44ef61f79e2168134f8a5a6d6520baba56052d67:GMT/Ch07/Submission.lean (declaration layout: theorem Submission.X inside namespace GMT.Ch07)`
- `lake env lean /tmp/mloc-split/Types.lean; lake env lean /tmp/mloc-split/Assembly.lean; lake env lean /tmp/mloc-split/Children.lean; lake env lean /tmp/mloc-split/Inst.lean; lake env lean /tmp/mloc-split/Final.lean (#print axioms)`
- `independent reviewer: lake env lean /tmp/mloc-review/ReviewStatements.lean, ReviewInst.lean, ReviewAssembly.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-minimality-localizes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-minimality-localizes-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-minimality-localizes-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/tmp/mloc-split/Types.lean`
- `/tmp/mloc-split/Assembly.lean`
- `/tmp/mloc-split/Children.lean`
- `/tmp/mloc-split/Inst.lean`
- `/tmp/mloc-split/Final.lean`
- `/tmp/mloc-split/proposal.json`
- `/tmp/mloc-review/ReviewStatements.lean`
- `/tmp/mloc-review/ReviewInst.lean`
- `/tmp/mloc-review/ReviewAssembly.lean`

The snapshot Contract.lean and Submission.lean are byte-identical to the workspace files (project b4d606db, mathlib 25730c7c). Neither the snapshot project nor SimonGMT has a lemma on mass equality away from spt(S − T), or on measures agreeing on Borel subsets of an open set given agreement on its open subsets (rg: no relevant match). The pinned Mathlib supplies only the general tools: ext_of_generate_finite, isPiSystem_isOpen, Monotone.measure_iUnion (valid for arbitrary sets), Measure.restrict_apply/restrict_apply', isFiniteMeasure_restrict, withDensity_apply, measure_add_sdiff, and Metric.infEDist with continuous_infEDist, infEDist_zero_of_mem and infEDist_pos_iff_notMem_closure. Mathlib's existing measure ext lemma is global, so the localized uniqueness lemma is a genuine new child. The DAG holds the accepted dtc_vanish_off_support (candidate 44ef61f7), whose frozen type is reused byte-for-byte; runtime.py maps an accepted name with identical type to the existing node and skips handoff installation for it. The two new names occur nowhere in dag.json. In this session all child types elaborate, S − T uses the contract instance GMT.Ch07.instSubGeometricCurrentOnEuclid, and Measure (Euclid P) is Borel. Both new children are proved in full, the measure child using only propext, Classical.choice and Quot.sound. The frozen parent type assembles from the children plus the frozen prerequisite cmc_massOn_eq_imRep_measure, and an independent reviewer confirmed all of this (ACCEPT).
