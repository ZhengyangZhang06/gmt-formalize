# Parent-supplied natural-language proof

- Parent DAG node: `root.gauss_green-a1.variation_formula-a1`
- Child DAG node: `root.gauss_green-a1.variation_formula-a1.compact_inner_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is step 2 of the parent proof (reduction to compact sets: O is σ-compact and μ is continuous from below). Compare Simon Ch. 1, Remark 1.16 (chapter-01.txt lines 287–295), where a closed subset of a σ-compact space is written as an increasing union of compact sets.

1. Closed exhaustion. O is an open subset of the metric space ℝ^N, so there are closed sets F_0 ⊆ F_1 ⊆ F_2 ⊆ … with F_n ⊆ O for every n and ⋃_n F_n = O. For example, if O = ℝ^N take F_n := ℝ^N. Otherwise take F_n := {x : dist(x, ℝ^N ∖ O) ≥ 1/(n+1)}:
- F_n is closed because x ↦ dist(x, ℝ^N ∖ O) is continuous.
- F_n ⊆ O because points of the closed set ℝ^N ∖ O have distance 0.
- F_n increases with n.
- The F_n exhaust O, because each x ∈ O has a ball around it inside O and therefore positive distance to ℝ^N ∖ O.
Mathlib's IsOpen.exists_iUnion_isClosed provides such a monotone family.
2. Compact exhaustion. Put K_n := F_n ∩ B̄(0, n), where B̄(0, n) = {x : |x| ≤ n}.
- K_n is closed and bounded in ℝ^N, so it is compact (Heine–Borel: a closed subset of the compact ball; isCompact_closedBall with IsCompact.inter_left).
- K_n ⊆ F_n ⊆ O.
- If m ≤ n, then F_m ⊆ F_n and B̄(0, m) ⊆ B̄(0, n), so K_m ⊆ K_n.
3. ⋃_n K_n = O. The inclusion ⊆ follows from step 2. Conversely, let x ∈ O. Choose n with x ∈ F_n (step 1) and m ∈ ℕ with m ≥ |x| (Archimedean property). With p := max(n, m), x ∈ F_n ⊆ F_p and |x| ≤ m ≤ p, so x ∈ K_p.
4. Continuity from below. For any measure and any increasing sequence of sets, μ(⋃_n K_n) = sup_n μ(K_n) (Mathlib Monotone.measure_iUnion, which needs no measurability; here the K_n are closed anyway). With step 3, μ(O) = sup_n μ(K_n).
5. Each K_n is a compact subset of O, so μ(K_n) ≤ c by hypothesis. Therefore μ(O) = sup_n μ(K_n) ≤ c. ∎

## Key steps

1. O = ⋃_n F_n with closed, increasing F_n ⊆ O.
2. K_n := F_n ∩ B̄(0, n) are compact, increasing, contained in O, and ⋃_n K_n = O.
3. Continuity from below gives μ(O) = sup_n μ(K_n) ≤ c.

## Reference use

### local-project

Queries:
- `diff project/GMT/Ch03/Contract.lean <workspace>/GMT/Ch03/Contract.lean (identical); grep -n '### 11' -A 8 project/GMT/Ch03/README.md`
- `rg -n -i 'lusin' mathlib/Mathlib`
- `rg -n 'exists_isClosed.*continuousOn|continuousOn.*isClosed.*measure' mathlib/Mathlib/MeasureTheory`
- `grep -n 'theorem' Poincare/SimonGMT/Chapter01/Lusin.lean; rg -n 'exists_isClosed_continuousOn|IsClosed C ∧.*ContinuousOn' Poincare/SimonGMT`
- `rg -n 'MeasurableSet.exists_isClosed_sdiff_lt|of_pseudoMetrizableSpace_of_isFiniteMeasure|tendsto_measure_thickening_of_isClosed|exists_cthickening_subset_open|exists_continuousMap_one_of_isCompact_subset_isOpen|IsOpen.exists_iUnion_isClosed|enorm_integral_le_lintegral_enorm|lintegral_indicator_one' mathlib/Mathlib`
- `rg -n 'instance.*TietzeExtension|ContinuousMap.exists_restrict_eq|exists_forall_mem_restrict_eq' mathlib/Mathlib`
- `rg -n 'AEStronglyMeasurable.inner|thickening_subset_cthickening_of_le|Monotone.measure_iUnion|integral_sub\'|integral_indicator_one|add_thirds|le_of_forall_pos_le_add|exists_pos_mul_lt|EuclideanSpace.equiv|enorm_eq_ofReal_abs' mathlib/Mathlib`
- `lake env lean GMT/Scratch/VarFormulaAvail.lean (import GMT.Ch03.Submission only: SimonGMT Chapter01 Lusin lemma and TietzeExtension are unknown identifiers)`
- `lake env lean GMT/Scratch/VarFormulaSplit.lean (assembly of the 6 child types ⇒ frozen parent type, #print axioms)`
- `lake env lean GMT/Scratch/VarFormulaFull.lean (all six children proved plus assembly, #print axioms)`
- `lake env lean GMT/Scratch/VarFormulaStmtCheck.lean (six lean_statement strings after import GMT.Ch03.Submission only, contract scope)`
- `python3 lean_contract.validate_lean_statement on the six strings; dag.json lean_name scan; grep -rl gaussGreenVar .humanize GMT`
- `sed -n 300,384p verifier/gmt-compare.py (frozen_inputs / candidate_inputs import policy)`
- `sed -n 270,372p book/chapter-01.txt (Simon 1.15, 1.16, 1.17); sed -n 505,530p book/chapter-02.txt ((2.4))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Complex/Tietze.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/VarFormulaSplit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/VarFormulaFull.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/VarFormulaStmtCheck.lean`

Snapshot: project d09bc8a, Mathlib 25730c7c. Contract.lean is identical to the workspace copy. README §11 marks GaussGreenRepresentation as new, and nothing in the project or SimonGMT states the total-variation formula itself.

Available and cited by the children:
- Mathlib MeasurableSet.exists_isClosed_sdiff_lt and Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure (Regular.lean:1036, 1072).
- Mathlib tendsto_measure_thickening_of_isClosed (BorelSpace/Metric.lean:160).
- Mathlib IsCompact.exists_cthickening_subset_open and IsCompact.cthickening, Metric.isOpen_thickening, Metric.self_subset_thickening and Metric.thickening_subset_cthickening_of_le (Thickening.lean:426, 283, 74, 309, 272).
- Mathlib IsOpen.exists_iUnion_isClosed (HausdorffDistance.lean:207).
- Mathlib Monotone.measure_iUnion (Measure/Continuity.lean:71).
- Mathlib exists_continuousMap_one_of_isCompact_subset_isOpen (UrysohnsLemma.lean:529).
- Mathlib ContinuousMap.exists_forall_mem_restrict_eq (TietzeExtension.lean) with Set.instTietzeExtensionUnitClosedBall (Analysis/Complex/Tietze.lean:54).
- Mathlib AEStronglyMeasurable.inner (StronglyMeasurable/Inner.lean:50).
- Mathlib enorm_integral_le_lintegral_enorm, integral_sub' (Bochner/Basic.lean:333, 268), integral_indicator_one (Bochner/Set.lean:533) and lintegral_indicator_one (Lebesgue/Basic.lean:572).
- Mathlib ENNReal.exists_pos_mul_lt, ENNReal.add_thirds and ENNReal.le_of_forall_pos_le_add, plus EuclideanSpace.equiv.
- SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable (Lusin.lean:127): real-valued Lusin under a closed-inner-regularity hypothesis.

No match, hence supplied as children:
- Mathlib has no Lusin continuity theorem; rg 'lusin' finds only Lusin separation and Lusin–Souslin in Constructions/Polish/Basic.lean.
- SimonGMT has no vector-valued Lusin; its only Lusin results are in Chapter01/Lusin.lean.
- Neither library has the open/compact regularity statements, the Tietze–Urysohn unit-field lemma, or the pairing bounds in the frozen forms needed here.
- The sibling lusin_closed_subset_continuousOn_volume (c1_approximation branch) covers only volume, so it does not apply to an arbitrary μ.

Import closure: after import GMT.Ch03.Submission alone, TietzeExtension, Poincare.SimonGMT.Chapter01.Lusin and StronglyMeasurable.Inner are not in scope. The children may add these imports, because gmt-compare.py does not byte-check Submission.lean.

Scratch checks:
- All six frozen statements elaborate against GMT.Ch03.Submission in the contract scope and pass validate_lean_statement.
- The six children and the assembly were all proved in GMT/Scratch/VarFormulaFull.lean with axioms propext, Classical.choice and Quot.sound only.
- The gaussGreenVar_ names collide with nothing in the DAG.
