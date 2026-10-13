# Parent-supplied natural-language proof

- Parent DAG node: `root.gauss_green-a1.variation_formula-a1`
- Child DAG node: `root.gauss_green-a1.variation_formula-a1.open_outer_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is step 4 of the parent proof. There, a compact neighbourhood L of K with μ(L ∖ K) < ε is built from thickenings by continuity from above, together with an open V with K ⊆ V ⊆ L. Here continuity from above is applied directly to the open thickenings, which yields V at once.

1. A compact neighbourhood inside O. There is δ₀ > 0 with L₀ := {x : dist(x, K) ≤ δ₀} ⊆ O (Mathlib IsCompact.exists_cthickening_subset_open). If K = ∅ then L₀ = ∅, and if O = ℝ^N any δ₀ > 0 works. Otherwise x ↦ dist(x, ℝ^N ∖ O) is continuous and positive on the nonempty compact K, so it has a minimum 2δ₀ > 0 there. If dist(x, K) ≤ δ₀, compactness gives k ∈ K with |x − k| ≤ δ₀. Then dist(x, ℝ^N ∖ O) ≥ 2δ₀ − δ₀ > 0, so x ∈ O. L₀ is closed and bounded, hence compact (IsCompact.cthickening), and L₀ ⊆ O, so μ(L₀) < ∞ by hypothesis. Likewise μ(K) < ∞, because K is a compact subset of O.
2. Open thickenings. For r > 0 let V_r := {x : dist(x, K) < r} (Mathlib Metric.thickening r K; V_r = ∅ if K = ∅). Then:
- V_r is open (Metric.isOpen_thickening).
- K ⊆ V_r, since points of K have distance 0 < r (Metric.self_subset_thickening).
- V_r ⊆ V_s whenever r ≤ s.
- V_r ⊆ L₀ whenever r ≤ δ₀ (Metric.thickening_subset_cthickening_of_le).
3. Continuity from above. K is closed (compact in a Hausdorff space), so ⋂_{r>0} V_r = closure K = K. Since μ(V_{δ₀}) ≤ μ(L₀) < ∞, continuity from above along the decreasing family V_r gives μ(V_r) → μ(K) as r ↓ 0 (Mathlib tendsto_measure_thickening_of_isClosed). Concretely, μ(V_{δ₀/m}) ↓ μ(K) as m → ∞, and r ↦ μ(V_r) is monotone.
4. Choice of V. Since μ(K) < ∞ and ε > 0, μ(K) < μ(K) + ε (ENNReal.lt_add_right). By step 3 there is r with 0 < r < δ₀ and μ(V_r) < μ(K) + ε. Put V := V_r.
5. Verification.
- V is open and K ⊆ V, by step 2.
- V ⊆ L₀ ⊆ O because r ≤ δ₀.
- μ(V) ≤ μ(L₀) < ∞.
- K ⊆ V, K is Borel (closed) and μ(K) < ∞, so μ(V ∖ K) = μ(V) − μ(K) < ε (Mathlib measure_sdiff and ENNReal.sub_lt_of_lt_add, using μ(V) < μ(K) + ε). ∎

## Key steps

1. Some closed δ₀-neighbourhood L₀ of K is compact and contained in O, so μ(L₀) < ∞ and μ(K) < ∞.
2. The open r-neighbourhoods V_r of K are open, contain K, lie in L₀ for r ≤ δ₀, and decrease to K as r ↓ 0, so μ(V_r) → μ(K) by continuity from above.
3. Choose r ∈ (0, δ₀) with μ(V_r) < μ(K) + ε. Then V := V_r works, with μ(V ∖ K) = μ(V) − μ(K) < ε.

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
