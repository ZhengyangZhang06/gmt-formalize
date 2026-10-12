# Parent-supplied natural-language proof

- Parent DAG node: `root.gauss_green-a1.variation_formula-a1`
- Child DAG node: `root.gauss_green-a1.variation_formula-a1.pairing_upper_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is step 1 of the parent proof (S ≤ μ(O)), for a single field g. The parent bounds |⟨g, ν⟩| a.e. by the indicator of tsupport g ⊆ O and then integrates. Here the same a.e. bound is taken against the indicator of O and integrated with the lower Lebesgue integral. That route needs no integrability, measurability or compact-support hypothesis, which is why the statement has none.

Notation. f(x) := ⟨g(x), ν(x)⟩ ∈ ℝ. For t ∈ ℝ, ‖t‖ₑ := ofReal(|t|) ∈ [0, ∞) is the extended norm of t. 1_O : ℝ^N → [0, ∞] is the indicator function of O.

1. A.e. pointwise bound. We claim ‖f(x)‖ₑ ≤ 1_O(x) for μ-a.e. x. Fix x in the μ-full set where |ν(x)| ≤ 1.
 (a) Suppose x ∈ O. By the Cauchy–Schwarz inequality, |f(x)| ≤ |g(x)| |ν(x)| ≤ 1 · 1 = 1. Hence ‖f(x)‖ₑ = ofReal(|f(x)|) ≤ ofReal(1) = 1 = 1_O(x).
 (b) Suppose x ∉ O. Since tsupport g ⊆ O, x ∉ tsupport g. Since support g ⊆ tsupport g, g(x) = 0 (Mathlib image_eq_zero_of_notMem_tsupport). Then f(x) = ⟨0, ν(x)⟩ = 0 and ‖f(x)‖ₑ = 0 = 1_O(x).
2. For every real t, t ≤ |t| and ofReal is monotone, so ofReal(t) ≤ ofReal(|t|) = ‖t‖ₑ (Real.enorm_eq_ofReal_abs). Taking t := ∫ f dμ gives ofReal(∫ f dμ) ≤ ‖∫ f dμ‖ₑ.
3. ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f(x)‖ₑ dμ(x). This holds with no hypothesis on f (Mathlib enorm_integral_le_lintegral_enorm). If f is not μ-integrable, the Bochner integral is 0 and the left side is 0. Otherwise this is the triangle inequality for the Bochner integral.
4. By step 1 and monotonicity of the lower integral under μ-a.e. inequalities (lintegral_mono_ae), ∫⁻ ‖f‖ₑ dμ ≤ ∫⁻ 1_O dμ. Since O is measurable, ∫⁻ 1_O dμ = μ(O) (lintegral_indicator_one).
5. Chaining steps 2, 3 and 4 gives ofReal(∫⟨g, ν⟩ dμ) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ μ(O). ∎

## Key steps

1. For μ-a.e. x, |⟨g(x), ν(x)⟩| ≤ 1_O(x): Cauchy–Schwarz gives the bound on O, and off O we have x ∉ tsupport g, so g(x) = 0.
2. ofReal(∫f) ≤ ‖∫f‖ₑ ≤ ∫⁻‖f‖ₑ dμ, with no integrability needed.
3. ∫⁻‖f‖ₑ dμ ≤ ∫⁻ 1_O dμ = μ(O) because O is measurable.

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
