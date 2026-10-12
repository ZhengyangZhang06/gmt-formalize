# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.median_exists-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–2 of the parent proof (Simon Ch. 6, proof of 5.1, (31): the choice of an integer median β_F of the integer-valued θ_F).

Notation. For k ∈ ℤ put A_k := F ∩ {x : u(x) ≤ k} and m_k := μ(A_k).
- Each A_k is measurable, because F is measurable and {x : u(x) ≤ k} is measurable as u is measurable.
- A_k ⊆ F, so m_k ≤ μ(F) = ofReal a < ∞.
- Since a > 0, we have 0 < ofReal(a/2) < ofReal a.
- ofReal(a/2) + ofReal(a/2) = ofReal(a/2 + a/2) = ofReal a, by ENNReal.ofReal_add with a/2 ≥ 0.

1. (Monotonicity.) If k ≤ l are integers then A_k ⊆ A_l, because u(x) ≤ k ≤ l. Hence k ↦ A_k and k ↦ m_k are monotone.

2. (Limit at +∞.)
   - ⋃_{k ∈ ℤ} A_k = F: each A_k ⊆ F, and every x ∈ F lies in A_{⌈u(x)⌉} because u(x) ≤ ⌈u(x)⌉ (Int.le_ceil).
   - By continuity from below (tendsto_measure_iUnion_atTop, for the monotone family A indexed by ℤ, whose atTop filter is countably generated), m_k → μ(F) = ofReal a as k → +∞.
   - Since ofReal(a/2) < ofReal a, the set (ofReal(a/2), ∞] is a neighbourhood of ofReal a, so m_k > ofReal(a/2) for all large k.
   - Fix such a k₁; then ofReal(a/2) ≤ m_{k₁}.

3. (Limit at −∞.) For j ∈ ℕ put B_j := A_{−j}.
   - If j ≤ j' then −j' ≤ −j, so B_{j'} ⊆ B_j by step 1: the family is antitone.
   - Each B_j is measurable, and μ(B_0) ≤ ofReal a ≠ ∞.
   - ⋂_j B_j = ∅. Given x, let j := toNat(1 − ⌊u(x)⌋) ∈ ℕ. Then (j : ℤ) ≥ 1 − ⌊u(x)⌋ (Int.self_le_toNat), hence −j ≤ ⌊u(x)⌋ − 1 ≤ u(x) − 1 < u(x) (Int.floor_le). So u(x) ≤ −j fails, and x ∉ B_j.
   - By continuity from above for measurable sets one of which has finite measure (tendsto_measure_iInter_atTop), m_{−j} = μ(B_j) → μ(∅) = 0 as j → ∞.
   - Since ofReal(a/2) > 0, the set [0, ofReal(a/2)) is a neighbourhood of 0, so there is j₀ ∈ ℕ with m_{−j₀} < ofReal(a/2).

4. (Least element.) Let K := {k ∈ ℤ : ofReal(a/2) ≤ m_k}.
   - By step 2, k₁ ∈ K, so K ≠ ∅.
   - K is bounded below by −j₀: if k ∈ K and k < −j₀, then by step 1, m_k ≤ m_{−j₀} < ofReal(a/2) ≤ m_k, a contradiction.
   - By Int.exists_least_of_bdd (with classical decidability), K has a least element β.

5. (First inequality.) β ∈ K says exactly ofReal(a/2) ≤ μ(F ∩ {x : u(x) ≤ β}).

6. (Second inequality.)
   - β − 1 ∉ K, since otherwise minimality would give β ≤ β − 1. Hence m_{β−1} < ofReal(a/2).
   - Let x ∈ F and write u(x) = k with k ∈ ℤ (integrality hypothesis). Either k ≤ β − 1, and then x ∈ A_{β−1}; or k ≥ β, and then β ≤ u(x).
   - Hence F ⊆ A_{β−1} ∪ (F ∩ {x : β ≤ u(x)}). By monotonicity and subadditivity of μ:
     ofReal a = μ(F) ≤ m_{β−1} + μ(F ∩ {x : β ≤ u(x)}).
   - If μ(F ∩ {x : β ≤ u(x)}) < ofReal(a/2), then ENNReal.add_lt_add with m_{β−1} < ofReal(a/2) gives ofReal a < ofReal(a/2) + ofReal(a/2) = ofReal a, which is absurd.
   - Hence ofReal(a/2) ≤ μ(F ∩ {x : β ≤ u(x)}).

7. By steps 5 and 6, the integer β has both required properties. ∎

## Key steps

1. A_k := F ∩ {u ≤ k} is measurable and monotone in k ∈ ℤ, with m_k := μ(A_k) ≤ ofReal a.
2. ⋃_k A_k = F (via ⌈u(x)⌉), so by continuity from below m_k → ofReal a; hence some k₁ has m_{k₁} ≥ ofReal(a/2).
3. ⋂_j A_{−j} = ∅ (via ⌊u(x)⌋ and toNat), so by continuity from above (finite measure) m_{−j} → 0; hence some j₀ has m_{−j₀} < ofReal(a/2).
4. K := {k : ofReal(a/2) ≤ m_k} is nonempty and bounded below by −j₀; β := its least element (Int.exists_least_of_bdd) gives μ(F ∩ {u ≤ β}) ≥ ofReal(a/2).
5. β − 1 ∉ K, and integrality gives F ⊆ A_{β−1} ∪ (F ∩ {u ≥ β}); subadditivity and ofReal(a/2) + ofReal(a/2) = ofReal a then give μ(F ∩ {u ≥ β}) ≥ ofReal(a/2).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean && cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (IDENTICAL; HEAD d8d46c95)`
- `rg -n -i median mathlib/Mathlib -l (single hit: Mathlib/LinearAlgebra/AffineSpace/Simplex/Centroid.lean, geometric median of a simplex, irrelevant)`
- `rg -n -i median project -l (no match); rg -n -i median lake-packages-25730c7c/simongmt/Poincare -l (no match)`
- `rg -n -F over mathlib/Mathlib: 'theorem tendsto_measure_iUnion_atTop', 'theorem tendsto_measure_iInter_atTop', 'theorem exists_least_of_bdd', 'theorem ofReal_integral_eq_lintegral_ofReal', "theorem lintegral_const_mul'", 'theorem setLIntegral_const ', 'theorem lintegral_mono_set ', "theorem setLIntegral_mono' ", 'theorem integral_indicator_const ', 'theorem measureReal_restrict_apply ', 'theorem measureReal_union ', 'theorem integrableOn_const', 'theorem ofReal_le_iff_le_toReal', 'theorem measure_mono_null ', 'theorem setIntegral_const ', 'theorem measure_union_le ', 'theorem le_ceil ', 'theorem floor_le ', 'theorem measurableSet_le ' (all found)`
- `rg -n abs_integral_le_integral_abs / '^lemma integral_mono ' / norm_integral_le_integral_norm / 'theorem integral_add |theorem integral_sub |theorem integral_const_mul ' in mathlib/Mathlib/MeasureTheory/Integral/Bochner (found)`
- `rg -n 'ofReal_mul |theorem ofReal_add |theorem ofReal_le_ofReal |theorem ofReal_lt_ofReal_iff |theorem ofReal_pos |theorem toReal_ofReal |theorem ofReal_ofNat|protected theorem add_lt_add' mathlib/Mathlib (found under Mathlib/Basic/ENNReal at this revision)`
- `rg -n 'lemma isFiniteMeasure_restrict|theorem measure_ne_top_of_subset|lemma cast_ne_zero|lemma add_halves' mathlib/Mathlib (found); Int.self_le_toNat found in Lean core Init/Data/Int/Order.lean:697`
- `sed -n 190,235p mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean; rg -n 'theorem exists_least_of_bdd' -A 6 mathlib/Mathlib/Order/Int/LeastGreatest.lean`
- `python3 scan of dag.json (476 nodes): lean_names with prefix fiw_tb_tda_ (8 existing, none fiw_tb_tda_im_*); selected node depth 4, status decomposing, frozen lean_statement identical to handoff`
- `python3 -I /tmp/im-tools/scope.py (verifier gmt-compare.py contract_scope on Contract.lean: namespace GMT.Ch06 plus replayed open/noncomputable section/end commands)`
- `python3 -I /tmp/im-tools/check.py (runtime lean_contract.validate_lean_statement on the 4 child types: all PASS, unchanged by normalization)`
- `lean /tmp/im-decomp/{Smoke,Stmts,Proto,Proto2,Full}.lean with LEAN_PATH = workspace .lake/build/lib/lean (Submission at d8d46c95) + lake-packages-25730c7c/*/.lake/build/lib/lean (0 errors; Full.lean proves all 4 children and the frozen parent; #print axioms = propext, Classical.choice, Quot.sound)`
- `sed -n 1860,1925p book/chapter-06.txt (Simon 5.1 proof: (31) median choice of beta_F, integer if theta_F is; (35) |beta_F| <= 2 int |theta_F|)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/AffineSpace/Simplex/Centroid.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Int/LeastGreatest.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Floor/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Int/Cast/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Field/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-median-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-median-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/im-decomp/Stmts.lean`
- `/tmp/im-decomp/Proto.lean`
- `/tmp/im-decomp/Proto2.lean`
- `/tmp/im-decomp/Full.lean`

No reusable median result exists locally. The only 'median' match in the pinned Mathlib (25730c7c) is the geometric median of a simplex in LinearAlgebra/AffineSpace/Simplex/Centroid.lean. There is none in the frozen Ch06 project (snapshot Contract.lean = workspace Contract.lean = Submission.lean at d8d46c95, so there are no accepted helpers) and none in SimonGMT. So the four median obligations of the supplied proof become new children.

Every Mathlib lemma cited in the child proofs exists at the pinned revision:
- continuity and least elements: tendsto_measure_iUnion_atTop and tendsto_measure_iInter_atTop (Measure/Continuity.lean:198, 220); Int.exists_least_of_bdd (Order/Int/LeastGreatest.lean:69);
- Bochner integral: ofReal_integral_eq_lintegral_ofReal (Bochner/Basic.lean:739); abs_integral_le_integral_abs (Bochner/Basic.lean:982); integral_mono, integral_add, integral_sub, integral_const_mul (Bochner/Basic.lean); integral_indicator_const and setIntegral_const (Bochner/Set.lean:528, 524);
- lower integral: lintegral_const_mul' (Lebesgue/Add.lean:420); setLIntegral_const, lintegral_mono_set, setLIntegral_mono' (Lebesgue/Basic.lean:121, 98, 254);
- measures: measureReal_restrict_apply and measureReal_union (Measure/Real.lean:102, 227); integrableOn_const (IntegrableOn.lean:119); isFiniteMeasure_restrict; measure_ne_top_of_subset; measure_mono_null; measure_union_le; measurableSet_le;
- integers: Int.le_ceil and Int.floor_le (Floor/Defs.lean); Int.cast_ne_zero;
- ENNReal (under Mathlib/Basic/ENNReal at this revision): ofReal_le_iff_le_toReal, ofReal_mul, ofReal_add, ofReal_pos, ofReal_lt_ofReal_iff, toReal_ofReal, add_lt_add.

Lean checks:
- In the comparator's replayed contract scope after import GMT.Ch06.Submission, all four child types elaborate and pass validate_lean_statement.
- The frozen parent type follows from them by a five-line assembly.
- Complete prototype proofs of all four children compile under default heartbeats (/tmp/im-decomp/Full.lean, 263 lines), with axioms [propext, Classical.choice, Quot.sound] for each child and for the parent.
- No dag.json lean_name begins with fiw_tb_tda_im_, so the names do not collide.
