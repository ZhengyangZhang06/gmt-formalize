# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.mean_deviation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (comparison of u with its mean ū on F; this is the step that feeds the Poincaré inequality in Simon's (32)).

Preliminaries. μ(F) = ofReal a ≠ ∞, so constants are integrable on F (integrableOn_const), and (μ(F)).toReal = a because a > 0. Write ū := a⁻¹ ∫_F u dμ.

1. Fix x ∈ α. The function y ↦ u(x) − u(y) is integrable on F (a constant minus the integrable u). So y ↦ |u(x) − u(y)| is nonnegative and integrable on F.

2. By setIntegral_const, ∫_F u(x) dμ(y) = (μ(F)).toReal · u(x) = a · u(x). By linearity (integral_sub), and using a ≠ 0,
   a⁻¹ ∫_F (u(x) − u(y)) dμ(y) = a⁻¹ (a · u(x) − ∫_F u dμ) = u(x) − a⁻¹ ∫_F u dμ = u(x) − ū.

3. Since a⁻¹ > 0 and |∫_F f dμ| ≤ ∫_F |f| dμ (abs_integral_le_integral_abs, equivalently norm_integral_le_integral_norm), step 2 gives
   |u(x) − ū| = a⁻¹ · |∫_F (u(x) − u(y)) dμ(y)| ≤ a⁻¹ ∫_F |u(x) − u(y)| dμ(y).

4. Apply, in turn: the monotone map ENNReal.ofReal; ENNReal.ofReal_mul (a⁻¹ ≥ 0); and ofReal_integral_eq_lintegral_ofReal (integrability and nonnegativity from step 1). This gives
   ofReal|u(x) − ū| ≤ ofReal(a⁻¹ ∫_F |u(x) − u(y)| dμ(y)) = ofReal(a⁻¹) · ofReal(∫_F |u(x) − u(y)| dμ(y)) = ofReal(a⁻¹) · ∫⁻_F ofReal|u(x) − u(y)| dμ(y).

5. Step 4 holds for every x. So by lintegral_mono, and then lintegral_const_mul' (ofReal(a⁻¹) ≠ ∞),
   ∫⁻_F ofReal|u(x) − ū| dμ(x) ≤ ∫⁻_F ofReal(a⁻¹) · ∫⁻_F ofReal|u(x) − u(y)| dμ(y) dμ(x) = ofReal(a⁻¹) · ∫⁻_F ∫⁻_F ofReal|u(x) − u(y)| dμ(y) dμ(x). ∎

## Key steps

1. For fixed x, y ↦ u(x) − u(y) is integrable on F, and ∫_F u(x) dμ(y) = a·u(x) because (μ F).toReal = a.
2. u(x) − ū = a⁻¹ ∫_F (u(x) − u(y)) dμ(y), hence |u(x) − ū| ≤ a⁻¹ ∫_F |u(x) − u(y)| dμ(y).
3. ofReal|u(x) − ū| ≤ ofReal(a⁻¹) · ∫⁻_F ofReal|u(x) − u(y)| dμ(y), by ofReal_mul and ofReal_integral_eq_lintegral_ofReal.
4. Integrate in x over F (lintegral_mono) and pull out the finite constant ofReal(a⁻¹) (lintegral_const_mul').

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
