# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.translation_dual-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 3 (weak estimate). The bound of the parent's Step 2(e) for the fields G_t(y) = g(y − th)·h is taken here as the hypothesis. Indeed div G_t(y) = Dφ_t(y)(h) for φ_t(y) := g(y − th), and |φ_t| ≤ 1.

Notation. L := volume, i.e. Lebesgue measure on ℝ^n. Dg(z) := fderiv ℝ g z. Fix g as in the conclusion and let J := ∫ (u(x + h) − u(x))·g(x) dx.

1. Integrability. g is continuous (it is C^∞) and |g| ≤ 1, so g is measurable and bounded. u is integrable, and so is x ↦ u(x + h) (Integrable.comp_add_right; L is translation invariant). Hence the following are integrable (an integrable function times a bounded measurable one, e.g. Integrable.bdd_mul):
   - x ↦ u(x + h)·g(x);
   - x ↦ u(x)·g(x);
   - y ↦ u(y)·g(y − h).
   Therefore J = ∫ u(x + h) g(x) dx − ∫ u(x) g(x) dx (integral_sub).

2. Translation. Put f(y) := u(y)·g(y − h). Then f(x + h) = u(x + h)·g(x), so translation invariance (integral_add_right_eq_self) gives ∫ u(x + h) g(x) dx = ∫ f(x + h) dx = ∫ f(y) dy = ∫ u(y) g(y − h) dy. Recombining with integral_sub, J = ∫ u(y)·(g(y − h) − g(y)) dy.

3. Fundamental theorem of calculus. Fix y and let γ(t) := g(y − t•h) for t ∈ ℝ.
   (a) g is C^1, so by the chain rule (HasFDerivAt.comp_hasDerivAt) γ has derivative γ'(t) = Dg(y − t•h)(−h) = −Dg(y − t•h)(h) at every t.
   (b) γ' is continuous, hence interval integrable on [0, 1].
   (c) By intervalIntegral.integral_eq_sub_of_hasDerivAt, g(y − h) − g(y) = γ(1) − γ(0) = ∫_0^1 γ'(t) dt.
   (d) Hence g(y − h) − g(y) = −∫_0^1 Dg(y − t•h)(h) dt = −∫_{(0,1]} Dg(y − t•h)(h) dt (intervalIntegral.integral_of_le).

4. Domination and measurability.
   (a) Dg is continuous (ContDiff.continuous_fderiv) and vanishes outside the compact set tsupport g (HasCompactSupport.fderiv). So z ↦ Dg(z)(h) is continuous with compact support, hence bounded: |Dg(z)(h)| ≤ K for all z, for some K ≥ 0 (Continuous.bounded_above_of_compact_support).
   (b) Let ν be Lebesgue measure on ℝ restricted to (0, 1], a finite measure, and let F(y, t) := u(y)·Dg(y − t•h)(h).
   (c) F is a.e.-strongly measurable for L ⊗ ν: (y, t) ↦ u(y) is a.e.-strongly measurable (AEStronglyMeasurable.fst), and (y, t) ↦ Dg(y − t•h)(h) is continuous.
   (d) |F(y, t)| ≤ K·|u(y)|, and (y, t) ↦ K·|u(y)| is L ⊗ ν-integrable because u is integrable and ν is finite (Integrable.comp_fst). Hence F is L ⊗ ν-integrable (Integrable.mono').

5. Fubini. By steps 2 and 3, J = ∫ u(y)·(−∫ Dg(y − t•h)(h) dν(t)) dy = −∫ (∫ F(y, t) dν(t)) dy, moving the factor u(y) into the t-integral (integral_const_mul, integral_neg). By step 4 and MeasureTheory.integral_integral_swap, J = −∫ I(t) dν(t), where I(t) := ∫ u(y)·Dg(y − t•h)(h) dy.

6. Bound for each t. Fix t ∈ ℝ and set φ_t(y) := g(y − t•h).
   (a) φ_t is C^∞, as g composed with the smooth map y ↦ y − t•h.
   (b) φ_t has compact support: φ_t = g ∘ (Homeomorph.subRight (t•h)), and HasCompactSupport.comp_homeomorph applies.
   (c) |φ_t(y)| ≤ 1 for all y.
   (d) Dφ_t(y) = Dg(y − t•h) (fderiv_comp_sub), so Dφ_t(y)(h) = Dg(y − t•h)(h) and I(t) = ∫ u(y)·Dφ_t(y)(h) dy.
   (e) The hypothesis applied to φ_t gives |I(t)| ≤ B.

7. Conclusion. ν is Lebesgue measure on (0, 1], so J = −∫_0^1 I(t) dt and |J| = |∫_0^1 I(t) dt| ≤ B·|1 − 0| = B (intervalIntegral.norm_integral_le_of_norm_le_const). ∎

## Key steps

1. Translation invariance gives ∫(u(·+h) − u)g = ∫ u(y)(g(y−h) − g(y)) dy.
2. FTC along t ↦ g(y − th) gives g(y−h) − g(y) = −∫_0^1 Dg(y−th)(h) dt.
3. Domination by K|u(y)| on ℝ^n × (0,1] and Fubini give J = −∫_0^1 ∫ u(y) Dg(y−th)(h) dy dt.
4. For φ_t = g(·−th) ∈ C_c^∞ with |φ_t| ≤ 1, the hypothesis bounds each inner integral by B. Integrating over [0,1] gives |J| ≤ B.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c95, mathlib 25730c7c)`
- `rg -n 'fiw_tb_te_' project (0 matches); python3 scan of dag.json lean_name fields (354 nodes, no fiw_tb_te_ names, no duplicated names)`
- `grep -rn 'theorem exists_contDiff_support_eq_eq_one_iff|theorem _root_.Disjoint.exists_thickenings|theorem closure_thickening_subset_cthickening|alias _root_.MeasurableSet.exists_isCompact_diff_lt|theorem integral_mul_right_eq_self|theorem integral_integral_swap|theorem integral_eq_sub_of_hasDerivAt|lemma Integrable.comp_fst|theorem ofReal_integral_eq_lintegral_ofReal|theorem isFiniteMeasure_withDensity_ofReal|theorem StrictMono.range_inj_of_wellFoundedLT|lemma range_succAbove|theorem extDeriv_apply' mathlib/Mathlib`
- `rg -n 'IsCompact.cthickening|fderiv_comp_sub' mathlib/Mathlib`
- `rg -n 'covectorEuclideanNorm_smul|covectorEuclideanNorm' simongmt/Poincare (no smul lemma; only zero/nonneg/neg in Chapter06/Mass.lean)`
- `read SimonGMT Chapter06 Currents.lean, Forms.lean, Mass.lean, FormsDuality.lean (TestFormOn, GeometricCurrentOn, exteriorDerivativeTestOn, boundary_apply, exteriorDerivative_apply, massAdmissibleOn, le_massOn, wedgeCovectors_apply_det)`
- `git show d771ac3a:GMT/Ch06/Submission.lean (br_la_abs_apply_le_mul_mass proof); git cat-file -t ba202ac0 / 469f0133 (present)`
- `python3 -I tools/gen.py (verifier gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement) then lake env lean gen/Challenge_*.lean (all elaborate)`
- `lake env lean SolutionSim.lean (parent frozen type from 4 sorried Submission.X children; #print axioms: propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean Child1Proto.lean and Child2Proto.lean (complete proofs; axioms propext, Classical.choice, Quot.sound); lake env lean Child4Cutoff.lean (compiles)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/SuccPred.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/tmp/te-decomp-7c1e/SolutionSim.lean`
- `/tmp/te-decomp-7c1e/Child1Proto.lean`
- `/tmp/te-decomp-7c1e/Child2Proto.lean`
- `/tmp/te-decomp-7c1e/Child4Cutoff.lean`

The snapshot is project d8d46c95 with Mathlib 25730c7c. The project and the DAG contain no fiw_tb_te_ declarations, so the four proposed names are globally fresh.

The pinned Mathlib has every lemma the child proofs cite:
- exists_contDiff_support_eq_eq_one_iff, Disjoint.exists_thickenings, closure_thickening_subset_cthickening, IsCompact.cthickening;
- MeasurableSet.exists_isCompact_sdiff_lt (exists_isCompact_diff_lt is deprecated);
- integral_add_right_eq_self, Integrable.comp_add_right, intervalIntegral.integral_eq_sub_of_hasDerivAt, integral_integral_swap, Integrable.comp_fst, fderiv_comp_sub;
- ofReal_integral_eq_lintegral_ofReal, isFiniteMeasure_withDensity_ofReal;
- StrictMono.range_inj_of_wellFoundedLT, Fin.range_succAbove.
InnerRegularCompactLTTop and OuterRegular instances for finite measures on Eucl n are inferred.

SimonGMT supplies covectorEuclideanNorm, massAdmissibleOn, le_massOn, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply, exteriorDerivative_apply and wedgeCovectors_apply_det. It has no homogeneity lemma for covectorEuclideanNorm; the mass_bound child proves one.

The accepted br_la_abs_apply_le_mul_mass (d771ac3a) proves the mass_bound type up to renaming. Its proof compiled verbatim under the fresh name. The directional_form child was proved completely in scratch.

All four frozen child types elaborate in the comparator's exact challenge scope, and together they imply the parent's frozen type in Lean.
