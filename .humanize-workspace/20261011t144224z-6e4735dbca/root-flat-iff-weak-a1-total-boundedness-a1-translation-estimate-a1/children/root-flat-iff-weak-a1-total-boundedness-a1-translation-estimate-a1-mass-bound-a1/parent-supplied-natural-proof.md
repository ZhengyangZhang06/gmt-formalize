# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 1 (F3), stated for a general domain U. Up to renaming of bound variables (Y, ω, C ↦ Z, η, c) this is the type of the comparator-accepted Submission.br_la_abs_apply_le_mul_mass (commit d771ac3ae563701d45563ad2e197624b3f42977f). Its Lean proof may be copied under this fresh name, and doing so was checked to compile.

Notation. For an n-covector β on ℝ^P, |β| := covectorEuclideanNorm β = √(Σ_{I : Fin n → Fin P} s_I(β)), where:
- s_I(β) := (β(e_{I(0)}, …, e_{I(n−1)}))² if I is strictly increasing, and s_I(β) := 0 otherwise;
- e_k := EuclideanSpace.basisFun (Fin P) ℝ k.
M(Z) := Z.mass, which by definition is Z.massOn U.

1. Homogeneity. For t ∈ ℝ and an n-covector β, |t • β| = |t|·|β|.
   (a) (t • β)(v) = t·β(v) for every v (ContinuousAlternatingMap.smul_apply), so s_I(t • β) = t²·s_I(β) for every I, in both cases of the definition.
   (b) Summing over I gives Σ_I s_I(t • β) = t²·Σ_I s_I(β) (Finset.mul_sum).
   (c) Since t² ≥ 0, Real.sqrt_mul gives √(t²·S) = √(t²)·√S, and √(t²) = |t| (Real.sqrt_sq_eq_abs). Hence |t • β| = |t|·|β|.

2. One-sided bound. Claim: if θ ∈ TestFormOn U n satisfies |θ(x)| ≤ c for all x, then Z(θ) ≤ c·M(Z).toReal.
   (a) θ' := c⁻¹ • θ lies in TestFormOn U n (it is a submodule), and its underlying form is x ↦ c⁻¹ • θ(x).
   (b) tsupport θ' ⊆ U, because every element of TestFormOn U n has topological support in U (the second component of its membership proof).
   (c) For every x, step 1 and c > 0 give |θ'(x)| = c⁻¹·|θ(x)| ≤ c⁻¹·c = 1.
   (d) So θ' ∈ massAdmissibleOn U n U, and GeometricCurrentOn.le_massOn gives ENNReal.ofReal(Z(θ')) ≤ Z.massOn U = M(Z).
   (e) Since M(Z) ≠ ∞, ENNReal.ofReal_le_iff_le_toReal turns this into Z(θ') ≤ M(Z).toReal.
   (f) Z is linear (map_smul), so Z(θ') = c⁻¹·Z(θ). Multiplying c⁻¹·Z(θ) ≤ M(Z).toReal by c > 0 (inv_mul_le_iff₀) gives Z(θ) ≤ c·M(Z).toReal.

3. Two-sided bound.
   (a) Step 2 with θ := η gives Z(η) ≤ c·M(Z).toReal.
   (b) The underlying form of −η is x ↦ −η(x), and |−η(x)| = |η(x)| ≤ c (covectorEuclideanNorm_neg). Step 2 with θ := −η gives Z(−η) ≤ c·M(Z).toReal.
   (c) Linearity gives Z(−η) = −Z(η) (map_neg), so −Z(η) ≤ c·M(Z).toReal.
   (d) Together with (a), abs_le gives |Z(η)| ≤ c·M(Z).toReal. ∎

## Key steps

1. covectorEuclideanNorm(t • β) = |t|·covectorEuclideanNorm(β): every squared coefficient is scaled by t², and √(t²) = |t|.
2. c⁻¹•θ is mass-admissible whenever |θ| ≤ c. So le_massOn and ofReal_le_iff_le_toReal give c⁻¹Z(θ) ≤ M(Z).toReal.
3. Apply this to θ = η and θ = −η, using covectorEuclideanNorm_neg and linearity, to get |Z(η)| ≤ c·M(Z).toReal.

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
