# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.weight_null_where_current_vanishes-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.weight_null_where_current_vanishes-a1.covector_space_finite_dimensional-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent-supplied proof (finite-dimensionality of Λ^n via injective evaluation on tuples of basis vectors).
Notation: E := ℝ^P = EuclideanSpace ℝ (Fin P). Λ^n := Covector E n = E [⋀^Fin n]→L[ℝ] ℝ, the continuous alternating n-linear forms on E, with pointwise addition and scalar multiplication.

1. Basis. Let e = (e_1,…,e_P) be the standard basis of E (EuclideanSpace.basisFun (Fin P) ℝ, viewed as a Module.Basis indexed by Fin P).

2. Evaluation map. Define L : Λ^n → ((Fin n → Fin P) → ℝ) by L(α)(I) := α(e_{I(1)},…,e_{I(n)}) = α(e ∘ I) for each index map I : Fin n → Fin P. For fixed I, α ↦ α(e ∘ I) is additive and ℝ-homogeneous, because (α + β)(v) = α(v) + β(v) and (cα)(v) = c·α(v). So L is ℝ-linear.

3. Injectivity. Suppose L(α) = L(β). Then α(e ∘ v) = β(e ∘ v) for every map v : Fin n → Fin P, in particular for every injective v. An alternating n-linear map on a module with basis e is determined by its values on the tuples e ∘ v with v injective (Module.Basis.ext_alternating). So the underlying alternating maps of α and β coincide. A continuous alternating map is determined by its underlying alternating map (ContinuousAlternatingMap.toAlternatingMap_injective). Hence α = β, and L is injective.

4. Conclusion. The codomain (Fin n → Fin P) → ℝ ≅ ℝ^{P^n} is a finite-dimensional real vector space, since its index type Fin n → Fin P is finite. A vector space with an injective linear map into a finite-dimensional space is finite-dimensional (FiniteDimensional.of_injective, applied to L and step 3). Therefore Λ^n = Covector (Euclid P) n is finite-dimensional over ℝ. ∎

## Key steps

1. Fix the standard basis e of ℝ^P = EuclideanSpace ℝ (Fin P) (EuclideanSpace.basisFun).
2. Define the ℝ-linear map L(α) = (α(e ∘ I))_{I : Fin n → Fin P} into the finite-dimensional space (Fin n → Fin P) → ℝ.
3. L is injective: Module.Basis.ext_alternating identifies the underlying alternating maps, and ContinuousAlternatingMap.toAlternatingMap_injective identifies the continuous ones.
4. FiniteDimensional.of_injective gives FiniteDimensional ℝ (Covector (Euclid P) n).

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606d, mathlib 25730c7c); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `cat GMT/Ch07/Submission.lean (IMRep, IMRep.action, IMRep.Represents, IMRep.measure, IsUnitOrientationOf, MultiVector)`
- `grep -n 'def Covector|abbrev DifferentialForm|def IsTestForm|abbrev TestFormOn|structure GeometricCurrentOn|def VanishesOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -n 'theorem|lemma' and sed -n 140,260p mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `grep -rn 'locallyIntegrableOn_iff|IntegrableOn.of_bound|integral_withDensity_eq_integral_smul|measure_eq_zero_iff_ae_notMem|ae_all_iff|withDensity_absolutelyContinuous|AbsolutelyContinuous.ae_le|Module.Basis.ext_alternating|FiniteDimensional.of_injective|toAlternatingMap_injective|ContinuousAlternatingMap.le_opNorm|continuous_eval_const' mathlib/Mathlib`
- `grep -rn 'FiniteDimensional' simongmt/Poincare/SimonGMT/Chapter06/*.lean and mathlib Alternating dirs (no instance for continuous alternating maps)`
- `git diff c4996af 2e5d20d -- GMT/Ch07/Submission.lean (accepted sibling imsupp_unit_orientation_ne_zero_norm_le_one)`
- `python3 over dag.json: all lean_name values; grep -rIl 'imsupp_covector_finiteDimensional|imsupp_orient_apply_ae_eq_zero_of_vanishesOn' .humanize/; git grep the same names over all 459 refs (no match)`
- `sed -n 755,772p book/chapter-06.txt (Simon 6.3.2(3))`
- `lake env lean /tmp/wnwcv_decomp_a40c/{Stmts,Full,Synth,SubmissionTest}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-a40c945682/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-2d6f974584/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-5c07baa22c/parent-child-handoff.json`
- `/tmp/wnwcv_decomp_a40c/Stmts.lean`
- `/tmp/wnwcv_decomp_a40c/Full.lean`
- `/tmp/wnwcv_decomp_a40c/Synth.lean`
- `/tmp/wnwcv_decomp_a40c/SubmissionTest.lean`

Snapshot: the contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606d, mathlib 25730c7c). VanishesOn is defined in SimonGMT CurrentLocalEquality.lean; TestFormOn and IsTestForm (ContDiff ℝ ∞ plus compact support) in Currents.lean and Forms.lean.

The snapshot Mathlib provides every lemma the split needs:
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (LocallyIntegrableOn on an open set; no local finiteness)
- integral_withDensity_eq_integral_smul (no integrability hypothesis)
- locallyIntegrableOn_iff, IntegrableOn.of_bound, AbsolutelyContinuous.ae_le
- Module.Basis.ext_alternating, FiniteDimensional.of_injective, ContinuousAlternatingMap.toAlternatingMap_injective, ContinuousAlternatingMap.le_opNorm
- ae_all_iff, measure_eq_zero_iff_ae_notMem

FiniteDimensional/Module.Finite ℝ (Covector (Euclid P) n) is not an instance (infer_instance fails), so child 1 is a real obligation.

Lean checks: both children and the parent's exact frozen type were kernel-checked inside a copy of Submission.lean at the accepted sibling commit 2e5d20d, using only propext, Classical.choice and Quot.sound. The proposed names imsupp_covector_finiteDimensional and imsupp_orient_apply_ae_eq_zero_of_vanishesOn are unused in the DAG and in GMT sources on every git ref.
