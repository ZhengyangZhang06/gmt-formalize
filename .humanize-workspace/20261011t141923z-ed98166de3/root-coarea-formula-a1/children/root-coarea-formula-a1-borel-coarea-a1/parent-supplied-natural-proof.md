# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1`
- Child DAG node: `root.coarea_formula-a1.borel_coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 of the parent proof.

Notation: J*f := coareaJacobian M f, μ := μHE[m+k], ν := μHE[k] and P := WithLp 2 (ℝᵐ × ℝᵏ).

1. Preliminaries.
   - f is differentiable at each point of U, since it is C¹ on the open set U.
   - For y ∈ ℝᵐ, U ∩ f⁻¹{y} = U ∖ (U ∩ f⁻¹(ℝᵐ∖{y})), and U ∩ f⁻¹(ℝᵐ∖{y}) is open because f is continuous on the open set U. So U ∩ f⁻¹{y} is Borel.
   - Consequently X ∩ f⁻¹{y} = X ∩ (U ∩ f⁻¹{y}) is Borel for every Borel X ⊆ U.
2. Charts covering the regular set. Let R := {x ∈ M : J*f(x) ≠ 0}.
   - For each x ∈ R, child coarea_exists_straightening_chart gives (Ω_x, O_x, Ψ_x): Ω_x ⊆ P open; O_x open with x ∈ O_x; Ψ_x C¹ and injective on Ω_x with injective derivative; Ψ_x(Ω_x) = O_x ∩ M; and f(Ψ_x p) = p₁ and tangentSpace M (Ψ_x p) = range DΨ_x(p) for p ∈ Ω_x.
   - ℝᴺ is second countable, so there is a countable T ⊆ R with ∪_{x∈T} O_x = ∪_{x∈R} O_x.
   - Choose a surjection e : ℕ → T ⊔ {∗}, for instance onto Option T, which is countable and nonempty. Set (Ω_n, O_n, Ψ_n) := (Ω_x, O_x, Ψ_x) if e(n) = x ∈ T, and (∅, ∅, 0) if e(n) = ∗.
   - Every (Ω_n, O_n, Ψ_n) has all the chart properties above. For the empty chart they hold vacuously, and Ψ_n(∅) = ∅ = ∅ ∩ M. So Ψ_n(Ω_n) = O_n ∩ M for all n.
   - Every x ∈ R lies in A_n := O_n ∩ M for some n, since x ∈ O_x ⊆ ∪_{x′∈T} O_{x′} and e is onto.
3. Disjoint decomposition. Each A_n is Borel (O_n open, M Borel). Let S_n := A_n ∖ ∪_{l<n} A_l (Mathlib disjointed). The S_n are pairwise disjoint Borel sets with S_n ⊆ A_n = Ψ_n(Ω_n), and R′ := ∪_n S_n = ∪_n A_n. Then R ⊆ R′ ⊆ M. Let C′ := M ∖ R′, which is Borel. If x ∈ C′ then J*f(x) = 0, since otherwise x ∈ R ⊆ R′.
4. One chart at a time. For each n, apply child coarea_formula_on_straightening_chart to (Ω_n, Ψ_n, S := S_n, g). Its hypotheses hold: f is differentiable at Ψ_n(p) ∈ O_n ∩ M ⊆ U for p ∈ Ω_n, and S_n ⊆ Ψ_n(Ω_n). So φ_n(y) := ∫_{S_n∩f⁻¹{y}} g dν is Borel in y, and ∫_{S_n} g·J*f dμ = ∫ φ_n dLᵐ.
5. Left side. M = R′ ∪ C′ with R′ and C′ disjoint and C′ Borel, so ∫_M g·J*f dμ = ∫_{R′} g·J*f dμ + ∫_{C′} g·J*f dμ. The second term is 0 because ofReal(J*f) = ofReal(0) = 0 on C′. By countable additivity over the disjoint Borel sets S_n (lintegral_iUnion), then step 4, then lintegral_tsum (each φ_n is Borel):
   ∫_{R′} g·J*f dμ = Σ_n ∫_{S_n} g·J*f dμ = Σ_n ∫ φ_n dLᵐ = ∫ Σ_n φ_n dLᵐ.
6. Regular part of the fibres. For every y, the sets S_n ∩ f⁻¹{y} are pairwise disjoint and Borel (step 1, since S_n ⊆ U), and their union is R′ ∩ f⁻¹{y}. So Σ_n φ_n(y) = ∫_{R′∩f⁻¹{y}} g dν.
7. Critical part of the fibres. By child coarea_critical_fibers_null, there is an Lᵐ-null set Z with ν(M ∩ f⁻¹{y} ∩ {J*f = 0}) = 0 for y ∉ Z. Let y ∉ Z. Then C′ ∩ f⁻¹{y} ⊆ M ∩ f⁻¹{y} ∩ {J*f = 0} is ν-null. M ∩ f⁻¹{y} is the disjoint union of the Borel sets R′ ∩ f⁻¹{y} and C′ ∩ f⁻¹{y}, so
   ∫_{M∩f⁻¹{y}} g dν = ∫_{R′∩f⁻¹{y}} g dν + 0 = Σ_n φ_n(y).
8. Conclusion. y ↦ ∫_{M∩f⁻¹{y}} g dν agrees Lᵐ-a.e. with the Borel function Σ_n φ_n (Measurable.ennreal_tsum), so it is AEMeasurable. By steps 5–7,
   ∫_M g·J*f dμ = ∫ Σ_n φ_n dLᵐ = ∫ ∫_{M∩f⁻¹{y}} g dν dLᵐ(y).

## Key steps

1. Fibres X∩f⁻¹{y} of Borel sets X ⊆ U are Borel, and f is differentiable on U.
2. Straightening charts (child) at every regular point; countably many of them cover R = {J*f ≠ 0} by second countability, padded with empty charts.
3. Disjointify A_n = O_n∩M into Borel sets S_n ⊆ Ψ_n(Ω_n); R′ = ∪S_n ⊇ R, and J*f = 0 on C′ = M∖R′.
4. Apply the one-chart formula (child) on each S_n and sum with lintegral_iUnion and lintegral_tsum.
5. Critical fibres C′∩f⁻¹{y} are μHE[k]-null for a.e. y (child), so the fibre integrals over M and over R′ agree a.e.; this gives AEMeasurability and the identity.

## Reference use

### local-project

Queries:
- `rg -il 'coarea' mathlib/Mathlib`
- `rg -n 'theorem .*[Ss]ard' mathlib/Mathlib`
- `rg -n 'def coareaJacobian|def tangentSpace|def CoareaFormula|def C1Sard' project/GMT/Ch02/Contract.lean`
- `rg -n 'Submission\.' project`
- `rg -n 'theorem hausdorffMeasure_apply|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def|theorem euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib`
- `rg -n 'theorem lintegral_liminf_le |theorem measurable_fderiv |theorem ContDiffOn.exists_lipschitzOnWith|def toOpenPartialHomeomorph|theorem OpenPartialHomeomorph.contDiffAt_symm|theorem WithLp.volume_preserving_toLp|theorem isOpen_iUnion_countable|theorem exists_surjective_nat|theorem normDet_comp |theorem normDet_codRestrict|theorem _root_.ContinuousLinearMap.normDet_sq' mathlib/Mathlib`
- `grep -n '^theorem\|^def' mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `grep -rn 'theorem iUnion_disjointed\|theorem disjoint_disjointed\|theorem MeasurableSet.disjointed\|theorem lintegral_iUnion\|theorem lintegral_tsum\|theorem lintegral_union\|theorem setLIntegral_measure_zero\|theorem ContDiffOn.differentiableOn' mathlib/Mathlib`
- `grep -n '^theorem\|^lemma\|^def\|^noncomputable def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/*.lean`
- `#print axioms for Chapter02.weighted_area_formula_of_injective_derivative, weighted_area_formula_volume_of_injective_derivative, IsSimonLocalRepresentation.exists_open_image_eq_inter, coareaLinearJacobian_eq_zero_iff, coareaLinearJacobian_eq_sqrt_det, coareaHorizontalLinear_normDet, euclideanHausdorffMeasure_image_le_of_lipschitzOn, continuous_normDet, measurable_areaJacobianAt, coarea_projection_lintegral, coarea_linear_lintegral`
- `python3 -I gen_checks.py (verifier gmt-compare.py child_modules/contract_scope + lean_contract.validate_lean_statement on the six statements); lean NodeChallenge_00..05.lean against a scratch olean of GMT.Ch02.Submission`
- `lean FinalAssembly.lean (sorried stand-ins of the six child types and the frozen simon_submanifold_tangent_basics type; sorry-free check_C, check_F, check_parent : CoareaFormula; #print axioms)`
- `lean SkeletonE.lean; lean Inst.lean (#synth InnerProductSpace ℝ (WithLp 2 (Rn m × Rn k))); python3 -I lemmaL2.py`
- `python3 -I: list lean_name of every node in dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1/parent-child-handoff.json`
- `/tmp/coarea-decomp-94z3yF/check/FinalAssembly.lean`
- `/tmp/coarea-decomp-94z3yF/check/SkeletonE.lean`

Nothing in the snapshot proves the nonlinear co-area formula or a Sard-type theorem: rg -il coarea over mathlib/Mathlib finds no file, and rg 'theorem .*[Ss]ard' finds no match.

project/GMT/Ch02/Contract.lean fixes tangentSpace (l.86), coareaJacobian (l.123: √det(L∘L†) with L = fderiv f x ∘ subtypeL), CoareaFormula (l.349) and C1Sard (l.362). The project has no Submission.* declarations.

Mathlib supplies:
- the normDet API (NormDet.lean: ContinuousLinearMap.normDet_sq l.267, normDet_comp l.324, normDet_codRestrict l.365, normDet_eq_norm_det_toMatrix);
- μHE = c·μH (Measure.lean l.74) and hausdorffMeasure_apply (Hausdorff.lean l.546);
- the C¹ inverse function theorem (InverseFunctionTheorem/ContDiff.lean l.31; OpenPartialHomeomorph.contDiffAt_symm, Operations.lean l.881) and the implicit-function version (Implicit.lean l.457);
- measurable_fderiv (FDeriv/Measurable.lean l.378) and ContDiffOn.exists_lipschitzOnWith (RCLike.lean l.149);
- WithLp.volume_preserving_toLp (Haar/InnerProductSpace.lean l.211), lintegral_prod, lintegral_liminf_le (Lebesgue/Add.lean l.233), lintegral_iUnion/lintegral_tsum, disjointed, TopologicalSpace.isOpen_iUnion_countable (Bases.lean l.932) and exists_surjective_nat.

The pinned SimonGMT package supplies:
- weighted_area_formula_(volume_)of_injective_derivative (WeightedArea.lean);
- IsSimonLocalRepresentation.exists_open_image_eq_inter (Simon 4.2, SubmanifoldTopology.lean);
- coareaLinearJacobian_eq_zero_iff, coareaLinearJacobian_eq_sqrt_det and coareaHorizontalLinear_normDet (CoareaLinearAlgebra.lean);
- euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz.lean) and continuous_normDet (AreaApproximation.lean).
#print axioms reports only propext, Classical.choice and Quot.sound for all of them. These modules are not imported by the contract, so children must add the imports, which the comparator permits.

No node in dag.json reserves any of the six proposed bare names.

All six statements pass validate_lean_statement and elaborate in the comparator's replayed contract scope. The six generated NodeChallenge modules compile. #synth confirms that WithLp 2 (Rn m × Rn k) carries WithLp.instProdInnerProductSpace.

In FinalAssembly.lean, Lean accepts sorry-free proofs of coarea_critical_fibers_null, coarea_formula_of_measurable and CoareaFormula from sorried stand-ins of exactly the child types and of the frozen sibling type. The split therefore implies the selected parent.
