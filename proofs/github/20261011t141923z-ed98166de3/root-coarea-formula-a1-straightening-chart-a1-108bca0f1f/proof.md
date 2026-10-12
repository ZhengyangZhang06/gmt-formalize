# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1`
- Child DAG node: `root.coarea_formula-a1.straightening_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the parent proof. Relative properness of the new chart is not needed and is not asserted. The tangent identity is derived directly from the original chart.

Notation: n := m + k and P := WithLp 2 (ℝᵐ × ℝᵏ), an inner product space of dimension n; for p ∈ P, p₁ := WithLp.fst p. Since U is open and f is C¹ on U, f is differentiable at every point of U.

1. A chart at x₀. The submanifold hypothesis gives open V ⊆ ℝⁿ, open W ⊆ ℝᴺ and ψ with x₀ ∈ W and IsSimonLocalRepresentation 1 M V W ψ. That is: ψ is C¹ on V, injective on V, ψ(V) = W ∩ M, and Dψ(x) is injective for x ∈ V. Since x₀ ∈ W ∩ M = ψ(V), x₀ = ψ(x₀′) for some x₀′ ∈ V. Put G := f ∘ ψ. As ψ(V) ⊆ M ⊆ U, G is C¹ on V and DG(x) = Df(ψ x) ∘ Dψ(x) for x ∈ V (chain rule).
2. DG(x₀′) is surjective. By hT, tangentSpace M x₀ = range Dψ(x₀′). By child coarea_jacobian_linear_algebra part (1), with A := Dψ(x₀′), the hypothesis coareaJacobian M f x₀ ≠ 0 implies that Df(x₀) ∘ Dψ(x₀′) = DG(x₀′) is surjective. By rank–nullity, K₀ := ker DG(x₀′) ⊆ ℝⁿ has dimension n − m = k.
3. Completing G to a local diffeomorphism. Since dim K₀ = k = dim ℝᵏ, there is a linear isomorphism e : K₀ → ℝᵏ. Let π := e ∘ P_{K₀} : ℝⁿ → ℝᵏ, where P_{K₀} is the orthogonal projection onto K₀; π is linear and π|_{K₀} = e is injective. Define Φ : ℝⁿ → P by Φ(x) := toLp(G(x), π(x − x₀′)). Then Φ is C¹ on V with DΦ(x)v = toLp(DG(x)v, πv).
4. DΦ(x₀′) is invertible. If DG(x₀′)v = 0 and πv = 0, then v ∈ K₀ and e(v) = πv = 0, so v = 0. Thus DΦ(x₀′) : ℝⁿ → P is an injective linear map between spaces of the same dimension n, hence a linear isomorphism.
5. Inverse function theorem.
   - The set V′ := {x ∈ V : DΦ(x) is invertible} is open (DΦ is continuous on V and invertible operators form an open set) and contains x₀′.
   - Apply the C¹ inverse function theorem at x₀′ (Mathlib ContDiffAt.toOpenPartialHomeomorph) and intersect its source with V′. This gives an open V₁ with x₀′ ∈ V₁ ⊆ V′ ⊆ V such that Ω := Φ(V₁) is open in P and Φ|_{V₁} : V₁ → Ω is a homeomorphism. Let Λ : Ω → V₁ be its inverse.
   - For every x ∈ V₁, Φ is C¹ near x with invertible derivative. So Λ is C¹ at every p ∈ Ω with DΛ(p) = DΦ(Λ p)⁻¹ (OpenPartialHomeomorph.contDiffAt_symm). In particular DΛ(p) is a linear isomorphism P → ℝⁿ.
   (Mathlib's implicit function theorem, HasStrictFDerivAt.implicitToOpenPartialHomeomorph in Analysis/Calculus/Implicit.lean, yields the same chart up to the linear identification ker DG(x₀′) ≅ ℝᵏ and ℝᵐ × ℝᵏ ≅ P.)
6. Define Ψ := ψ ∘ Λ, using the global extension of Λ given by the partial homeomorphism; values off Ω are irrelevant. Then:
   (a) Ψ is C¹ on Ω: Λ is C¹ on Ω with Λ(Ω) = V₁ ⊆ V, and ψ is C¹ on V.
   (b) Ψ is injective on Ω: Λ is injective on Ω and ψ is injective on V.
   (c) For p ∈ Ω, DΨ(p) = Dψ(Λ p) ∘ DΛ(p) by the chain rule, and this is a composition of injective linear maps.
   (d) Apply SimonGMT IsSimonLocalRepresentation.exists_open_image_eq_inter (Simon 4.2) to the open set V₁ ⊆ V: there is an open O ⊆ W with ψ(V₁) = O ∩ M. Then Ψ(Ω) = ψ(Λ(Ω)) = ψ(V₁) = O ∩ M, and x₀ = ψ(x₀′) ∈ ψ(V₁) ⊆ O.
   (e) For p ∈ Ω, Φ(Λ p) = p, and the first component of Φ(x) is G(x). Hence p₁ = G(Λ p) = f(ψ(Λ p)) = f(Ψ p).
   (f) For p ∈ Ω we have Λ p ∈ V. So by hT, tangentSpace M (Ψ p) = tangentSpace M (ψ(Λ p)) = range Dψ(Λ p). Since DΛ(p) is surjective, range Dψ(Λ p) = range(Dψ(Λ p) ∘ DΛ(p)) = range DΨ(p).
Thus Ω, O and Ψ have all the required properties.

## Key steps

1. Pick a Simon chart ψ with x₀ = ψ(x₀′); G := f∘ψ is C¹ with DG = Df∘Dψ.
2. hT and child part (1): coareaJacobian M f x₀ ≠ 0 implies DG(x₀′) is surjective, so K₀ = ker DG(x₀′) has dimension k.
3. Φ(x) := (G(x), π(x − x₀′)), with π injective on K₀, has invertible derivative at x₀′; the C¹ inverse function theorem gives Φ : V₁ → Ω with C¹ inverse Λ and DΛ invertible on Ω.
4. Ψ := ψ∘Λ is C¹ and injective with injective derivative; Ψ(Ω) = ψ(V₁) = O ∩ M by Simon 4.2, and f∘Ψ = first component.
5. range DΨ(p) = range Dψ(Λp) = tangentSpace M (Ψp) by hT, because DΛ(p) is invertible.

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
