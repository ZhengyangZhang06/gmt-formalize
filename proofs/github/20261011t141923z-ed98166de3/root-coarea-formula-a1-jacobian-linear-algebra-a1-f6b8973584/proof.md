# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1`
- Child DAG node: `root.coarea_formula-a1.jacobian_linear_algebra-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 0.2(a), 0.2(b) (Lemma L) and 3.3 of the parent proof, i.e. the linear algebra of Simon 6.2, specialized to the frozen definition coareaJacobian.

Notation.
- T := tangentSpace M x, a linear subspace of ℝᴺ carrying the restricted inner product.
- ι : T → ℝᴺ is the inclusion and D := fderiv ℝ f x : ℝᴺ → ℝᵐ.
- L := D ∘ ι : T → ℝᵐ; this is (fderiv ℝ f x).comp (tangentSpace M x).subtypeL. L* : ℝᵐ → T is its adjoint.
- Unfolding the definition (its let-binding is definitional): coareaJacobian M f x = Real.sqrt(det(L ∘ L*)).

Facts about normDet used below (Mathlib Analysis/InnerProductSpace/NormDet.lean):
- normDet ≥ 0.
- For X between spaces of equal finite dimension, normDet(X) = |det| of the matrix of X in any orthonormal bases (normDet_eq_norm_det_toMatrix).
- normDet(X.codRestrict p) = normDet(X) (normDet_codRestrict). So following a map by the isometric inclusion of a subspace does not change normDet.

Part (1).
1. LL* is self-adjoint and positive semidefinite, since ⟨LL*v, v⟩ = |L*v|² ≥ 0 for v ∈ ℝᵐ. Hence det(LL*) ≥ 0 (a product of nonnegative eigenvalues), and Real.sqrt(det(LL*)) = 0 iff det(LL*) = 0.
2. ker(LL*) = ker(L*): if LL*v = 0 then |L*v|² = ⟨LL*v, v⟩ = 0. Also ker(L*) = (range L)^⊥. Hence the following are equivalent: det(LL*) = 0; LL* is not injective; (range L)^⊥ ≠ 0; range L ≠ ℝᵐ; L is not surjective. (Equivalently, apply SimonGMT coareaLinearJacobian_eq_sqrt_det and coareaLinearJacobian_eq_zero_iff to the linear map L, after identifying (L ∘L adjoint L).det with (L ∘ₗ L.adjoint).det.) With step 1: coareaJacobian M f x = 0 iff L is not surjective.
3. Since T = range A, range L = D(T) = D(range A) = range(D ∘ A). So L is surjective iff D ∘ A = (fderiv ℝ f x).comp A is surjective. Steps 2 and 3 prove (1).

Part (2). Let P := WithLp 2 (ℝᵐ × ℝᵏ) and p₁ := WithLp.fst p. Define i₁ : ℝᵐ → P, a ↦ toLp(a,0), and j : ℝᵏ → P, b ↦ toLp(0,b). These are linear isometries onto the orthogonal subspaces P₁ = {toLp(a,0)} and P₂ = {toLp(0,b)}, and P = P₁ ⊕ P₂ (the inner product of P is the sum of the component inner products).
4. A is injective with range T. So Ã : P → T, Ã p := A p, is a linear isomorphism, dim T = m + k, and A = ι ∘ Ã. Hence normDet(A) = normDet(Ã) = |det Ã| in orthonormal bases. The hypothesis D(A p) = p₁ says L ∘ Ã = fst, where fst(p) := p₁; in particular L is surjective. Let Q := ker L ⊆ T and let Q^⊥ be its orthogonal complement in T. By rank–nullity, dim Q = k and dim Q^⊥ = m.
5. For b ∈ ℝᵏ, L(Ã(j b)) = fst(toLp(0,b)) = 0, so Ã(j b) ∈ Q. Thus Θ₂ := Ã ∘ j : ℝᵏ → Q is an injective linear map between k-dimensional spaces, hence an isomorphism. Since B b = A(toLp(0,b)) = ι(Θ₂ b), B is Θ₂ followed by the isometric inclusion Q → ℝᴺ. Therefore normDet(B) = normDet(Θ₂) = |det Θ₂|, using orthonormal bases of ℝᵏ and Q.
6. Let π₁ : T → Q^⊥ and π₂ : T → Q be the orthogonal projections, and set α := π₁ ∘ Ã ∘ i₁ : ℝᵐ → Q^⊥ and β := π₂ ∘ Ã ∘ i₁ : ℝᵐ → Q. Use two orthonormal bases:
   - on P: i₁ of the standard basis of ℝᵐ followed by j of the standard basis of ℝᵏ;
   - on T: an orthonormal basis of Q^⊥ followed by one of Q.
   The column of Ã at i₁(e_i) has Q^⊥-coordinates α e_i and Q-coordinates β e_i. The column at j(e_l) is Θ₂ e_l ∈ Q (step 5). So the matrix of Ã is the block matrix [[α, 0], [β, Θ₂]], which is block lower triangular. Hence |det Ã| = |det α|·|det Θ₂|.
7. Since L vanishes on Q, L t = L(π₁ t) for every t ∈ T. Let λ := L|_{Q^⊥} : Q^⊥ → ℝᵐ. For a ∈ ℝᵐ, λ(α a) = L(π₁ Ã(i₁ a)) = L(Ã(i₁ a)) = fst(toLp(a,0)) = a, i.e. λ ∘ α = id on ℝᵐ. Both maps are between m-dimensional spaces, so in orthonormal bases det(λ)·det(α) = 1, hence |det λ|·|det α| = 1.
8. L = λ ∘ π₁, so L* = π₁* ∘ λ*, where π₁* : Q^⊥ → T is the inclusion and π₁ ∘ π₁* = id on Q^⊥. Hence LL* = λλ*. If Λ is the matrix of λ in an orthonormal basis of Q^⊥ and the standard basis of ℝᵐ, then LL* has matrix ΛΛᵀ. So det(LL*) = (det Λ)² and coareaJacobian M f x = √det(LL*) = |det λ|. (This is also SimonGMT coareaHorizontalLinear_normDet with coareaLinearJacobian_eq_sqrt_det: normDet(L|_{(ker L)^⊥}) = √det(L L*).)
9. Combining steps 4–8: coareaJacobian M f x · normDet(A) = |det λ|·|det α|·|det Θ₂| = |det Θ₂| = normDet(B). The degenerate cases are covered:
   - if m = 0, then LL* is the identity of the zero space, coareaJacobian M f x = 1, and α, λ are maps of zero-dimensional spaces with determinant 1;
   - if k = 0, then Q = 0, Θ₂ is the map of zero-dimensional spaces, and normDet(B) = 1.

## Key steps

1. LL* is positive semidefinite and ker(LL*) = ker L* = (range L)^⊥, so √det(LL*) = 0 iff L is not surjective.
2. range L = D(range A) = range(D∘A), which gives part (1).
3. For (2): Ã : P → T is an isomorphism with L∘Ã = fst; Q = ker L has dimension k and Θ₂ = Ã∘j : ℝᵏ → Q is an isomorphism, so normDet(B) = |det Θ₂| and normDet(A) = |det Ã|.
4. In orthonormal bases adapted to P₁⊕P₂ and Q^⊥⊕Q the matrix of Ã is block lower triangular [[α,0],[β,Θ₂]], so |det Ã| = |det α|·|det Θ₂|.
5. λ := L|_{Q^⊥} satisfies λ∘α = id and LL* = λλ*, so √det(LL*) = |det λ| = 1/|det α|; multiply.

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
