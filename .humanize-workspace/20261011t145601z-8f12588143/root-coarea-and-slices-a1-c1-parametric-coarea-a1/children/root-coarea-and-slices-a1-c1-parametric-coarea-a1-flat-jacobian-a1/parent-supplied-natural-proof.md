# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.flat_jacobian-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (the flat half of the parent's LA). There it is applied with A = Dψ(u), Γ = DG(u), T = DΦ(u) and E = E_u; the parent's |det DΦ(u)| (absolute determinant in orthonormal bases) is normDet(T) here.

Facts from Mathlib Analysis/InnerProductSpace/NormDet.lean:
(F1) normDet_comp_of_finrank_eq: for linear f : U → V and g : V → W with finrank U = finrank V, normDet(g∘f) = normDet(g)·normDet(f).
(F2) LinearIsometry.normDet_eq_one and normDet_id.
(F3) normDet_eq_norm_det_toMatrix: if β and γ are orthonormal bases of U and V indexed by the same finite type, then normDet(f) = |det(toMatrix β γ f)|.

1. (Γ is surjective; dimensions.) For y ∈ ℝᵐ let v := T⁻¹(toLp(y, 0)) (T is bijective); then Γ v = (T v).fst = y. So Γ is surjective, K := ker Γ has finrank n − m = k (rank–nullity; SimonGMT coarea_kernel_finrank), and K^⊥ has finrank m (Submodule.finrank_add_finrank_orthogonal).

2. (Second component; corestriction of E.) Let π := snd∘T : ℝⁿ → ℝᵏ (WithLp.sndₗ ∘ₗ T), so that T v = toLp(Γ v, π v) for all v. Applying fst and snd to T(E z) = toLp(0, z) gives Γ(E z) = 0 and π(E z) = z for all z ∈ ℝᵏ. Hence E takes values in K. Let E' : ℝᵏ → K be its corestriction (LinearMap.codRestrict), so E = ι_K∘E', and let π_K := π∘ι_K : K → ℝᵏ. Then π_K∘E' = id_{ℝᵏ}.

3. (Parent (iv).) finrank ℝᵏ = k = finrank K, so (F1) and normDet_id give normDet(π_K)·normDet(E') = normDet(π_K∘E') = 1.

4. (Parent (i).) A∘E = (A∘ι_K)∘E' and finrank ℝᵏ = finrank K, so by (F1) normDet(A∘E) = normDet(A∘ι_K)·normDet(E').

5. (Parent (iii).) Let Γ_⊥ := Γ∘ι_{K^⊥} : K^⊥ → ℝᵐ; this is SimonGMT coareaHorizontalLinear Γ = Γ.domRestrict K^⊥. Since Γ is surjective, SimonGMT coareaHorizontalLinear_normDet gives normDet(Γ_⊥) = normDet(Γ*). Reason: Γ* takes values in K^⊥ = range Γ*, and its corestriction to K^⊥ is the adjoint of Γ_⊥. Corestriction does not change normDet (normDet_codRestrict). A map between spaces of equal dimension has the same normDet as its adjoint, because their matrices in orthonormal bases are transposes (SimonGMT normDet_adjoint_of_finrank_eq).

6. (Parent (ii): normDet(T) = normDet(Γ_⊥)·normDet(π_K).) Let c : WithLp 2 (K^⊥ × K) → ℝⁿ, c(toLp(a, b)) := a + b. It is a linear isometric equivalence, since ℝⁿ = K^⊥ ⊕ K orthogonally; c is the inverse of SimonGMT coareaCoordinates Γ (see coareaCoordinates_symm_apply). So (F1) and (F2) give normDet(T∘c) = normDet(T)·normDet(c) = normDet(T).
For a ∈ K^⊥ and b ∈ K we have Γ b = 0, hence (T∘c)(toLp(a, b)) = T(a + b) = toLp(Γ_⊥ a, π a + π_K b).
Choose orthonormal bases β₁ of K^⊥ indexed by Fin m and β₂ of K indexed by Fin k (reindexed stdOrthonormalBasis, using step 1). Let γ₁, γ₂ be the standard orthonormal bases of ℝᵐ and ℝᵏ. Let β := β₁.prod β₂ and γ := γ₁.prod γ₂ be the product orthonormal bases of WithLp 2 (K^⊥ × K) and of P (Mathlib OrthonormalBasis.prod), both indexed by Fin m ⊕ Fin k.
By the formula above, toMatrix β γ (T∘c) = Matrix.fromBlocks M₁₁ 0 M₂₁ M₂₂ with M₁₁ = toMatrix β₁ γ₁ Γ_⊥, M₂₁ = toMatrix β₁ γ₂ (π∘ι_{K^⊥}) and M₂₂ = toMatrix β₂ γ₂ π_K. The upper right block vanishes because the ℝᵐ-component of (T∘c)(toLp(0, b)) is Γ b = 0. By Matrix.det_fromBlocks_zero₁₂ the determinant is det M₁₁·det M₂₂. Applying (F3) to T∘c, Γ_⊥ and π_K yields normDet(T) = normDet(T∘c) = |det M₁₁|·|det M₂₂| = normDet(Γ_⊥)·normDet(π_K).

7. (Conclusion.) By steps 4, 6, 3 and 5:
normDet(A∘E)·normDet(T) = normDet(A∘ι_K)·normDet(E')·normDet(Γ_⊥)·normDet(π_K) = normDet(A∘ι_K)·normDet(Γ_⊥)·(normDet(π_K)·normDet(E')) = normDet(A∘ι_K)·normDet(Γ*). ∎
No property of A is used; if A∘ι_K is not injective, both sides vanish.

## Key steps

1. Γ = fst∘T is surjective, K = ker Γ has dimension k, and T v = (Γ v, π v) with π = snd∘T.
2. E = ι_K∘E' with π_K∘E' = id, so normDet(π_K)·normDet(E') = 1 and normDet(A∘E) = normDet(A∘ι_K)·normDet(E') (normDet_comp_of_finrank_eq).
3. normDet(Γ|_{K^⊥}) = normDet(Γ*) (SimonGMT coareaHorizontalLinear_normDet).
4. T∘c is block lower triangular in product orthonormal bases of K^⊥ ⊕ K and ℝᵐ ⊕ ℝᵏ, so normDet(T) = normDet(Γ|_{K^⊥})·normDet(π_K).
5. Multiply the identities.

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -l -i "coarea" mathlib/Mathlib (no match)`
- `rg -l -i "area.formula|areaFormula" mathlib/Mathlib (no match)`
- `rg -n "pcoarea_|parametric_coarea|c1_parametric" project/GMT (no match)`
- `diff project/GMT/Ch03/Contract.lean <workspace>/GMT/Ch03/Contract.lean (identical)`
- `rg -n "theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul" mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `rg -n "theorem normDet_comp_of_finrank_eq|theorem normDet_eq_norm_det_toMatrix|theorem normDet_codRestrict|theorem normDet_eq_abs_det|theorem normDet_eq_zero_iff_ker_ne_bot|theorem normDet_sq" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "def prod |theorem prod_apply" mathlib/Mathlib/Analysis/InnerProductSpace/ProdL2.lean`
- `rg -n "volume_preserving_toLp|theorem measurePreserving" mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `rg -n "def toOpenPartialHomeomorph|contDiffAt_symm|ContinuousLinearEquiv.isOpen|ContDiffOn.exists_lipschitzOnWith|theorem measurable_fderiv" mathlib/Mathlib`
- `rg -n "theorem MeasurableSet.image_of_continuousOn_injOn|theorem isOpen_iUnion_countable|theorem lintegral_iUnion |theorem lintegral_tsum|theorem AEMeasurable.ennreal_tsum|theorem Measurable.lintegral_prod_right'" mathlib/Mathlib`
- `grep -rn "theorem weighted_area_formula_lipschitzOn_fiberSum|theorem ae_fderivWithin_eq_of_lipschitz_extension|theorem exists_lipschitz_extension_finiteDimensional|def areaJacobianWithin|def weightedAreaFiberSum|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|theorem coareaLinearJacobian_eq_zero_iff|theorem coarea_kernel_finrank|theorem coareaHorizontalLinear_normDet|theorem normDet_adjoint_of_finrank_eq|theorem coareaCoordinates_symm_apply" Poincare/SimonGMT`
- `python3 -I dag.json scan: lean_name and theorems fields of all 116 nodes vs the six proposed names; grep -rl "pcoarea_" runs/<run>`
- `python3 -I /tmp/pcoarea_v2_scripts/scope_check.py (gmt-compare.py contract_scope for GMT.Ch03.main_theorem + lean_contract.validate_lean_statement) then lake env lean GMT/Scratch/PCoareaC1V2ScopeGen.lean`
- `python3 -I /tmp/pcoarea_v2_scripts/gen_assembly.py then lake env lean GMT/Scratch/PCoareaC1V2AssemblyGen.lean (#print axioms Submission.c1_parametric_coarea_formula)`
- `lake env lean GMT/Scratch/PCoareaC1V2Refs.lean (#check of every lemma cited in the six child proofs)`
- `lake env lean GMT/Scratch/PCoareaC1V2Inst.lean (LinearIsometryEquiv.measurePreserving on WithLp 2 (Rn m × Rn k), finrank P = m + k, normDet T = |det (e ∘ T)|)`
- `lake env lean GMT/Scratch/PCoareaC1V2Tsum.lean (#check AEMeasurable.tsum)`
- `python3 -I /tmp/pcoarea_v2_scripts/flat_check_pure.py (numerical test of flat_jacobian)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/ProdL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/PCoareaC1V2ScopeGen.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/PCoareaC1V2AssemblyGen.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/PCoareaC1V2Refs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/PCoareaC1V2Inst.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/PCoareaC1V2Tsum.lean`

Snapshot revisions: project d09bc8a, Mathlib 25730c7c, plus the pinned simongmt package (lake-packages-25730c7c). The snapshot Contract.lean is identical to the workspace one. No-match results: Mathlib has no co-area formula ('coarea': no file) and no nonlinear area formula; neither the project nor SimonGMT has a parametric co-area formula or any 'pcoarea_' declaration. So the six children are new obligations. Every library fact the children cite exists in this snapshot, and Lean #check confirms each one with the stated form: (a) SimonGMT weighted_area_formula_lipschitzOn_fiberSum, which needs no rank hypothesis; ae_fderivWithin_eq_of_lipschitz_extension; exists_lipschitz_extension_finiteDimensional; weightedAreaFiberSum; euclideanHausdorffMeasure_image_le_of_lipschitzOn; coareaLinearJacobian_eq_zero_iff; coarea_kernel_finrank; coareaHorizontalLinear_normDet; normDet_adjoint_of_finrank_eq; coareaCoordinates_symm_apply. (b) Mathlib normDet_comp_of_finrank_eq, normDet_eq_norm_det_toMatrix, normDet_codRestrict, normDet_eq_abs_det, LinearIsometry.normDet_eq_one, ContinuousLinearMap.normDet_sq, OrthonormalBasis.prod(_apply), Matrix.det_fromBlocks_zero₁₂. (c) ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, restrOpen, ContinuousLinearEquiv.isOpen, ContDiffOn.exists_lipschitzOnWith, measurable_fderiv. (d) WithLp.volume_preserving_toLp, LinearIsometryEquiv.measurePreserving, which holds for the same volume on WithLp 2 (Rn m × Rn k); lintegral_image_eq_lintegral_abs_det_fderiv_mul, valid for an arbitrary integrand; MeasurableSet.image_of_continuousOn_injOn; isOpen_iUnion_countable; lintegral_iUnion; lintegral_tsum; lintegral_prod; Measurable.lintegral_prod_right'; and AEMeasurable.ennreal_tsum, a deprecated alias of AEMeasurable.tsum. Validation results: (1) All six frozen child types pass lean_contract.validate_lean_statement and elaborate in the comparator's replayed Contract scope. (2) With the six child types and the sibling's frozen dag.json type as sorry stubs, the parent assembly proves the exact frozen parent type. Its axioms are propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only. (3) None of the six names collides with the 116 current DAG nodes.
