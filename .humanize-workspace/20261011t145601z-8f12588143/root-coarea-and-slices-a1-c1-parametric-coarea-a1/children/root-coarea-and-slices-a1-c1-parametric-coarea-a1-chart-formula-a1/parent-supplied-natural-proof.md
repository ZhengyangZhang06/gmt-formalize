# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (slices of an implicit-function chart) and step 4 (regular part: area formula on the slices, Tonelli on ℝᵐ × ℝᵏ, change of variables), stated for an arbitrary C¹ chart Φ whose first component is G. It uses the siblings c1_injective_area (injective area formula on the slices) and flat_jacobian (Jacobian identity).

Notation:
- O := source(Φ) and Ω := target(Φ), both open; Φ⁻¹ := Φ.symm.
- T_u := DΦ(u) for u ∈ O, and Λ_w := DΦ⁻¹(w) for w ∈ Ω.
- j : ℝᵏ → P, j(z) := toLp(0, z).
- For y ∈ ℝᵐ, ι_y : ℝᵏ → P, ι_y(z) := toLp(y, z) = toLp(y, 0) + j(z); it is affine with derivative j.
- ρ := ψ∘Φ⁻¹ : P → ℝᴺ.

1. (Derivatives.) Φ is C¹ on the open set O and Φ⁻¹ is C¹ on the open set Ω, so both are differentiable there; Φ maps O into Ω and Φ⁻¹ maps Ω into O. Let u ∈ O and w := Φ(u).
- Since Φ⁻¹∘Φ = id on the neighbourhood O of u, the chain rule gives Λ_w∘T_u = id_{ℝⁿ}.
- Since Φ∘Φ⁻¹ = id on the neighbourhood Ω of w, T_u∘Λ_w = id_P.
So T_u is bijective with inverse Λ_{Φ(u)}. Since G = fst∘Φ on the neighbourhood O of u, DG(u) = fst∘T_u (Filter.EventuallyEq.fderiv_eq, WithLp.fstL), i.e. (T_u v).fst = DG(u)v. Moreover ρ is C¹ on Ω (ContDiffOn.comp, since Φ⁻¹(Ω) ⊆ O), and Dρ(w) = Dψ(Φ⁻¹ w)∘Λ_w for w ∈ Ω; in particular Dρ(Φ u) = Dψ(u)∘Λ_{Φ(u)}.

2. (Slices.) B' := Φ(B) ⊆ Ω is Borel, because Φ is continuous and injective on the Borel set B (Lusin–Souslin, MeasurableSet.image_of_continuousOn_injOn). For y ∈ ℝᵐ put Ω_y := ι_y⁻¹(Ω) (open), B'_y := ι_y⁻¹(B') ⊆ Ω_y (Borel), and χ_y := ρ∘ι_y : ℝᵏ → ℝᴺ.
(a) ψ(B ∩ G⁻¹{y}) = χ_y(B'_y). Suppose u ∈ B and G(u) = y, and put z := (Φ u).snd. Then Φ(u) = toLp((Φ u).fst, z) = toLp(G u, z) = ι_y(z) ∈ B', so z ∈ B'_y, and χ_y(z) = ψ(Φ⁻¹(Φ u)) = ψ(u). Conversely, if z ∈ B'_y then ι_y(z) = Φ(u) for some u ∈ B, so G(u) = (Φ u).fst = y and χ_y(z) = ψ(Φ⁻¹(Φ u)) = ψ(u).
(b) χ_y is C¹ on Ω_y, since ι_y is affine and maps Ω_y into Ω and ρ is C¹ on Ω. Its derivative is Dχ_y(z) = Dρ(ι_y z)∘j.
(c) χ_y is injective on Ω_y: ι_y is injective, Φ⁻¹ is injective on Ω, and ψ is injective on O ⊇ Φ⁻¹(Ω).

3. (Area formula on every slice.) Apply the sibling c1_injective_area with V := Ω_y, χ := χ_y, S := B'_y and the Borel φ. For every y ∈ ℝᵐ,
∫_{ψ(B∩G⁻¹{y})} φ dHᵏ = ∫_{B'_y} φ(χ_y z)·ofReal(normDet(Dχ_y z)) dz.
Define F : P → [0, ∞] by F(w) := 1_{B'}(w)·φ(ρ(w))·ofReal(normDet(Dρ(w)∘j)). For z ∈ B'_y the integrand equals F(ι_y z) by 2(b), and F(ι_y z) = 0 for z ∉ B'_y. Hence (lintegral_indicator, B'_y Borel), for every y:
(*) ∫_{ψ(B∩G⁻¹{y})} φ dHᵏ = ∫_{ℝᵏ} F(toLp(y, z)) dz.

4. (F is Borel.)
- w ↦ Dρ(w) is Borel (Mathlib measurable_fderiv, which needs no hypothesis on ρ), and Q ↦ Q∘j is continuous.
- Q ↦ normDet(Q) is continuous on ℝᵏ →L ℝᴺ: normDet(Q) = √det(Q*∘Q) by ContinuousLinearMap.normDet_sq and normDet ≥ 0, and the adjoint, composition and ContinuousLinearMap.continuous_det are continuous. So w ↦ ofReal(normDet(Dρ(w)∘j)) is Borel.
- ρ is continuous on the open set Ω ⊇ B', so ρ̃ := Ω.piecewise ρ (const) is Borel (ContinuousOn.measurable_piecewise) and equals ρ on B'.
Hence F = 1_{B'}·(φ∘ρ̃)·ofReal(normDet(Dρ(·)∘j)) is Borel.

5. (Tonelli; first claim.) toLp : ℝᵐ × ℝᵏ → P is a measurable equivalence carrying Lᵐ ⊗ Lᵏ to the volume of P (Mathlib WithLp.volume_preserving_toLp). So F∘toLp is Borel, y ↦ ∫ F(toLp(y, z)) dz is Borel (Measurable.lintegral_prod_right'), and
∫_P F = ∫_{ℝᵐ×ℝᵏ} F∘toLp = ∫_{ℝᵐ}∫_{ℝᵏ} F(toLp(y, z)) dz dy (MeasurePreserving.lintegral_comp, lintegral_prod).
By (*), y ↦ ∫_{ψ(B∩G⁻¹{y})} φ dHᵏ coincides everywhere with a Borel function. So it is measurable, in particular Lᵐ-a.e. measurable (first claim). Moreover
∫_{ℝᵐ}∫_{ψ(B∩G⁻¹{y})} φ dHᵏ dy = ∫_P F = ∫_{B'} h, where h(w) := φ(ρ w)·ofReal(normDet(Dρ(w)∘j)) (lintegral_indicator).

6. (Change of variables.) Let e : P → ℝⁿ be a linear isometric equivalence (finrank P = m + k = finrank ℝⁿ; e.g. via reindexed orthonormal-basis coordinates). e preserves volume (LinearIsometryEquiv.measurePreserving), so ∫_{B'} h = ∫_{e(B')} h∘e⁻¹ (MeasurePreserving.setLIntegral_comp_emb). The map e∘Φ is injective on the Borel set B and has derivative e∘T_u at every u ∈ B (HasFDerivAt.hasFDerivWithinAt). So Mathlib lintegral_image_eq_lintegral_abs_det_fderiv_mul, which is valid for an arbitrary integrand, gives
∫_{e(Φ(B))} h∘e⁻¹ = ∫_B ofReal|det(e∘T_u)|·h(Φ(u)) du.
Here |det(e∘T_u)| = normDet(e∘T_u) (LinearMap.normDet_eq_abs_det) = normDet(e)·normDet(T_u) (normDet_comp_of_finrank_eq) = normDet(T_u) (LinearIsometry.normDet_eq_one). Also h(Φ u) = φ(ψ u)·ofReal(normDet(Dψ(u)∘Λ_{Φ(u)}∘j)) by step 1, since Φ⁻¹(Φ u) = u.

7. (Jacobian identity; second claim.) For u ∈ B apply the sibling flat_jacobian with A := Dψ(u), Γ := DG(u), T := T_u and E := Λ_{Φ(u)}∘j. Its hypotheses hold: T_u is bijective and (T_u v).fst = DG(u)v by step 1, and T_u(E z) = (T_u∘Λ_{Φ(u)})(j z) = j z = toLp(0, z). It yields
normDet(Dψ(u)∘Λ_{Φ(u)}∘j)·normDet(T_u) = normDet(Dψ(u)∘ι_{K(u)})·normDet(DG(u)*) = J(u).
As all factors are ≥ 0 (ENNReal.ofReal_mul), ofReal(normDet(T_u))·h(Φ u) = φ(ψ(u))·ofReal(J(u)) for u ∈ B. By steps 5–6 and setLIntegral_congr_fun (B is Borel):
∫_{ℝᵐ}∫_{ψ(B∩G⁻¹{y})} φ dHᵏ dy = ∫_B φ(ψ(u))·ofReal(J(u)) du. ∎

## Key steps

1. DΦ(u) is invertible with inverse DΦ⁻¹(Φ u), and DG(u) = fst∘DΦ(u) on the source.
2. Slices: ψ(B ∩ G⁻¹{y}) = χ_y(B'_y), where χ_y = ψ∘Φ⁻¹∘toLp(y,·) is C¹ and injective on the open Ω_y and B' = Φ(B) is Borel.
3. Sibling c1_injective_area on every slice: the inner integral is ∫ F(toLp(y, z)) dz with F Borel on P.
4. Tonelli through WithLp.volume_preserving_toLp: the inner integral is measurable in y, and ∫∫ = ∫_{Φ(B)} h.
5. Change of variables for e∘Φ (e a volume-preserving isometry): ∫_{Φ(B)} h = ∫_B normDet(DΦ(u))·h(Φ u) du.
6. Sibling flat_jacobian: normDet(Dψ(u)∘DΦ⁻¹(Φu)∘j)·normDet(DΦ(u)) = J(u).

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
