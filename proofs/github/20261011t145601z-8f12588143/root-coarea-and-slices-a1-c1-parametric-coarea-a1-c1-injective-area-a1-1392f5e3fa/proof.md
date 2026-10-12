# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.c1_injective_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 4, the paragraph 'In detail'. This is the injective area formula on the k-dimensional parameter domain: Simon Ch. 2, (3.2) and its weighted form (3.5), cf. (4.13). The Lipschitz version of the area formula is used because no rank condition on Dχ is available. Lemma names refer to Mathlib 25730c7c and the pinned simongmt package (namespace Poincare.SimonGMT.Chapter02).

1. (Trivial case.) If V = ∅ then S = ∅ and both sides are 0. Assume V ≠ ∅.

2. (Countable cover by good balls.) For each z ∈ V choose r_z > 0 with ball(z, 2r_z) ⊆ V (V is open); then closedBall(z, r_z) ⊆ V. The open balls ball(z, r_z), z ∈ V, are contained in V and cover V. Since ℝᵏ is second countable, Mathlib isOpen_iUnion_countable gives a countable set T of centres in V with ⋃_{z∈T} ball(z, r_z) = ⋃_{z∈V} ball(z, r_z) = V. Enumerate these balls as b_q = ball(z_q, r_q), q ∈ ℕ, repeating a ball if T is finite. Then V = ⋃_q b_q and closedBall(z_q, r_q) ⊆ V for every q.

3. (Lipschitz bounds.) closedBall(z_q, r_q) is convex and compact (ℝᵏ is proper), and χ is C¹ on it (ContDiffOn.mono). Mathlib ContDiffOn.exists_lipschitzOnWith gives K_q such that χ is K_q-Lipschitz on closedBall(z_q, r_q), hence on b_q and on every subset of b_q.

4. (Disjoint Borel pieces.) Let S_q := (S ∩ b_q) \ ⋃_{q'<q} b_{q'} (Mathlib disjointed applied to q ↦ S ∩ b_q). The S_q are Borel and pairwise disjoint, S_q ⊆ b_q ⊆ V, and ⋃_q S_q = S: each z ∈ S ⊆ V lies in some b_q, and for the least such q we have z ∈ S_q.

5. (Borel, disjoint images.) χ is continuous on V. If R ⊆ V is Borel, then χ is continuous and injective on the Borel subset R of the Polish space ℝᵏ, so χ(R) is Borel (Lusin–Souslin: Mathlib MeasurableSet.image_of_continuousOn_injOn). Hence χ(S) and every χ(S_q) are Borel. The χ(S_q) are pairwise disjoint because χ is injective on V and the S_q are disjoint, and χ(S) = ⋃_q χ(S_q) (Set.image_iUnion).

6. (Lipschitz area formula on one piece.) Fix q. The weight φ∘χ is a.e.-measurable for Lebesgue measure restricted to S_q: χ is continuous on the Borel set S_q, so ContinuousOn.aemeasurable makes it a.e.-measurable there, and φ is Borel (Measurable.comp_aemeasurable). Apply SimonGMT weighted_area_formula_lipschitzOn_fiberSum with s := S_q (Borel, hence null-measurable), the K_q-Lipschitz bound of χ on S_q, and w := φ∘χ. Together with finrank ℝ ℝᵏ = k (finrank_euclideanSpace_fin) this gives
∫ weightedAreaFiberSum S_q χ (φ∘χ) dHᵏ = ∫_{S_q} ofReal(areaJacobianWithin χ S_q z)·φ(χ(z)) dz,
where areaJacobianWithin χ S_q z = normDet(fderivWithin ℝ χ S_q z).

7. (Fibre sums of an injective map.) By definition, weightedAreaFiberSum S_q χ (φ∘χ) y is the sum of φ(χ(z)) over the fibre {z ∈ S_q : χ(z) = y}. Since χ is injective on S_q, this fibre is empty if y ∉ χ(S_q) and is a single point z with χ(z) = y if y ∈ χ(S_q). Hence the fibre sum equals 1_{χ(S_q)}(y)·φ(y) for every y. This InjOn version is proved directly; SimonGMT's lemma for globally injective maps is not needed. Since χ(S_q) is Borel (step 5), the left side of step 6 equals ∫_{χ(S_q)} φ dHᵏ (lintegral_indicator).

8. (Within derivative versus derivative.) Apply SimonGMT exists_lipschitz_extension_finiteDimensional to the Lipschitz bound of χ on b_q: there is a globally Lipschitz g : ℝᵏ → ℝᴺ with g = χ on b_q. By SimonGMT ae_fderivWithin_eq_of_lipschitz_extension (s := S_q, using g = χ on S_q), fderivWithin ℝ χ S_q z = Dg(z) for Lebesgue-a.e. z ∈ S_q. For z ∈ S_q, the open ball b_q is a neighbourhood of z on which g = χ, so Dg(z) = Dχ(z) (Filter.EventuallyEq.fderiv_eq). Therefore areaJacobianWithin χ S_q z = normDet(Dχ(z)) for a.e. z ∈ S_q. Steps 6–7, lintegral_congr_ae (for Lebesgue measure restricted to S_q) and commutativity of multiplication in [0, ∞] give
∫_{χ(S_q)} φ dHᵏ = ∫_{S_q} φ(χ(z))·ofReal(normDet(Dχ(z))) dz.

9. (Summation.) Set integrals are countably additive over pairwise disjoint Borel sets (Mathlib lintegral_iUnion, valid for an arbitrary integrand). With steps 4, 5 and 8 this gives
∫_{χ(S)} φ dHᵏ = Σ_q ∫_{χ(S_q)} φ dHᵏ = Σ_q ∫_{S_q} φ(χ(z))·ofReal(normDet(Dχ(z))) dz = ∫_S φ(χ(z))·ofReal(normDet(Dχ(z))) dz. ∎

## Key steps

1. Trivial if V = ∅. Lindelöf: V = ⋃ b_q with closed balls in V, and χ is Lipschitz on each closed ball (ContDiffOn.exists_lipschitzOnWith).
2. Disjoint Borel pieces S_q ⊆ b_q with ⋃ S_q = S. Lusin–Souslin: the χ(S_q) are Borel, and pairwise disjoint by injectivity.
3. SimonGMT weighted_area_formula_lipschitzOn_fiberSum on each S_q with weight φ∘χ.
4. Injectivity on S_q: the fibre sum is 1_{χ(S_q)}·φ, so the left side is ∫_{χ(S_q)} φ dHᵏ.
5. Lipschitz extension from b_q plus ae_fderivWithin_eq_of_lipschitz_extension: areaJacobianWithin = normDet(Dχ) a.e. on S_q.
6. Sum over q with lintegral_iUnion on both sides.

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
