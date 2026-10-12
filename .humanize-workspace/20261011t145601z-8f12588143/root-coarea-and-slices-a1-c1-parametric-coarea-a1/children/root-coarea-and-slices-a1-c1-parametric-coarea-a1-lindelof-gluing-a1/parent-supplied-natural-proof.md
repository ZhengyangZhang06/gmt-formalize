# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.lindelof_gluing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 0(b), 0(c) and 5 (Lusin–Souslin images, countable additivity, Lindelöf). The critical piece is described by an arbitrary set Z, so no measurability of the critical set is needed.

1. (Lindelöf.) For each p ∈ D \ Z choose an open O_p ∋ p as in (Loc). Since ℝⁿ is second countable, Mathlib isOpen_iUnion_countable gives a countable subfamily of (O_p)_{p∈D\Z} with the same union. List it as a sequence (O'_j)_{j∈ℕ}, padding with ∅ if it is finite or empty. Then D \ Z ⊆ ⋃_{p∈D\Z} O_p = ⋃_j O'_j. Every Borel subset of D ∩ O'_j is good: by (Loc) if O'_j = O_p; and if O'_j = ∅ the only subset is ∅, which is good by (Crit) because ∅ ⊆ Z (or directly, since all three integrals vanish).

2. (Disjoint pieces.) Fix a Borel B ⊆ D and a Borel φ. Let B_0 := B \ ⋃_j O'_j and B_{j+1} := (B ∩ O'_j) \ ⋃_{i<j} O'_i. The B_t (t ∈ ℕ) are Borel (the O'_j are open), pairwise disjoint, and ⋃_t B_t = B.
- B_0 ⊆ B ⊆ D and B_0 ⊆ Z, since a point of B_0 outside Z would lie in D \ Z ⊆ ⋃_j O'_j. So B_0 is good by (Crit).
- B_{j+1} ⊆ D ∩ O'_j is good by step 1.

3. (Slices are Borel and disjoint.) For every y and t, G⁻¹{y} is closed (G is continuous), so B_t ∩ G⁻¹{y} is a Borel subset of D. ψ is continuous and injective on it, so ψ(B_t ∩ G⁻¹{y}) is Borel (Lusin–Souslin, Mathlib MeasurableSet.image_of_continuousOn_injOn; ℝⁿ is Polish). For fixed y these sets are pairwise disjoint in t, because ψ is injective on D and the B_t are disjoint. Their union is ψ(B ∩ G⁻¹{y}) (Set.image_iUnion, Set.iUnion_inter). Hence by lintegral_iUnion, for every y:
f(y) := ∫_{ψ(B∩G⁻¹{y})} φ dHᵏ = Σ_t f_t(y), where f_t(y) := ∫_{ψ(B_t∩G⁻¹{y})} φ dHᵏ.

4. (Measurability.) Each f_t is Lᵐ-a.e. measurable because B_t is good. Hence f = Σ_t f_t is Lᵐ-a.e. measurable (AEMeasurable.ennreal_tsum; in this Mathlib it is a deprecated alias that still compiles, its replacement being AEMeasurable.tsum).

5. (Identity.)
∫_B φ(ψ(u))·w(u) du
= Σ_t ∫_{B_t} φ(ψ(u))·w(u) du (lintegral_iUnion over the disjoint Borel sets B_t, valid for an arbitrary integrand)
= Σ_t ∫ f_t dLᵐ (each B_t is good)
= ∫ Σ_t f_t dLᵐ (lintegral_tsum, the f_t being a.e. measurable)
= ∫ f dLᵐ (step 3).
Hence B is good. ∎

## Key steps

1. Lindelöf: countably many good open sets O'_j (padded with ∅) cover D \ Z.
2. Disjoint Borel pieces B_0 ⊆ D ∩ Z and B_{j+1} ⊆ D ∩ O'_j, each of them good.
3. The slices ψ(B_t ∩ G⁻¹{y}) are Borel (Lusin–Souslin) and disjoint (injectivity), so the inner integral is Σ_t f_t(y).
4. AEMeasurable.ennreal_tsum for measurability; lintegral_iUnion on the left and lintegral_tsum on the right.

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
