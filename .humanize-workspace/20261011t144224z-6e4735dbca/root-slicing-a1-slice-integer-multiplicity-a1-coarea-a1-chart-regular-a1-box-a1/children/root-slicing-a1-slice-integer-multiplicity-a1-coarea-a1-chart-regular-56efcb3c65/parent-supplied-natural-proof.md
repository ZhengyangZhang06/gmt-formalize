# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.integrand_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k) with inner product ⟨·,·⟩; e_i := EuclideanSpace.single i 1; D := fderiv ℝ. Let S′ := B ∩ χ⁻¹(S), 𝒥(y) := √det(⟨DΦ(χ y)(Dχ(y)e_{i+1}), DΦ(χ y)(Dχ(y)e_{j+1})⟩)_{i,j<m} and F̃ := S′.indicator (y ↦ g(Φ(χ y))·ofReal 𝒥(y)). Measurable means Borel measurable.

This is step 8 of the parent proof (slicing_im_creg_box_coarea), where F̃ is the integrand handed to Tonelli. No sibling lemma is used. Mathlib results used: ContinuousOn.measurable_piecewise, measurable_fderiv_apply_const, ContDiff.continuous_fderiv_apply, continuous_inner, Continuous.matrix_det, Measurable.of_eval and Measurable.indicator. Lean note: the frozen import closure has neither Measurable.inner nor a MeasurableSpace instance on Matrix. So inner products are handled through the continuous map (u, u′) ↦ ⟨u, u′⟩ composed with a measurable pair, and the determinant through the entry function in Fin m → Fin m → ℝ.

1. (Measurable extension of χ.) χ is C¹ on B, hence continuous on B (ContDiffOn.continuousOn). Let χ̃ := B.piecewise χ 0, which is χ on B and 0 off B. It is Borel measurable by ContinuousOn.measurable_piecewise, since χ is continuous on the measurable set B and the constant 0 is continuous on Bᶜ.
2. (S′ is Borel.) Since χ̃ = χ on B, S′ = B ∩ χ⁻¹(S) = B ∩ χ̃⁻¹(S). This set is Borel because B is open and χ̃ is measurable.
3. (Replace χ by χ̃ in the integrand.) For k < m+1 let a_k(y) := DΦ(χ̃ y)(Dχ(y)e_k), and for i, j < m let M(y)_{ij} := ⟨a_{i+1}(y), a_{j+1}(y)⟩. Put F̂(y) := g(Φ(χ̃ y))·ofReal √det M(y). Only the outer occurrences of χ become χ̃; Dχ(y) is kept. For y ∈ S′ ⊆ B, χ̃(y) = χ(y), so the integrands of F̃ and of S′.indicator F̂ agree on S′. Set.indicator_congr gives F̃ = S′.indicator F̂. By Measurable.indicator and step 2, it suffices to show that F̂ is measurable.
4. (The factor g∘Φ∘χ̃.) Φ is C¹, hence continuous and measurable. χ̃ is measurable (step 1) and g is measurable, so y ↦ g(Φ(χ̃ y)) is measurable.
5. (The vectors a_k.) Fix k. Then y ↦ Dχ(y)e_k is measurable by measurable_fderiv_apply_const, which holds for any map χ between finite-dimensional spaces. Because Φ is C¹, the map (x, u) ↦ DΦ(x)u on ℝ^{m+1} × ℝ^{m+1} is continuous (ContDiff.continuous_fderiv_apply with 1 ≠ 0), hence Borel measurable; the product of these second-countable spaces carries the product Borel σ-algebra. Composing it with the measurable map y ↦ (χ̃ y, Dχ(y)e_k) shows that a_k is measurable.
6. (The entries.) The inner product (u, u′) ↦ ⟨u, u′⟩ on ℝ^P × ℝ^P is continuous (continuous_inner), hence measurable. Composing it with y ↦ (a_{i+1}(y), a_{j+1}(y)) shows that y ↦ M(y)_{ij} is measurable for all i, j < m.
7. (Determinant, square root, ofReal.) The map y ↦ (M(y)_{ij})_{i,j} into Fin m → Fin m → ℝ is measurable (Measurable.of_eval, applied twice). The function N ↦ det(Matrix.of N) on Fin m → Fin m → ℝ is continuous, because det is a polynomial in the entries (Continuous.matrix_det applied to the continuous identity); hence it is measurable. So y ↦ det M(y) is measurable. Real.sqrt is continuous and ENNReal.ofReal is measurable, so y ↦ ofReal √det M(y) is measurable. For m = 0 the matrix is empty with determinant 1, and the same argument applies.
8. (Conclusion.) F̂ is the product of the measurable [0,∞]-valued functions of steps 4 and 7, hence measurable (Measurable.mul). By step 3, F̃ = S′.indicator F̂ is measurable. ∎

## Key steps

1. χ̃ := B.piecewise χ 0 is Borel (ContinuousOn.measurable_piecewise), so S′ = B ∩ χ̃⁻¹(S) is Borel.
2. On S′ replace the outer χ by χ̃ (Set.indicator_congr) and reduce to measurability of F̂ (Measurable.indicator).
3. a_k(y) := DΦ(χ̃ y)(Dχ(y)e_k) is measurable: measurable_fderiv_apply_const plus the continuous (x,u) ↦ DΦ(x)u (ContDiff.continuous_fderiv_apply).
4. Inner products via continuous_inner; entries via Measurable.of_eval; det via Continuous.matrix_det on Fin m → Fin m → ℝ; then √, ofReal, and the product with g∘Φ∘χ̃.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1-box-a1/{parent-child-handoff.json,parent-supplied-plan.md} and nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/decomposition-v1.json`
- `python3 scans of dag.json: status of the box siblings (jacobian, tonelli: decomposing); byte comparison of title/statement/lean_statement of the accepted node root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1; lean_name collision scan for slicing_im_creg_box_* (none); depth histogram (max 5) and max_depth 6 from swarm-project.json`
- `git show 9fc44225b304fca8af9dead3256575ef03818d1e:GMT/Ch06/Submission.lean (accepted lpf_raf_* block, lines 362–655, plus import Poincare.SimonGMT.Chapter02.AreaDomain)`
- `grep -rn 'slicing_im_creg|chart_change_of_variables|lintegral_image_eq_lintegral_abs_det_fderiv_mul' local-references/197bdd4b88278494/project (no match)`
- `grep in pinned Mathlib: lintegral_image_eq_lintegral_abs_det_fderiv_mul, MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurable_piecewise, Continuous.measurable2, measurable_fderiv_apply_const, ContDiff.continuous_fderiv_apply, ContDiffOn.differentiableOn, ContDiff.differentiable, Measurable.of_eval_matrix and the Matrix MeasurableSpace instance, Measurable.inner, setLIntegral_congr_fun, lintegral_indicator, LipschitzOnWith.comp, EuclideanSpace.equiv = PiLp.continuousLinearEquiv (coe = ofLp, symm = toLp 2), Fin.cons_self_tail, Measurable.enorm, ofReal_norm, LinearMap.toContinuousLinearMap, HasFDerivAt.unique, HasFDerivAt.congr_of_eventuallyEq`
- `grep -n '^theorem' simongmt Poincare/SimonGMT/Chapter02/Coarea{Linear,LinearAlgebra,Projection}.lean (only linear co-area; no C¹ chart co-area)`
- `python3: contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the four child types`
- `lake env lean /tmp/box-decomp/Stmts.lean (all statements elaborate) and /tmp/box-decomp/Assembly.lean (frozen box type from 6 stubs; sorryAx only from stubs)`
- `lake env lean /tmp/box-decomp/{Meas,Bulk,Slice}.lean (Meas axiom-clean; Bulk and Slice sorryAx only from the area_formula stub); probes show Measurable.inner, Measurable.of_eval_matrix and MeasurableSpace (Matrix ..) unavailable after import GMT.Ch06.Submission`
- `lake env lean /tmp/box-decomp/Integrated.lean (accepted 9fc44225 block + three children + box assembly; children propext, Classical.choice, Quot.sound; box sorryAx only from jacobian/tonelli stubs)`
- `independent reviewer re-ran the checks in /tmp/box-review-7q3k (comparator wrapper form, byte comparisons, variant with jacobian/tonelli as named axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1-box-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1-box-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Matrix/MeasurableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/box-decomp/preamble.lean`
- `/tmp/box-decomp/Stmts.lean`
- `/tmp/box-decomp/Assembly.lean`
- `/tmp/box-decomp/Meas.lean`
- `/tmp/box-decomp/Bulk.lean`
- `/tmp/box-decomp/Slice.lean`
- `/tmp/box-decomp/Integrated.lean`
- `/tmp/box-decomp/draft/subproblems_final.json`

The snapshot (project d8d46c95, Mathlib 25730c7c) has no slicing_im_creg_* declaration, and SimonGMT has only linear co-area, so the box needs the DAG's own lemmas. The comparator-accepted lpf_raf_chart_change_of_variables (candidate 9fc44225) is reused by name with a byte-identical type. jacobian and tonelli are not yet accepted, so the new children avoid them and only the parent assembly uses them. Mathlib supplies change of variables, Lusin–Souslin, piecewise measurability, fderiv measurability and C¹ joint continuity. The frozen import closure lacks Measurable.inner and a Matrix MeasurableSpace instance, so integrand_measurable uses continuous_inner and Continuous.matrix_det on Fin m → Fin m → ℝ. Lean checks in the exact comparator scope: all child types elaborate and validate, the parent type follows from them plus jacobian and tonelli, and the three new children are fully proved (Integrated.lean, standard axioms only).
