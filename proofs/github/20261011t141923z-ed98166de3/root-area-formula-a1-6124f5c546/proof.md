# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2 §3, 3.1-3.5 and the printed arguments (pp. 53-54). Erratum applied (GMT/Ch02/README.md and the SimonGMT ledger): in 3.4 the printed target measure dH^m(y) is corrected to dH^n(y) (as printed in 3.5); with H^m, m > n, the left side would be 0 or ∞. The printed text proves only the linear case 3.1 and refers to [Har79]/[Fed69] for 3.2; the general nonlinear statement is available as kernel-checked theorems of the pinned SimonGMT library (Poincare/SimonGMT/Chapter02/AreaDomain.lean, axioms propext, Classical.choice, Quot.sound only), so the remaining work is to identify the frozen notions with the library ones.

PART I. PRINTED ARGUMENT (cleaned transcription).
3.1. If L is a linear map ℝⁿ → ℝ^{n+k}, k ≥ 0, then L(ℝⁿ) ⊆ F with F an n-dimensional subspace; choosing an orthogonal q with q(F) = ℝⁿ × {0} and p(x,y) = x, p∘q∘L : ℝⁿ → ℝⁿ and Lⁿ((p∘q∘L)(A)) = |det(p∘q∘L)|Lⁿ(A); since (p∘q∘L)*(p∘q∘L) = L*∘q*∘(p*∘p)∘q∘L = L*∘L, |det(p∘q∘L)| = √det(L*∘L), and since q is an isometry, H^n(L(A)) = √det(L*∘L) H^n(A), A ⊆ ℝⁿ.
3.2. More generally, given a 1:1 Lipschitz f : A → ℝ^m (A ⊆ ℝⁿ Lebesgue measurable, m ≥ n), by an approximation argument based on the linear case 3.1 (see [Har79] or [Fed69]), H^n(f(A)) = ∫_A Jf dH^n, where Jf(y) = √det(df_y* ∘ df_y) (3.3).
3.4. If f is not 1:1 we have the general area formula (which follows quite easily from 3.2) ∫_{ℝ^m} H⁰(f⁻¹(y) ∩ A) dH^n(y) = ∫_A Jf dLⁿ [erratum: dH^n, not dH^m], where H⁰(f⁻¹(y) ∩ A) is the multiplicity N(f,y).
3.5. More generally, if h is a non-negative H^n-measurable function on A, then ∫ Σ_{x∈f⁻¹(y)} h(x) dH^n(y) = ∫_A h Jf dH^n. This follows directly from 3.4 if we approximate h by simple functions.

PART II. COMPLETE PROOF OF THE FROZEN STATEMENT AreaFormula.
Let n ≤ m, A ⊆ ℝⁿ with NullMeasurableSet A volume, f : ℝⁿ → ℝᵐ with LipschitzOnWith K f A (ℝ^d = EuclideanSpace ℝ (Fin d)). Write L_x := fderivWithin ℝ f A x : ℝⁿ →L[ℝ] ℝᵐ.

1. Library theorems used (namespace Poincare.SimonGMT.Chapter02, with E = ℝⁿ, F = ℝᵐ, s = A, any K):
 (a) weighted_area_formula_lipschitzOn_fiberSum (hs : NullMeasurableSet s volume) (hL : LipschitzOnWith K f s) (hw : AEMeasurable w (volume.restrict s)) : ∫⁻ y, weightedAreaFiberSum s f w y ∂μHE[finrank ℝ E] = ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) * w x ∂volume;
 (b) aemeasurable_weightedAreaFiberSum_lipschitzOn (same hypotheses) : AEMeasurable (weightedAreaFiberSum s f w) μHE[finrank ℝ E];
 (c) area_formula_lipschitzOn_multiplicity (hs) (hL) : ∫⁻ y, areaMultiplicity s f y ∂μHE[finrank ℝ E] = ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) ∂volume.
 Mathematically these are 3.2-3.5: the library proves them by extending f to a global Lipschitz map (componentwise McShane extension), Rademacher, the approximation of the Lipschitz map on countably many Borel pieces by linear maps (Federer's argument) with the linear case 3.1, and the identification of fderivWithin with the derivative of the extension at a.e. point of A (density points).
2. Dimension: finrank ℝ (EuclideanSpace ℝ (Fin n)) = n (Mathlib finrank_euclideanSpace_fin), so μHE[finrank ℝ ℝⁿ] = μHE[n] after rewriting.
3. Jacobian: areaJacobianWithin f A x = (L_x).normDet (definition, via the underlying linear map). For any linear map L between finite-dimensional real inner product spaces, normDet L ≥ 0 and (normDet L)² = det(L* ∘ L) (Mathlib LinearMap.normDet_nonneg, LinearMap.normDet_sq; also SimonGMT areaJacobianAt_eq_sqrt_det_adjoint_comp), hence normDet L = √det(L*∘L). The continuous-linear determinant of ContinuousLinearMap.adjoint L_x ∘L L_x equals the linear determinant of the corresponding linear map, so areaJacobian (fderivWithin ℝ f A x) = Real.sqrt((ContinuousLinearMap.adjoint L_x ∘L L_x).det) = areaJacobianWithin f A x for every x.
4. Fibers: areaFiber A f y = {x // x ∈ A ∧ f x = y}, while ↥(A ∩ f⁻¹'{y}) = {x // x ∈ A ∩ f⁻¹'{y}}; membership x ∈ A ∩ f⁻¹'{y} unfolds definitionally to x ∈ A ∧ f x = y. Hence weightedAreaFiberSum A f h y = ∑' x : areaFiber A f y, h x.1 = ∑' x : ↥(A ∩ f⁻¹'{y}), h x (equal index types, or transport along the obvious equivalence of subtypes, Equiv.tsum_eq). Likewise areaMultiplicity A f y = ∑' _ : ↥(A ∩ f⁻¹'{y}), 1 = ENat.toENNReal (A ∩ f⁻¹'{y}).encard (Mathlib ENNReal.tsum_set_one) = fiberCount A f y.
5. (3.4) By 1(c), 2, 3, 4: ∫⁻ y, fiberCount A f y ∂μHE[n] = ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderivWithin ℝ f A x)) ∂volume. This is the first conjunct (the corrected 3.4).
6. (3.5) Let h : ℝⁿ → [0,∞] be AEMeasurable for volume restricted to A. By 1(b), 2, 4 the function y ↦ ∑' x : ↥(A ∩ f⁻¹'{y}), h x is AEMeasurable for μHE[n]; by 1(a), 2, 3, 4 its μHE[n]-integral equals ∫⁻ x in A, ENNReal.ofReal(areaJacobian(fderivWithin ℝ f A x)) * h x ∂volume = ∫⁻ x in A, h x * ENNReal.ofReal(areaJacobian(fderivWithin ℝ f A x)) ∂volume (commutativity of multiplication in ENNReal). This is the second conjunct (3.5; here Hⁿ on the source ℝⁿ is volume, as recorded in the contract).
7. The hypothesis n ≤ m is not needed by the library statements (it only reflects the printed setting). Steps 5 and 6 prove AreaFormula.

## Key steps

1. Printed route: linear case 3.1, approximation for injective Lipschitz maps 3.2, multiplicity 3.4, simple-function approximation 3.5.
2. Invoke the kernel-checked SimonGMT theorems weighted_area_formula_lipschitzOn_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitzOn and area_formula_lipschitzOn_multiplicity.
3. Identify finrank ℝ ℝⁿ = n, areaJacobianWithin = normDet = √det(L*L) = areaJacobian, weightedAreaFiberSum = tsum over A ∩ f⁻¹{y}, areaMultiplicity = encard = fiberCount, and commute the product.

## Reference use

### local-project

Queries:
- `rg -n 'def BVCompactness' -A 10 project/GMT/Ch02/Contract.lean`
- `rg -n 'bvVariationOn|IsLocallyBV' project/GMT/Ch02/README.md`
- `rg -n 'theorem (IsOpen.measure_pos|IsCompact.measure_lt_top|setLIntegral_const|lintegral_add_right|le_div_iff_mul_le|div_lt_top)' mathlib/Mathlib`
- `rg -n 'theorem (_root_.)?(IsOpen.)?measure_pos' mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean; rg -n 'theorem (_root_.)?(IsCompact.)?measure_lt_top' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/*.lean`
- `rg -n 'theorem (_root_.)?(HasCompactSupport.)?contDiff_convolution_left|theorem integral_lineDeriv_mul_eq|theorem (_root_.)?(Convex.)?addHaar_frontier|theorem convolution_tendsto_right' mathlib/Mathlib`
- `rg -n 'theorem (HasCompactSupport.contDiff_convolution_left|LipschitzWith.integral_lineDeriv_mul_eq|Convex.addHaar_frontier|mul_meas_ge_le_lintegral₀|ContDiffBump.convolution_tendsto_right)' mathlib/Mathlib`
- `rg -n 'exists_isClosed_sdiff_lt|exists_isClosed_diff_lt' mathlib/Mathlib; rg -n 'theorem LipschitzWith.ae_differentiableAt' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; rg -n 'theorem tendstoUniformlyOn_of_ae_tendsto' mathlib/Mathlib`
- `rg -il 'BoundedVariation|poincare' mathlib/Mathlib`
- `rg -n 'Submission.|theorem .*bv_compactness_poincare_extension|lipschitz_extension_and_rademacher' project`
- `grep -n '^theorem|^def|^noncomputable def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then a full read of BV.lean`
- `python3 -I gen_checks.py (replays verifier gmt-compare.py contract_scope and child_modules for all 12 lean_statements); lake env lean AssemblyCheck.lean and NodeChallenge_00..11.lean against a scratch olean of GMT.Ch02.Submission`
- `#print axioms ChildCheck.unweighted_bound, ChildCheck.bvVariationOn_empty, ChildCheck.main_from_children`
- `read dag.json (active nodes) and nodes/root/decomposition-review-receipt-v1.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convex/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root/decomposition-review-receipt-v1.json`
- `/tmp/gmt-ch02-decomp-v2-3S9D56/AssemblyCheck.lean`

Contract.lean:245-252 confirms that BVCompactness integrates the whole sum ‖u k x‖ₑ + bvVariationOn (u k) W over W. README row 7 describes the unweighted printed bound, but the frozen contract is authoritative, so bv_results now proves the conversion (step A0) before A1. The snapshot Mathlib supplies every fact A0 needs: _root_.IsOpen.measure_pos (OpenPos.lean:47), _root_.IsCompact.measure_lt_top (Typeclasses/Finite.lean:346), lintegral_add_right (Lebesgue/Add.lean:339), setLIntegral_const (Lebesgue/Basic.lean:121), ENNReal.le_div_iff_mul_le (ENNReal/Inv.lean:369) and ENNReal.div_lt_top (Inv.lean:214). A0 was kernel-checked as a scratch lemma against the frozen notation; it depends only on propext, Classical.choice and Quot.sound. The pinned SimonGMT BV.lean defines bvVariationOn as an iSup, over Lipschitz C_c fields with tsupport ⊆ W and sup norm ≤ 1, of ofReal ∫_W u·div g. Hence bvVariationOn u ∅ = 0, which was also kernel-checked. The same file provides ofReal_integral_le_bvVariationOn, IsC1TestField.isLipschitzTestField, bvVariationOn_le_liminf_of_locallyL1 and isLocallyBV_of_locallyL1_of_uniform_bound, which are used in A3-A4. Mathlib supplies the Section T tools: HasCompactSupport.contDiff_convolution_left, ContDiffBump.convolution_tendsto_right, LipschitzWith.integral_lineDeriv_mul_eq, Convex.addHaar_frontier and mul_meas_ge_le_lintegral₀. It also has the names cited by the unchanged children: MeasurableSet.exists_isClosed_sdiff_lt (Regular.lean:1036), LipschitzWith.ae_differentiableAt (Rademacher.lean:385) and tendstoUniformlyOn_of_ae_tendsto (Egorov.lean:205). There is no BV compactness, BV Poincaré or BV extension theorem in ℝⁿ; the BoundedVariation matches concern one-dimensional variation and vector measures. The project snapshot has no Submission.* declarations, and dag.json has only the root node, so the twelve bare lean_names do not collide. Using the comparator's own scope replay, all 12 child statements elaborate after import GMT.Ch02.Submission, the 12 generated NodeChallenge modules compile, and the 16-component constructor proves type_of% GMT.Ch02.main_theorem from the children.
