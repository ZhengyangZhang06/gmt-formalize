# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.lipschitz_image_hausdorff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2 §1, Theorem 1.8 and its printed proof (pp. 44-45). No erratum. Formal conventions of the frozen statement: 𝓗^m := Chapter01.simonHausdorffMeasureReal m = c_m·μH[m] with c_m = ω_m/2^m ∈ (0,∞) (Mathlib μH[m] = hausdorffMeasure m); Carathéodory 𝓗^m-measurability is rendered NullMeasurableSet / AEMeasurable; the Lipschitz constant K ∈ ℝ≥0 plays the role of Lip f (K^m is ENNReal.rpow); N(f,y) = fiberCount A f y = encard(A ∩ f⁻¹{y}) ∈ [0,∞].

PART I. PRINTED PROOF (cleaned transcription).
(i) Observe first that if δ > 0 and C₁, C₂, … are chosen with A ⊆ ∪_j C_j and diam C_j < δ for each j, then f(A) ⊆ ∪_j f(C_j) and diam f(C_j) ≤ (Lip f)δ < (1 + Lip f)δ. Hence H^m_{(1+Lip f)δ}(f(A)) ≤ Σ_j ω_m (diam f(C_j)/2)^m ≤ (Lip f)^m Σ_j ω_m (diam C_j/2)^m, and taking inf over all such collections {C_j} and then letting δ ↓ 0 we obtain H^m(f(A)) ≤ (Lip f)^m H^m(A). Notice this part of the argument is valid even if A is not H^m-measurable and did not depend on the σ-compactness of X. Next suppose that A is H^m-measurable and observe that the regularity property 1.15(2) of Ch. 1 together with the σ-compactness of X implies that we can take a sequence K₁, K₂, … of compact sets in X with K_j ⊆ A for each j and H^m(A∖(∪_j K_j)) = 0. By the first part above we then have H^m(f(A∖(∪_j K_j))) = 0 and hence f(A) = f(A∖(∪_j K_j)) ∪ (∪_j f(K_j)). Now f(K_j) is compact, hence Borel, for each j, and H^m(f(A∖(∪_j K_j))) ≤ (Lip f)^m H^m(A∖(∪_j K_j)) = 0, so f(A) is H^m-measurable as claimed.
(ii) By the σ-compactness of X, for each i = 1, 2, … we can partition A into a disjoint union ∪_{j=1}^∞ A_{ij} where each A_{ij} is H^m-measurable and diam(A_{ij}) < 1/i; furthermore we can do this successively, partitioning each A_{ik} to give the new sets A_{i+1,j}, so that each of the sets A_{i+1,j} is contained in one of the A_{ik}. Observe that then Σ_j χ_{f(A_{ij})} is a non-negative function which is H^m-measurable by (i) and which increases pointwise (at every point) to N(f,y), and so N(f,y) is H^m-measurable and by the monotone convergence theorem ∫_Y N(f,y) dH^m(y) = lim_i ∫_Y Σ_j χ_{f(A_{ij})} dH^m = lim_i Σ_j H^m(f(A_{ij})), and Σ_j H^m(f(A_{ij})) ≤ (Lip f)^m Σ_j H^m(A_{ij}) = (Lip f)^m H^m(A) by part (i).

PART II. COMPLETE PROOF OF THE FROZEN STATEMENT.
Let X be a σ-compact metric space and Y a metric space, both with their Borel σ-algebras, m ≥ 0 real, A ⊆ X with NullMeasurableSet A 𝓗^m and 𝓗^m(A) < ∞, f : X → Y with LipschitzOnWith K f A.

(i) Inequality.
1. For every set E ⊆ A: μH[m](f(E)) ≤ K^m μH[m](E). This is the covering argument of Part I; formally Mathlib LipschitzOnWith.hausdorffMeasure_image_le (needs 0 ≤ m), applied to f restricted to E (LipschitzOnWith K f E by monotonicity). Multiplying by c_m: 𝓗^m(f(E)) ≤ K^m 𝓗^m(E). With E = A this is the inequality in (i). In particular, if 𝓗^m(E) = 0 then 𝓗^m(f(E)) = 0 (K^m < ∞).

(i) Measurability.
2. Inner compact approximation. Since A is null-measurable there is a measurable (Borel) A₀ ⊆ A with 𝓗^m(A∖A₀) = 0 (Mathlib NullMeasurableSet.exists_measurable_subset_ae_eq). The measure ν := 𝓗^m restricted to A₀ is a finite Borel measure on the σ-compact metric space X, hence inner regular with respect to compact sets on Borel sets (a finite Borel measure on a metric space is inner regular by closed sets; intersecting a closed set with the members of an increasing compact exhaustion of X gives compact sets whose measures converge). So for every j there is a compact Q_j ⊆ A₀ with 𝓗^m(A₀∖Q_j) < 1/j. Let A₁ := ∪_j Q_j ⊆ A; then 𝓗^m(A∖A₁) ≤ 𝓗^m(A∖A₀) + 𝓗^m(A₀∖Q_j) < 1/j for all j, so 𝓗^m(A∖A₁) = 0. (This is exactly the argument of SimonGMT Poincare.SimonGMT.Chapter02.nullMeasurableSet_image_of_lipschitzOn_sigmaCompact(_of_nullMeasurable), there written for natural m; it transfers verbatim to real m with 𝓗^m in place of μHE[n].)
3. f(A) = (∪_j f(Q_j)) ∪ f(A∖A₁). Each f(Q_j) is compact (f is continuous on Q_j ⊆ A), hence closed, hence Borel in Y; and 𝓗^m(f(A∖A₁)) = 0 by step 1. A Borel set union a null set is null-measurable, so NullMeasurableSet (f(A)) 𝓗^m.
4. Steps 2-3 apply to any null-measurable E ⊆ A with 𝓗^m(E) < ∞ (with f still K-Lipschitz on E): f(E) is 𝓗^m-null-measurable.

(ii) Multiplicity.
5. Nested countable Borel partitions. X is σ-compact metric, hence separable; let {q_l} be a countable dense subset. For i ≥ 1 and l ≥ 1 put Q_{i,l} := B(q_l, 1/(3i)) ∖ ∪_{l′<l} B(q_{l′}, 1/(3i)); for fixed i these are disjoint Borel sets covering X with diam Q_{i,l} ≤ 2/(3i) < 1/i. Let {P_{i,j}}_j be the nonempty sets among Q_{1,l₁} ∩ … ∩ Q_{i,l_i} (countably many). Then {P_{i,j}}_j is a countable partition of X into Borel sets of diameter < 1/i, and every P_{i+1,j′} is contained in a unique P_{i,j}.
6. Pieces. A_{i,j} := A ∩ P_{i,j}: null-measurable, 𝓗^m(A_{i,j}) ≤ 𝓗^m(A) < ∞, pairwise disjoint in j, ∪_j A_{i,j} = A, and each A_{i,j} is the disjoint union of the A_{i+1,j′} with P_{i+1,j′} ⊆ P_{i,j}. By step 4, every f(A_{i,j}) is null-measurable.
7. Counting functions. N_i(y) := Σ_j 1_{f(A_{i,j})}(y) = #{j : A_{i,j} ∩ f⁻¹{y} ≠ ∅}. Each N_i is AEMeasurable for 𝓗^m (countable sum of indicators of null-measurable sets).
 (a) N_i ≤ N_{i+1}: if A_{i,j} meets f⁻¹{y}, one of its sub-pieces A_{i+1,j′} does, and distinct j give distinct j′.
 (b) N_i(y) ≤ fiberCount A f y: choosing one point of A ∩ f⁻¹{y} in each piece A_{i,j} that meets f⁻¹{y} defines an injection (pieces are disjoint).
 (c) sup_i N_i(y) = fiberCount A f y: if F ⊆ A ∩ f⁻¹{y} is finite with #F = p, let 1/i be smaller than the least distance between distinct points of F; then distinct points of F lie in distinct pieces A_{i,j} (diam < 1/i), so N_i(y) ≥ p. Taking the supremum over finite F gives sup_i N_i(y) ≥ encard(A ∩ f⁻¹{y}), including the value ∞; with (b) equality holds.
8. AEMeasurability of fiberCount A f: it is the supremum of the countable family of AEMeasurable functions N_i (step 7c; Mathlib AEMeasurable.iSup / Measurable.iSup after choosing measurable modifications).
9. Integral bound. By monotone convergence for AEMeasurable functions (Mathlib lintegral_iSup′ with 7a), ∫ fiberCount A f d𝓗^m = lim_i ∫ N_i d𝓗^m, and ∫ N_i d𝓗^m = Σ_j 𝓗^m(f(A_{i,j})) (integral of a countable sum of indicators of null-measurable sets) ≤ Σ_j K^m 𝓗^m(A_{i,j}) (step 1) = K^m 𝓗^m(A) (countable additivity for disjoint null-measurable sets). Hence ∫_Y fiberCount A f d𝓗^m ≤ K^m 𝓗^m(A).
10. Steps 1, 3, 8 and 9 are the four conclusions of LipschitzImageHausdorff.

## Key steps

1. Image inequality from the covering argument (Mathlib LipschitzOnWith.hausdorffMeasure_image_le scaled by ω_m/2^m).
2. Inner regularity: compact Q_j ⊆ A with 𝓗^m(A∖∪Q_j) = 0 (finite Borel measure on a σ-compact metric space).
3. f(A) = ∪f(Q_j) (Borel) ∪ f(null set) (null), hence null-measurable.
4. Nested countable Borel partitions of X of mesh < 1/i give pieces A_{ij}; N_i = Σ_j 1_{f(A_ij)} is a.e.-measurable and increases to N.
5. Monotone convergence and (i) give ∫N = lim Σ_j 𝓗^m(f(A_ij)) ≤ K^m 𝓗^m(A).

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
