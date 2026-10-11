# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.c1_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2 §1, Theorem 1.5 and its printed proof (pp. 42-44). Erratum/reading applied (documented in GMT/Ch02/README.md): the set {∇f ≠ ∇g} is read as {x : not (f is differentiable at x with Df(x) = Dg(x))}, i.e. {x | ¬ HasFDerivAt f (fderiv ℝ g x) x}; it differs from the literal set by an Lⁿ-null set by Rademacher. Uses the sibling results Rademacher (child lipschitz_ext_rademacher, second conjunct) and WhitneyExtension (child whitney_extension).

PART I. PRINTED PROOF (cleaned transcription).
Proof of Theorem 1.5. By Rademacher's theorem f is differentiable on a set B ⊆ ℝⁿ with Lⁿ(ℝⁿ∖B) = 0. By Lusin's theorem (which applies to sets of infinite measure for Lⁿ) there is a closed set C ⊆ B such that ∇f|C is continuous and Lⁿ(ℝⁿ∖C) < ε/2. On C we define h(x) = f(x), ν(x) = ∇f(x) and R(x,y) for x, y ∈ C as in 1.6(*). Evidently (since C ⊆ B) lim_{y→x, y∈C} R(x,y) = 0 for every x ∈ C, but not necessarily uniformly with respect to x on compact subsets of C as in 1.6(*). We therefore proceed as follows. For k = 1, 2, … let η_k(x) = sup{|R(x,y)| : y ∈ C ∩ B_{1/k}(x)∖{x}}. Then η_k ↓ 0 pointwise in C, and hence by Egoroff's theorem (applied to the finite measure sets C ∩ B_j(0), j = 1, 2, …) there is an Lⁿ-measurable set A′ ⊆ C such that Lⁿ(C∖A′) < ε/4 and η_k converges uniformly to zero on each bounded subset of A′. Since we can take a closed set A ⊆ A′ with Lⁿ(A′∖A) < ε/4 we thus have Lⁿ(ℝⁿ∖A) < ε and 1.6(*) holds. Hence we can apply the Whitney Theorem 1.6, and the proof is complete.

PART II. COMPLETE PROOF OF THE FROZEN STATEMENT.
Statement: for every n ∈ ℕ, every Lipschitz f : ℝⁿ → ℝ (LipschitzWith K f) and every real ε > 0 there is g : ℝⁿ → ℝ with ContDiff ℝ 1 g and volume({x | f x ≠ g x} ∪ {x | ¬ HasFDerivAt f (fderiv ℝ g x) x}) < ENNReal.ofReal ε. Here ℝⁿ = EuclideanSpace ℝ (Fin n), Lⁿ = volume.

0. The case n = 0. Then ℝ⁰ is a single point, so f is constant and every function on ℝ⁰ is C¹; take g := f. The set {x | f x ≠ g x} is empty and HasFDerivAt f (fderiv ℝ g x) x holds trivially (both sides are maps on a zero-dimensional space and f = g), so the exceptional set is empty and has measure 0 < ENNReal.ofReal ε. (Note that volume on ℝ⁰ is the Dirac mass at 0, of total mass 1, so this case must be treated separately.) From now on n ≥ 1.
1. Differentiability set. B := {x : DifferentiableAt ℝ f x} is a Borel set (Mathlib measurableSet_of_differentiableAt) and Lⁿ(ℝⁿ∖B) = 0 by Rademacher (sibling conjunct; Mathlib LipschitzWith.ae_differentiableAt).
2. Gradient field. Let ν(x) ∈ ℝⁿ be the vector with ⟨ν(x), v⟩ = fderiv ℝ f x v for all v (the gradient; ν(x) = 0 where f is not differentiable). ν is Borel measurable (Mathlib measurable_fderiv composed with the continuous linear isometry between the dual and ℝⁿ), and |ν(x)| ≤ K because ‖fderiv ℝ f x‖ ≤ K for a K-Lipschitz f.
3. Lusin step: there is a closed C ⊆ B with ν|C continuous and Lⁿ(ℝⁿ∖C) < ε/2. Construction: let S_1 := {x : |x| < 1} and S_j := {x : j − 1 < |x| < j} for j ≥ 2 (open, bounded, pairwise disjoint) and Z := ∪_{j≥1} {x : |x| = j} (Lⁿ-null since n ≥ 1); then ℝⁿ = Z ∪ ∪_j S_j. For each j and each coordinate i ≤ n apply the finite-measure Lusin theorem (SimonGMT Poincare.SimonGMT.Chapter01.exists_isClosed_continuousOn_of_measurable, whose regularity hypothesis for Lebesgue measure is Mathlib MeasurableSet.exists_isClosed_sdiff_lt) to the Borel function ⟨ν, e_i⟩ on the bounded Borel set S_j ∩ B, with error ε2^{−j−2}/(n+1); intersecting the n closed sets obtained gives a closed C_j ⊆ S_j ∩ B with Lⁿ((S_j ∩ B)∖C_j) < ε2^{−j−2} and ν|C_j continuous. Put C := ∪_j C_j. The family {C_j} is locally finite (a bounded set meets only finitely many S_j), so C is closed. ν|C is continuous: a point x ∈ C lies in exactly one C_j, and the open set S_j ∋ x satisfies S_j ∩ C = C_j, so continuity on C at x reduces to continuity on C_j. Finally Lⁿ(ℝⁿ∖C) ≤ Lⁿ(ℝⁿ∖B) + Lⁿ(Z) + Σ_j Lⁿ((S_j∩B)∖C_j) < 0 + 0 + ε/4 < ε/2.
4. Remainders. For x ≠ y put R(x,y) := (f(y) − f(x) − ⟨ν(x), y − x⟩)/|y − x|, so |R| ≤ 2K. For k ≥ 1 define η_k(x) := sup{|R(x,y)| : y ∈ C, 0 < |y − x| < 1/k} for x ∈ C (sup ∅ := 0) and η_k(x) := 0 for x ∉ C.
 (a) 0 ≤ η_{k+1} ≤ η_k ≤ 2K.
 (b) η_k(x) → 0 for every x ∈ C: x ∈ B, so f is differentiable at x with derivative ⟨ν(x), ·⟩, i.e. R(x,y) → 0 as y → x.
 (c) Each η_k is Borel measurable. Let D ⊆ C be countable and dense in C. For fixed x ∈ C, y ↦ |R(x,y)| is continuous on ℝⁿ∖{x} and {y ∈ C : 0 < |y − x| < 1/k} is relatively open in C, so D is dense in it; hence η_k(x) = sup_{q∈D} 1{0 < |q − x| < 1/k}·|R(x,q)|. For each fixed q the function x ↦ 1_C(x)1{0 < |q − x| < 1/k}|R(x,q)| is Borel (f continuous, ν Borel), and a countable supremum of Borel functions is Borel.
5. Egorov step. For j ≥ 1 let C′_j := C ∩ {x : j − 1 ≤ |x| < j} (Borel, finite measure). By Egorov's theorem (Mathlib MeasureTheory.tendstoUniformlyOn_of_ae_tendsto, applied on C′_j to the strongly measurable η_k and the limit 0, using 4(b)) there is a measurable t_j ⊆ C′_j with Lⁿ(t_j) ≤ ε2^{−j−4} and η_k → 0 uniformly on A′_j := C′_j∖t_j. Put A′ := ∪_j A′_j ⊆ C. Then Lⁿ(C∖A′) ≤ Σ_j Lⁿ(t_j) ≤ ε/16 < ε/8, and every bounded subset of A′ lies in A′_1 ∪ … ∪ A′_J for some J, on which η_k → 0 uniformly.
6. Closed inner approximation. For each j choose a closed F_j ⊆ A′_j with Lⁿ(A′_j∖F_j) < ε2^{−j−4} (Mathlib MeasurableSet.exists_isClosed_sdiff_lt; Lebesgue measure is weakly regular). Since F_j ⊆ {j − 1 ≤ |x| < j}, the family {F_j} is locally finite, so A := ∪_j F_j is closed, A ⊆ A′ ⊆ C ⊆ B and Lⁿ(A′∖A) < ε/8. Therefore Lⁿ(ℝⁿ∖A) ≤ Lⁿ(ℝⁿ∖C) + Lⁿ(C∖A′) + Lⁿ(A′∖A) < ε/2 + ε/8 + ε/8 < ε.
7. Whitney hypotheses. Apply WhitneyExtension with this closed A, h := f and the field ν. h is continuous (f Lipschitz); ν is continuous on A ⊆ C (step 3). Let K ⊆ A be compact and ε′ > 0. K is bounded and contained in A′, so η_k → 0 uniformly on K: choose k with η_k(x) ≤ ε′ for all x ∈ K and put δ := 1/k. For x ∈ K and y ∈ A with 0 < |y − x| < δ we have y ∈ C, hence |R(x,y)| ≤ η_k(x) ≤ ε′, i.e. |f(y) − f(x) − ⟨ν(x), y − x⟩| ≤ ε′|y − x|. This is exactly hypothesis (W) of the frozen WhitneyExtension.
8. Conclusion. WhitneyExtension gives g : ℝⁿ → ℝ with ContDiff ℝ 1 g, g(x) = f(x) and fderiv ℝ g x v = ⟨ν(x), v⟩ for all x ∈ A, v ∈ ℝⁿ. For x ∈ A: f(x) = g(x), and since x ∈ B, f has derivative fderiv ℝ f x = ⟨ν(x), ·⟩ = fderiv ℝ g x at x, i.e. HasFDerivAt f (fderiv ℝ g x) x. Hence {x | f x ≠ g x} ∪ {x | ¬ HasFDerivAt f (fderiv ℝ g x) x} ⊆ ℝⁿ∖A, whose measure is < ε (step 6); since this measure is a real number < ε, it is < ENNReal.ofReal ε. This proves C1Approximation (the case n = 0 was treated in step 0).

## Key steps

1. Case n = 0: take g = f.
2. Rademacher: f is differentiable on a Borel set B of full measure; the gradient field ν is Borel and bounded.
3. Lusin on bounded shells: closed C ⊆ B with ν continuous on C and Lⁿ(ℝⁿ∖C) < ε/2.
4. The remainder suprema η_k (over a countable dense subset of C) are Borel, decrease to 0 on C; Egorov on shells gives A′ ⊆ C with Lⁿ(C∖A′) < ε/8 and uniform convergence on bounded subsets.
5. Closed A ⊆ A′ with Lⁿ(A′∖A) < ε/8, so Lⁿ(ℝⁿ∖A) < ε.
6. The uniform convergence of η_k on compact subsets of A is exactly the Whitney hypothesis; Whitney gives g ∈ C¹ with g = f and Dg = Df on A, so the exceptional set lies in ℝⁿ∖A.

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
