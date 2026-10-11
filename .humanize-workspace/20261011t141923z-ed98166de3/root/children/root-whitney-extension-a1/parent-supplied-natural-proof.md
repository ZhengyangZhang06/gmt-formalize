# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.whitney_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2 §1, Theorem 1.6 (pp. 42-43). The book gives no proof in general: it says (For the proof see for example [EG92] or [Fed69]; for the case n = 1 see Remark 1.7(2)). Remark 1.7(2) (printed) treats n = 1: ℝ∖A is a countable union of disjoint open intervals I_j = (a,b), on each of which one chooses g_j ∈ C¹[a,b] with g_j(a) = h(a), g_j(b) = h(b), g_j′(a) = ν(a), g_j′(b) = ν(b) and sup_{I_j}|g_j′ − ν(a)| ≤ 3ε_C(b−a), and sets g = g_j on I_j, g = h on A. Below we supply the complete proof in every dimension, following the cited reference [EG92] (Evans-Gariepy, Whitney's extension theorem): a Whitney-type covering of ℝⁿ∖A, a partition of unity with derivative bounds ≲ 1/dist(·,A), and the averaged first-order Taylor polynomials of h at nearest points of A. No erratum applies.

Statement being proved (exact frozen form). Let n ∈ ℕ, ℝⁿ = EuclideanSpace ℝ (Fin n), A ⊆ ℝⁿ closed, h : ℝⁿ → ℝ continuous on A, ν : ℝⁿ → ℝⁿ continuous on A, and assume
(W) for every compact K ⊆ A and every ε > 0 there is δ > 0 such that for all x ∈ K and all y ∈ A with 0 < |y − x| < δ: |h(y) − h(x) − ⟨ν(x), y − x⟩| ≤ ε|y − x|.
Then there is g : ℝⁿ → ℝ of class C¹ with g(x) = h(x) and Dg(x)v = ⟨ν(x), v⟩ for all x ∈ A, v ∈ ℝⁿ.

Proof.

0. Trivial cases and notation. If A = ∅ take g ≡ 0. Assume A ≠ ∅ from now on. Put U := ℝⁿ∖A (open), d(x) := dist(x, A) (1-Lipschitz, d > 0 exactly on U, and for every x there is a nearest point a ∈ A with |x − a| = d(x) since A is closed and nonempty in ℝⁿ), and r(x) := min{1, d(x)}/20, which is 1/20-Lipschitz. If U = ∅ (A = ℝⁿ) the construction below has no balls and g := h; the argument of steps 5-6 then applies verbatim (only the case x ∈ A occurs).

1. Covering. Apply the Vitali covering lemma (Mathlib: Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall with radii bounded by R = 1/20 and enlargement factor τ = 5 > 3) to the family of closed balls B̄(x, r(x)), x ∈ U. It yields a subfamily of pairwise disjoint balls B̄(s_j, r_j), r_j := r(s_j), j ∈ J, such that every B̄(x, r(x)) with x ∈ U is contained in some B̄(s_j, 5r_j). J is countable (pairwise disjoint sets with nonempty interior in the separable space ℝⁿ). In particular U = ∪_j B̄(s_j, 5r_j).

2. Geometry of the cover.
(F1) If |x − s_j| ≤ 10r_j then |r(x) − r_j| ≤ |x − s_j|/20 ≤ r_j/2, hence r_j/2 ≤ r(x) ≤ 3r_j/2, i.e. (2/3)r(x) ≤ r_j ≤ 2r(x); and since d(s_j) ≥ 20r_j (because r_j ≤ d(s_j)/20), d(x) ≥ d(s_j) − |x − s_j| ≥ 10r_j > 0, so x ∈ U.
(F2) For x ∈ U let J(x) := {j : |x − s_j| < 10r_j}. Then #J(x) ≤ N := 33ⁿ. Indeed for j ∈ J(x) the disjoint balls B̄(s_j, r_j) lie in B̄(x, 11r_j) ⊆ B̄(x, 22r(x)) and have radius r_j ≥ (2/3)r(x); comparing Lebesgue measures, #J(x)·((2/3)r(x))ⁿ ≤ (22r(x))ⁿ.
(F3) Local finiteness: for x₀ ∈ U only finitely many balls B(s_j, 10r_j) meet B(x₀, r(x₀)). If z lies in both, then r_j ≥ (2/3)r(z) ≥ (2/3)(19/20)r(x₀) ≥ r(x₀)/2 and r_j ≤ 2r(z) ≤ (21/10)r(x₀) < 3r(x₀), so B̄(s_j, r_j) ⊆ B̄(x₀, 34r(x₀)); disjointness and comparison of measures bound the number of such j by 68ⁿ.
(F4) For x ∈ U and j ∈ J(x), choose for every j a point a_j ∈ A with |s_j − a_j| = d(s_j) (fixed once and for all). Then |a_j − x| ≤ |a_j − s_j| + |s_j − x| = d(s_j) + |s_j − x| ≤ d(x) + 2|s_j − x| < d(x) + 20r_j ≤ d(x) + 40r(x) ≤ 3d(x), using r_j ≤ 2r(x) and r(x) ≤ d(x)/20.

3. Partition of unity. Fix θ ∈ C^∞(ℝⁿ) with 0 ≤ θ ≤ 1, θ = 1 on B̄(0,5) and θ = 0 outside B(0,9) (a smooth bump, e.g. Mathlib ContDiffBump with rIn = 5, rOut = 9), and let Λ := sup|Dθ| < ∞. Put θ_j(x) := θ((x − s_j)/r_j): θ_j ∈ C^∞, θ_j = 1 on B̄(s_j, 5r_j), tsupport θ_j ⊆ B̄(s_j, 9r_j) ⊆ U, |Dθ_j| ≤ Λ/r_j. By (F3) the sum Σ(x) := Σ_j θ_j(x) is locally finite on U, hence C^∞ on U; Σ ≥ 1 on U (every x ∈ U lies in some B̄(s_j,5r_j)) and Σ ≤ N by (F2). Define v_j := θ_j/Σ on U. Then v_j ∈ C^∞(U), 0 ≤ v_j ≤ 1, Σ_j v_j = 1 on U, Σ_j Dv_j = 0 on U (derivative of a locally finite sum), v_j and Dv_j vanish at x ∈ U unless j ∈ J(x) (θ_j vanishes on a neighbourhood of x when |x − s_j| ≥ 10r_j > 9r_j), and for j ∈ J(x):
|Dv_j(x)| ≤ |Dθ_j(x)|/Σ(x) + θ_j(x)|DΣ(x)|/Σ(x)² ≤ Λ/r_j + Σ_{i∈J(x)} Λ/r_i ≤ (3/2)Λ(1 + N)/r(x) =: C₁/r(x),
using r_i ≥ (2/3)r(x) for i ∈ J(x).

4. Definition of g. Let P_j(x) := h(a_j) + ⟨ν(a_j), x − a_j⟩ (affine). Set g(x) := h(x) for x ∈ A and g(x) := Σ_j v_j(x)P_j(x) for x ∈ U. On U, g is a locally finite sum of C^∞ functions, hence C^∞, with Dg(x) = Σ_j P_j(x)Dv_j(x) + Σ_j v_j(x)⟨ν(a_j), ·⟩.

5. Estimates near a point a ∈ A. Fix a ∈ A, put K_a := A ∩ B̄(a, 4) (compact, contained in A) and let ω(t) := sup{|ν(p) − ν(q)| : p, q ∈ K_a, |p − q| ≤ t}, so ω(t) → 0 as t → 0 (uniform continuity of ν on the compact K_a). Given ε > 0 let δ_ε ∈ (0,1] be a δ given by (W) for the compact set K_a and ε.
(5a) First-order estimate. Let x ∈ ℝⁿ with |x − a| < δ_ε/4. If x ∈ A, x ≠ a, then by (W) (base point a ∈ K_a, y = x ∈ A): |g(x) − h(a) − ⟨ν(a), x − a⟩| ≤ ε|x − a|. If x ∈ U then d(x) ≤ |x − a| and for j ∈ J(x), by (F4), |a_j − a| ≤ |a_j − x| + |x − a| ≤ 4|x − a| < δ_ε ≤ 1, so a_j ∈ K_a. Using Σ_j v_j(x) = 1,
g(x) − h(a) − ⟨ν(a), x − a⟩ = Σ_{j∈J(x)} v_j(x)( [h(a_j) − h(a) − ⟨ν(a), a_j − a⟩] + ⟨ν(a_j) − ν(a), x − a_j⟩ ).
By (W) (base a, y = a_j; the bracket is 0 if a_j = a) the first bracket is ≤ ε|a_j − a| ≤ 4ε|x − a| in absolute value, and the second term is ≤ ω(4|x − a|)·3d(x) ≤ 3ω(4|x − a|)|x − a|. Hence |g(x) − g(a) − ⟨ν(a), x − a⟩| ≤ (4ε + 3ω(4|x − a|))|x − a| for all x with |x − a| < δ_ε/4. Since ε > 0 is arbitrary and ω(t) → 0, g is differentiable at a with Dg(a)v = ⟨ν(a), v⟩ (and g(a) = h(a)).
(5b) Derivative estimate on U. Let x ∈ U with |x − a| < δ_ε/8 and let a* ∈ A with |x − a*| = d(x) ≤ |x − a|. Then |a* − a| ≤ 2|x − a| and, for j ∈ J(x), |a_j − a*| ≤ |a_j − x| + |x − a*| ≤ 4d(x) < δ_ε/2, and a*, a_j ∈ K_a. Let P*(x') := h(a*) + ⟨ν(a*), x' − a*⟩. Since Σ_j Dv_j(x) = 0,
Σ_j P_j(x)Dv_j(x) = Σ_{j∈J(x)} (P_j(x) − P*(x))Dv_j(x), and P_j(x) − P*(x) = [h(a_j) − h(a*) − ⟨ν(a*), a_j − a*⟩] + ⟨ν(a_j) − ν(a*), x − a_j⟩,
so by (W) (base a* ∈ K_a, y = a_j) and (F4), |P_j(x) − P*(x)| ≤ 4εd(x) + 3ω(4d(x))d(x). As d(x) < 1, r(x) = d(x)/20, so |Dv_j(x)| ≤ 20C₁/d(x), and with #J(x) ≤ N:
‖Σ_j P_j(x)Dv_j(x)‖ ≤ 20NC₁(4ε + 3ω(4d(x))).
Moreover |Σ_j v_j(x)ν(a_j) − ν(a)| = |Σ_{j∈J(x)} v_j(x)(ν(a_j) − ν(a))| ≤ ω(4|x − a|). Therefore
‖Dg(x) − ⟨ν(a), ·⟩‖ ≤ 20NC₁(4ε + 3ω(4|x − a|)) + ω(4|x − a|) for x ∈ U, |x − a| < δ_ε/8.

6. g is C¹ with the required values. g is differentiable at every point: on the open set U because it is C^∞ there, and at every a ∈ A by (5a), with Dg(a) = ⟨ν(a), ·⟩. Dg is continuous at every point of U (U open, g smooth there). Let a ∈ A and η > 0; choose ε > 0 with 80NC₁ε < η/3, then ρ ∈ (0, δ_ε/8) such that ω(4ρ)(60NC₁ + 1) < η/3 and such that |ν(x) − ν(a)| < η for x ∈ A ∩ B(a, ρ) (continuity of ν on A). For |x − a| < ρ: if x ∈ U, (5b) gives ‖Dg(x) − Dg(a)‖ < η; if x ∈ A, Dg(x) − Dg(a) = ⟨ν(x) − ν(a), ·⟩ has norm < η. So Dg is continuous on ℝⁿ, i.e. g is C¹ (ContDiff ℝ 1 g ⇔ differentiable with continuous derivative). Finally g = h on A by definition and fderiv ℝ g x v = ⟨ν(x), v⟩ for x ∈ A by (5a). This proves WhitneyExtension.

Remarks for formalization. (i) The covering lemma, the bump function, local finiteness of the sum (finitely many nonzero terms on B(x₀, r(x₀))) and nearest points are standard Mathlib facts. (ii) Only the uniform hypothesis (W) on the single compact set K_a for each base point a is used, in the exact form of the frozen statement (base point in K, comparison point anywhere in A). (iii) The case n = 0 is covered: ℝ⁰ is a point, A = ∅ or A = ℝ⁰.

## Key steps

1. Trivial case A empty; otherwise set U = complement of A, d = dist(·,A), r = min(1,d)/20.
2. Vitali covering of U by disjoint balls B(s_j, r_j) with U covered by the 5-fold enlargements; bounded overlap (≤ 33ⁿ) and local finiteness of the 10-fold enlargements.
3. Smooth partition of unity v_j subordinate to B(s_j,10r_j) with Σv_j = 1, ΣDv_j = 0 and |Dv_j| ≤ C₁/r(x).
4. Define g = h on A and g = Σ v_j(h(a_j) + ⟨ν(a_j), x − a_j⟩) on U with a_j nearest points; nearby a_j satisfy |a_j − x| ≤ 3d(x).
5. Near a ∈ A, the uniform hypothesis on the compact K_a = A ∩ B̄(a,4) and uniform continuity of ν give the first-order estimate (g differentiable at a with Dg(a) = ν(a)) and Dg(x) → ν(a) for x ∈ U.
6. Hence g is differentiable everywhere with continuous derivative, i.e. C¹, with g = h and Dg = ⟨ν,·⟩ on A.

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
