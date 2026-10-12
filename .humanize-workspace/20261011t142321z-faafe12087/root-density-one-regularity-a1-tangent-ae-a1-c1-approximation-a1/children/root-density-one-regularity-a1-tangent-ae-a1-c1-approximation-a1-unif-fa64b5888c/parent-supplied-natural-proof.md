# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1.tangent_ae-a1.c1_approximation-a1`
- Child DAG node: `root.density_one_regularity-a1.tangent_ae-a1.c1_approximation-a1.uniform_remainder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3-5 of the parent proof, filling in the measure-theoretic details for the given closed set C and tolerance δ. The parent proof is Simon, Ch. 2, proof of Theorem 1.5, p. 44: 'For each k = 1, 2, ... let η_k(x) = sup{|R(x,y)| : y ∈ C ∩ B_{1/k}(x) \ {x}}. Then η_k ↓ 0 pointwise in C, and hence by Egoroff's Theorem (applied to the finite measure sets C ∩ B_j(0), j = 1, 2, ...) there is an L^n-measurable set A_0 ⊆ C such that L^n(C \ A_0) < ε/4 and η_k converges uniformly to zero on each bounded subset of A_0. Since we can take a closed set A ⊆ A_0 with L^n(A_0 \ A) < ε/4 ... 1.6(*) holds'. Continuity of Df on C is not used here; the parent supplies it separately.

Notation: L^n = volume on R^n; |.| is the Euclidean norm; ||.|| is the operator norm; Df(x) := fderiv R f x. For k >= 1 let S_k := {x : k - 1 <= |x| < k}; the S_k are Borel, bounded and pairwise disjoint, with union R^n.

1. (Set-up.) Choose real numbers δ_k > 0 (k >= 1) with sum_k 2δ_k < δ, e.g. δ_k := min(δ,1) 2^{-k-2}.
- f is continuous, since it is Lipschitz.
- x ↦ Df(x) is Borel (Mathlib measurable_fderiv).
- C is closed, hence Borel. Each P_k := C ∩ S_k is Borel with L^n(P_k) <= L^n(closedBall(0,k)) < ∞. The P_k are pairwise disjoint with union C.

2. (Remainder quotients.) For x ≠ y let R(x,y) := (f(y) - f(x) - Df(x)(y - x))/|y - x|. Since |f(y) - f(x)| <= K|y - x| and |Df(x)(y - x)| <= ||Df(x)|| |y - x|, we have |R(x,y)| <= K + ||Df(x)||. For j >= 1 and x ∈ R^n let
φ_j(x) := sup({0} ∪ {|R(x,y)| : y ∈ C, 0 < |y - x| < 1/j}),
a real number in [0, K + ||Df(x)||]. The parent puts φ_j := 0 off C; using the same formula at every x changes nothing below, because only points of C are used. Then:
(a) |f(y) - f(x) - Df(x)(y - x)| <= φ_j(x)|y - x| whenever y ∈ C and 0 < |y - x| < 1/j.
(b) φ_{j+1} <= φ_j.
(c) φ_j(x) → 0 as j → ∞ for every x ∈ C. Given τ > 0: f is differentiable at x (by the hypothesis C ⊆ {f differentiable}), so there is r > 0 with |f(y) - f(x) - Df(x)(y - x)| <= τ|y - x| whenever |y - x| < r. For j > 1/r, every y in the defining set has |y - x| < 1/j < r, hence |R(x,y)| <= τ and 0 <= φ_j(x) <= τ.

3. (Each φ_j is Borel.) R^n is second countable, so C has a countable subset D with C ⊆ closure(D) (Mathlib TopologicalSpace.IsSeparable.exists_countable_dense_subset). Fix x and j, and let O := {y : 0 < |y - x| < 1/j}, an open set.
Claim: φ_j(x) = sup({0} ∪ {|R(x,y)| : y ∈ D ∩ O}).
- The inequality '>=' holds because D ⊆ C.
- For '<=', let y ∈ C ∩ O and τ > 0. The function z ↦ |R(x,z)| is continuous on O: f is continuous, Df(x) is a fixed continuous linear map, and |z - x| ≠ 0 on O. So there is an open W with y ∈ W ⊆ O and |R(x,z)| > |R(x,y)| - τ for all z ∈ W. As y ∈ closure(D), W contains a point z of D, and z ∈ D ∩ O. Hence the right-hand side is > |R(x,y)| - τ for every τ > 0, which proves the claim.
Consequently, for every x, φ_j(x) = sup({0} ∪ {ψ_{j,y}(x) : y ∈ D}), where for fixed y the function ψ_{j,y} is defined by ψ_{j,y}(x) := |f(y) - f(x) - Df(x)(y - x)|/|y - x| if 0 < |y - x| < 1/j, and ψ_{j,y}(x) := 0 otherwise.
Each ψ_{j,y} is Borel:
- {x : 0 < |y - x| < 1/j} is open;
- f is continuous;
- x ↦ Df(x)(y - x) is Borel, being the continuous evaluation (L, v) ↦ L(v) applied to the Borel map x ↦ (Df(x), y - x);
- x ↦ |y - x| is continuous and nonzero on that open set.
A pointwise supremum of countably many Borel real functions that is pointwise bounded (here by K + ||Df(x)||) is Borel. Hence φ_j is Borel. If C = ∅, then φ_j ≡ 0.

4. (Egorov on the bounded pieces.) Fix k >= 1. On the Borel set P_k of finite measure, the Borel functions φ_j converge pointwise to 0 (step 2(c)). By Egorov's theorem (Mathlib tendstoUniformlyOn_of_ae_tendsto, for the measure L^n, the set P_k and tolerance δ_k) there is a Borel set t_k ⊆ P_k with L^n(t_k) <= δ_k such that φ_j → 0 uniformly on E_k := P_k \ t_k. E_k is Borel with finite measure.

5. (A closed set.) For each k, choose by inner regularity a closed F_k ⊆ E_k with L^n(E_k \ F_k) < δ_k (Mathlib MeasurableSet.exists_isClosed_sdiff_lt; L^n is weakly regular). Let A := union_k F_k.
- F_k ⊆ S_k, and the ball B(x,1) meets S_k only for the finitely many k with |x| - 1 < k < |x| + 2. So the family (F_k) is locally finite, and A is closed (Mathlib LocallyFinite.isClosed_iUnion).
- A ⊆ union_k E_k ⊆ C.
- If x ∈ C \ A, then x ∈ P_k for some k and x ∉ F_k, so x ∈ t_k ∪ (E_k \ F_k). Hence L^n(C \ A) <= sum_k (L^n(t_k) + L^n(E_k \ F_k)) <= sum_k 2δ_k < δ.

6. (Uniform remainder estimate.) Let Q ⊆ A be compact and η > 0.
- Q is bounded, so there is an integer N >= 1 with |x| < N for all x ∈ Q.
- For x ∈ Q, let k be the index with x ∈ S_k; then k <= N. Since x ∈ A, x ∈ F_{k'} ⊆ S_{k'} for some k', and disjointness of the S_k gives k' = k. So x ∈ F_k ⊆ E_k. Thus Q ⊆ E_1 ∪ ... ∪ E_N.
- By step 4 there are j_1, ..., j_N such that φ_j(z) < η whenever j >= j_k and z ∈ E_k. Let j := max(1, j_1, ..., j_N) and ρ := 1/j > 0.
- Let x ∈ Q and y ∈ A with |x - y| < ρ. If y = x, then |f(y) - f(x) - Df(x)(y - x)| = 0 <= η|y - x|. If y ≠ x, then y ∈ C (because A ⊆ C) and 0 < |y - x| < 1/j, so by step 2(a), |f(y) - f(x) - Df(x)(y - x)| <= φ_j(x)|y - x| <= η|y - x|.
Together with step 5, this proves the statement.

Formalization remark (not needed for the argument): two equivalent variants may be used instead.
(i) Because C is closed, step 5 can be replaced by outer regularity. Z := union_k t_k has L^n(Z) <= sum_k δ_k < δ, so there is an open U ⊇ Z with L^n(U) < δ (Mathlib Set.exists_isOpen_lt_of_lt). Then A := C \ U is closed, A ⊆ C, and L^n(C \ A) <= L^n(U) < δ. Every x ∈ A lies in E_k for the k with x ∈ S_k, so step 6 applies verbatim. The pieces may also be taken to be C ∩ B(0,J), as in Simon's text, since a compact Q lies in one such ball.
(ii) In step 2 the supremum may be taken over all y with 0 < |y - x| < 1/j instead of y ∈ C; (a)-(c) and step 6 are unchanged. Measurability is then immediate: (x, L) ↦ sup_{0<|v|<1/j} |f(x+v) - f(x) - L(v)|/|v| is a pointwise-bounded supremum of continuous functions, hence lower semicontinuous and Borel, and φ_j(x) is its value at the Borel point (x, Df(x)).
Variant (ii), with Egorov on balls and outer regularity, is how the comparator-accepted proof of Submission.aetp_lipschitz_c1_approximation proceeds (git commit 4d18f1d64ced18737b95cceccbeb3b1995ce254c, GMT/Ch05/Submission.lean, the part after 'intro f K hf ε hε'). That code can be adapted: intersect the Egorov pieces with C and take A := C \ U.

## Key steps

1. The remainder quotients φ_j(x) = sup{|R(x,y)| : y ∈ C, 0 < |y-x| < 1/j} are finite (f is Lipschitz), decrease in j, tend to 0 on C (f is differentiable there), and bound the Taylor remainder.
2. Each φ_j is Borel: the supremum over C equals the supremum over a countable dense D ⊆ C, which is a countable supremum of Borel functions.
3. Egorov's theorem on each bounded piece P_k = C ∩ S_k gives a Borel E_k ⊆ P_k with L^n(P_k \ E_k) <= δ_k and φ_j → 0 uniformly on E_k.
4. Inner regularity gives closed F_k ⊆ E_k. A = union of the F_k is closed (locally finite), A ⊆ C, and L^n(C \ A) <= sum 2δ_k < δ.
5. A compact Q ⊆ A lies in E_1 ∪ ... ∪ E_N, giving j with φ_j < η on Q, hence the remainder estimate with ρ = 1/j.

## Reference use

### local-project

Queries:
- `cat nodes/root-density-one-regularity-a1-tangent-ae-a1-c1-approximation-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md,parent-supplied-natural-proof.json}`
- `sed -n 140,300p book/chapter-02.txt (Simon Thm 1.5 printed proof p.44, Thm 1.6 Whitney, Remark 1.7)`
- `python3 import-closure scan of Poincare.SimonGMT.Chapter03.Rectifiable over .lake/packages/simongmt (closure: Chapter01.Basic, Chapter01.Hausdorff, Chapter01.MetricCriterion, Chapter02.Lipschitz, Chapter03.Rectifiable)`
- `comm -23 <(ls Chapter02/*.lean basenames) <(ls .lake/packages/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02/*.olean basenames) -> MISSING: WhitneyExtension; ls Chapter01 build | grep Lusin (Lusin.olean present)`
- `grep -n 'theorem|def |structure' and sed -n on SimonGMT Chapter02/{WhitneyJet,WhitneyCover,WhitneyPartition,WhitneyExtension}.lean and Chapter01/Lusin.lean`
- `python3 scan of lean_name fields in dag.json and nodes/**/*.json for whitney|lusin|egorov|remainder; grep -rl and git grep over all refs for tae_c1_lusin_clm_volume|tae_c1_uniform_remainder|tae_whitney_c1_extension (no match)`
- `git show 4d18f1d:GMT/Ch05/Submission.lean (accepted Submission.aetp_lipschitz_c1_approximation)`
- `git for-each-ref ... ; git show <branch>:GMT/Ch05/Submission.lean | grep ^import (accepted branches add imports)`
- `sed -n 330,420p verifier/gmt-compare.py (candidate_inputs: new Lean files only under GMT/Ch05/)`
- `rg -n -e 'theorem continuousOn_clm_apply' -e 'isClosed_iUnion' -e 'continuousOn_iUnion' -e 'exists_isOpen_lt_of_lt' -e 'exists_countable_dense_subset' -e 'theorem Measurable.iSup' -e 'MeasurableSet.exists_isClosed_sdiff_lt' -e 'tendstoUniformlyOn_of_ae_tendsto' -e 'exists_disjoint_subfamily_covering_enlargement_ball' -e 'LowerSemicontinuous.measurable' -e 'lowerSemicontinuous_iSup' -e 'exists_infDist_eq_dist' -e 'contDiff_one_iff_fderiv' -e 'of_pseudoMetrizableSpace_secondCountable_of_locallyFinite' <snapshot>/mathlib/Mathlib/{Topology,MeasureTheory,Analysis/Normed,Analysis/Calculus/ContDiff}`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean (identical)`
- `lake env lean /tmp/tae-c1a-dec-q8m3/Check1.lean and Check1b.lean (contract lines 1-460 + the three frozen child types as sorry + instance/lemma #checks)`
- `lake env lean /tmp/tae-c1a-dec-q8m3/WhitneyExtensionCopy.lean (0 errors); lake env lean Check4.lean / Check5.lean (SimonGMT Whitney pasted into fresh namespace, child 3 proved, parent assembly, exact-type examples, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-c1-approximation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-c1-approximation-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-c1-approximation-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/github-workflow.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Semicontinuity/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/tae-c1a-dec-q8m3/Check1b.lean`
- `/tmp/tae-c1a-dec-q8m3/Check5.lean`
- `/tmp/tae-c1a-dec-q8m3/WhitneyExtensionCopy.lean`

The snapshot pins project ea56075 and Mathlib 25730c7c; the snapshot `Contract.lean` is byte-identical to the workspace copy. SimonGMT is at rev 2b36630.

The contract's import closure contains only the SimonGMT modules Chapter01.{Basic,Hausdorff,MetricCriterion}, Chapter02.Lipschitz and Chapter03.Rectifiable.

In the shared build tree:
- `Chapter02/WhitneyExtension` (the home of `exists_contDiff_one_extension_of_whitney`, cited in supplied step 7) is the only Chapter02 module with no `.olean`. It cannot be imported.
- Its dependencies WhitneyJet (`HasWhitneyC1Compatibility`, `exists_local_uniform_estimate`), WhitneyCover and WhitneyPartition are built.
- `Chapter01/Lusin` (`exists_isClosed_continuousOn_of_measurable`, for real-valued functions on finite-measure sets) is built.

Accepted branches already add extra imports to `Submission.lean`. The verifier allows new Lean files only under `GMT/Ch05/`.

All Mathlib lemmas cited in the child proofs exist in the snapshot: `continuousOn_clm_apply`, `LocallyFinite.isClosed_iUnion`/`continuousOn_iUnion`, `Set.exists_isOpen_lt_of_lt`, `IsSeparable.exists_countable_dense_subset`, `Measurable.iSup`, `MeasurableSet.exists_isClosed_sdiff_lt`, the WeaklyRegular instance for volume, `tendstoUniformlyOn_of_ae_tendsto`, `Vitali.exists_disjoint_subfamily_covering_enlargement_ball`, `LowerSemicontinuous.measurable`, `IsClosed.exists_infDist_eq_dist`, `contDiff_one_iff_fderiv`. `measurable_fderiv`, `measurableSet_of_differentiableAt` and `LipschitzWith.ae_differentiableAt` are already in scope.

No searched source contains a σ-finite Lusin theorem for volume, or the C¹ approximation theorem with derivative agreement. The closest is the accepted `Submission.aetp_lipschitz_c1_approximation` (commit 4d18f1d): it requires 1 ≤ n, has no derivative conclusion, and proves Whitney inline.

Lean results:
- The three proposed frozen types elaborate in the contract scope with the contract imports only.
- The parent assembly compiles to the exact frozen type, with `sorryAx` only from children 1 and 2.
- Child 3 is proved from the SimonGMT copy with only propext, Classical.choice and Quot.sound.
- No name collisions.
