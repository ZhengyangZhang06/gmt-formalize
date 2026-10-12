# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1`
- Child DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the printed proof of Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 44). It is run inside the closed ball B := B_R(0) so that every measure involved is finite, exactly as in step 2 of the parent proof. Only the set {f ≠ g} is needed.

Notation:
- Lⁿ is volume on ℝⁿ = EuclideanSpace ℝ (Fin n).
- B_R(0) = closedBall 0 R.
- Df(x) := fderiv ℝ f x ∈ L(ℝⁿ, ℝ).
- e_1, …, e_n is the standard basis and |·| the Euclidean norm.

Tools:
- Rademacher's theorem: Mathlib LipschitzWith.ae_differentiableAt; simongmt Chapter02.rademacher_ae_differentiableAt.
- Mathlib measurableSet_of_differentiableAt, measurable_fderiv, measurable_fderiv_apply_const.
- norm_fderiv_le_of_lipschitz.
- Inner regularity of Lⁿ by closed sets: MeasurableSet.exists_isClosed_sdiff_lt (volume on ℝⁿ is regular).
- Lusin's theorem for real functions: simongmt Chapter01.exists_isClosed_continuousOn_of_measurable. Its regularity hypothesis is exactly the preceding inner regularity.
- continuousOn_clm_apply.
- Egoroff's theorem: Mathlib tendstoUniformlyOn_of_ae_tendsto.
- Whitney's extension theorem: simongmt Chapter02.exists_contDiff_one_extension_of_whitney, for data satisfying Chapter02.HasWhitneyC1Compatibility. Its module is Poincare.SimonGMT.Chapter02.WhitneyExtension. At the pinned revision it depends only on propext, Classical.choice and Quot.sound. It is not imported by GMT.Ch05.Submission and is not prebuilt in the shared package tree.

Let n ∈ ℕ, K ∈ ℝ≥0, f : ℝⁿ → ℝ K-Lipschitz, R ∈ ℝ and ε ∈ (0, ∞].

1. Reduction. Put ε' := min(ε, 1). Then 0 < ε' ≤ 1, ε' is finite and ε' ≤ ε. So it suffices to construct g ∈ C¹(ℝⁿ) with Lⁿ(B ∩ {f ≠ g}) < ε'. B is compact, so Lⁿ(B) < ∞.

2. Differentiability set.
- Let D := {x ∈ ℝⁿ : f is differentiable at x}. D is a Borel set, and by Rademacher's theorem Lⁿ(ℝⁿ \ D) = 0.
- The map x ↦ Df(x) is Borel measurable, hence so is each real function φ_i(x) := Df(x)e_i (1 ≤ i ≤ n).
- Since f is K-Lipschitz, ‖Df(x)‖ ≤ K for every x ∈ ℝⁿ.

3. Lusin step.
- B ∩ D is Borel with Lⁿ(B ∩ D) < ∞. By inner regularity choose a closed C₀ ⊆ B ∩ D with Lⁿ((B ∩ D) \ C₀) < ε'/4.
- For each i ∈ {1, …, n}, apply Lusin's theorem to the Borel function φ_i on the closed (hence Borel) set C₀ of finite measure, with tolerance ε'/(4(n+1)). This gives a closed C_i ⊆ C₀ with Lⁿ(C₀ \ C_i) < ε'/(4(n+1)) and φ_i continuous on C_i.
- Put C := C₀ ∩ C_1 ∩ … ∩ C_n, so C = C₀ when n = 0. Then:
(a) C is closed and C ⊆ B ∩ D.
(b) x ↦ Df(x) is continuous on C. Every φ_i is continuous on C, so for each v = Σ_i v_i e_i the function x ↦ Df(x)v = Σ_i v_i φ_i(x) is continuous on C. In finite dimensions this gives continuity of x ↦ Df(x) on C in operator norm (continuousOn_clm_apply).
(c) B \ C ⊆ (B \ D) ∪ ((B ∩ D) \ C₀) ∪ ⋃_{i=1}^{n} (C₀ \ C_i), so Lⁿ(B \ C) ≤ 0 + ε'/4 + n·ε'/(4(n+1)) < ε'/2.

4. Remainder bound functions.
- For x ≠ y put R(x, y) := (f(y) − f(x) − Df(x)(y − x))/|y − x|. Then |R(x, y)| ≤ (K|y − x| + ‖Df(x)‖|y − x|)/|y − x| ≤ 2K.
- C is a subset of the separable metric space ℝⁿ, hence separable. Fix a countable Q ⊆ C with C ⊆ closure(Q) (take Q = ∅ if C = ∅).
- For k ∈ ℕ and x ∈ ℝⁿ put η_k(x) := sup{|R(x, q)| : q ∈ Q, 0 < |q − x| < 1/(k+1)} if x ∈ C and this set is nonempty, and η_k(x) := 0 otherwise. Thus 0 ≤ η_k ≤ 2K.
- This is the parent's η_k: by (i) below, the supremum over Q equals the supremum of |R(x, y)| over all y ∈ C with 0 < |y − x| < 1/(k+1).

(i) Bound on C: for x, y ∈ C with 0 < |y − x| < 1/(k+1),
|f(y) − f(x) − Df(x)(y − x)| ≤ η_k(x)·|y − x|.
Proof: choose q_j ∈ Q with q_j → y (possible since y ∈ C ⊆ closure(Q)). The condition 0 < |q − x| < 1/(k+1) is open in q, so it holds for q = q_j once j is large, and then |R(x, q_j)| ≤ η_k(x). The map q ↦ R(x, q) is continuous at q = y ≠ x: f is continuous, Df(x) is a fixed linear map, and |q − x| ≠ 0 near y. Hence |R(x, y)| = lim_j |R(x, q_j)| ≤ η_k(x); multiply by |y − x|.

(ii) Measurability.
- For fixed q ∈ Q, define ψ_q(x) := |R(x, q)| if 0 < |q − x| < 1/(k+1), and ψ_q(x) := 0 otherwise.
- ψ_q is Borel. The set {x : 0 < |q − x| < 1/(k+1)} is open. On it, x ↦ f(q) − f(x) − Df(x)(q − x) is Borel, because f is continuous and x ↦ Df(x) is Borel. And x ↦ |q − x| is continuous and nonzero there.
- Since every ψ_q ≥ 0, we have η_k(x) = 1_C(x)·sup_{q ∈ Q} ψ_q(x), with the supremum over ∅ equal to 0.
- This is the Borel indicator of the closed set C times a countable supremum of Borel functions bounded by 2K. Hence η_k is Borel measurable.

(iii) Pointwise convergence on C.
- Let x ∈ C and τ > 0. Since x ∈ D, f is differentiable at x with derivative Df(x). So there is δ > 0 with |f(y) − f(x) − Df(x)(y − x)| ≤ τ|y − x| whenever |y − x| < δ.
- If 1/(k+1) ≤ δ, every q in the set defining η_k(x) has |q − x| < δ. So |R(x, q)| ≤ τ and η_k(x) ≤ τ.
- Hence η_k(x) → 0 as k → ∞, for every x ∈ C.

5. Egoroff step.
- C ⊆ B has finite measure, each η_k is Borel, and η_k → 0 at every point of C.
- By Egoroff's theorem there is a measurable t ⊆ C with Lⁿ(t) < ε'/4 such that η_k → 0 uniformly on A₀ := C \ t.
- A₀ is measurable with finite measure. By inner regularity there is a closed A ⊆ A₀ with Lⁿ(A₀ \ A) < ε'/4.
- Then A is closed, A ⊆ C ⊆ B ∩ D, and η_k → 0 uniformly on A.
- Since B \ A ⊆ (B \ C) ∪ t ∪ (A₀ \ A), we get Lⁿ(B \ A) < ε'/2 + ε'/4 + ε'/4 = ε'.

6. Whitney compatibility: HasWhitneyC1Compatibility A f Df holds.
(i) f is Lipschitz, hence continuous, hence continuous on A.
(ii) Df is continuous on C ⊇ A by 3(b), hence continuous on A.
(iii) Remainder condition.
- Let K' ⊆ A be compact and τ > 0. By uniform convergence on A, choose k with η_k(x) ≤ τ for all x ∈ A. Put δ := 1/(k+1) > 0.
- Let x ∈ K' and y ∈ A with dist(x, y) < δ.
- If y = x, then |f(y) − f(x) − Df(x)(y − x)| = 0 = τ|y − x|.
- Otherwise x, y ∈ C and 0 < |y − x| < 1/(k+1). By 4(i), |f(y) − f(x) − Df(x)(y − x)| ≤ η_k(x)|y − x| ≤ τ|y − x|.

7. Whitney extension and conclusion.
- A is closed, so the Whitney extension theorem gives g : ℝⁿ → ℝ with ContDiff ℝ 1 g and g = f on A. (It also gives Dg = Df on A, which is not needed.)
- Hence B ∩ {x : f(x) ≠ g(x)} ⊆ B \ A.
- So Lⁿ(B ∩ {f ≠ g}) ≤ Lⁿ(B \ A) < ε' ≤ ε. ∎

## Key steps

1. Reduce to a finite tolerance ε' = min(ε, 1); B = closedBall 0 R has finite measure
2. Rademacher: the differentiability set D is Borel and conull; Df is Borel; ‖Df‖ ≤ K
3. Inner regularity plus coordinatewise Lusin (tolerance ε'/(4(n+1))): closed C ⊆ B ∩ D, Df continuous on C, Lⁿ(B \ C) < ε'/2
4. Remainder suprema η_k over a countable dense Q ⊆ C (radius 1/(k+1)): bounded by 2K, Borel, bound |f(y) − f(x) − Df(x)(y − x)| ≤ η_k(x)|y − x| for all x, y ∈ C, and η_k → 0 pointwise on C
5. Egoroff plus inner regularity: closed A ⊆ C with η_k → 0 uniformly on A and Lⁿ(B \ A) < ε'
6. HasWhitneyC1Compatibility A f Df (continuity of f and Df on A; uniform remainder with δ = 1/(k+1))
7. Whitney extension gives a C¹ g with g = f on A, so Lⁿ(B ∩ {f ≠ g}) ≤ Lⁿ(B \ A) < ε

## Reference use

### local-project

Queries:
- `cmp GMT/Ch05/{Contract,Submission}.lean <snapshot>/project/GMT/Ch05/{Contract,Submission}.lean`
- `rg -n 'rsod_lipschitz|rsod_c1_|C1Approx|c1_approx|IsC1Submanifold' <snapshot>/project`
- `grep -n '^theorem\|^def\|notation' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn -i lusin <snapshot>/mathlib/Mathlib --include=*.lean`
- `rg -n 'theorem tendstoUniformlyOn_of_ae_tendsto |theorem isOpen_iUnion_countable|theorem countable_iff_exists_subset_range|theorem contDiff_piLp. |theorem dist_apply_le |theorem LinearMap.exists_antilipschitzWith|theorem measurable_fderiv_apply_const|theorem norm_fderiv_le_of_lipschitz|theorem _root_.MeasurableSet.exists_isClosed_sdiff_lt|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem norm_image_sub_le_of_norm_fderiv_le |theorem continuousOn_clm_apply|theorem ContDiff.continuous_fderiv' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem measurable_fderiv\b\|theorem measurableSet_of_differentiableAt\b\|exists_antilipschitzWith\|theorem finrank_euclideanSpace_fin' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem\|^structure\|^def' .lake/packages/simongmt/Poincare/SimonGMT/{Chapter02/WhitneyJet.lean,Chapter02/WhitneyExtension.lean,Chapter02/AreaCritical.lean,Chapter01/Lusin.lean,Chapter02/Lipschitz.lean}`
- `sed -n 1,200p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/{Rectifiable.lean,SubmanifoldCover.lean}`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 (WhitneyExtension.olean absent)`
- `#print axioms exists_contDiff_one_extension_of_whitney, area_image_criticalSet_eq_zero, exists_isClosed_continuousOn_of_measurable, euclideanHausdorffMeasure_image_le_of_lipschitzOn (private package copy)`
- `grep -rl <each proposed lean_name> <run dir>, GMT, simongmt (collision check)`
- `python3 gmt-compare.contract_scope(Contract.lean, GMT.Ch05.main_theorem); lean_contract.validate_lean_statement(each child type)`
- `lake env lean /tmp/rc1c-check/RC1C/Statements.lean; lake env lean /tmp/rc1c-check2/GMT/Ch05/{Glue2,Glue4,CmpTest,Child3Check}.lean`
- `sed -n 160,275p book/chapter-02.txt (Thm 1.5 printed proof); sed -n 25,66p book/chapter-03.txt (Lemma 1.2 printed proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/rc1c-check/RC1C/Statements.lean`
- `/tmp/rc1c-check2/GMT/Ch05/Glue2.lean`
- `/tmp/rc1c-check2/GMT/Ch05/Glue4.lean`
- `/tmp/rc1c-check2/GMT/Ch05/CmpTest.lean`
- `/tmp/rc1c-check2/GMT/Ch05/Child3Check.lean`

Pins and identity: the snapshot is pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its GMT/Ch05 Contract.lean and Submission.lean are byte-identical to the workspace copies.

No-match results:
- None of the four proposed names occurs in the snapshot project, the run directory or simongmt.
- No Ch05 C¹-approximation, Whitney or immersion-chart lemma exists there.
- IsC1Submanifold occurs only in Ch05 Contract/Submission/README.
- The only C1Approximation hit is the separate Ch02 contract, whose README calls the simongmt Whitney route unbuilt.
- Mathlib has no Lusin continuity theorem (only Lusin–Souslin/separation) and no Whitney C¹ extension.
- simongmt SubmanifoldCover.lean proves only the easy direction of Lemma 1.2.

Usable Mathlib (snapshot paths):
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187).
- measurableSet_of_differentiableAt, measurable_fderiv, measurable_fderiv_apply_const (Analysis/Calculus/FDeriv/Measurable.lean:372, 378, 391).
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947).
- MeasurableSet.exists_isClosed_sdiff_lt (MeasureTheory/Measure/Regular.lean:1036).
- tendstoUniformlyOn_of_ae_tendsto (MeasureTheory/Function/Egorov.lean:205).
- LinearMap.exists_antilipschitzWith and continuousOn_clm_apply (Normed/Module/FiniteDimension.lean:231, 518).
- ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271).
- norm_image_sub_le_of_norm_fderiv_le (Calculus/MeanValue.lean:499).
- contDiff_piLp' (ContDiff/WithLp.lean:78).
- PiLp.dist_apply_le (Normed/Lp/PiLp.lean:652).
- TopologicalSpace.isOpen_iUnion_countable (Topology/Bases.lean:932).
- Set.countable_iff_exists_subset_range (Data/Set/Countable.lean:119).
- finrank_euclideanSpace_fin (InnerProductSpace/PiL2.lean:205).

Usable simongmt (pinned package, outside the snapshot):
- Chapter03.CountablyRectifiable.
- Chapter02 rademacher_ae_differentiableAt and euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- Chapter01 exists_isClosed_continuousOn_of_measurable (Lusin).
- Chapter02 HasWhitneyC1Compatibility and exists_contDiff_one_extension_of_whitney.
- Chapter02 area_image_criticalSet_eq_zero.
- #print axioms shows each uses only propext, Classical.choice and Quot.sound.
- Build caveat: WhitneyExtension.olean is absent from the shared package tree. It was built only in the private copy /tmp/rc1c-pk.

Lean checks (v4.35.0-rc3):
- The four child types elaborate in the comparator contract scope and pass validate_lean_statement.
- The comparator-form targets close with exact Submission.X.
- The parent assembly compiles with only the four child sorries.
- Child 2 compiles from child 1 alone, and child 4 from child 3 alone.
- The independent reviewer produced a complete sorry-free proof of child 3 using only the standard axioms, re-run successfully.
- Its axiom audit shows the parent depends only on children 1 and 3 once 2 and 4 are glued.

Informational, outside the snapshot: the separate gmt-ch02 run has accepted Lean for c1approx_lusin_closed_continuousOn, c1approx_egorov_closed_compact_uniform and c1approx_measurable_remainder_modulus (commits 7faf241, 93121fe, a019cf7).
