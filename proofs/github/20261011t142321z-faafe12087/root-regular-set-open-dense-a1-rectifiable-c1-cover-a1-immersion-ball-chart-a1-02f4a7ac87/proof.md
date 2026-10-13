# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1`
- Child DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.immersion_ball_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4–5 of the parent proof. This is the last paragraph of the printed proof of Simon Ch. 3, Lemma 1.2: if the Jacobian of G is nonzero at a point, then for some σ > 0, G(B̆_σ) is an n-dimensional C¹ submanifold, with G providing a local representation. Here the chart is checked against the frozen definition IsC1Submanifold.

Notation:
- Hⁿ = μHE[n]; Lⁿ = volume on ℝⁿ.
- B_σ(a) = closedBall a σ, B̆_σ(a) = ball a σ, S_σ(a) = sphere a σ.
- DG(x) := fderiv ℝ G x; ‖·‖ on linear maps is the operator norm.

Tools: LinearMap.injective_iff_antilipschitz (or LinearMap.exists_antilipschitzWith), ContDiff.differentiable, ContDiff.continuous_fderiv, Convex.norm_image_sub_le_of_norm_fderiv_le (mean value inequality), isCompact_sphere, isCompact_closedBall, simongmt Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, measure_ball_lt_top.

Let n, ℓ ∈ ℕ, G : ℝⁿ → ℝ^{n+ℓ} with ContDiff ℝ 1 G, and a ∈ ℝⁿ with DG(a) injective. Write L := DG(a).

1. Lower bound for L. L is an injective linear map on the finite-dimensional space ℝⁿ, so it is antilipschitz: there is c > 0 with |Lv| ≥ c|v| for all v ∈ ℝⁿ.
- For n = 0, any c > 0 works since v = 0.
- For n ≥ 1, one may take c := min_{|v| = 1} |Lv|. This is positive because the unit sphere is compact, v ↦ |Lv| is continuous, and Lv ≠ 0 for v ≠ 0.

2. Choice of σ. G is C¹, so it is differentiable everywhere and x ↦ DG(x) is continuous. Choose δ > 0 with ‖DG(z) − L‖ < c/2 whenever |z − a| < δ, and set σ := δ/2 > 0. Then ‖DG(z) − L‖ < c/2 for every z ∈ B_σ(a).

3. Injective derivatives. For z ∈ B_σ(a) and v ∈ ℝⁿ: c|v| ≤ |Lv| ≤ |DG(z)v| + ‖DG(z) − L‖·|v| ≤ |DG(z)v| + (c/2)|v|. Hence |DG(z)v| ≥ (c/2)|v|, so DG(z) is injective for every z ∈ B_σ(a), in particular for every z ∈ B̆_σ(a).

4. Mean value estimates.
- Let h(z) := G(z) − Lz. Then h is differentiable with Dh(z) = DG(z) − L, and ‖Dh(z)‖ ≤ c/2 on the convex set B_σ(a).
- By the mean value inequality, |h(y) − h(x)| ≤ (c/2)|y − x| for x, y ∈ B_σ(a).
- Since G(y) − G(x) = L(y − x) + (h(y) − h(x)), we get:
(a) |G(y) − G(x)| ≥ |L(y − x)| − |h(y) − h(x)| ≥ c|y − x| − (c/2)|y − x| = (c/2)|y − x|. In particular G is injective on B_σ(a).
(b) |G(y) − G(x)| ≤ ‖L‖·|y − x| + (c/2)|y − x| = Λ|y − x|, with Λ := ‖L‖ + c/2. So G is Λ-Lipschitz on B_σ(a).

5. The chart. Let N := G(B̆_σ(a)), V := B̆_σ(a), W := ℝ^{n+ℓ} \ G(S_σ(a)), and φ := G.
(i) V and W are open. V is open as an open ball. S_σ(a) is closed and bounded in ℝⁿ, hence compact. G is continuous, so G(S_σ(a)) is compact, hence closed, and W is open.
(ii) N ⊆ W. Suppose G(x) = G(z) with x ∈ V and z ∈ S_σ(a). Then x, z ∈ B_σ(a), so x = z by 4(a). This contradicts |x − a| < σ = |z − a|. Consequently φ(V) = N = W ∩ N.
(iii) φ is C¹ on V (restriction of the C¹ map G). φ is injective on V ⊆ B_σ(a) by 4(a). Dφ(x) = DG(x) is injective for every x ∈ V by step 3.
(iv) Properness.
- Let K ⊆ W be compact. If x ∈ B_σ(a) and G(x) ∈ K, then x ∉ S_σ(a): otherwise G(x) ∈ G(S_σ(a)), which is disjoint from W ⊇ K. So |x − a| < σ, i.e. x ∈ V.
- Therefore V ∩ G⁻¹(K) = B_σ(a) ∩ G⁻¹(K).
- The latter is closed (K is compact hence closed, and G is continuous) and contained in the compact ball B_σ(a), hence compact.
(v) Let y ∈ N. Then y ∈ W by (ii). So V, W, φ satisfy every requirement of the definition of IsC1Submanifold n at y:
- V is open, W is open, and y ∈ W;
- φ is C¹ on V and injective on V;
- φ(V) = W ∩ N;
- V ∩ φ⁻¹(K) is compact for every compact K ⊆ W;
- Dφ(x) is injective for all x ∈ V.
Hence IsC1Submanifold n N.

6. Finite measure.
- N = G(B̆_σ(a)), and G is Λ-Lipschitz on B̆_σ(a) ⊆ B_σ(a) by 4(b).
- By the Lipschitz image estimate for μHE, Hⁿ(N) ≤ Λⁿ·Hⁿ(B̆_σ(a)).
- Hⁿ on ℝⁿ is Lebesgue measure, so Hⁿ(B̆_σ(a)) = Lⁿ(B̆_σ(a)) < ∞. Hence Hⁿ(N) < ∞.
- Together with step 5, this proves the claim for this σ > 0. ∎

## Key steps

1. Antilipschitz bound: c > 0 with |DG(a)v| ≥ c|v|
2. Choose σ with ‖DG(z) − DG(a)‖ < c/2 on closedBall a σ; then DG(z) is injective there
3. Mean value inequality for G − DG(a): G is injective (|G(y) − G(x)| ≥ (c/2)|y − x|) and Λ-Lipschitz on closedBall a σ
4. Chart V = ball a σ, W = complement of G(sphere a σ), φ = G: W is open, G(V) ⊆ W, G '' V = W ∩ N, properness via V ∩ G⁻¹K = closedBall a σ ∩ G⁻¹K
5. Hⁿ(G(ball a σ)) ≤ Λⁿ·Lⁿ(ball a σ) < ∞

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
