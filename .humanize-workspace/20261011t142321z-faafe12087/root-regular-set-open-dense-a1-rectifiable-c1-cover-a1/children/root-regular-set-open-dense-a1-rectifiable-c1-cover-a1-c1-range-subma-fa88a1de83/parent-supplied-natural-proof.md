# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1`
- Child DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_range_submanifold_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 (critical values) and step 6 (Lindelöf) of the parent proof. This is the last paragraph of the printed proof of Simon Ch. 3, Lemma 1.2:
- by the area formula, the image of the set where the Jacobian of G vanishes is Hⁿ-null;
- near each point where the Jacobian is nonzero, G(B̆_σ(x)) is an n-dimensional C¹ submanifold;
- so the image is a null set plus countably many submanifolds.
Uses the sibling rsod_c1_immersion_ball_isC1Submanifold (child immersion_ball_chart).

Tools:
- simongmt Chapter02.area_image_criticalSet_eq_zero, in the prebuilt module Poincare.SimonGMT.Chapter02.AreaCritical. It states μHE[finrank ℝ E](f '' {x | DifferentiableAt ℝ f x ∧ ¬ Injective (fderiv ℝ f x)}) = 0.
- finrank_euclideanSpace_fin, ContDiff.differentiable, TopologicalSpace.isOpen_iUnion_countable, Set.countable_iff_exists_subset_range.

Notation: Hⁿ = μHE[n]; DG(x) := fderiv ℝ G x.

Let n, ℓ ∈ ℕ and G : ℝⁿ → ℝ^{n+ℓ} with ContDiff ℝ 1 G. In particular G is differentiable at every point.

1. Critical values. Let Crit := {x : G is differentiable at x and DG(x) is not injective}. Since finrank ℝ ℝⁿ = n, the critical-value theorem gives Hⁿ(G(Crit)) = 0. Put N₀ := G(Crit).

2. Regular points.
- Let Reg := {x : DG(x) is injective}. Since G is differentiable everywhere, every x ∉ Reg belongs to Crit.
- For each a ∈ Reg, apply rsod_c1_immersion_ball_isC1Submanifold to n, ℓ, G and a, using ContDiff ℝ 1 G and injectivity of DG(a). This yields σ_a > 0 such that P_a := G(B̆_{σ_a}(a)) satisfies IsC1Submanifold n P_a and Hⁿ(P_a) < ∞.
- Fix such a choice a ↦ σ_a.

3. Countable subcover. The sets B̆_{σ_a}(a), a ∈ Reg, are open in ℝⁿ, which is second countable. Hence there is a countable T ⊆ Reg with ⋃_{a ∈ T} B̆_{σ_a}(a) = ⋃_{a ∈ Reg} B̆_{σ_a}(a).

4. Enumeration.
- If Reg = ∅, put N_q := ∅ for all q ∈ ℕ. The empty set satisfies IsC1Submanifold n vacuously and has measure 0 < ∞.
- If Reg ≠ ∅, the countable set T ⊆ Reg is contained in the range of some e : ℕ → Reg. Put N_q := P_{e(q)}; by step 2 it satisfies IsC1Submanifold n and Hⁿ(N_q) < ∞.

5. Covering.
- Let y ∈ G(ℝⁿ), say y = G(x).
- If DG(x) is not injective, then x ∈ Crit and y ∈ N₀.
- Otherwise x ∈ Reg (so Reg ≠ ∅), and x ∈ B̆_{σ_x}(x) ⊆ ⋃_{a ∈ Reg} B̆_{σ_a}(a) = ⋃_{a ∈ T} B̆_{σ_a}(a).
- Choose a ∈ T with x ∈ B̆_{σ_a}(a), and q with e(q) = a. Then y = G(x) ∈ P_a = N_q.
- Hence G(ℝⁿ) ⊆ N₀ ∪ ⋃_q N_q, with Hⁿ(N₀) = 0 and every N_q an n-dimensional C¹ submanifold of finite Hⁿ-measure. ∎

## Key steps

1. N₀ = G(Crit) is Hⁿ-null by area_image_criticalSet_eq_zero (finrank ℝ ℝⁿ = n)
2. At each regular point a, rsod_c1_immersion_ball_isC1Submanifold gives σ_a with G(ball a σ_a) a finite-measure IsC1Submanifold
3. Second countability: countably many of the balls ball a σ_a cover all regular points
4. Enumerate the chosen patches through e : ℕ → Reg (or use ∅ when there are no regular points)
5. Every G(x) lies in N₀ (critical x) or in some patch (regular x)

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
