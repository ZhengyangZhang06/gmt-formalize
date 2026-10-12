# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1`
- Child DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.lipschitz_range_c1_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the first part of the printed proof of Simon Ch. 3, Lemma 1.2 ('only if'): the sets Z_j, E_j = F_j(Z_j) and inclusion (1). It is used in the ball-localized form of the last paragraph of step 2 and of step 3 of the parent proof. Uses the sibling rsod_lipschitz_c1_approx_closedBall (child c1_approx_ball).

Notation:
- Hⁿ = μHE[n]; Lⁿ = volume on ℝⁿ; B_m(0) = closedBall 0 m.
- d := n + ℓ, so ℝ^{n+ℓ} = EuclideanSpace ℝ (Fin d), with coordinates v_c for c ∈ Fin d.

Tools: PiLp.dist_apply_le, contDiff_piLp', measure_iUnion_fintype_le, measure_iUnion_null, ENNReal.exists_inv_nat_lt, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, simongmt Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, Nat.pair / Nat.unpair.

Let n, ℓ ∈ ℕ, K ∈ ℝ≥0 and F : ℝⁿ → ℝ^{n+ℓ} K-Lipschitz.

1. Coordinates. For c ∈ Fin d let F_c(x) := F(x)_c. A coordinate of a Euclidean vector is bounded by its norm, so |F_c(x) − F_c(y)| ≤ |F(x) − F(y)| ≤ K|x − y|. Hence each F_c is K-Lipschitz.

2. Scalar approximations. For i ∈ ℕ let ε_i := 1/((i + 1)(d + 1)) ∈ (0, ∞). For all m, i ∈ ℕ and c ∈ Fin d, apply rsod_lipschitz_c1_approx_closedBall to F_c with radius R := m and tolerance ε_i. This gives g_{m,i,c} : ℝⁿ → ℝ with ContDiff ℝ 1 g_{m,i,c} and Lⁿ(B_m(0) ∩ {x : F_c(x) ≠ g_{m,i,c}(x)}) < ε_i.

3. Vector approximations.
- Let G_{m,i}(x) ∈ ℝ^{n+ℓ} be the vector with coordinates (g_{m,i,c}(x))_{c ∈ Fin d}. Every coordinate function of G_{m,i} is C¹, so G_{m,i} is C¹.
- If F(x) ≠ G_{m,i}(x), then F_c(x) ≠ g_{m,i,c}(x) for some c, because vectors with equal coordinates are equal.
- Hence B_m(0) ∩ {F ≠ G_{m,i}} ⊆ ⋃_{c ∈ Fin d} (B_m(0) ∩ {F_c ≠ g_{m,i,c}}).
- By finite subadditivity, Lⁿ(B_m(0) ∩ {F ≠ G_{m,i}}) ≤ d·ε_i = d/((i + 1)(d + 1)) ≤ 1/(i + 1).

4. The exceptional set.
- Let Z := ⋃_{m ∈ ℕ} ⋂_{i ∈ ℕ} (B_m(0) ∩ {F ≠ G_{m,i}}).
- For each m, the inner intersection is contained in B_m(0) ∩ {F ≠ G_{m,i}} for every i. So its Lⁿ-measure is at most 1/(i + 1) for every i ∈ ℕ, and is therefore 0. (If it were some a > 0, pick i with 1/i < a; then 1/(i + 1) ≤ 1/i < a, a contradiction.)
- As a countable union of Lⁿ-null sets, Lⁿ(Z) = 0.

5. Its image is Hⁿ-null.
- On ℝⁿ, Hⁿ = Lⁿ, so Hⁿ(Z) = 0.
- F is K-Lipschitz, in particular on Z. The Lipschitz image estimate gives Hⁿ(F(Z)) ≤ Kⁿ·Hⁿ(Z) = 0.
- Put N₀ := F(Z).

6. Covering.
- Let y = F(x) ∈ F(ℝⁿ). If x ∈ Z, then y ∈ N₀.
- Otherwise choose m ∈ ℕ with |x| ≤ m, so x ∈ B_m(0).
- As x ∉ Z, x ∉ ⋂_i (B_m(0) ∩ {F ≠ G_{m,i}}). So for some i, x ∉ B_m(0) ∩ {F ≠ G_{m,i}}.
- Since x ∈ B_m(0), this means F(x) = G_{m,i}(x), i.e. y ∈ G_{m,i}(ℝⁿ).

7. Enumeration.
- For k ∈ ℕ let G_k := G_{m,i} with (m, i) := Nat.unpair(k).
- Since Nat.unpair(Nat.pair(m, i)) = (m, i), every G_{m,i} occurs among the G_k.
- By step 6, F(ℝⁿ) ⊆ N₀ ∪ ⋃_k G_k(ℝⁿ). Each G_k is C¹ by step 3, and Hⁿ(N₀) = 0 by step 5. ∎

## Key steps

1. Each coordinate F_c of F is K-Lipschitz
2. Apply rsod_lipschitz_c1_approx_closedBall to every (m, i, c) with radius m and tolerance ε_i = 1/((i+1)(n+ℓ+1))
3. Assemble coordinates into C¹ maps G_{m,i} with Lⁿ(B_m(0) ∩ {F ≠ G_{m,i}}) ≤ 1/(i+1)
4. Z = ⋃_m ⋂_i (B_m(0) ∩ {F ≠ G_{m,i}}) is Lⁿ-null
5. Hⁿ = Lⁿ on ℝⁿ and the Lipschitz image bound give Hⁿ(F(Z)) = 0
6. Off Z, F(x) = G_{m,i}(x) for some i (with m ≥ |x|); enumerate the G_{m,i} via Nat.unpair

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
