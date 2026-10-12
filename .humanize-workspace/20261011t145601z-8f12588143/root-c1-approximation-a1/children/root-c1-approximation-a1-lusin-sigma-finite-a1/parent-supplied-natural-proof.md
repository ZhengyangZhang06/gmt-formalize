# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_approximation-a1`
- Child DAG node: `root.c1_approximation-a1.lusin_sigma_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the Lusin step of Simon's proof of Ch. 2, Theorem 1.5 (chapter-02.txt lines 248–251: “By Lusin's theorem (which applies to sets of infinite measure for Lⁿ) there is a closed set C ⊆ B such that ∇f|C is continuous and Lⁿ(ℝⁿ ∖ C) < ε/2”), i.e. Step 4 of the parent proof. Here the differentiability set B is replaced by an arbitrary Borel set S, and ∇f by an arbitrary Borel map u into a finite-dimensional space. The ingredients are Simon Ch. 1, Theorem 1.15(2) (closed inner regularity, chapter-01.txt lines 274–285) and Ch. 1, Theorem 1.17 (Lusin's theorem for real-valued functions on sets of finite measure, chapter-01.txt lines 346–380). Notation: |x| is the Euclidean norm, B_r(0) the open ball of radius r about 0 (B_0(0) := ∅), Lⁿ = volume.

Statement. Let F be a finite-dimensional real normed space with its Borel σ-algebra, u : ℝⁿ → F Borel, S ⊆ ℝⁿ Borel and ε ∈ (0, ∞]. Then there is a closed C ⊆ S with Lⁿ(S ∖ C) < ε and u|C continuous.

Proof.

1. Closed inner regularity. For every Borel T ⊆ ℝⁿ with Lⁿ(T) < ∞ and every δ ∈ (0, ∞] there is a closed F' ⊆ T with Lⁿ(T ∖ F') < δ. This is Simon 1.15(2) for the Radon measure Lⁿ. In Lean, Lebesgue measure on Rn n is weakly regular and the statement is MeasurableSet.exists_isClosed_sdiff_lt.

2. Real-valued Lusin on a set of finite measure. For every Borel T with Lⁿ(T) < ∞, every Borel v : ℝⁿ → ℝ and every δ ∈ (0, ∞] there is a closed C' ⊆ T with Lⁿ(T ∖ C') < δ and v|C' continuous. This is Simon 1.17. In Lean it is Poincare.SimonGMT.Chapter01.exists_isClosed_continuousOn_of_measurable (module Poincare.SimonGMT.Chapter01.Lusin) applied with ν := volume; its regularity hypothesis hreg is exactly Step 1.

3. F-valued Lusin on a set of finite measure. Let T be Borel with Lⁿ(T) < ∞ and δ ∈ (0, ∞]. Let d := dim F, fix a basis b_1, …, b_d of F, and let e : F → ℝ^d be the coordinate isomorphism (Lean: (Module.finBasis ℝ F).equivFunL). Both e and e⁻¹ are linear maps between finite-dimensional spaces, hence continuous. The coordinate functions u_l := (e ∘ u)_l (l = 1, …, d) are Borel, being compositions of the Borel map u with continuous maps.
Choose positive reals δ_0, δ_1, …, δ_d with δ_0 + δ_1 + … + δ_d < δ. By Step 1 there is a closed C^0 ⊆ T with Lⁿ(T ∖ C^0) < δ_0. By Step 2, for each l = 1, …, d there is a closed C^l ⊆ T with Lⁿ(T ∖ C^l) < δ_l and u_l|C^l continuous. Put C_T := C^0 ∩ C^1 ∩ … ∩ C^d.
Then C_T is closed, and C_T ⊆ C^0 ⊆ T; the set C^0 guarantees this inclusion also when d = 0. Moreover T ∖ C_T = ⋃_{l=0}^{d} (T ∖ C^l), so Lⁿ(T ∖ C_T) ≤ Σ_l Lⁿ(T ∖ C^l) < δ. Every u_l is continuous on C_T ⊆ C^l, so e ∘ u is continuous on C_T, because a map into ℝ^d is continuous on a set iff all its coordinates are. Therefore u = e⁻¹ ∘ (e ∘ u) is continuous on C_T.

4. Exhaustion by annuli. For j = 1, 2, … let T_j := S ∩ {x : j − 1 ≤ |x| < j} = S ∩ (B_j(0) ∖ B_{j−1}(0)). Each T_j is Borel with Lⁿ(T_j) ≤ Lⁿ(B_j(0)) < ∞, and S is the disjoint union of the T_j: a point x ∈ S lies in T_j for j = ⌊|x|⌋ + 1.
Choose positive reals ε_j with Σ_{j≥1} ε_j < ε. For instance ε_j := 2^{−j−1} min{ε, 1} works: its sum is min{ε, 1}/2 < ε, also when ε = ∞. By Step 3 there are closed sets C_j ⊆ T_j with Lⁿ(T_j ∖ C_j) < ε_j and u|C_j continuous. Put C := ⋃_{j≥1} C_j. Clearly C ⊆ S.

5. C is closed and u|C is continuous. The family (C_j) is locally finite: if z ∈ ℝⁿ and y ∈ C_j ∩ B_1(z), then j − 1 ≤ |y| < |z| + 1, so the ball B_1(z) meets C_j only for the finitely many j < |z| + 2. A union of a locally finite family of closed sets is closed (Lean: LocallyFinite.isClosed_iUnion), so C is closed. Moreover u is continuous on C by the pasting lemma for locally finite closed families (Lean: LocallyFinite.continuousOn_iUnion): each point of C has a neighbourhood meeting only finitely many C_j, and a map continuous on each of finitely many closed sets is continuous on their union.

6. Measure estimate. If x ∈ S ∖ C, let j be such that x ∈ T_j. Since x ∉ C ⊇ C_j, we have x ∈ T_j ∖ C_j. Hence S ∖ C ⊆ ⋃_j (T_j ∖ C_j), and by countable subadditivity Lⁿ(S ∖ C) ≤ Σ_j Lⁿ(T_j ∖ C_j) ≤ Σ_j ε_j < ε. ∎

## Key steps

1. Closed inner regularity of Lⁿ on finite-measure Borel sets (Simon 1.15(2); MeasurableSet.exists_isClosed_sdiff_lt).
2. Real-valued finite-measure Lusin (Simon 1.17; SimonGMT exists_isClosed_continuousOn_of_measurable with ν := volume).
3. F-valued finite-measure case: intersect the closed sets for the basis coordinates of u, plus one inner-regularity set; the errors sum to less than δ.
4. Exhaust S by the bounded pieces T_j = S ∩ {j−1 ≤ |x| < j} and choose closed C_j ⊆ T_j with errors ε_j, where Σ ε_j < ε.
5. C = ⋃ C_j is a locally finite union, hence closed, and u|C is continuous by pasting; Lⁿ(S ∖ C) ≤ Σ ε_j < ε.

## Reference use

### local-project

Queries:
- `rg -n -i "lusin" mathlib/Mathlib (snapshot)`
- `rg -n "theorem tendstoUniformlyOn_of_ae_tendsto" mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `rg -n "exists_isClosed_sdiff_lt|exists_isClosed_lt_add" mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n "theorem measurableSet_of_differentiableAt|theorem measurable_fderiv" mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `rg -n "theorem LipschitzWith.ae_differentiableAt" mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n "protected theorem Measurable.iSup" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `rg -n "measurable_apply'|Measurable.apply_continuousLinearMap" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `rg -n "isClosed_iUnion|continuousOn_iUnion" mathlib/Mathlib/Topology/LocallyFinite.lean`
- `rg -n "IsSeparable.exists_countable_dense_subset|IsSeparable.of_separableSpace|exists_countable_dense" mathlib/Mathlib/Topology`
- `rg -n "mem_closure_iff_nhdsWithin_neBot|theorem le_of_tendsto" mathlib/Mathlib/Topology`
- `rg -n "theorem tendstoUniformlyOn_iff|IsBounded.subset_ball|eventually_all_finset" mathlib/Mathlib`
- `rg -n "union|iUnion|biUnion" mathlib/Mathlib/Topology/UniformSpace/UniformConvergence*.lean LocallyUniformConvergence.lean`
- `grep -n "theorem|structure" simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean Chapter02/WhitneyJet.lean Chapter01/Lusin.lean`
- `grep -rn rademacher_ae_differentiableAt simongmt/Poincare`
- `grep -rl Chapter02.WhitneyExtension simongmt/Poincare; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `grep -rl <each proposed lean_name> .humanize simongmt/Poincare; python dag.json lean_name listing`
- `#check ENNReal.exists_pos_sum_of_countable, Poincare.SimonGMT.Chapter02.rademacher_ae_differentiableAt; elaboration of all child statements via gmt-compare.py contract_scope/child_modules in a /tmp scratch copy`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/ClusterPt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`

Snapshot: project d09bc8a, whose Contract.lean is byte-identical to the workspace copy, and Mathlib 25730c7c, plus the pinned simongmt package.

Available in Mathlib:
- finite-measure Egorov: MeasureTheory.tendstoUniformlyOn_of_ae_tendsto (Egorov.lean:205; gives μ t ≤ ε and uniform convergence on s ∖ t)
- closed inner regularity: MeasurableSet.exists_isClosed_sdiff_lt (Regular.lean:1036); volume on Rn n is WeaklyRegular
- Rademacher: LipschitzWith.ae_differentiableAt (Rademacher.lean:385)
- measurableSet_of_differentiableAt and measurable_fderiv (FDeriv/Measurable.lean:372, 378), with the Borel instances on E →L[ℝ] F
- Measurable.iSup for conditionally complete linear orders, so it covers ℝ with junk values (BorelSpace/Order.lean:909)
- LocallyFinite.isClosed_iUnion and LocallyFinite.continuousOn_iUnion (LocallyFinite.lean:128, 103)
- IsSeparable.of_separableSpace and IsSeparable.exists_countable_dense_subset; mem_closure_iff_nhdsWithin_neBot; le_of_tendsto; Metric.tendstoUniformlyOn_iff; Filter.eventually_all_finset; ENNReal.exists_pos_sum_of_countable

Available in SimonGMT:
- real-valued finite-measure Lusin exists_isClosed_continuousOn_of_measurable (Chapter01/Lusin.lean:127). The module is built but not imported by the contract.
- rademacher_ae_differentiableAt (Chapter02/Lipschitz.lean:192)
- HasWhitneyC1Compatibility (WhitneyJet.lean:34; fields continuous_value, continuous_derivative, remainder)
- exists_contDiff_one_extension_of_whitney (WhitneyExtension.lean:373). This module is not imported by the contract and has no prebuilt .olean, but it compiles against the pinned Mathlib.

Not found, so supplied as children:
- no Lusin continuity theorem in Mathlib (only Lusin–Souslin)
- no σ-finite or vector-valued Lusin in either library
- no σ-finite Egorov with closed sets
- no finite-union lemma for TendstoUniformlyOn
- no C¹ approximation theorem in either library

The proposed lean_names are unused in the run directory and in SimonGMT. All four child types elaborate in the comparator's exact child context, and complete Lean proofs of the children and of the parent from them compile with standard axioms only.
