# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_approximation-a1`
- Child DAG node: `root.c1_approximation-a1.scalar_c1_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Ch. 2, Theorem 1.5 (C¹ Approximation Theorem): statement chapter-02.txt lines 165–168, printed proof lines 246–266. This is Steps 3, 4 and 8 of the parent proof for scalar f. Steps 5–7 are supplied by the sibling uniform_remainder, and the σ-finite Lusin step by the sibling lusin_sigma_finite. Notation: Lⁿ = volume, and Dh(x) = fderiv ℝ h x, with Mathlib's convention that this is 0 where h is not differentiable.

Statement. For n ∈ ℕ, K ≥ 0, a K-Lipschitz f : ℝⁿ → ℝ and ε ∈ (0, ∞], there is a C¹ map g : ℝⁿ → ℝ with Lⁿ({x : f(x) ≠ g(x) or Df(x) ≠ Dg(x)}) < ε.

Proof.

1. Rademacher (Simon lines 246–248). Let B := {x : f is differentiable at x}. B is Borel, being the differentiability set of a continuous map (Lean: measurableSet_of_differentiableAt). By Rademacher's theorem, Lⁿ(ℝⁿ ∖ B) = 0 (Simon Ch. 2, Theorem 1.4, chapter-02.txt line 62; Lean: LipschitzWith.ae_differentiableAt, or Poincare.SimonGMT.Chapter02.rademacher_ae_differentiableAt). The map Df : ℝⁿ → L(ℝⁿ, ℝ) is Borel (Lean: measurable_fderiv). Note that ε/2 ∈ (0, ∞].

2. Lusin (Simon lines 248–251). Apply the sibling theorem lusin_sigma_finite (Lean: Submission.lusin_closed_subset_continuousOn_volume) with F := L(ℝⁿ, ℝ) (finite-dimensional, with its Borel σ-algebra), u := Df, S := B and ε/2. This gives a closed C ⊆ B with Lⁿ(B ∖ C) < ε/2 such that Df|C is continuous.

3. Uniform remainder (Simon lines 251–265). C is closed, hence Borel, and for every x ∈ C ⊆ B the function f is differentiable at x with derivative Df(x) (Lean: DifferentiableAt.hasFDerivAt). Apply the sibling theorem uniform_remainder (Lean: Submission.lipschitz_uniform_remainder_on_closed_subset) to f, K, L := Df, S := C and ε/2. This gives a closed A ⊆ C with Lⁿ(C ∖ A) < ε/2 such that for every compact Q ⊆ A and ε' > 0 there is δ > 0 with |f(y) − f(x) − Df(x)(y − x)| ≤ ε'|y − x| for all x ∈ Q and y ∈ A with |x − y| < δ.

4. Whitney's hypotheses (Simon lines 264–266). On the closed set A take h := f with the gradient field Df.
- h is continuous on A, since f is Lipschitz.
- Df is continuous on A, since A ⊆ C and Df|C is continuous.
- The estimate of Step 3 is exactly 1.6(‡): R(x, y) → 0 as y → x with y ∈ A, uniformly for x in each compact subset of A.
In Lean these three facts are the fields continuous_value, continuous_derivative and remainder of Poincare.SimonGMT.Chapter02.HasWhitneyC1Compatibility A f (fderiv ℝ f). The remainder field has literally the form of the conclusion of Step 3.

5. Whitney extension (Simon Ch. 2, Theorem 1.6, chapter-02.txt lines 173–184). Whitney's theorem (Lean: Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney, module Poincare.SimonGMT.Chapter02.WhitneyExtension) gives g : ℝⁿ → ℝ with g ∈ C¹(ℝⁿ) (ContDiff ℝ 1 g), g = f on A, and HasFDerivAt g (Df(a)) a for every a ∈ A. Hence Dg(a) = Df(a) for all a ∈ A (Lean: HasFDerivAt.fderiv).

6. Measure estimate. By Step 5, every x with f(x) ≠ g(x) or Df(x) ≠ Dg(x) lies outside A. Since A ⊆ C ⊆ B, we have ℝⁿ ∖ A ⊆ (ℝⁿ ∖ B) ∪ (B ∖ C) ∪ (C ∖ A). Therefore Lⁿ({f ≠ g} ∪ {Df ≠ Dg}) ≤ Lⁿ(ℝⁿ ∖ B) + Lⁿ(B ∖ C) + Lⁿ(C ∖ A) < 0 + ε/2 + ε/2 = ε. The strict inequality holds in [0, ∞] also when ε = ∞, because then Lⁿ(B ∖ C) < ε/2 and Lⁿ(C ∖ A) < ε/2 are finite (Lean: ENNReal.add_lt_add, ENNReal.add_halves). ∎

Lean remark. The module Poincare.SimonGMT.Chapter02.WhitneyExtension is not imported by the frozen contract and has no prebuilt .olean in the pinned package tree, although its dependencies WhitneyJet and WhitneyPartition are built. Adding the import compiles it; this was checked against the pinned Mathlib and takes about 25 s.

## Key steps

1. Rademacher: the differentiability set B is Borel of full measure, and Df is Borel.
2. Sibling Lusin with u = Df on S = B and ε/2: closed C ⊆ B, Lⁿ(B ∖ C) < ε/2, Df|C continuous.
3. Sibling uniform_remainder with L = Df on S = C and ε/2: closed A ⊆ C, Lⁿ(C ∖ A) < ε/2, remainder estimate 1.6(‡) on A.
4. HasWhitneyC1Compatibility A f Df and SimonGMT's Whitney extension: a C¹ g with g = f and Dg = Df on A.
5. The exceptional set lies in (ℝⁿ ∖ B) ∪ (B ∖ C) ∪ (C ∖ A), of measure < 0 + ε/2 + ε/2 = ε.

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
