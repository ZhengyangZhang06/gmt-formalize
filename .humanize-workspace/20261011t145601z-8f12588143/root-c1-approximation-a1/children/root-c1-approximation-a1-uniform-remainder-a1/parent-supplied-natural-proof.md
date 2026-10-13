# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_approximation-a1`
- Child DAG node: `root.c1_approximation-a1.uniform_remainder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon's proof of Ch. 2, Theorem 1.5, chapter-02.txt lines 251–265. The ingredients are: R(x, y) as in 1.6(‡) (lines 179–181); η_k(x) = sup{|R(x, y)| : y ∈ C ∩ B_{1/k}(x) ∖ {x}} (line 258); “η_k ↓ 0 pointwise in C” (line 260); Egoroff and the closed set A (lines 260–265); “and 1.6(‡) holds” (line 265). This is Steps 5–7 of the parent proof together with the verification of 1.6(‡) in its Step 8. The closed set C is replaced by an arbitrary Borel set S on which f is differentiable, and Df by an arbitrary Borel map L with L(x) = Df(x) on S. The continuity of Df|C, used in the parent's measurability remark, is not needed: continuity of f suffices. Notation: |·| is the Euclidean norm, ‖L(x)‖ the operator norm, Lⁿ = volume, and for y ≠ x, R(x, y) := (f(y) − f(x) − L(x)(y − x))/|y − x|.

Statement. Let f : ℝⁿ → ℝ be K-Lipschitz, L : ℝⁿ → L(ℝⁿ, ℝ) Borel, S ⊆ ℝⁿ Borel, f differentiable at every x ∈ S with derivative L(x), and ε ∈ (0, ∞]. Then there is a closed A ⊆ S with Lⁿ(S ∖ A) < ε such that for every compact Q ⊆ A and every ε' > 0 there is δ > 0 with |f(y) − f(x) − L(x)(y − x)| ≤ ε'|y − x| for all x ∈ Q and y ∈ A with |x − y| < δ.

Proof.

1. The functions η_k. For k ≥ 1 and x, y ∈ ℝⁿ let φ_k(x, y) := |R(x, y)| if 0 < |y − x| < 1/k, and φ_k(x, y) := 0 otherwise. For every x ∈ ℝⁿ let η_k(x) := sup_{y ∈ S} φ_k(x, y) (η_k :≡ 0 if S = ∅). For x ∈ S this is Simon's η_k(x) = sup{|R(x, y)| : y ∈ S ∩ B_{1/k}(x) ∖ {x}} with the convention sup ∅ = 0. We use the same formula at x ∉ S, where the values play no role.
If 0 < |y − x| < 1/k, then |f(y) − f(x)| ≤ K|y − x| and |L(x)(y − x)| ≤ ‖L(x)‖ |y − x|, so |R(x, y)| ≤ K + ‖L(x)‖. Hence 0 ≤ φ_k(x, y) ≤ K + ‖L(x)‖ for all x, y. So η_k(x) is a real number with 0 ≤ η_k(x) ≤ K + ‖L(x)‖, and φ_k(x, y) ≤ η_k(x) for every y ∈ S.

2. η_k → 0 pointwise on S (Simon lines 253, 260). Let x ∈ S and e > 0. Since f is differentiable at x with derivative L(x), there is ρ > 0 such that |f(y) − f(x) − L(x)(y − x)| ≤ (e/2)|y − x| whenever |y − x| < ρ. Let k > 1/ρ. If y ∈ S and 0 < |y − x| < 1/k, then |y − x| < ρ and so φ_k(x, y) = |R(x, y)| ≤ e/2. For all other y ∈ S, φ_k(x, y) = 0. Hence 0 ≤ η_k(x) ≤ e/2 < e for all k > 1/ρ, i.e. η_k(x) → 0.

3. Each η_k is Borel (parent Step 5). Since ℝⁿ is a separable metric space, S has a countable subset D with S ⊆ closure(D) (Lean: TopologicalSpace.IsSeparable.exists_countable_dense_subset).
Fix k and x. We claim η_k(x) = M := sup_{y ∈ D} φ_k(x, y). If S = ∅, then D = ∅ and both sides are 0. Otherwise D ≠ ∅ because S ⊆ closure(D), so M ≥ 0; and M ≤ η_k(x) because D ⊆ S.
For the reverse inequality let y ∈ S. If y lies outside the open shell U := {z : 0 < |z − x| < 1/k}, then φ_k(x, y) = 0 ≤ M. If y ∈ U, the function z ↦ |R(x, z)| = |f(z) − f(x) − L(x)(z − x)|/|z − x| is continuous at z = y, because f is continuous and |y − x| > 0. Since y ∈ closure(D) and U is a neighbourhood of y, there are points z ∈ D ∩ U arbitrarily close to y, and for each of them |R(x, z)| = φ_k(x, z) ≤ M. Letting z → y through D ∩ U gives φ_k(x, y) = |R(x, y)| ≤ M (Lean: le_of_tendsto along 𝓝[D] y, which is non-trivial by mem_closure_iff_nhdsWithin_neBot). Taking the supremum over y ∈ S gives η_k(x) ≤ M, which proves the claim.
Next, for fixed y the function x ↦ φ_k(x, y) is Borel. The set {x : 0 < |y − x| < 1/k} is open, and on it x ↦ |f(y) − f(x) − L(x)(y − x)|/|y − x| is Borel: f is continuous, L is Borel, the evaluation map (T, v) ↦ T v is continuous on L(ℝⁿ, ℝ) × ℝⁿ (so x ↦ L(x)(y − x) is Borel), and x ↦ |y − x| is continuous. Therefore η_k = sup_{y ∈ D} φ_k(·, y) is the pointwise supremum of countably many Borel functions and is finite everywhere, hence Borel (Lean: Measurable.iSup over the countable index type D).

4. Egoroff and the closed set (Simon lines 260–265). Apply the sibling theorem egorov_sigma_finite (Lean: Submission.egorov_closed_subset_uniformOn_compact_volume) to the Borel functions η_k, the Borel limit g :≡ 0, the Borel set S and ε. Its convergence hypothesis, η_k(x) → 0 for x ∈ S, holds by Step 2. It yields a closed A ⊆ S with Lⁿ(S ∖ A) < ε such that η_k → 0 uniformly on every compact Q ⊆ A.

5. The estimate 1.6(‡) on A (Simon line 265). Let Q ⊆ A be compact and ε' > 0. By uniform convergence on Q there is k₀ ≥ 1 with η_{k₀}(x) < ε' for all x ∈ Q. Put δ := 1/k₀ > 0, and let x ∈ Q and y ∈ A with |x − y| < δ. If y = x, both sides of the desired inequality vanish. Otherwise 0 < |y − x| < 1/k₀ and y ∈ A ⊆ S, so by Step 1 |R(x, y)| = φ_{k₀}(x, y) ≤ η_{k₀}(x) < ε'. That is, |f(y) − f(x) − L(x)(y − x)| ≤ ε'|y − x|. ∎

## Key steps

1. Define φ_k(x,y) = |R(x,y)| on the shell 0 < |y−x| < 1/k (0 elsewhere) and η_k(x) = sup_{y∈S} φ_k(x,y); the Lipschitz bound gives 0 ≤ η_k(x) ≤ K + ‖L(x)‖.
2. Differentiability at x ∈ S with derivative L(x) gives η_k(x) → 0.
3. Borel measurability: η_k is the supremum over a countable D ⊆ S with S ⊆ closure(D), by continuity of f off the diagonal; each x ↦ φ_k(x,y) is Borel because L is Borel.
4. Apply the sibling σ-finite Egoroff theorem with limit 0: closed A ⊆ S, Lⁿ(S ∖ A) < ε, uniform convergence on compact subsets of A.
5. η_{k₀} < ε' on Q gives |f(y) − f(x) − L(x)(y − x)| ≤ ε'|y − x| for y ∈ A, |x − y| < 1/k₀.

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
