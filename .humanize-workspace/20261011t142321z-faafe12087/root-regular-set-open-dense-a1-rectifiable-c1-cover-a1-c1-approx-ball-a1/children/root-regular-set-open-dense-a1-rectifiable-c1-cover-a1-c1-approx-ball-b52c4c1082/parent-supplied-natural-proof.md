# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1`
- Child DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1.uniform_taylor_remainder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4–5 of the parent proof. These follow Simon Ch. 2, proof of Theorem 1.5 (p. 44): "For each k … let η_k(x) = sup{|R(x, y)| : y ∈ C ∩ B_{1/k}(x) \ {x}}. Then η_k ↓ 0 pointwise in C, and hence by Egoroff's Theorem … there is an Lⁿ-measurable set A₀ ⊆ C such that Lⁿ(C \ A₀) < ε/4 and η_k converges uniformly to zero … Since we can take a closed set A ⊆ A₀ with Lⁿ(A₀ \ A) < ε/4 …".

Here C is any closed set of finite measure on which f is differentiable. The parent applies the statement to its Lusin set C ⊆ B_R(0) ∩ D with δ = ε'/2. The two tolerances below are then exactly the parent's ε'/4 and ε'/4. Continuity of Df on C is not used.

Notation and tools:
- Lⁿ = volume on ℝⁿ = EuclideanSpace ℝ (Fin n).
- |·| is the Euclidean norm (for real numbers ‖·‖ = |·|), ‖·‖ is the operator norm on L(ℝⁿ, ℝ), and Df(x) := fderiv ℝ f x.
- norm_fderiv_le_of_lipschitz: ‖Df(x)‖ ≤ K for every x ∈ ℝⁿ.
- Separability: IsSeparable.of_separableSpace and IsSeparable.exists_countable_dense_subset.
- Measurability: measurable_fderiv; ContinuousLinearMap.measurable_apply₂; Measurable.iSup (countable suprema of Borel real functions); Measurable.indicator.
- Egoroff: tendstoUniformlyOn_of_ae_tendsto, for strongly measurable functions on a measurable set of finite measure. It returns a measurable t whose measure is at most the tolerance.
- Inner regularity: MeasurableSet.exists_isClosed_sdiff_lt (Lⁿ on ℝⁿ is weakly regular).

Let n, K, f, C and δ be as in the statement.

1. Finite tolerance. Put δ' := min(δ, 1). Then 0 < δ' ≤ 1, δ' < ∞ and δ' ≤ δ. It suffices to find a closed A ⊆ C with the uniform estimate and Lⁿ(C \ A) < δ'.

2. Remainder and its bound. For x ≠ y put R(x, y) := (f(y) − f(x) − Df(x)(y − x))/|y − x|. We have |f(y) − f(x)| ≤ K|y − x| and |Df(x)(y − x)| ≤ ‖Df(x)‖|y − x| ≤ K|y − x|. So |f(y) − f(x) − Df(x)(y − x)| ≤ 2K|y − x| for all x, y, hence |R(x, y)| ≤ 2K.

3. Countable dense subset. ℝⁿ is a separable metric space, so C is separable. Fix a countable Q ⊆ C with C ⊆ closure(Q); Q = ∅ if C = ∅.

4. The functions ψ and η.
- For k ∈ ℕ and q ∈ ℝⁿ define ψ_{k,q} : ℝⁿ → ℝ by ψ_{k,q}(x) := |R(x, q)| if 0 < |q − x| < 1/(k+1), and ψ_{k,q}(x) := 0 otherwise. By step 2, 0 ≤ ψ_{k,q} ≤ 2K.
- Define η_k(x) := sup_{q ∈ Q} ψ_{k,q}(x) if x ∈ C (the supremum over Q = ∅ is 0), and η_k(x) := 0 if x ∉ C. Then 0 ≤ η_k ≤ 2K.
- For all x ∈ C and q ∈ Q, ψ_{k,q}(x) ≤ η_k(x), because the family (ψ_{k,q}(x))_{q ∈ Q} is bounded above by 2K.
- Every ψ_{k,q} ≥ 0. So for x ∈ C, η_k(x) equals sup{|R(x, q)| : q ∈ Q, 0 < |q − x| < 1/(k+1)} when this set is nonempty, and 0 otherwise. This is the parent's η_k.

5. Bound on C. Claim: for k ∈ ℕ and x, y ∈ C with 0 < |y − x| < 1/(k+1),
|f(y) − f(x) − Df(x)(y − x)| ≤ η_k(x)·|y − x|.
Proof:
- The set W := {q : 0 < |q − x| < 1/(k+1)} is open and contains y.
- The map q ↦ |R(x, q)| = |f(q) − f(x) − Df(x)(q − x)|/|q − x| is continuous at q = y: f is continuous (it is Lipschitz), Df(x) is a fixed continuous linear map, and |y − x| ≠ 0.
- Since y ∈ C ⊆ closure(Q), there are q_j ∈ Q with q_j → y. W is a neighbourhood of y, so q_j ∈ W for all large j. Then |R(x, q_j)| = ψ_{k,q_j}(x) ≤ η_k(x) by step 4, since x ∈ C.
- Letting j → ∞ gives |R(x, y)| ≤ η_k(x). Multiplying by |y − x| > 0 proves the claim.

6. Measurability. Fix k and q.
- U := {x : 0 < |q − x| < 1/(k+1)} is open, hence Borel.
- x ↦ Df(x)(q − x) is Borel. The map x ↦ (Df(x), q − x) into L(ℝⁿ, ℝ) × ℝⁿ is Borel, since x ↦ Df(x) is Borel (measurable_fderiv) and x ↦ q − x is continuous. Evaluation (L, v) ↦ L v is Borel on this product of second-countable spaces (ContinuousLinearMap.measurable_apply₂). Compose the two.
- f is continuous, so x ↦ f(q) − f(x) − Df(x)(q − x) is Borel.
- Hence x ↦ |f(q) − f(x) − Df(x)(q − x)|/|q − x| is Borel, as a quotient of a Borel function by a continuous one.
- ψ_{k,q} equals this function on U and 0 off U, so ψ_{k,q} is Borel.
- Q is countable, so x ↦ sup_{q ∈ Q} ψ_{k,q}(x) is Borel (Measurable.iSup).
- η_k is this function times the indicator of the closed, hence Borel, set C. So η_k is Borel, hence strongly measurable.

7. Pointwise convergence on C. Let x ∈ C and τ > 0.
- f is differentiable at x with derivative Df(x). So there is r > 0 with |f(y) − f(x) − Df(x)(y − x)| ≤ τ|y − x| whenever |y − x| < r.
- Choose k₀ ∈ ℕ with 1/(k₀+1) < r. Let k ≥ k₀ and q ∈ Q.
- If 0 < |q − x| < 1/(k+1), then |q − x| < 1/(k₀+1) < r, so ψ_{k,q}(x) = |R(x, q)| ≤ τ. Otherwise ψ_{k,q}(x) = 0 ≤ τ.
- Hence 0 ≤ η_k(x) ≤ τ for all k ≥ k₀. As τ > 0 was arbitrary, η_k(x) → 0 as k → ∞, for every x ∈ C.

8. Egoroff step. C is closed, hence Borel, with Lⁿ(C) < ∞. Each η_k is strongly measurable, and the limit 0 is constant. η_k(x) → 0 for every x ∈ C, in particular for Lⁿ-a.e. x ∈ C. Egoroff's theorem with tolerance δ'/2 > 0 gives a Borel t ⊆ C with Lⁿ(t) ≤ δ'/2 such that η_k → 0 uniformly on C \ t.

9. Closed subset. C \ t is Borel with Lⁿ(C \ t) ≤ Lⁿ(C) < ∞. By inner regularity choose a closed A ⊆ C \ t with Lⁿ((C \ t) \ A) < δ'/2. Then A is closed, A ⊆ C, and η_k → 0 uniformly on A.

10. Measure estimate. C \ A ⊆ t ∪ ((C \ t) \ A). Using Lⁿ(t) ≤ δ'/2 < ∞,
Lⁿ(C \ A) ≤ Lⁿ(t) + Lⁿ((C \ t) \ A) < δ'/2 + δ'/2 = δ' ≤ δ.

11. Uniform remainder estimate. Let τ > 0.
- By uniform convergence on C \ t ⊇ A, there is k ∈ ℕ with |η_k(x)| < τ, hence η_k(x) < τ, for all x ∈ A.
- Put ρ := 1/(k+1) > 0, and let x, y ∈ A with |x − y| < ρ.
- If y = x, then f(y) − f(x) − Df(x)(y − x) = 0 = τ|y − x|.
- If y ≠ x, then x, y ∈ C and 0 < |y − x| < 1/(k+1). By step 5, |f(y) − f(x) − Df(x)(y − x)| ≤ η_k(x)|y − x| ≤ τ|y − x|.

Steps 9–11 give the required closed set A. ∎

Formalization note: a sorry-free Lean proof following exactly these steps was compiled against a scratch copy of the base Submission, with no additional imports. It uses only propext, Classical.choice and Quot.sound. It is also part of the lake-verified scratch file /tmp/c1ab-decomp/lakeverify/GMT/Ch05/Submission.lean; a standalone copy is /tmp/c1ab-decomp/proj/C1abTest/Remainder.lean (scratch, may be removed). There:
- ψ is `fun k q x => if 0 < ‖q - x‖ ∧ ‖q - x‖ < 1 / ((k : ℝ) + 1) then |f q - f x - fderiv ℝ f x (q - x)| / ‖q - x‖ else 0`;
- η_k is `C.indicator (fun x => ⨆ q : Q, ψ k q x)`;
- step 5 uses `le_of_tendsto` along `𝓝[Q] y`;
- step 7 uses `HasFDerivAt.isLittleO`, run with τ/2 in place of τ to get the strict inequality that `Metric.tendsto_atTop` asks for.

## Key steps

1. Reduce to the finite tolerance δ' = min(δ, 1)
2. Remainder bound |f(y) − f(x) − Df(x)(y − x)| ≤ 2K|y − x|, from the Lipschitz bound and ‖Df‖ ≤ K
3. Countable dense Q ⊆ C; η_k = 1_C · sup_{q∈Q} ψ_{k,q} with window 0 < |q − x| < 1/(k+1), so 0 ≤ η_k ≤ 2K
4. Closure argument: |f(y) − f(x) − Df(x)(y − x)| ≤ η_k(x)|y − x| for x, y ∈ C with 0 < |y − x| < 1/(k+1)
5. η_k is Borel: a countable supremum of Borel ψ_{k,q} times the indicator of C
6. Differentiability on C gives η_k → 0 pointwise on C
7. Egoroff (tolerance δ'/2) and inner regularity (δ'/2) give a closed A ⊆ C with Lⁿ(C \ A) < δ' and η_k → 0 uniformly on A
8. Uniform estimate with ρ = 1/(k+1), where η_k < τ on A

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `rg -n 'rsod_c1ab|RsodC1ab' <snapshot>/project; grep -rl rsod_c1ab <run dir> GMT .lake/packages/simongmt lake-packages-25730c7c/simongmt; git log --all --oneline -S'rsod_c1ab'`
- `rg -n -i lusin <snapshot>/mathlib/Mathlib -l`
- `rg -n -i whitney <snapshot>/mathlib/Mathlib -l`
- `rg -n 'theorem tendstoUniformlyOn_of_ae_tendsto |theorem _root_.MeasurableSet.exists_isClosed_sdiff_lt|theorem measurable_apply₂|theorem continuousOn_clm_apply|theorem IsSeparable.exists_countable_dense_subset|theorem IsSeparable.of_separableSpace|theorem measurable_fderiv |theorem measurableSet_of_differentiableAt |theorem norm_fderiv_le_of_lipschitz|theorem LipschitzWith.ae_differentiableAt|protected theorem Measurable.iSup|theorem Measurable.apply_continuousLinearMap' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem\|^structure\|import\|^namespace' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/{Chapter01/Lusin.lean,Chapter02/WhitneyCover.lean,Chapter02/WhitneyJet.lean,Chapter02/WhitneyPartition.lean,Chapter02/WhitneyExtension.lean}`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter0{1,2}/*.olean; head of .trace for Lusin, WhitneyJet, WhitneyPartition, WhitneyCover; grep lake-packages /proc/mounts`
- `python3 scan of dag.json for c1_approx/lusin/whitney nodes; git show 4d18f1d6 (aetp_lipschitz_c1_approximation)`
- `LEAN_PATH=<scratch build>:<shared package oleans> lean /tmp/c1ab-decomp/proj/C1abTest/{Assembly,Lusin,Remainder,Whitney,Sol_*,Chal_*}.lean and PasteTest/GMT/Ch05/Submission.lean`
- `lake build GMT.Ch05.Submission + lake env lean AxCheck.lean in /tmp/c1ab-decomp/lakeverify; lake build GMT.ImpLusin / GMT.ImpJet in /tmp/c1ab-decomp/lakeimport`
- `python3 lean_contract.validate_lean_statement(each child type); gmt-compare.contract_scope(Contract.lean, GMT.Ch05.main_theorem)`
- `sed -n 150,280p book/chapter-02.txt (statement of Thm 1.6 and printed proof of Thm 1.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Manifold/WhitneyEmbedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-rectifiable-c1-cover-a1-c1-approx-ball-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/c1ab-decomp/proj/C1abTest/Assembly.lean`
- `/tmp/c1ab-decomp/proj/C1abTest/Lusin.lean`
- `/tmp/c1ab-decomp/proj/C1abTest/Remainder.lean`
- `/tmp/c1ab-decomp/proj/C1abTest/Whitney.lean`
- `/tmp/c1ab-decomp/lakeverify/GMT/Ch05/Submission.lean`

Pins and identity: the snapshot is pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its GMT/Ch05 Contract.lean and Submission.lean are byte-identical to the workspace copies.

No-match results:
- 'rsod_c1ab' / 'RsodC1ab' occur nowhere in the snapshot project, the run directory, GMT/, simongmt or git history.
- Snapshot Mathlib has no Lusin continuity theorem: lusin hits are only the Lusin separation and Lusin–Souslin theorems in MeasureTheory/Constructions/Polish/Basic.lean and Jacobian.lean comments.
- Snapshot Mathlib has no Whitney C¹ extension: whitney hits are only Geometry/Manifold/WhitneyEmbedding.lean and partitions of unity.

Usable snapshot Mathlib:
- tendstoUniformlyOn_of_ae_tendsto (MeasureTheory/Function/Egorov.lean:205; gives μ t ≤ ε).
- MeasurableSet.exists_isClosed_sdiff_lt (MeasureTheory/Measure/Regular.lean:1036; volume on Rn n is WeaklyRegular by inferInstance).
- measurableSet_of_differentiableAt, measurable_fderiv and ContinuousLinearMap.measurable_apply₂ (Analysis/Calculus/FDeriv/Measurable.lean:372, 378, 95).
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947).
- LipschitzWith.ae_differentiableAt (Analysis/Calculus/Rademacher.lean:385).
- continuousOn_clm_apply (Analysis/Normed/Module/FiniteDimension.lean:518).
- Measurable.iSup (MeasureTheory/Constructions/BorelSpace/Order.lean:909).
- Measurable.apply_continuousLinearMap (BorelSpace/ContinuousLinearMap.lean:75).
- IsSeparable.exists_countable_dense_subset (Topology/Metrizable/Basic.lean:185) and IsSeparable.of_separableSpace (Topology/Bases.lean:599).

Pinned simongmt (outside the snapshot):
- Chapter01.exists_isClosed_continuousOn_of_measurable (Lusin.lean:127). Its .olean was built in place, and `lake build` of a file importing it succeeds.
- Chapter02.exists_contDiff_one_extension_of_whitney (WhitneyExtension.lean:373), with HasWhitneyC1Compatibility (WhitneyJet.lean:34).
- WhitneyExtension has no .olean. The WhitneyCover/Jet/Partition .olean files come from a foreign build (/home/zhengyang/root-copy-…/poincare in their .trace logs).
- The package tree is a read-only ceph mount, so importing any of the four fails under `lake build` ("read-only file system"). Pasting the four sources into a private namespace with only their Mathlib imports passes `lake build`.

Lean results:
- All three child types validate and elaborate in comparator form after `import GMT.Ch05.Submission`.
- The exact parent type compiles from them.
- A lake-built scratch Submission proves all three children and the parent using only propext, Classical.choice and Quot.sound.
