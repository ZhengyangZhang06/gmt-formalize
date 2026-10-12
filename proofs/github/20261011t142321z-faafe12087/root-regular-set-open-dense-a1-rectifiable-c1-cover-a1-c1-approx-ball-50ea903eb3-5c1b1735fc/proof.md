# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1`
- Child DAG node: `root.regular_set_open_dense-a1.rectifiable_c1_cover-a1.c1_approx_ball-a1.whitney_c1_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof. It applies Whitney's extension theorem (Simon Ch. 2, Theorem 1.6, pp. 42–43); Simon does not print its proof and refers to [EG92] and [Fed69]. The parent uses its formal version in the pinned simongmt library: Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney (Poincare/SimonGMT/Chapter02/WhitneyExtension.lean:373), for data satisfying Poincare.SimonGMT.Chapter02.HasWhitneyC1Compatibility (WhitneyJet.lean:34).

The hypothesis here is Simon's 1.6(*), written with the operator-norm derivative D in place of the gradient. The conclusion keeps only g = h on A; the parent does not need ∇g = D on A.

The cited theorem is sorry-free at the pin; #print axioms gives only propext, Classical.choice and Quot.sound. It says: let E be a real normed space with [FiniteDimensional ℝ E], A ⊆ E closed, h : E → ℝ and D : E → (E →L[ℝ] ℝ) with HasWhitneyC1Compatibility A h D. Then there is g : E → ℝ with ContDiff ℝ 1 g, EqOn g h A, and HasFDerivAt g (D a) a for all a ∈ A.

HasWhitneyC1Compatibility A h D is the structure with fields:
- continuous_value : ContinuousOn h A;
- continuous_derivative : ContinuousOn D A;
- remainder : ∀ K, IsCompact K → K ⊆ A → ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ A, dist x y < δ → ‖h y − h x − D x (y − x)‖ ≤ ε‖y − x‖.

Let n, A, h and D be as in the statement.

1. E := ℝⁿ = EuclideanSpace ℝ (Fin n) is a finite-dimensional real normed space. So the cited theorem applies with this E, for every n including n = 0.

2. The three hypotheses after "A is closed" are, word for word, the three fields of HasWhitneyC1Compatibility A h D: continuity of h on A, continuity of D on A, and the compact-uniform remainder condition (with K := Q, ε := τ, δ := ρ; for real numbers ‖·‖ = |·|). Hence HasWhitneyC1Compatibility A h D holds; in Lean, apply the anonymous constructor to the three hypotheses.

3. Apply exists_contDiff_one_extension_of_whitney to the closedness of A and the compatibility from step 2. This gives g : ℝⁿ → ℝ with ContDiff ℝ 1 g, g(a) = h(a) for all a ∈ A, and Dg(a) = D(a) for all a ∈ A.

4. Discard the derivative statement: g is a C¹ function with g = h on A. ∎

Formalization note (verified at the pinned toolchain v4.35.0-rc3 with `lake build` against the read-only shared package tree, which is how the comparator builds):
- None of Poincare.SimonGMT.Chapter02.{WhitneyCover, WhitneyJet, WhitneyPartition, WhitneyExtension} can be imported.
  - WhitneyExtension has no .olean in the shared tree.
  - The other three have .olean files from a foreign build: their .trace logs record the build directory /home/zhengyang/root-copy-20260903-…/poincare. Lake therefore treats them as stale and tries to rebuild them into the read-only shared tree.
  - `lake build` of a file importing WhitneyJet fails with "failed to remove output artifacts: read-only file system". Plain `lean` with a hand-made LEAN_PATH does not detect this.
- Working route:
  - Add to GMT/Ch05/Submission.lean only the Mathlib imports of those four files: Mathlib.MeasureTheory.Covering.Vitali, Mathlib.Topology.MetricSpace.Lipschitz, Mathlib.Analysis.Normed.Module.FiniteDimension, Mathlib.Data.Set.Card, Mathlib.Analysis.Calculus.ContDiff.Defs, Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension, Mathlib.Analysis.Calculus.ContDiff.RCLike, Mathlib.Analysis.Calculus.Deriv.Inv and Mathlib.Algebra.BigOperators.Finprod. Mathlib.Topology.MetricSpace.HausdorffDistance is already imported.
  - Inside `namespace Submission`, paste the bodies of WhitneyCover.lean, WhitneyJet.lean, WhitneyPartition.lean and WhitneyExtension.lean, in that order (about 1200 source lines).
  - Drop `module`, the `public import` lines and `@[expose] public section`.
  - Wrap each pasted file in its own `section … end`, so that its `open` commands do not leak into later declarations.
  - Rename `namespace/end Poincare.SimonGMT.Chapter02` to a node-private `namespace/end RsodC1abWhitney`. With all four files in the same namespace, dot notation works unchanged.
  - The files declare no instances, and their few @[simp] lemmas concern only their own definitions.
  - Then prove this statement by steps 2–4: `obtain ⟨g, hg, hgh, -⟩ := RsodC1abWhitney.exists_contDiff_one_extension_of_whitney hA (RsodC1abWhitney.HasWhitneyC1Compatibility.mk hh hD hrem)`, followed by `exact ⟨g, hg, fun a ha => hgh ha⟩`.
- A scratch Submission built this way, together with the other two children and the selected parent, passed `lake build` (3018 jobs). The only `sorry` was the frozen `main_theorem`. `#print axioms` for the parent and for each child gives only propext, Classical.choice and Quot.sound. Scratch file (may be removed): /tmp/c1ab-decomp/lakeverify/GMT/Ch05/Submission.lean.
- The private namespace avoids clashes with any other branch that pastes the same files.
- Alternative source: the accepted proof of Submission.aetp_lipschitz_c1_approximation (commit 4d18f1d6, another branch) proves a Whitney extension inline as a local `have`, using only the base imports. Its hypothesis is a local uniform estimate, so it would need adaptation.

## Key steps

1. ℝⁿ is a finite-dimensional real normed space, so simongmt's Whitney theorem applies
2. The hypotheses are exactly the three fields of HasWhitneyC1Compatibility A h D
3. exists_contDiff_one_extension_of_whitney gives g ∈ C¹ with g = h (and Dg = D) on A
4. Keep ContDiff ℝ 1 g and g = h on A

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
