# Parent-supplied natural-language proof

- Parent DAG node: `root.chart_tangent_differential-a1.chart_differential-a1`
- Child DAG node: `root.chart_tangent_differential-a1.chart_differential-a1.chart_line_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof Step 5: Simon, Ch. 2, (4.7) and (4.10) (chapter-02.txt ≈ lines 922–957, printed pp. 56–57). The derivative of f along the chart curve γ(t) = ψ(u + tw) is compared with the derivative along the straight line γ̃(t) = ψ(u) + t·Dψ(u)w, using the local Lipschitz bound of f on the open set U. Both curves pass through ψ(u) with velocity Dψ(u)w. Simon's ψ is C¹, but only differentiability of ψ at u is used here, and injectivity of Dψ(u) is not needed. All Mathlib names refer to the pinned snapshot and are available after `import GMT.Ch03.Submission`.

Fix w ∈ ℝⁿ and put x := ψ(u), τ := Dψ(u)w (= fderiv ℝ ψ u w) and ℓ := D(f∘ψ)(u)w (= fderiv ℝ (f ∘ ψ) u w).

1. The goal as a little-o statement. By definition, HasLineDerivAt ℝ f ℓ x τ means that t ↦ f(x + t·τ) has derivative ℓ at t = 0. Equivalently (`hasLineDerivAt_iff_isLittleO_nhds_zero`): f(x + tτ) − f(x) − tℓ = o(t) as t → 0 (t ∈ ℝ).

2. A Lipschitz neighbourhood of x. Since x = ψ(u) ∈ U and f is locally Lipschitz on U, there are L ≥ 0 and T ∈ 𝓝[U] x such that f is L-Lipschitz on T. As U is open and x ∈ U, 𝓝[U] x = 𝓝 x (`IsOpen.nhdsWithin_eq`), so T is a neighbourhood of x.

3. Line derivatives of ψ and of f∘ψ at u in direction w. ψ is differentiable at u with derivative Dψ(u). The chain rule with the affine map t ↦ u + tw (`HasFDerivAt.hasLineDerivAt`) gives HasLineDerivAt ℝ ψ τ u w, i.e.
 (a) ψ(u + tw) − ψ(u) − tτ = o(t) as t → 0.
 Likewise f∘ψ is differentiable at u with derivative D(f∘ψ)(u), so HasLineDerivAt ℝ (f∘ψ) ℓ u w, i.e.
 (b) f(ψ(u + tw)) − f(ψ(u)) − tℓ = o(t) as t → 0.

4. Both curves eventually lie in T. The map t ↦ u + tw is continuous with value u at t = 0, and ψ is continuous at u because it is differentiable there. So ψ(u + tw) → ψ(u) = x as t → 0. Also x + tτ → x as t → 0, by continuity of t ↦ x + tτ. Since T is a neighbourhood of x, there is a neighbourhood of 0 in ℝ on which both ψ(u + tw) ∈ T and x + tτ ∈ T.

5. Comparison of the two curves (Simon (4.7)). For t in that neighbourhood, the Lipschitz bound on T (`LipschitzOnWith.norm_sub_le`) gives
 ‖f(x + tτ) − f(ψ(u + tw))‖ ≤ L·‖(x + tτ) − ψ(u + tw)‖ = L·‖ψ(u + tw) − ψ(u) − tτ‖.
 The equality holds because the two vectors are negatives of each other (x = ψ(u)). Hence f(x + tτ) − f(ψ(u + tw)) = O(ψ(u + tw) − ψ(u) − tτ) as t → 0 (`Asymptotics.IsBigO.of_bound`). By (a) and `Asymptotics.IsBigO.trans_isLittleO`,
 (c) f(x + tτ) − f(ψ(u + tw)) = o(t) as t → 0.

6. Conclusion. For every t ∈ ℝ, using x = ψ(u),
 f(x + tτ) − f(x) − tℓ = [f(x + tτ) − f(ψ(u + tw))] + [f(ψ(u + tw)) − f(ψ(u)) − tℓ].
 The two brackets are o(t) by (c) and (b), so their sum is o(t) (`Asymptotics.IsLittleO.add`, `Asymptotics.IsLittleO.congr_left`). By step 1 this is HasLineDerivAt ℝ f ℓ x τ, i.e. HasLineDerivAt ℝ f (fderiv ℝ (f ∘ ψ) u w) (ψ u) (fderiv ℝ ψ u w). Since w ∈ ℝⁿ was arbitrary, the claim holds for every w. (For w = 0, in particular when n = 0, τ = 0 and ℓ = 0, and the statement is the derivative of a constant function; the argument covers this case.) ∎

## Key steps

1. Rewrite the goal HasLineDerivAt ℝ f ℓ x τ, with x = ψ u, τ = Dψ(u)w and ℓ = D(f∘ψ)(u)w, as f(x + tτ) − f(x) − tℓ = o(t) (hasLineDerivAt_iff_isLittleO_nhds_zero).
2. U is open and f is locally Lipschitz on U, so f is L-Lipschitz on a neighbourhood T of x.
3. Chain rule along t ↦ u + tw (HasFDerivAt.hasLineDerivAt): ψ(u + tw) − ψ(u) − tτ = o(t) and f(ψ(u + tw)) − f(ψ(u)) − tℓ = o(t).
4. For t near 0, both ψ(u + tw) and x + tτ lie in T, so ‖f(x + tτ) − f(ψ(u + tw))‖ ≤ L‖ψ(u + tw) − ψ(u) − tτ‖ = o(t) (Simon (4.7)).
5. Adding the two o(t) terms gives f(x + tτ) − f(x) − tℓ = o(t), which is the HasLineDerivAt claim, for every w.

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json; cmp local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `grep -n "theorem\|lemma" mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `grep -rn "ae_differentiableAt\b\|ae_differentiableAt_of\|LocallyLipschitz.*ae_\|ae_differentiableWithinAt" mathlib/Mathlib --include=*.lean`
- `grep -n "LocallyLipschitzOn" mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean mathlib/Mathlib/Topology/Algebra/MetricSpace/Lipschitz.lean mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean mathlib/Mathlib/Analysis/Convex/Continuous.lean mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `grep -n "def HasLineDerivAt\|hasLineDerivAt_iff_isLittleO_nhds_zero\|HasFDerivAt.hasLineDerivAt" mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `grep -rn "theorem measure_null_of_locally_null\|theorem countable_cover_nhdsWithin\|theorem isOpen_biUnion_countable\|theorem ae_all_iff\|theorem ae_ball_iff\|theorem ae_iff" mathlib/Mathlib/MeasureTheory mathlib/Mathlib/Topology/Bases.lean`
- `grep -n "lipschitzOnWith_iff_norm_div_le\|LipschitzOnWith.norm_div_le" mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean; grep -rn "theorem IsBigO.trans_isLittleO" mathlib/Mathlib/Analysis/Asymptotics; grep -rn "theorem IsOpen.nhdsWithin_eq\|theorem ContinuousOn.isOpen_inter_preimage\|theorem DifferentiableWithinAt.differentiableAt\|theorem ContDiffOn.contDiffAt\|theorem ContDiffAt.differentiableAt" mathlib/Mathlib`
- `grep -rn "rademacher\|Rademacher\|LocallyLipschitzOn\|lineDeriv\|LineDeriv\|∀ᵐ.*DifferentiableAt\|ae_differentiable" lake-packages-25730c7c/simongmt/Poincare/SimonGMT --include=*.lean`
- `python3 -I scan of dag.json nodes for lean_statement containing DifferentiableAt / HasLineDerivAt / LocallyLipschitzOn; grep -rl <proposed names> run dir, GMT/**/*.lean; git log --all --oneline -S<proposed name>`
- `grep -n "Rademacher\|1.4 Theorem\|locally Lipschitz" book/chapter-02.txt; sed -n 1,75p and 900,965p book/chapter-02.txt`
- `lake env lean GMT/Scratch/ChartDiffA1SplitCheck.lean; lake env lean GMT/Scratch/ChartDiffA1ChildProofs.lean; lake env lean GMT/Scratch/ChartDiffA1FullCheck.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Asymptotics/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-differential-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartDiffA1SplitCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartDiffA1ChildProofs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartDiffA1FullCheck.lean`

Snapshot manifest: project d09bc8a, Mathlib 25730c7c. The snapshot's project/GMT/Ch03/Contract.lean is byte-identical to the workspace contract.

Found in Mathlib:
- Rademacher (Analysis/Calculus/Rademacher.lean): only LipschitzOnWith.ae_differentiableWithinAt_of_mem and LipschitzWith.ae_differentiableAt. No locally-Lipschitz-on-an-open-set version giving DifferentiableAt, and no `LocallyLipschitz*ae_*` lemma anywhere in Mathlib. So child local_rademacher is a genuine new obligation.
- LocallyLipschitzOn (Topology/EMetricSpace/Lipschitz.lean): defined as ∀ x ∈ s, ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t. Has .mono and .continuousOn. There is NO LocallyLipschitzOn.comp (only LocallyLipschitz.comp and LipschitzOnWith.comp).
- ContDiffOn.locallyLipschitzOn requires Convex, so the parent glue uses ContDiffAt.exists_lipschitzOnWith (ContDiff/RCLike.lean).
- Line derivatives (LineDeriv/Basic.lean): HasLineDerivAt f f' x v := HasDerivAt (fun t ↦ f (x + t • v)) f' 0; hasLineDerivAt_iff_isLittleO_nhds_zero; HasFDerivAt.hasLineDerivAt.
- Null sets and countable covers: measure_null_of_locally_null (OuterMeasure/Basic.lean); TopologicalSpace.countable_cover_nhdsWithin and isOpen_biUnion_countable (Topology/Bases.lean); ae_iff, ae_all_iff, ae_ball_iff (OuterMeasure/AE.lean).
- Other lemmas used: LipschitzOnWith.norm_sub_le (to_additive of norm_div_le, Normed/Group/Uniform.lean); Asymptotics.IsBigO.trans_isLittleO (Asymptotics/Basic.lean); IsOpen.nhdsWithin_eq (Topology/NhdsWithin.lean); ContinuousOn.isOpen_inter_preimage (Topology/ContinuousOn.lean); DifferentiableWithinAt.differentiableAt (FDeriv/Basic.lean); ContDiffOn.contDiffAt and ContDiffAt.differentiableAt (ContDiff/Defs.lean).

Pinned SimonGMT: only rademacher_ae_differentiableAt (Chapter02/Lipschitz.lean), a wrapper of LipschitzWith.ae_differentiableAt. No match for a.e. differentiability under LocallyLipschitzOn, for HasLineDerivAt/lineDeriv, or for a chart directional-derivative lemma.

DAG and naming: no other node's lean_statement is a local Rademacher or the pointwise line-derivative lemma. The proposed names have no hit in dag.json, nodes/, Lean sources or git history.

Lean checks (git-ignored GMT/Scratch, after import GMT.Ch03.Submission):
- ChartDiffA1SplitCheck.lean: frozen parent assembled from the two frozen child types; compiles.
- ChartDiffA1FullCheck.lean: both children proved plus the assembly; compiles with axioms [propext, Classical.choice, Quot.sound] only.

Book: Simon chapter-02.txt lines 59–72 (Theorem 1.4) and 900–957 ((4.5)–(4.10)).
