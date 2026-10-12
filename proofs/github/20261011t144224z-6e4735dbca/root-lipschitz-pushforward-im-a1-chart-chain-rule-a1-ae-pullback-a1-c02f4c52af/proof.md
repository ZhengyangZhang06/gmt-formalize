# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_pullback-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k) with norm |·|; Hⁿ = μHE[n] (Mathlib's Euclidean-normalized n-dimensional Hausdorff measure) on ℝ^P; Lⁿ = volume on ℝⁿ. For a measure μ and a set A, μ⌞A = μ.restrict A, and “q holds μ⌞A-a.e.” means ∀ᵐ x ∂(μ.restrict A), q x. Write S := Ω ∩ Φ⁻¹(M).

This is steps 1–3 of the parent proof (lpf_chart_chain_rule): Hⁿ-null exceptional sets in M ∩ Φ(Ω) pull back to Lⁿ-null sets of parameters, and Ω ∩ Φ⁻¹(M) is Lⁿ-null-measurable, so Hⁿ⌞(M ∩ Φ(Ω))-a.e. statements become Lⁿ⌞(Ω ∩ Φ⁻¹(M))-a.e. statements.

0. (Null sets pull back.) Fix c > 0 with c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω. The sibling lemma chart_preimage_null (Submission.lpf_raf_chart_preimage_null) applied to (P, n, Φ, Ω, c) gives:
(N) for every Z ⊆ ℝ^P with Hⁿ(Z) = 0, Lⁿ(Ω ∩ Φ⁻¹(Z)) = 0.

1. (S is Lⁿ-null-measurable.) Since M is Hⁿ-null-measurable, there is a measurable set B ⊆ M with B = M Hⁿ-a.e. (Mathlib NullMeasurableSet.exists_measurable_subset_ae_eq); in particular Hⁿ(M ∖ B) = 0 (ae_eq_set). Because B ⊆ M,
S = (Ω ∩ Φ⁻¹(B)) ∪ (Ω ∩ Φ⁻¹(M ∖ B)):
if w ∈ S and Φ(w) ∈ B, then w lies in the first set; if w ∈ S and Φ(w) ∉ B, then Φ(w) ∈ M ∖ B and w lies in the second set; conversely both sets are contained in S because B ⊆ M and M ∖ B ⊆ M. The first set is measurable, since Ω and B are measurable sets and Φ is a measurable map. The second set has Lⁿ-measure 0 by (N) with Z := M ∖ B. The union of a measurable set and an Lⁿ-null set is Lⁿ-null-measurable (MeasurableSet.nullMeasurableSet, NullMeasurableSet.of_null, NullMeasurableSet.union). Hence S is Lⁿ-null-measurable; this is the first conjunct.

2. (The exceptional set in ℝ^P is Hⁿ-null.) Let Z := {x ∈ ℝ^P : ¬p(x)} ∩ (M ∩ Φ(Ω)). The hypothesis ∀ᵐ x ∂(Hⁿ⌞(M ∩ Φ(Ω))), p x says exactly (Hⁿ⌞(M ∩ Φ(Ω)))({x : ¬p(x)}) = 0 (ae_iff). For every measure μ and all sets s, t one has μ(t ∩ s) ≤ (μ⌞s)(t), with no measurability assumption on s or t (Mathlib Measure.le_restrict_apply). With s := M ∩ Φ(Ω) and t := {x : ¬p(x)} this gives Hⁿ(Z) ≤ 0, so Hⁿ(Z) = 0.

3. (The exceptional set of parameters is Lⁿ-null.) By (N), Lⁿ(Ω ∩ Φ⁻¹(Z)) = 0. Let w ∈ S with ¬p(Φ(w)). Then w ∈ Ω, Φ(w) ∈ M, Φ(w) ∈ Φ(Ω) because w ∈ Ω, and ¬p(Φ(w)); hence Φ(w) ∈ Z and w ∈ Ω ∩ Φ⁻¹(Z). Thus {w : ¬(w ∈ S → p(Φ(w)))} = {w : w ∈ S ∧ ¬p(Φ(w))} ⊆ Ω ∩ Φ⁻¹(Z), so this set is Lⁿ-null by monotonicity (measure_mono_null), i.e. ∀ᵐ w ∂Lⁿ, w ∈ S → p(Φ(w)) (ae_iff).

4. (Conclusion.) Since S is Lⁿ-null-measurable (step 1), for every property q one has (∀ᵐ w ∂(Lⁿ⌞S), q(w)) ⟺ (∀ᵐ w ∂Lⁿ, w ∈ S → q(w)) (Mathlib ae_restrict_iff'₀). Applying this with q(w) := p(Φ(w)) to step 3 gives ∀ᵐ w ∂(Lⁿ⌞S), p(Φ(w)), the second conjunct. ∎

(Remark: the null-measurability of S from step 1 is what makes step 4 valid; for a non-measurable S the measure Lⁿ⌞S need not be concentrated on S.)

## Key steps

1. chart_preimage_null: every Hⁿ-null Z ⊆ ℝ^P has Lⁿ(Ω ∩ Φ⁻¹(Z)) = 0.
2. Choose a measurable B ⊆ M with Hⁿ(M ∖ B) = 0; Ω ∩ Φ⁻¹(M) = (Ω ∩ Φ⁻¹(B)) ∪ (Ω ∩ Φ⁻¹(M ∖ B)) is measurable ∪ Lⁿ-null, hence Lⁿ-null-measurable.
3. Z := {¬p} ∩ (M ∩ Φ(Ω)) satisfies Hⁿ(Z) ≤ (Hⁿ⌞(M ∩ Φ(Ω)))({¬p}) = 0 (Measure.le_restrict_apply).
4. {w ∈ Ω ∩ Φ⁻¹(M) : ¬p(Φ w)} ⊆ Ω ∩ Φ⁻¹(Z) is Lⁿ-null, and ae_restrict_iff'₀ (using null-measurability) turns this into the restricted a.e. statement.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean (identical)`
- `python3 scan of dag.json: lean_name, status, candidate_commit and parent of lpf_raf_chart_preimage_null, lpf_lli_countable_lipschitz_cover, lpf_lipschitz_localization and lpf_weighted_tangent_on_c1_chart; no node uses an lpf_ccr_* name; children of local_lipschitz_area-a1 and skeleton_polyhedral-a1 (cross-branch reuse precedents)`
- `python3 read of nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/{parent-child-handoff.json,decomposition-v1.json} and of the parent-child-handoff.json, accepted-candidate.json and isolated-comparator-result.json of the two reused nodes (passed=true for both)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|_install_parent_supplied_child_handoff|existing_by_name' /runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py; sed -n 60,215p store.py (reuse requires an identical type plus accepted status with a candidate_commit; reused children skip handoff installation)`
- `python3 replay of _existing_lean_name_problem and _topological on the 5 proposed children against the current dag.json (no problem; order chart_preimage_null, countable_lipschitz_cover, line_deriv_comp, ae_diff_comp, ae_pullback)`
- `git show 9080c178c7e23350ae33476f7bfa68f0965fe15e 6941b70febfeca396a5e8105097428578fe61416 -- GMT/Ch06/Submission.lean (accepted Lean proofs of the reused declarations)`
- `grep -n '^theorem' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean (LipschitzOnWith.ae_differentiableWithinAt_of_mem l.361; LipschitzWith.ae_differentiableAt l.385; no LocallyLipschitzOn version)`
- `grep in mathlib for ContDiff.locallyLipschitz, ae_restrict_iff'₀, le_restrict_apply, exists_measurable_subset_ae_eq, HasDerivAt.unique, HasFDerivAt.comp_hasDerivAt_of_eq, LipschitzOnWith.extend_finite_dimension, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, DifferentiableWithinAt.differentiableAt, ae_all_iff, HereditarilyLindelofSpace.isLindelof`
- `grep -n 'theorem rademacher_ae_differentiableAt|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (l.192, l.216)`
- `grep -n 'structure IsRectifiableTriple' -A 25 GMT/Ch06/Contract.lean (fields subset, nullMeasurableSet, pos, integrableOn used by the assembly)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope prefix); lean_contract.validate_lean_statement on all 5 child statements`
- `lake env lean /tmp/ccr2_scratch/Integrated.lean (accepted proofs, full proofs of the 3 new children and the assembly of Submission.lpf_chart_chain_rule; #print axioms)`
- `lake env lean /tmp/ccr2_scratch/stmts/Challenge_{chart_preimage_null,countable_lipschitz_cover,ae_pullback,ae_diff_comp,line_deriv_comp}.lean and /tmp/ccr2_scratch/IntegratedSol.lean (comparator challenge and solution forms; only sorry warnings)`
- `sed -n 28,70p and 905,960p book/chapter-02.txt (Simon Ch. 2: 1.2 Lipschitz extension, 1.4 Rademacher, 4.5–4.10 directional derivatives)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-pr-b8935c5987/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-pr-b8935c5987/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-pr-b8935c5987/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-countable-dc002d2f60/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-countable-dc002d2f60/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-countable-dc002d2f60/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/Lindelof.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/ccr2_scratch/scope_prefix.txt`
- `/tmp/ccr2_scratch/Integrated.lean`
- `/tmp/ccr2_scratch/IntegratedSol.lean`
- `/tmp/ccr2_scratch/stmts/Challenge_ae_pullback.lean`
- `/tmp/ccr2_scratch/stmts/Challenge_ae_diff_comp.lean`
- `/tmp/ccr2_scratch/stmts/Challenge_line_deriv_comp.lean`
- `/tmp/ccr2_scratch/stmts/Challenge_chart_preimage_null.lean`
- `/tmp/ccr2_scratch/stmts/Challenge_countable_lipschitz_cover.lean`

Snapshot. The snapshot (project d8d46c95, Mathlib 25730c7c) carries the frozen Ch06 Contract, byte-identical to the workspace copy.

Reuse.
- Reused: lpf_raf_chart_preimage_null (accepted 2026-10-12T05:20:13Z, candidate 9080c178) and lpf_lli_countable_lipschitz_cover (accepted 08:47:11Z, candidate 6941b70f). Both passed the isolated comparator, their frozen types are byte-identical to the proposed ones, and both already have cross-branch reuse precedents (skeleton_polyhedral-a1 and local_lipschitz_area-a1).
- lpf_lipschitz_localization is no longer proposed, following the correction.
- No DAG node uses lpf_ccr_ae_pullback, lpf_ccr_ae_differentiableAt_comp or lpf_ccr_hasDerivAt_line_of_comp.
- Replaying the runtime name check on dag.json passes, and the dependency graph is acyclic.

Available library support.
- Mathlib: Rademacher on a set (LipschitzOnWith.ae_differentiableWithinAt_of_mem) and globally (LipschitzWith.ae_differentiableAt), ContDiff.locallyLipschitz, ae_restrict_iff'₀, Measure.le_restrict_apply, NullMeasurableSet.exists_measurable_subset_ae_eq, HasDerivAt.unique, HasFDerivAt.comp_hasDerivAt_of_eq and LipschitzOnWith.extend_finite_dimension.
- SimonGMT Ch02/Lipschitz: rademacher_ae_differentiableAt and the Hⁿ Lipschitz image bound.
- No packaged a.e.-differentiability exists for LocallyLipschitzOn maps on open sets, nor any a.e. pullback along antilipschitz charts; these become the new children.

Kernel check under the exact comparator child scope:
- The accepted proofs, complete proofs of the three new children, and the assembly of lpf_chart_chain_rule against its byte-identical frozen type all typecheck.
- Every child depends only on propext, Classical.choice and Quot.sound.
- The parent picks up sorryAx only through the stubbed sibling dependency lpf_weighted_tangent_on_c1_chart.
- All five statements pass validate_lean_statement and elaborate as comparator challenges.
- `exact Submission.X` closes each child's frozen type and the parent's.

Printed source. Simon Ch. 2, 1.2 (Lipschitz extension), 1.4 (Rademacher) and 4.7/4.10 (directional derivatives of Lipschitz maps along curves and lines) supply the printed mathematics for ae_diff_comp and line_deriv_comp.
