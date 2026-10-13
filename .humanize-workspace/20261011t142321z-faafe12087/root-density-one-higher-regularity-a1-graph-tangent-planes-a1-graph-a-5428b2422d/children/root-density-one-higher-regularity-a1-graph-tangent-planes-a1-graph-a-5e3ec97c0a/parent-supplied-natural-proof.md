# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.blowup_two_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is step 6 (near-linearity) of the parent proof, stated for an arbitrary C¹ map on an open set. Notation: L := fderiv ℝ G x = DG(x), DG(z) := fderiv ℝ G z.
1. Regularity. Since U is open and G is C¹ on U, G is differentiable at every z ∈ U (ContDiffOn.differentiableOn with 1 ≠ 0, then DifferentiableOn.differentiableAt using U ∈ 𝓝 z), and z ↦ DG(z) is continuous on U (ContDiffOn.continuousOn_fderiv_of_isOpen, 1 ≤ 1).
2. A good ball. Choose δ₀ > 0 with ball(x, δ₀) ⊆ U (U open; Metric.isOpen_iff) and δ₁ > 0 such that ‖DG(z) − L‖ < ε for every z ∈ U with dist(z, x) < δ₁ (continuity of DG at x within U; Metric.continuousOn_iff). Put δ := min(δ₀, δ₁) > 0. Then every z ∈ ball(x, δ) lies in U and satisfies ‖DG(z) − L‖ ≤ ε.
3. The scales. The interval (0, δ/(|ρ| + 1)) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT); fix t in it. For v ∈ closedBall(0, ρ) we have ‖v‖ ≤ ρ ≤ |ρ| < |ρ| + 1, hence ‖(x + t•v) − x‖ = t‖v‖ ≤ t(|ρ| + 1) < δ, i.e. x + t•v ∈ ball(x, δ) ⊆ U. This proves (a) for this t. (If ρ < 0 the closed ball is empty and (a), (b) hold vacuously; the argument below covers this case too.)
4. An auxiliary map. Define h : ℝⁿ → ℝ^{n+ℓ}, h(v) := t⁻¹•G(x + t•v) − L v. Let v ∈ closedBall(0, ρ) and z := x + t•v ∈ ball(x, δ) ⊆ U. The affine map v ↦ x + t•v has derivative t•id, and G is differentiable at z (step 1), so by the chain rule h has derivative t⁻¹•(DG(z) ∘ (t•id)) − L = DG(x + t•v) − L at v (HasFDerivAt.comp, HasFDerivAt.const_smul, HasFDerivAt.sub, using t⁻¹·t = 1). By step 2 its operator norm is at most ε.
5. Mean value inequality. closedBall(0, ρ) is convex, and h has, at every point of it, a derivative of norm ≤ ε (step 4, passing from HasFDerivAt to HasFDerivWithinAt). By Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le, ‖h v − h v'‖ ≤ ε‖v − v'‖ for all v, v' ∈ closedBall(0, ρ).
6. Conclusion. By linearity of L and of t⁻¹•(·), h v − h v' = t⁻¹•(G(x + t•v) − G(x + t•v')) − L(v − v'). With step 5 this is (b). Since (a) and (b) hold for every t in the member (0, δ/(|ρ| + 1)) of 𝓝[>] 0, the conjunction holds eventually along 𝓝[>] 0.

## Key steps

1. C¹ on the open set U: G is differentiable on U and z ↦ DG(z) is continuous on U
2. choose δ > 0 with ball(x, δ) ⊆ U and ‖DG(z) − L‖ ≤ ε on ball(x, δ)
3. for 0 < t < δ/(|ρ| + 1) and v ∈ closedBall(0, ρ): x + t•v ∈ ball(x, δ) ⊆ U, which is (a)
4. h(v) := t⁻¹•G(x + t•v) − L v has derivative DG(x + t•v) − L of norm ≤ ε on closedBall(0, ρ) (chain rule)
5. mean value inequality on the convex closed ball, and h v − h v' = t⁻¹•(G(x + t•v) − G(x + t•v')) − L(v − v'), give (b)

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json (project ea5607598f31, mathlib 25730c7c759d)`
- `diff GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean (identical frozen contract); verifier gmt-compare.contract_scope replay -> namespace GMT.Ch05 + opens`
- `python3 scan of dag.json lean_statements for LipschitzOnWith|graphPoint|HasApproximateTangentSpaceAt|blowUpMap|fderiv; candidate commits of accepted rsod_graphPoint_eq_finAddEquivProd_symm, rsod_norm_graphPoint_sq, aetp_c1_piece_approxTangent, tae_c1_chart_image_approxTangent`
- `rg -n 'dohr_tp_gat_' <snapshot> <run>/nodes <worktrees>/*/gmt-ch05/GMT (no match); python3 name scan of dag.json (names free)`
- `rg -n 'theorem norm_image_sub_le_of_norm_hasFDerivWithin_le' mathlib/Mathlib`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen' mathlib/Mathlib`
- `rg -n 'theorem integral_indicator (' mathlib/Mathlib; rg -n 'theorem restrict_restrict (' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem map_apply_of_aemeasurable' mathlib/Mathlib; rg -n 'integral_mono_measure' mathlib/Mathlib; rg -n '^theorem integral_map' mathlib/Mathlib`
- `rg -n 'uniformContinuous_of_continuous|bounded_above_of_compact_support|finAddEquivProd|euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_def' mathlib/Mathlib`
- `rg -n 'theorem hausdorffMeasure_image_le' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; rg -n 'euclideanHausdorffMeasure_image_le_of_lipschitzOn' <snapshot> (no match; found in .lake/packages/simongmt Chapter02/Lipschitz.lean:216)`
- `grep -n 'def HasApproximateTangentSpaceAt|def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `lean Probe.lean (#check of every cited lemma under import GMT.Ch05.Submission)`
- `lean Assembly.lean / ChildSmall.lean / ChildBig.lean; #print axioms of the three new children and of Submission.dohr_tp_graph_approx_tangent`
- `python3 -I gen_children.py (lean_contract.validate_lean_statement + gmt-compare.child_modules contract mode) then lean on 6 NodeChallenge and 6 NodeSolution modules`
- `grep -n -i 'approximate tangent' book/chapter-03.txt; WebSearch 'approximate tangent space C^1 submanifold blow-up'`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-a-5428b2422d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/4be3fb780add150d6ac3/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/dd296547b28b08453dda/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/1c8e05c936b9e4edfb8d/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/gat-7YzI2v/src/Probe.lean`
- `/tmp/gat-7YzI2v/src/Assembly.lean`
- `/tmp/gat-7YzI2v/src/ChildSmall.lean`
- `/tmp/gat-7YzI2v/src/ChildBig.lean`
- `/tmp/gat-full/GMT/Ch05/Submission.lean`

Pinned revisions match the workspace (project ea56075, Mathlib 25730c7c, simongmt 2b366308). The frozen Submission is byte-identical to the Contract.
The snapshot's pinned Mathlib supplies every cited tool:
- Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (MeanValue.lean:422)
- ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916)
- integral_indicator (Bochner/Set.lean:185) and Measure.restrict_restrict (Restrict.lean:205)
- Measure.map_apply_of_aemeasurable (Map.lean:166)
- integral_mono_measure (Bochner/Basic.lean:623) and integral_map (Bochner/Basic.lean:1081)
- LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733)
- euclideanHausdorffMeasure_def / EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:74/187)
- HasCompactSupport.uniformContinuous_of_continuous (to_additive of HeineCantor.lean:91)
- Continuous.bounded_above_of_compact_support (Normed/Group/Bounded.lean:153)
- EuclideanSpace.finAddEquivProd (PiL2.lean:378)
The convenient μHE Lipschitz image bound Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (simongmt Chapter02/Lipschitz.lean:216) is under the frozen imports, though not in the snapshot.
Reuse:
- Accepted checkpoints Submission.rsod_graphPoint_eq_finAddEquivProd_symm (candidate 18a457c4) and Submission.rsod_norm_graphPoint_sq (candidate a2b47723) have exactly the frozen types used for children (1) and (2). Their 4-6 line simp proofs recompile with standard axioms.
- The accepted Submission.aetp_c1_piece_approxTangent (candidate 94f10688) proves the analogous statement only for globally C^1 G, so it is not an ingredient of the supplied proof. Its bi-Lipschitz pattern was adapted for child (4).
- No accepted node duplicates children (3)-(5), and the names dohr_tp_gat_* are unused.
Lean checks:
- All cited lemmas resolve under import GMT.Ch05.Submission.
- Complete scratch proofs of children (3), (4) and (5) compile with axioms {propext, Classical.choice, Quot.sound}.
- The exact frozen parent type is proved from the five children with the same axioms (scratch Submission plus the verifier-generated NodeSolution modules).
- All five child statements pass validate_lean_statement and elaborate in the verifier-generated NodeChallenge modules.
