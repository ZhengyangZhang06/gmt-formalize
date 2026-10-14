# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.domain_geometry-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 4 (domains; Simon 7.3.3, proof of 3.3(1), item (9): the members with lim λ_i = λ > 0 live on U_S = η_{x,λ}(U), chapter-07.txt lines 445–467) together with the membership equivalence of parent step 0(e) (v ∈ G_{x,λ} ⟺ x + λv ∈ B_2(0)). Both are proved here directly from the definition of dilation, since the parent's sibling ambient_calculus is not available to this child. The inclusion closedBall 0 R ⊆ G for λR ≤ 1 is the closed-ball form of the inclusion B_{1/λ}(0) ⊆ G_{x,λ} of parent step 4, which parent step 5c uses.
Notation: η := η_{x,λ} = dilation x λ and G := η(B_2(0)).
1. (Formula for η.) By definition, dilation x λ u = −(λ⁻¹•x) + dilationCLM P λ u, and dilationCLM P λ = λ⁻¹ • id, so dilationCLM P λ u = λ⁻¹•u. Hence η(u) = λ⁻¹•u − λ⁻¹•x = λ⁻¹•(u − x) for every u ∈ ℝ^P.
2. ((a), ⇒.) Let v ∈ G, say v = η(u) with u ∈ B_2(0), i.e. ‖u‖ < 2. By step 1, λ•v = λ•(λ⁻¹•(u − x)) = (λλ⁻¹)•(u − x) = u − x, because λ ≠ 0. Hence x + λ•v = u and ‖x + λ•v‖ = ‖u‖ < 2.
3. ((a), ⇐.) Let ‖x + λ•v‖ < 2 and put u := x + λ•v, so u ∈ B_2(0). By step 1, η(u) = λ⁻¹•((x + λ•v) − x) = λ⁻¹•(λ•v) = (λ⁻¹λ)•v = v. Hence v = η(u) ∈ G.
4. ((b).) By (a), G = {v ∈ ℝ^P : ‖x + λ•v‖ < 2}. The map v ↦ ‖x + λ•v‖ is continuous (the continuous affine map v ↦ x + λ•v followed by the norm), so G is the set where a continuous function is strictly less than the constant 2, which is open (isOpen_lt).
5. ((c), first inclusion.) Assume λ ≤ 1 and ‖x‖ ≤ 1 − λ, and let v ∈ B_2(0), i.e. ‖v‖ < 2. Since ‖λ•v‖ = |λ|·‖v‖ = λ‖v‖ (λ > 0), the triangle inequality gives ‖x + λ•v‖ ≤ ‖x‖ + λ‖v‖ < (1 − λ) + 2λ = 1 + λ ≤ 2; the strict inequality uses λ > 0 and ‖v‖ < 2, the last one uses λ ≤ 1. By (a), v ∈ G. Hence B_2(0) ⊆ G.
6. ((c), second inclusion.) Under the same assumptions let R ∈ ℝ with λR ≤ 1 and let v ∈ closedBall 0 R, i.e. ‖v‖ ≤ R. Then ‖x + λ•v‖ ≤ ‖x‖ + λ‖v‖ ≤ (1 − λ) + λR ≤ (1 − λ) + 1 = 2 − λ < 2, using λ ≥ 0 for λ‖v‖ ≤ λR, the hypothesis λR ≤ 1, and λ > 0 for the last step. By (a), v ∈ G. Hence closedBall 0 R ⊆ G. (If R < 0 the closed ball is empty; the computation covers this case as well.)
7. Steps 2–6 prove (a), (b) and (c). ∎

## Key steps

1. dilation x λ u = λ⁻¹•(u − x); its inverse is v ↦ x + λ•v.
2. Hence v ∈ η_{x,λ}(B_2(0)) ⟺ ‖x + λ•v‖ < 2.
3. This set is a strict sublevel set of a continuous function, hence open.
4. For λ ≤ 1 and ‖x‖ ≤ 1 − λ: ‖x + λv‖ ≤ 1 − λ + λ‖v‖ < 2 when ‖v‖ < 2, or when ‖v‖ ≤ R with λR ≤ 1.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `grep -rn --include=*.lean -F in local-references/123e8435b4a2469b/mathlib/Mathlib for: ext_of_integral_eq_on_compactlySupported, Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure, isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts, cthickening_closedBall, IsCompact.exists_cthickening_subset_open, pow_left_inj₀, tendsto_integral_of_dominated_convergence, integral_smul_measure, integral_map, smul_unitBall, IsCompact.tendsto_subseq, tendsto_ofReal_atTop`
- `python3 scan of dag.json: cone_class subtree (lean_name, status, depends_on); accepted nodes whose lean_statement contains 'HasCompactSupport', 'map (dilation', 'withDensity' or 'dilation … ball'; equal-integral ⇒ measure-equality patterns; lean_name lookup of the ten proposed names`
- `python3 extraction of this node's parent-child-handoff.json and parent-supplied-natural-proof.json, of the dilate_homogeneity handoff (nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invaria-4622bb5be6) and of cone_class decomposition-v1.json (nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5982ed9bb9)`
- `git show fc55b7480dccf7e48261ad5b085ddd0c0cc9f1d6 -- GMT/Ch07/Submission.lean; git ls-tree -r --name-only d1625d7690ef2c4584f95774d9d18e9abd590050`
- `grep -n in /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py for _overlay_accepted_children, _existing_lean_name_problem, _dependency_problem, _topological, _install_parent_supplied_child_handoff`
- `sed -n 440,540p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt (Simon 7.3.3, proof of 3.3(1), items (6)–(11))`
- `lake env lean /tmp/psf_dec_9q4/{Assembly,DG,TM,INJ,VU,PC,NH,LB,VC,Full}.lean with #print axioms`
- `python3 replay of Runtime._dependency_problem, Runtime._topological and the lean_name collision rule on /tmp/psf_dec_9q4/gen/subproblems.json against dag.json; recomputation of the decomposition_scope digest`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d4cc3d3f0f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d4cc3d3f0f/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invaria-4622bb5be6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5982ed9bb9/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/psf_dec_9q4/Assembly.lean`
- `/tmp/psf_dec_9q4/Full.lean`

Pins match: manifest project b4d606db1 = workspace HEAD, Mathlib 25730c7c = .lake/packages/mathlib HEAD; the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and this node's proof base d1625d76 contains only the bare contract. Reuse: the only accepted declaration matching an obligation is Submission.dimred_cs_mi_withDensity_dilate (node dilate_homogeneity-a1, accepted, candidate fc55b748, which contains its dependency euclid_hausdorff_dilation_change_of_variables); its type is copied byte for byte. No accepted or library declaration states the other nine obligations: dag.json has no vague-uniqueness, parameter-continuity, rescaling-injectivity or transferred-lower-bound lemma, and none of the nine fresh idtp_fons_cc_psf_* names occurs in it. ambient_calculus is unaccepted and owned by another parent, so it cannot be shared; its facts are proved inline. Snapshot Mathlib provides everything the child proofs cite: Measure.ext_of_integral_eq_on_compactlySupported (RieszMarkovKakutani/Real.lean:412), Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (Measure/Regular.lean:1183), isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts (Typeclasses/Finite.lean:401), cthickening_closedBall (Normed/Module/Ball/Pointwise.lean:318, no nontriviality assumption), IsCompact.exists_cthickening_subset_open (MetricSpace/Thickening.lean:426), pow_left_inj₀ (GroupWithZero/Basic.lean:690), tendsto_integral_of_dominated_convergence (Integral/DominatedConvergence.lean:57), integral_smul_measure and integral_map (Bochner/Basic.lean:1052, 1081), smul_unitBall (Pointwise.lean:85), IsCompact.tendsto_subseq (Topology/Sequences.lean:298), ENNReal.tendsto_ofReal_atTop (ENNReal/Lemmas.lean:160). Lean: all ten child types elaborate; the parent's frozen type compiles from them; all nine new children were proved in scratch files, and the combined proof uses only the standard axioms plus the reused accepted lemma.
