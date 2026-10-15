# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.vague_unique-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 5b (basic fact (F6)) in the form recorded there as equivalent: finiteness on compact sets gives local finiteness and regularity on the σ-compact metric space ℝ^P, and regular measures are determined by their integrals of compactly supported continuous functions (Riesz–Markov–Kakutani uniqueness, Mathlib's Measure.ext_of_integral_eq_on_compactlySupported).
1. (Finite on compacts.) By hypothesis ν_i(K) < ∞ for every compact K ⊆ ℝ^P, i.e. ν_i is finite on compact sets (IsFiniteMeasureOnCompacts), for i = 1, 2.
2. (Locally finite.) ℝ^P is a finite-dimensional normed space, hence locally compact: every point has a compact neighbourhood (a closed ball), which has finite ν_i-measure by step 1. So ν_i is locally finite (isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts).
3. (Regular.) ℝ^P is a σ-compact metric space carrying its Borel σ-algebra, and every locally finite measure on such a space is regular (Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure): it is outer regular (ν_i(A) = inf{ν_i(O) : O ⊇ A open} for Borel A) and inner regular on open sets with respect to compact sets (ν_i(O) = sup{ν_i(K) : K ⊆ O compact}).
4. (Agreement on compact sets.) Let K be compact and ε > 0. By outer regularity of ν₂ and ν₂(K) < ∞ there is an open V ⊇ K with ν₂(V) ≤ ν₂(K) + ε; in particular ν₂(V) < ∞. ℝ^P is locally compact Hausdorff, so by Urysohn's lemma there is a continuous f : ℝ^P → [0, 1] with compact support contained in V and f = 1 on K; f is bounded with compact support, hence integrable for both measures. Using 1_K ≤ f ≤ 1_V (as real functions), the finiteness of ν₁(K) and ν₂(V), and the hypothesis (f is continuous with compact support), we get in ℝ: ν₁(K).toReal = ∫ 1_K dν₁ ≤ ∫ f dν₁ = ∫ f dν₂ ≤ ∫ 1_V dν₂ = ν₂(V).toReal ≤ ν₂(K).toReal + ε. As ε > 0 is arbitrary, ν₁(K).toReal ≤ ν₂(K).toReal, and since both values are finite, ν₁(K) ≤ ν₂(K); by symmetry ν₂(K) ≤ ν₁(K). Hence ν₁(K) = ν₂(K) for every compact K.
5. (Agreement on open sets.) By inner regularity on open sets (step 3), for every open O, ν_i(O) = sup{ν_i(K) : K ⊆ O compact}, so ν₁(O) = ν₂(O) by step 4.
6. (Agreement everywhere.) By outer regularity (step 3), for every Borel A, ν_i(A) = inf{ν_i(O) : O ⊇ A open}, so ν₁(A) = ν₂(A) by step 5. Hence ν₁ = ν₂. (Steps 4–6 are exactly the proof of Measure.ext_of_integral_eq_on_compactlySupported, which applies to the regular measures ν₁, ν₂ because every f ∈ C_c(ℝ^P, ℝ) is continuous with compact support, so the hypothesis gives ∫ f dν₁ = ∫ f dν₂.) ∎

## Key steps

1. Finite on compacts ⇒ locally finite on the locally compact space ℝ^P.
2. Locally finite on the σ-compact metric space ℝ^P ⇒ regular.
3. Urysohn functions 1_K ≤ f ≤ 1_V and outer regularity give ν₁(K) = ν₂(K) for compact K.
4. Inner regularity on open sets and outer regularity extend the equality to all Borel sets (Measure.ext_of_integral_eq_on_compactlySupported).

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
