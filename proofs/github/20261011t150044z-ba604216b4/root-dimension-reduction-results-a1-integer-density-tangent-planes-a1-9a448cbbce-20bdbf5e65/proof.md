# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1.total_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 0(a), 0(b), 0(c) and 3, with the needed facts of the parent's sibling ambient_calculus (parts (2) and (3); not available to this child) proved inline. The last two conclusions are exactly clause (3) of the parent; the first three are the properties of μ₀ used by parent steps 2 and 5.
Notation: B := B_{2r}(z) (open ball), η_{a,s} := dilation a s, m := μ(B) ∈ (0, ∞).
1. (Dilations act measurably.) For a ∈ ℝ^P and s ∈ ℝ, η_{a,s}(u) = −(s⁻¹•a) + s⁻¹•u = s⁻¹•(u − a) (definition of dilation and dilationCLM). This map is continuous (affine), hence Borel measurable. Consequently, for every measure ν, every c ∈ [0, ∞] and every Borel set A: (c•ν.map(η_{a,s}))(A) = c·ν(η_{a,s}⁻¹(A)) (Measure.smul_apply, Measure.map_apply).
2. (Constants.) For s > 0 we have s⁻¹^n > 0, so ofReal(s⁻¹^n) ≠ 0; and ofReal(t) ≠ ∞ for every real t. In particular ofReal(r⁻¹^n) ∈ (0, ∞).
3. (Total mass of μ₀.) By step 1 with A = ℝ^P (η_{z,r}⁻¹(ℝ^P) = ℝ^P) and Measure.restrict_apply: μ₀(ℝ^P) = ofReal(r⁻¹^n)·(μ⌞B)(ℝ^P) = ofReal(r⁻¹^n)·μ(ℝ^P ∩ B) = ofReal(r⁻¹^n)·m. A product of two elements of (0, ∞) is ≠ 0 (mul_ne_zero) and ≠ ∞ (ENNReal.mul_ne_top). Hence μ₀(ℝ^P) ≠ 0 and μ₀(ℝ^P) ≠ ∞.
4. (Concentration.) For every v ∈ ℝ^P: v ∈ η_{z,r}⁻¹(B_2(0)) ⟺ ‖r⁻¹•(v − z)‖ < 2 ⟺ r⁻¹‖v − z‖ < 2 ⟺ ‖v − z‖ < 2r (as r > 0) ⟺ v ∈ B. So η_{z,r}⁻¹(B_2(0)) = B and, taking complements, η_{z,r}⁻¹(B_2(0)ᶜ) = Bᶜ. The set B_2(0)ᶜ is closed, hence Borel, and Bᶜ is Borel; so by step 1 and Measure.restrict_apply, μ₀(B_2(0)ᶜ) = ofReal(r⁻¹^n)·μ(Bᶜ ∩ B) = ofReal(r⁻¹^n)·μ(∅) = 0.
5. (Members.) Let x ∈ ℝ^P and λ > 0. By step 1 with A = ℝ^P: μ₀^{x,λ}(ℝ^P) = ofReal(λ⁻¹^n)·μ₀(η_{x,λ}⁻¹(ℝ^P)) = ofReal(λ⁻¹^n)·μ₀(ℝ^P). By step 2 the first factor lies in (0, ∞) and by step 3 so does the second; hence μ₀^{x,λ}(ℝ^P) ≠ 0 and μ₀^{x,λ}(ℝ^P) ≠ ∞. ∎

## Key steps

1. Dilations are continuous, so (c•ν.map η)(A) = c·ν(η⁻¹A) for Borel A.
2. μ₀(ℝ^P) = ofReal(r⁻¹^n)·μ(B_{2r}(z)) ∈ (0, ∞).
3. η_{z,r}⁻¹(B_2(0)) = B_{2r}(z), so μ₀(B_2(0)ᶜ) = ofReal(r⁻¹^n)·μ(∅) = 0.
4. μ₀^{x,λ}(ℝ^P) = ofReal(λ⁻¹^n)·μ₀(ℝ^P) ∈ (0, ∞).

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
