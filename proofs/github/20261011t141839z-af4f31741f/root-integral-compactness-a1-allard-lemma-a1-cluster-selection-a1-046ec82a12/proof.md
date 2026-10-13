# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.cluster_selection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5(c) of the parent proof (Simon 8.5.10, proof of (8): 'we can select {z_1,…,z_Q} ⊆ {y_1,…,y_N} (Q ≤ N − 1) and τ̂ ≥ τ̃ … such that τ̂ ≤ ¼ min_{i≠j}|z_i − z_j|'). The book gives no construction. The parent's construction, via connected components of distance graphs, is replaced here by an equivalent greedy merging argument with the same conclusion, because Mathlib's SimpleGraph connectivity is outside Submission's import closure. Let k := #s ≥ 2.

1. Call a pair (Z, S) admissible if Z ⊆ s, Z ≠ ∅, #Z < k, S ≥ 0, every y ∈ s has some z ∈ Z with ‖y − z‖ ≤ S, and S ≤ d(5^{k − #Z} − 1)/2.

2. An admissible pair exists. Let y₀ ≠ y₁ in s with ‖y₀ − y₁‖ ≤ d, and put Z₁ := s \ {y₁}, S₁ := d. Then Z₁ ⊆ s, y₀ ∈ Z₁, #Z₁ = k − 1 < k and S₁ ≥ 0. Every y ∈ s other than y₁ lies in Z₁ (distance 0 ≤ d), and ‖y₁ − y₀‖ ≤ d. Finally d ≤ d(5¹ − 1)/2 = 2d.

3. Among the admissible pairs choose (Z, S) with #Z minimal. The cardinalities of admissible pairs form a nonempty set of natural numbers (Nat.find or a well-founded minimum).

4. Separation. Suppose distinct z, z' ∈ Z satisfy ‖z − z'‖ < 2d + 4S. Put Z' := Z \ {z'} and S' := 2d + 5S. Then Z' ⊆ s, z ∈ Z' (so Z' ≠ ∅), #Z' = #Z − 1 < k, and S' ≥ 0.
 Covering: for y ∈ s pick z'' ∈ Z with ‖y − z''‖ ≤ S. If z'' ≠ z', then z'' ∈ Z' and ‖y − z''‖ ≤ S ≤ S'. If z'' = z', then ‖y − z‖ ≤ ‖y − z'‖ + ‖z' − z‖ < S + 2d + 4S = S'.
 Bound: S' = 2d + 5S ≤ 2d + 5d(5^{k−#Z} − 1)/2 = d(5^{k−#Z+1} − 1)/2 = d(5^{k−#Z'} − 1)/2.
 So (Z', S') is admissible with #Z' < #Z, contradicting minimality. Hence ‖z − z'‖ ≥ 2d + 4S for all distinct z, z' ∈ Z.

5. Conclusion. The pair (Z, S) of step 3 satisfies Z ⊆ s, #Z < #s, 0 ≤ S, the covering property, and (step 4) the separation property. Since #Z ≥ 1, S ≤ d(5^{k−1} − 1)/2 ≤ 5^k d ≤ (10k)^k d (5 ≤ 10k, d > 0). ∎

## Key steps

1. Admissible pairs (Z,S): Z ⊆ s nonempty, #Z < k, S-covering of s, S ≤ d(5^{k−#Z} − 1)/2
2. Start: Z₁ = s \ {y₁}, S₁ = d is admissible
3. Take an admissible pair with #Z minimal
4. If two centres were closer than 2d + 4S, deleting one and setting S' = 2d + 5S gives a smaller admissible pair — contradiction
5. Hence separation ‖z − z'‖ ≥ 2d + 4S, and S ≤ 5^k d ≤ (10k)^k d

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'theorem exist_disjoint_covering_families|theorem image_sub_le_mul_sub_of_deriv_le|theorem monotoneOn_of_deriv_nonneg|theorem tendsto_integral_filter_of_dominated_convergence|theorem lintegral_iUnion |theorem contDiff_norm_sq|theorem le_opNorm |theorem lintegral_indicator_const |theorem withDensity_apply |theorem measure_biUnion |theorem tendsto_nhds_unique |theorem measure_ball_pos|theorem ofReal_div_of_pos|theorem one_lt_card_iff_nontrivial' mathlib/Mathlib`
- `rg -n 'countable_of_nonempty_interior|IsPath.length_lt|sum_fiberwise_of_maps_to|exists_bound_of_continuousOn|deriv_nonpos|theorem ConnectedComponent' mathlib/Mathlib`
- `rg -n 'theorem|def Real.smoothTransition' mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean (no derivative bound for smoothTransition exists)`
- `grep -n 'trace_smulRight|theorem fderiv_fun_smul|theorem trace_eq_matrix_trace' mathlib Mathlib/LinearAlgebra/Trace.lean Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `grep -n '^theorem|^def|^noncomputable def' simongmt Chapter08/{Varifold,FirstVariationRiesz,FirstVariationBounds,WeightedRadialIdentity,RadialFirstVariation}.lean and Chapter04/FirstVariation.lean (tangentialDivergence, jacobian, firstVariationRieszMeasure, isFirstVariationPolarRepresentation_riesz, firstVariationNormOn_le_of_polarRepresentation, weightedCutoffMass, hasDerivAt_normalized_weightedCutoffMass, squaredRadialVectorField, radialNormalSq)`
- `python3 transitive scan of 'import Poincare…' lines from Submission's imports (Chapter08 closure: Varifold, FirstVariation*, FirstVariationRiesz, PolarNorm, ScalarRiesz, VectorRiesz, DeformationFamily/Integral, JacobianBounds, VarifoldConvergence; no WeightedRadialIdentity, RadialFirstVariation or Chapter04)`
- `lake env lean /tmp/allard-decomp-v1/ImportCheck.lean and ImportCheck2.lean (#check from import GMT.Ch08.Submission: hasDerivAt_normalized_weightedCutoffMass, radialNormalSq_nonneg and SimpleGraph connectivity unknown; Besicovitch.exist_disjoint_covering_families, isFirstVariationPolarRepresentation_riesz, hasDerivAt_integral_of_dominated_loc_of_deriv_le, monotoneOn_of_deriv_nonneg, tendsto_integral_filter_of_dominated_convergence, Real.smoothTransition.contDiff, Finset.sum_fiberwise_of_maps_to, Finset.exists_subset_card_eq, contDiff_norm_sq available)`
- `grep 'helper declarations' nodes/*/rlcr-plan-v1.md (14 plans: one theorem per node, no helpers, no import changes); git show b70dd9d and fb766d9 (accepted solutions are pure insertions; an extra import was dropped)`
- `lake env lean /tmp/allard-decomp-v1/Assembly.lean (9 sorried children + sorry-free parent assembly + comparator-form targets)`
- `lake env lean /tmp/allard-decomp-v1/Glue.lean (sibling glue G2-G7)`
- `lake env lean /tmp/allard-decomp-v1/C1proof.lean, C3aproof.lean, DivProof.lean (complete proofs; axioms propext, Classical.choice, Quot.sound)`
- `python3 validate_lean_statement (verifier/lean_contract.py) on all 9 lean_statements; grep of dag.json, the run directory and all git refs for the 9 intcpt_allard_* names (0 hits)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Combinatorics/SimpleGraph/Connectivity/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Combinatorics/SimpleGraph/Paths.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-plane-disintegration-a1-pointwise-measure-a1/rlcr-plan-v1.md`
- `/tmp/allard-decomp-v1/Assembly.lean`
- `/tmp/allard-decomp-v1/Glue.lean`
- `/tmp/allard-decomp-v1/C1proof.lean`
- `/tmp/allard-decomp-v1/C3aproof.lean`
- `/tmp/allard-decomp-v1/DivProof.lean`

The snapshot is project 63436ae6 + Mathlib 25730c7c; its Contract is byte-identical to the workspace Contract and Submission. The leaf policy (all 14 rlcr-plans) allows one theorem per node, with no helper declarations and no import changes. Submission's import closure contains SimonGMT Varifold, FirstVariation*, FirstVariationRiesz and VarifoldConvergence. It does not contain WeightedRadialIdentity, RadialFirstVariation, Chapter04 or Mathlib's SimpleGraph connectivity. So the children's proofs cite only closure lemmas: Besicovitch.exist_disjoint_covering_families with countable_of_nonempty_interior; isFirstVariationPolarRepresentation_riesz; Varifold.tangentialDivergence via LinearMap.trace_smulRight and fderiv_fun_smul; hasDerivAt_integral_of_dominated_loc_of_deriv_le; monotoneOn_of_deriv_nonneg; tendsto_integral_filter_of_dominated_convergence; Real.smoothTransition; contDiff_norm_sq; Finset.sum_fiberwise_of_maps_to and Finset.exists_subset_card_eq. Each was #checked from import GMT.Ch08.Submission. The weighted radial identity is re-derived in the child weighted_radial_monotonicity, and the 5(c) clustering is done by greedy merging. In the scratch copy with the comparator's replayed scope, all 9 statements elaborate in comparator form and pass validate_lean_statement. The parent's frozen type is proved from the 9 sorried stubs by a sorry-free assembly, and the sibling glue compiles. Three children (good_point_monotonicity, first_variation_le_sup_mul, radial_field_divergence) are fully proved with axioms propext, Classical.choice and Quot.sound only. The 9 lean_names are unused anywhere in the DAG, the run directory and the git refs.
