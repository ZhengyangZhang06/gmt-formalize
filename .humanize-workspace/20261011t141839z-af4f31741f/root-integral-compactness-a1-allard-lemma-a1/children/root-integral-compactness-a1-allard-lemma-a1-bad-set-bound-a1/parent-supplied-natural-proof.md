# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (Simon 8.5.10, printed (4)–(5) and the Besicovitch estimate (A_1 ∪ A_2) ≤ cε), with ERRATUM (E2): in (1) the book's 'δ‖W‖(B_ρ(y))' means ‖δW‖(B_ρ(y)). Notation: μ := W.weight; ‖δW‖ := variationMeasure W; B_ρ(y) := closedBall y ρ, B°_ρ(y) := ball y ρ; G := Grassmannian N n; t_P(S) := ‖LinearMap.toContinuousLinearMap(projectionLinearMap S − projectionLinearMap P)‖ ≥ 0; for A ⊆ ℝ^N, T(A) := ∫⁻_{A ×ˢ univ} ofReal t_P(z.2) dW.measure(z); e := Real.exp 1; (1), (2), E as in the statement.

1. Besicovitch constant. By HasBesicovitchCovering.no_satelliteConfig for Euclidean N there are N_B ∈ ℕ and τ₀ > 1 such that there is no satellite configuration of N_B + 1 balls with parameter τ₀. Then Besicovitch.exist_disjoint_covering_families gives: for every index type ι and every family of closed balls B_{r_i}(c_i) (i ∈ ι) with 0 < r_i ≤ R, there are D_1,…,D_{N_B} ⊆ ι such that the balls indexed by each D_k are pairwise disjoint and every centre c_i lies in ⋃_k ⋃_{i∈D_k} B°_{r_i}(c_i) ⊆ ⋃_k ⋃_{i∈D_k} B_{r_i}(c_i). Put c₀ := N_B·(eΛ + 1) ≥ 0; it depends only on N and Λ.

2. Fix ε ∈ (0,1], U, W, P with the hypotheses. Both T and ‖δW‖ are monotone under inclusion, and for a countable family (A_i) of pairwise disjoint Borel sets, T(⋃A_i) = Σ_i T(A_i) (lintegral_iUnion applied to the pairwise disjoint measurable sets A_i ×ˢ univ) and ‖δW‖(⋃A_i) = Σ_i ‖δW‖(A_i). Put ν(A) := ofReal(eΛ/ε)·T(A) + ofReal(1/ε)·‖δW‖(A); ν is monotone and countably additive on pairwise disjoint Borel sets.

3. Mass bound. If y ∈ B_2(0) satisfies (1), then B°_1(y) ⊆ B°_3(0) ⊆ U (|z| ≤ |z − y| + |y| < 1 + 2) and μ(B°_1(y)) ≤ μ(B°_3(0)) ≤ ofReal Λ, so the sibling good_point_monotonicity (conclusion (iii), with ε ≥ 0) gives μ(B_ρ(y)) ≤ ofReal(e^εΛρ^n) ≤ ofReal(eΛρ^n) for all ρ ∈ (0,1) (e^ε ≤ e because ε ≤ 1, and Λ ≥ 0).

4. A ball at each bad point. Let y ∈ E; so |y| ≤ 2 and (1) ∧ (2) fails at y.
 – If (1) fails, choose ρ_y ∈ (0,1) with ofReal ε·μ(B_{ρ_y}(y)) < ‖δW‖(B_{ρ_y}(y)). Multiplying by ofReal(1/ε) and using ofReal(1/ε)·ofReal ε = 1: μ(B_{ρ_y}(y)) ≤ ofReal(1/ε)·‖δW‖(B_{ρ_y}(y)).
 – If (1) holds, then (2) fails: choose ρ_y ∈ (0,1) with ofReal(ερ_y^n) < T(B_{ρ_y}(y)). By step 3, μ(B_{ρ_y}(y)) ≤ ofReal(eΛρ_y^n) = ofReal(eΛ/ε)·ofReal(ερ_y^n) ≤ ofReal(eΛ/ε)·T(B_{ρ_y}(y)).
 In both cases (∗) μ(B_{ρ_y}(y)) ≤ ν(B_{ρ_y}(y)). Moreover B_{ρ_y}(y) ⊆ B°_3(0), since |y| ≤ 2 and ρ_y < 1.

5. Covering. Apply step 1 to the family (B_{ρ_y}(y))_{y∈E} (index type E, radii in (0,1), R := 1): there are D_1,…,D_{N_B} ⊆ E, each with pairwise disjoint balls, with E ⊆ ⋃_k ⋃_{y∈D_k} B_{ρ_y}(y). Each D_k is countable, because its balls are pairwise disjoint with nonempty interior (y ∈ B°_{ρ_y}(y) ⊆ interior B_{ρ_y}(y)) in the separable space ℝ^N (Set.PairwiseDisjoint.countable_of_nonempty_interior).

6. One family. For each k, by (∗), countable additivity of ν on the disjoint Borel balls, monotonicity (all balls lie in B°_3(0)) and the hypotheses T(B°_3(0)) < ofReal(ε²), ‖δW‖(B°_3(0)) < ofReal(ε²):
 Σ_{y∈D_k} μ(B_{ρ_y}(y)) ≤ Σ_{y∈D_k} ν(B_{ρ_y}(y)) = ν(⋃_{y∈D_k} B_{ρ_y}(y)) ≤ ν(B°_3(0)) ≤ ofReal(eΛ/ε)·ofReal(ε²) + ofReal(1/ε)·ofReal(ε²) = ofReal((eΛ + 1)ε).

7. Conclusion. By monotonicity and (countable) subadditivity of the outer measure μ (measure_mono, measure_iUnion_fintype_le, measure_biUnion_le):
 μ(E) ≤ Σ_{k=1}^{N_B} μ(⋃_{y∈D_k} B_{ρ_y}(y)) ≤ Σ_k Σ_{y∈D_k} μ(B_{ρ_y}(y)) ≤ N_B·ofReal((eΛ + 1)ε) = ofReal(c₀ε).
 E need not be measurable: only monotonicity and subadditivity of the outer measure were used. ∎

## Key steps

1. Fix the Besicovitch number N_B of Euclidean N and c₀ := N_B(eΛ + 1)
2. At points of B_2(0) satisfying (1), good_point_monotonicity gives μ(B_ρ(y)) ≤ eΛρ^n for ρ ∈ (0,1) (ε ≤ 1)
3. At each y ∈ E pick ρ_y ∈ (0,1) where (1) or (2) fails; in both cases μ(B_{ρ_y}(y)) ≤ ν(B_{ρ_y}(y)) with ν := (eΛ/ε)T + ε⁻¹‖δW‖, and B_{ρ_y}(y) ⊆ B°_3(0)
4. Besicovitch: N_B pairwise-disjoint (hence countable) subfamilies cover E
5. Per subfamily: Σμ ≤ Σν = ν(union) ≤ ν(B°_3(0)) ≤ (eΛ + 1)ε by the smallness hypotheses
6. Sum over the N_B subfamilies by outer-measure subadditivity: μ(E) ≤ c₀ε

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
