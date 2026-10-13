# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1.campanato_from_tilt-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.campanato_from_tilt-a1.tilt_lintegral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(d), 1(e), 4 and the first equality of step 5 of the parent proof (Simon Ch. 5, proof of 5.2, (10)). The finiteness μ(B_s(ζ)) < ∞ from parent step 3 is taken as an explicit hypothesis, so the lemma does not involve U.

Setting and notation. n, ℓ ∈ ℕ, N := n + ℓ, U ⊆ ℝ^N, V : RectifiableVarifold n ℓ U, μ := V.weight, p_y := V.tangentProj y. Hypotheses:
(H1) y ↦ p_y is μ-a.e. strongly measurable;
(H2) s > 0;
(H3) μ(B) < ∞, where B := B_s(ζ) is the closed ball.
T is a linear subspace of ℝ^N and P := T.starProjection is the orthogonal projection onto T. For a continuous linear A : ℝ^N → ℝ^N, hsNormSq(A) := Σ_{i ∈ Fin N} ‖A e_i‖², where e_i := EuclideanSpace.single i 1 is the i-th standard basis vector. ‖·‖ is the Euclidean norm on vectors and the operator norm on continuous linear maps. Put h(y) := hsNormSq(p_y − P).

1. ‖p_y‖ ≤ 1 for every y ∈ ℝ^N. By definition (RectifiableVarifold.tangentProj), p_y is W.starProjection for a subspace W (the chosen approximate tangent space) when one exists, and 0 otherwise. In the first case ‖W.starProjection‖ ≤ 1 (Submodule.starProjection_norm_le); in the second, ‖0‖ = 0 ≤ 1. Likewise ‖P‖ ≤ 1 by Submodule.starProjection_norm_le.

2. For every continuous linear A: 0 ≤ hsNormSq(A) ≤ N‖A‖².
 - Nonnegativity: hsNormSq(A) is a sum of squares.
 - Upper bound: ‖e_i‖ = 1, so ‖A e_i‖ ≤ ‖A‖ ‖e_i‖ = ‖A‖ (ContinuousLinearMap.le_opNorm). Hence ‖A e_i‖² ≤ ‖A‖², since squaring is monotone on [0, ∞). Summing over the N indices gives hsNormSq(A) ≤ N‖A‖².

3. 0 ≤ h(y) ≤ 4N for every y. By the triangle inequality and step 1, ‖p_y − P‖ ≤ ‖p_y‖ + ‖P‖ ≤ 2. So by step 2, 0 ≤ h(y) ≤ N‖p_y − P‖² ≤ N · 2² = 4N. In particular |h(y)| ≤ 4N for every y.

4. The map c : A ↦ hsNormSq(A − P), from continuous linear maps of ℝ^N to ℝ, is continuous. Indeed c(A) = Σ_i ‖(A − P) e_i‖² is a finite sum. Each summand is the composite of continuous maps: A ↦ A − P, then evaluation at the fixed vector e_i (A ↦ A e_i is continuous linear in A), then the norm, then squaring.

5. h = c ∘ (y ↦ p_y) is μ-a.e. strongly measurable. It is the composite of the continuous map c (step 4) with the map y ↦ p_y, which is μ-a.e. strongly measurable by (H1) (Continuous.comp_aestronglyMeasurable).

6. h is μ-integrable on B. We have μ(B) ≠ ∞ by (H3), h is μ-a.e. strongly measurable (step 5), and |h| ≤ 4N everywhere (step 3). So Measure.integrableOn_of_bounded applies: a bounded a.e. strongly measurable function on a set of finite measure is integrable there.

7. h is integrable on B (step 6) and h ≥ 0 everywhere (step 3). So ofReal_integral_eq_lintegral_ofReal, applied to μ restricted to B, gives ofReal(∫_B h dμ) = ∫⁻_B ofReal(h) dμ.

8. By definition (RectifiableVarifold.tiltExcess), V.tiltExcess ζ s T = (s^n)^{-1} ∫_B h dμ. By (H2), s^n > 0, in particular s^n ≠ 0. Hence s^n · V.tiltExcess ζ s T = s^n · ((s^n)^{-1} ∫_B h dμ) = ∫_B h dμ (mul_inv_cancel_left₀).

9. By steps 7 and 8: ∫⁻_{B_s(ζ)} ofReal(hsNormSq(p_y − P)) dμ(y) = ofReal(∫_B h dμ) = ofReal(s^n · V.tiltExcess ζ s T). ∎

## Key steps

1. ‖p_y‖ ≤ 1 (p_y is an orthogonal projection, Submodule.starProjection_norm_le, or 0) and ‖P‖ ≤ 1
2. hsNormSq A ≤ (n+ℓ)‖A‖² from ‖A e_i‖ ≤ ‖A‖, hence 0 ≤ hsNormSq(p_y − P) ≤ 4(n+ℓ)
3. A ↦ hsNormSq(A − P) is continuous, so y ↦ hsNormSq(p_y − P) is μ-a.e. strongly measurable
4. bounded + a.e. strongly measurable + μ(B_s(ζ)) < ∞ ⇒ integrable on B_s(ζ) (Measure.integrableOn_of_bounded)
5. ofReal_integral_eq_lintegral_ofReal: ofReal ∫_B h dμ = ∫⁻_B ofReal h dμ
6. s^n · tiltExcess ζ s T = ∫_B h dμ since s^n ≠ 0 (mul_inv_cancel_left₀)

## Reference use

### local-project

Queries:
- `sha256sum <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean`
- `rg -n 'tiltExcess' <snapshot>/project -t lean (outside Contract.lean/Submission.lean)`
- `rg -ln 'graphPoint' <snapshot> -t lean`
- `rg -n 'theorem setLIntegral_congr_fun|theorem setLIntegral_le_lintegral|theorem lintegral_indicator|theorem ofReal_integral_eq_lintegral_ofReal|theorem integrableOn_of_bounded|theorem starProjection_norm_le|theorem withDensity_apply ' <snapshot>/mathlib/Mathlib`
- `rg -n 'integrableOn_of_bounded|Integrable.of_bound|norm_single|opNorm_le_bound|le_opNorm' <snapshot>/mathlib/Mathlib`
- `rg -n 'pow_le_pow_iff_left₀|Continuous.comp_aestronglyMeasurable|mul_inv_cancel_left₀|dist_le_mul|sq_sqrt|norm_map' <snapshot>/mathlib/Mathlib`
- `python: scan dag.json lean_statement for graphPoint, hsNormSq+tangentProj, tiltExcess, 'weight ... < ⊤', IsCompact+weight; list lean_names matching weight|lt_top|finite|hsNormSq|tilt`
- `python: cross-parent reuse precedents in dag.json (children/depends_on whose parent differs); status and candidate_commit of rsod_weight_closedBall_eq_ofReal_integral, lip_approx_graph_coordinates, rsod_norm_graphPoint_sq, lip_approx_gm_graph_map_lipschitz`
- `grep -n '_existing_lean_name_problem|def _accepted_checkpoint|existing_by_name|store.ensure' runtime.py`
- `grep max_nodes|max_depth|max_children swarm-project.json and newest .humanize/swarm-configs/*.json`
- `for nm in allard52_cft_tilt_lintegral_eq allard52_cft_graph_map_sqrt_two: rg -l nm <snapshot>; grep -rl nm GMT .lake/packages/simongmt <run>/nodes; grep nm dag.json; git log --all -S nm`
- `git show 02c3706f8b397dd9abf13122f4a7824d7bf445d3:GMT/Ch05/Submission.lean; git show e2915745b92c2117161b0d9eaeb226a1f6c30d1b:GMT/Ch05/Submission.lean (accepted proofs of the reused declarations)`
- `lean src/Submission.lean -o build/GMT/Ch05/Submission.olean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = scratch build + lake-packages-25730c7c)`
- `lean check/Types.lean; lean check/Children.lean; lean check/Assembly.lean; lean check/Full.lean (+ #print axioms)`
- `python: lean_contract.validate_lean_statement on the four child types; byte comparison of the child and parent types against dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/GroupWithZero/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-from-tilt-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-weight-ba-26a0dc4b42/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-graph-coordinates-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-density-from-tangent-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/lean_contract.py`
- `/tmp/cft-decomp-Sbg0wT/check/Types.lean`
- `/tmp/cft-decomp-Sbg0wT/check/Children.lean`
- `/tmp/cft-decomp-Sbg0wT/check/Assembly.lean`
- `/tmp/cft-decomp-Sbg0wT/check/Full.lean`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Submission.lean, the workspace Submission.lean and Contract.lean are identical (sha256 c966f51e...).

The snapshot project has no tiltExcess or graphPoint lemmas beyond the frozen contract (no match), so the reusable pieces come from the DAG:
- rsod_weight_closedBall_eq_ofReal_integral: accepted, candidate 02c3706f.
- lip_approx_graph_coordinates: accepted, candidate e2915745.
- lip_approx_gm_graph_map_lipschitz: accepted but unusable, because it needs f globally 1-Lipschitz.
- any_radius_gr_tilt_integral_facts and lgc_hsNormSq_bounds: unaccepted, reserved by other branches.

Mathlib lemmas used, with snapshot locations:
- Measure.integrableOn_of_bounded: IntegrableOn.lean:716.
- ofReal_integral_eq_lintegral_ofReal: Bochner/Basic.lean:739.
- setLIntegral_congr_fun (EqOn form), setLIntegral_le_lintegral, lintegral_indicator: Lebesgue/Basic.lean:298, 258, 510.
- withDensity_apply: WithDensity.lean:44.
- Submodule.starProjection_norm_le: Projection/Basic.lean:386.
- ContinuousLinearMap.le_opNorm: Operator/Basic.lean:234.
- pow_le_pow_iff_left₀: GroupWithZero/Basic.lean:681.
- Continuous.comp_aestronglyMeasurable: AEStronglyMeasurable.lean:233.
- mul_inv_cancel_left₀: GroupWithZero/Defs.lean:257.
- LipschitzOnWith.dist_le_mul: MetricSpace/Lipschitz.lean:57.
- Real.sq_sqrt: Real/Sqrt.lean:177.

Runtime rules: an accepted declaration may be reused across parents only with an identical frozen type; there are many precedents in dag.json. The two new names allard52_cft_tilt_lintegral_eq and allard52_cft_graph_map_sqrt_two occur nowhere in dag.json, the snapshot, GMT/, simongmt, run nodes or git history. Limits are max_depth 6, max_children 12 and max_nodes 1000; the DAG has 340 nodes.

Lean checks:
- All four child types elaborate and pass validate_lean_statement.
- Assembly proves the exact frozen parent type from them.
- The two new children are fully proved.
- Full.lean, with the accepted proofs inserted, compiles with no sorry, and allard52_campanato_from_tilt depends only on propext, Classical.choice and Quot.sound.
