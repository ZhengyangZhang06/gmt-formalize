# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.cone_of_radial_tangency-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof (cone part: since x ∈ T_xM μ-a.e., x ∧ ξ = 0 and the homotopy/Lie-derivative argument of Simon Ch. 6, 2.25–2.27 and 2.33 gives η_{0,λ#}S = S), written out with the Euler-field Cartan formula. Write n = m + 1 and μ = R.measure.
1. (Reduction.) For λ > 0, dilation 0 λ (y) = −(λ^{−1}·0) + λ^{−1}y = λ^{−1}y is a bijection of ℝ^P, so dilation 0 λ '' univ = univ and every ω ∈ 𝒟^n(ℝ^P) satisfies IsTestForm ω ∧ tsupport ω ⊆ dilation 0 λ '' univ. Unfolding currentEval, blowUp (restrictDomain, then affinePushforward with linear part dilationCLM P λ = λ^{−1}·id and translation 0) and affinePullbackForm: currentEval(blowUp S 0 λ, ω) = S(ω^λ), where ω^λ(y) = ω(λ^{−1}y) ∘ (λ^{−1}·id) = λ^{−n} ω(λ^{−1}y) by n-linearity. It suffices to prove S(ω^λ) = S(ω) for all λ > 0 and ω.
2. (x ∧ ξ(x) = 0.) For μ-a.e. x (μ and H^n⌞M have the same null sets on M, as θ ≥ 1 there): by the field orients there are an approximate tangent space Q of M at x and an orthonormal basis τ = (τ_1, …, τ_n) of Q with ξ(x)(α) = ±α(τ) for all n-covectors α; by uniqueness of approximate tangent spaces Q = T_x, and p_x(x) = x gives x ∈ Q = span τ. Hence for every (n+1)-covector β, ξ(x)(β.curryLeft x) = ±β(x, τ_1, …, τ_n) = 0, because x, τ_1, …, τ_n are linearly dependent. (This step is exactly the sibling child wedge_vanishes, the accepted declaration dtc_cone_wedge_vanishes, applied to R.)
3. (Derivative in the scale.) Fix ω ∈ 𝒟^n(ℝ^P), choose R_ω with spt ω ⊆ B_{R_ω}(0), and for s > 0 let β_s(y) := s^n ω(sy), a test form, and G(s) := S(β_s) = ∫_M θ(y) ξ(y)(s^n ω(sy)) dH^n(y) (R represents S). For s in a compact interval [a, b] ⊂ (0, ∞) the integrand and its s-derivative θ(y) ξ(y)(n s^{n−1} ω(sy) + s^n Dω(sy)[y]) vanish unless |y| ≤ R_ω/a and are bounded there by C θ(y) (ξ(y) is a unit orientation for H^n-a.e. y ∈ M, so ‖ξ(y)‖ ≤ 1 by the sibling child orientation_norm, the accepted declaration unit_orientation_norm_le_one), which is H^n-integrable over M ∩ B̄_{R_ω/a}(0). Differentiating under the integral sign, G is differentiable on (0, ∞) with G'(s) = S(n s^{n−1} ω(s·) + s^n Dω(s·)[·]). Since Dβ_s(y)[y] = s^{n+1} Dω(sy)[y], s G'(s) = S(γ_s) with γ_s(y) := n β_s(y) + Dβ_s(y)[y].
4. (Cartan's formula and ∂S = 0.) For the (m+1)-form β = β_s and the Euler field X(y) = y, d(ι_Xβ)(y) + (dβ(y)).curryLeft y = (m + 1) β(y) + Dβ(y)[y], where ι_Xβ(y) := β(y).curryLeft y (the sibling child euler_cartan, the accepted declaration dtc_cone_euler_cartan, applied at every y, β_s being smooth; it follows from the coordinate formula dβ(y)(w_0, …, w_{m+1}) = Σ_i (−1)^i Dβ(y)[w_i](w_0, …, ŵ_i, …, w_{m+1})). Hence γ_s = d(ι_Xβ_s) + ι_X dβ_s, where ι_Xβ_s is a smooth compactly supported m-form and ι_X dβ_s(y) = (dβ_s(y)).curryLeft y is a test n-form. Therefore S(γ_s) = S(d(ι_Xβ_s)) + S(ι_X dβ_s). The first term equals (∂S)(ι_Xβ_s) = 0 because BoundaryVanishes S (n = m + 1, S.boundary = 0). The second equals ∫_M θ(y) ξ(y)((dβ_s(y)).curryLeft y) dH^n(y) = 0 by step 2. So G'(s) = 0 for every s > 0.
5. (Conclusion.) G is constant on (0, ∞). For λ > 0, ω^λ = β_{1/λ}, so S(ω^λ) = G(1/λ) = G(1) = S(ω). By step 1, currentEval(blowUp S 0 λ, ω) = S ω for all λ > 0 and ω, i.e. IsConeCurrent S.

## Key steps

1. currentEval (blowUp S 0 λ) ω = S(λ^{−n} ω(λ^{−1}·)), so the cone property is the constancy of G(s) = S(s^n ω(s·)).
2. x ∈ T_x μ-a.e. gives ξ(x)(β.curryLeft x) = 0 for all (n+1)-covectors β.
3. s G'(s) = S(n β_s + Dβ_s[y]) = S(d ι_X β_s) + S(ι_X dβ_s) by Cartan's formula for the Euler field; the first term vanishes by ∂S = 0 and the second by x ∧ ξ = 0, so G is constant.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n '^theorem\|^def\|^structure\|^abbrev' simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward,WedgeForms,Product,GeometricPointProduct,Representation}.lean; sed -n 25,140p simongmt Chapter03/Rectifiable.lean`
- `sed -n 40,160p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] definition, euclideanHausdorffMeasure_zero, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_smul₀)`
- `grep -n 'ae_tendsto_average_norm_sub\|exists_disjoint_subfamily_covering_enlargement_closedBall\|map_linearDependent\|starProjection_eq_self_iff\|hausdorffMeasure_smul₀' in the snapshot mathlib`
- `sed -n 340,430p book/chapter-07.txt (Simon 7.3.1 with footnote 2, Remark 7.3.4, Lemma 7.3.5 'left to the reader')`
- `python3 inspection of dag.json: sibling frozen types (dimred_im_mass_measure, dimred_minimizing_monotonicity), accepted lemmas in other branches (imrep_univ_tangent_starProjection_aemeasurable, dtc_cone_wedge_vanishes, dtc_cone_euler_cartan, unit_orientation_norm_le_one, stationary_imrep_radial_tangency_of_ball_ratio), duplicate lean_name scan, reuse precedent in cone_lemma-a1/decomposition-v1.json`
- `grep -c dimred_cs_ dag.json; grep -rl dimred_cs_ GMT .lake/packages/simongmt/Poincare; grep -rl dimred_cs_ --include=*.lean .swarm-worktrees (no match anywhere)`
- `git cat-file -t 74a7d91… 9203aee… 77ba671… 0325970… (all commits present)`
- `lake env lean /tmp/cs-decomp/CheckV2.lean (12 child types as Submission.X in namespace GMT.Ch07 with the contract opens, stubs of minimizing_implies_stationary, dimred_im_mass_measure, dimred_minimizing_monotonicity, assembly of dimred_invariant_cone_splitting, #print axioms, pp.coercions #check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-wedge-vanishes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-child-handoff.json`
- `/tmp/cs-decomp/CheckV2.lean`

The pins match: the snapshot is at project b4d606d (= workspace HEAD) and mathlib 25730c7c, and SimonGMT is at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

What the library lacks. SimonGMT provides geometric currents, boundary, massOn, support and the proper affine push-forward. It provides no slicing, no Cartesian products of currents, no IMRep push-forward, no homotopy formula, and no mass–measure identity for the contract's IMRep. WedgeForms is not imported by the contract. Therefore no child type may mention products or wedges; the product structure is passed as a measure identity, and the heavy constructions stay inside the proofs of split_off_spine and subspace_projection.

Mathlib facts used, all present in the snapshot:
- μHE[0] = μH[0] (counting measure);
- μHE[d] is invariant under isometries and satisfies the scaling law euclideanHausdorffMeasure_smul₀;
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall;
- VitaliFamily.ae_tendsto_average_norm_sub;
- AlternatingMap.map_linearDependent;
- Submodule.starProjection_eq_self_iff.

Reuse. Four comparator-accepted declarations from other branches are reused, with types byte-identical to dag.json: imrep_univ_tangent_starProjection_aemeasurable, dtc_cone_wedge_vanishes, dtc_cone_euler_cartan and unit_orientation_norm_le_one.

No reuse. stationary_imrep_radial_tangency_of_ball_ratio is accepted but covers only centre 0. The centre-z identity dtc_cone_monotonicity_identity and the cone criterion dtc_cone_of_wedge_vanishing are not accepted. So spine_tangency and cone_of_radial_tangency are new children under unique dimred_cs_ names.

Lean check. All 12 child types elaborate, and the assembly of the frozen dimred_invariant_cone_splitting type from them typechecks with only the stub sorries.
