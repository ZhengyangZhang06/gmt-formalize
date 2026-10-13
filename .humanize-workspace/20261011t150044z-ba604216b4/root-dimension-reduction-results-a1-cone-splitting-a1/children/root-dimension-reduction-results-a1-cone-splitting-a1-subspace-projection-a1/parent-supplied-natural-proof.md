# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.subspace_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 of the parent proof (footnote 2 of Simon 7.3.1, chapter-07.txt lines 358–362: orthogonal projection onto the subspace does not increase area). Cited results: Simon Ch. 6, 2.23–2.24 (push-forward f_#T for f proper on spt T, ∂f_# = f_#∂, spt f_#T ⊆ f(spt T)) and 3.3–3.9 (the push-forward of an integer multiplicity current by a Lipschitz map proper on its support is integer multiplicity, with f_#τ(M, θ, ξ)(ω) = ∫_M θ ⟨ω(f(x)), Λ_m d^Mf_x ξ(x)⟩ dH^m). Notation (all children): ℝ^P = Euclid P; H^k = μHE[k] (Mathlib's normalized k-dimensional Hausdorff measure, equal to Lebesgue measure on k-planes); ω_k = unitBallVolume k ∈ (0, ∞); for an IMRep R = (M, θ, ξ) (carrier, mult, orient) μ_R = R.measure = θ·H^k⌞M; T_x = approxTangentPlane k M x and p_x its orthogonal projection (starProjection). The parent node's dependency im_mass_measure (DAG node root.dimension_reduction_results-a1.im_mass_measure-a1, declaration dimred_im_mass_measure) gives, for an open U and R representing T in U: (a) M_W(T) = T.massOn W = μ_R(W) for open W ⊆ U; (b) x ∈ spt T iff μ_R(B_ε(x)) ≠ 0 for all ε > 0 (x ∈ U); (c) all representations of T have the same measure.
1. (Setting.) T is integer multiplicity; fix a representation R_T = (M, θ, ξ) and μ_T := R_T.measure. Let q be the orthogonal projection of ℝ^P onto V and p := I − q. By im_mass_measure (b) and second countability, μ_T(ℝ^P ∖ spt T) = 0, so μ_T(ℝ^P ∖ V) = 0 and H^m(M ∖ V) = 0; consequently H^m-a.e. x ∈ M has its approximate tangent plane T_x contained in V (approximate tangent planes of M and of M ∩ V agree H^m-a.e. on M ∩ V, and an approximate tangent plane of a subset of V lies in V), so Λ_m q ξ(x) = ξ(x) for μ_T-a.e. x.
2. (A competitor.) Let W be open with closure(W) compact, and S an integer multiplicity m-current in ℝ^P with ∂S = ∂T and K' := spt(S − T) a compact subset of W. We must show M_W(T) ≤ M_W(S). We have spt S ⊆ spt T ∪ K' ⊆ V ∪ K', and q is proper on V ∪ K' (q^{−1}(C) ∩ (V ∪ K') ⊆ (C ∩ V) ∪ K' for compact C, as q = id on V). Hence S'' := q_#S is defined, integer multiplicity, ∂S'' = q_#∂S = q_#∂T. By step 1, q_#T = T (q_#T(ω) = ∫_M θ ⟨ω(q(x)), Λ_m q ξ(x)⟩ dH^m = ∫_M θ ⟨ω(x), ξ(x)⟩ dH^m), so ∂S'' = ∂T and S'' − T = q_#(S − T), whose support lies in q(K'), a compact subset of V.
3. (The enlarged window.) A := q(W) is open in V (q : ℝ^P → V is a surjective linear map, hence open) and bounded. Choose ρ* > sup_{x∈W} |p(x)| and let W* := {t + y : t ∈ V^⊥, |t| < ρ*, y ∈ A}, the image of an open set of V^⊥ × V under the linear homeomorphism (t, y) ↦ t + y; W* is open with compact closure, W ⊆ W* (x = p(x) + q(x)), q(K') ⊆ A ⊆ W*, W* ∩ V = A and q^{−1}(W*) = q^{−1}(A). So spt(S'' − T) is a compact subset of V ∩ W*, and the minimality of T in V gives M_{W*}(T) ≤ M_{W*}(S'').
4. (Projection does not increase mass.) Let R_S = (M_S, θ_S, ξ_S) represent S and μ_S := R_S.measure. For a test form ω with tsupport ω ⊆ W* and Euclidean norm |ω(x)| ≤ 1: S''(ω) = ∫_{M_S} θ_S ⟨ω(q(x)), Λ_m q ξ_S(x)⟩ dH^m, and |Λ_m q ξ_S(x)| = |qτ_1 ∧ ⋯ ∧ qτ_m| ≤ Π |qτ_i| ≤ 1 for a unit simple ξ_S(x) = ±τ_1 ∧ ⋯ ∧ τ_m (Hadamard's inequality, |q| ≤ 1); hence |S''(ω)| ≤ μ_S(q^{−1}(W*)) and M_{W*}(S'') ≤ μ_S(q^{−1}(A)).
5. (Comparison.) S = T on the open set ℝ^P ∖ K', so μ_S = μ_T there (im_mass_measure (c) applied in ℝ^P ∖ K' to the restricted representations). Since μ_T is concentrated on V, q^{−1}(A) ∩ V = A, and W ∩ V ⊆ A (x = q(x) for x ∈ V): M_{W*}(T) = μ_T(W*) = μ_T(A) = μ_T(W) + μ_T(A ∖ W), and μ_S(q^{−1}(A)) ≤ μ_S(W) + μ_S(q^{−1}(A) ∖ W) = μ_S(W) + μ_T(q^{−1}(A) ∖ W) = μ_S(W) + μ_T(A ∖ W) (q^{−1}(A) ∖ W ⊆ ℝ^P ∖ K'). The term μ_T(A ∖ W) ≤ μ_T(closure W*) is finite. Combining with steps 3–4 and cancelling it: μ_T(W) ≤ μ_S(W), i.e. M_W(T) ≤ M_W(S) by im_mass_measure (a).
6. T is integer multiplicity and satisfies the minimality inequality for every such W and S, so IsMinimizingIn T univ.

## Key steps

1. spt T ⊆ V forces the carrier and the approximate tangent planes of T into V a.e., so q_#T = T for the orthogonal projection q onto V.
2. For a competitor S in W, S'' := q_#S is integer multiplicity with ∂S'' = ∂T and spt(S'' − T) ⊆ q(spt(S − T)) ⊆ V compact.
3. On the enlarged cylinder W* = {t + y : |t| < ρ*, t ⊥ V, y ∈ q(W)}, minimality in V gives μ_T(W*) ≤ M_{W*}(q_#S) ≤ μ_S(q^{−1}(q(W))) since |Λ_m q ξ| ≤ 1.
4. μ_S = μ_T off spt(S − T) and μ_T lives on V; cancelling the common finite term μ_T(q(W) ∖ W) gives M_W(T) ≤ M_W(S).

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
