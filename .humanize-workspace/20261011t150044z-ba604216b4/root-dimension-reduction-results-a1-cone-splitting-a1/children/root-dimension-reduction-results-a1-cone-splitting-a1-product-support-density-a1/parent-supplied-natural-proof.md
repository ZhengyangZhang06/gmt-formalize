# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 10 and 11 of the parent proof (supports from the product measure; densities of products, parent C3), with the computation written out. Notation (all children): ℝ^P = Euclid P; H^k = μHE[k] (Mathlib's normalized k-dimensional Hausdorff measure, equal to Lebesgue measure on k-planes); ω_k = unitBallVolume k ∈ (0, ∞); for an IMRep R = (M, θ, ξ) (carrier, mult, orient) μ_R = R.measure = θ·H^k⌞M; T_x = approxTangentPlane k M x and p_x its orthogonal projection (starProjection). The parent node's dependency im_mass_measure (DAG node root.dimension_reduction_results-a1.im_mass_measure-a1, declaration dimred_im_mass_measure) gives, for an open U and R representing T in U: (a) M_W(T) = T.massOn W = μ_R(W) for open W ⊆ U; (b) x ∈ spt T iff μ_R(B_ε(x)) ≠ 0 for all ε > 0 (x ∈ U); (c) all representations of T have the same measure. Let m := n − d ≥ 1 and λ_L := H^d⌞L, which is d-dimensional Lebesgue measure on L (isometry with Euclid d, μHE[d] = volume there); write B^L_r(c) := L ∩ B_r(c) and note λ_L(B^L_r(c)) = ω_d r^d (for d = 0, L = {0} and λ_L is the unit point mass at 0).
1. (Balls.) Let t ∈ L, y ∈ L^⊥ and ρ > 0. For s ∈ L, (fun y' => s + y')^{−1}(B_ρ(t + y)) = B_ρ(t − s + y). For y' ∈ L^⊥, |t − s + y − y'|² = |t − s|² + |y − y'|² (t − s ∈ L, y − y' ∈ L^⊥). Since μ₀ is concentrated on L^⊥, μ₀(B_ρ(t − s + y)) = μ₀(B_{r(s)}(y)) with r(s) := (ρ² − |t − s|²)^{1/2} if |t − s| < ρ, and = 0 otherwise. By the product hypothesis, μ(B_ρ(t + y)) = ∫_{B^L_ρ(t)} μ₀(B_{r(s)}(y)) dλ_L(s).
2. (Supports.) From step 1: μ(B_ε(t + y)) ≤ λ_L(B^L_ε(t)) μ₀(B_ε(y)) = ω_d ε^d μ₀(B_ε(y)); and since r(s) ≥ ε/2 for |t − s| < ε/2, μ(B_ε(t + y)) ≥ ω_d (ε/2)^d μ₀(B_{ε/2}(y)). Hence μ(B_ε(t + y)) ≠ 0 for all ε > 0 iff μ₀(B_ε(y)) ≠ 0 for all ε > 0. By im_mass_measure (b) (U = ℝ^P) for S, R and for S₀, R₀: t + y ∈ spt S ⟺ y ∈ spt S₀.
3. (Masses of balls.) By im_mass_measure (a), S.massOn(B_ρ(x)) = μ(B_ρ(x)) and S₀.massOn(B_ρ(x)) = μ₀(B_ρ(x)). Hence HasMassDensity S x θ means 0 ≤ θ and μ(B_ρ(x))/(ω_n ρ^n) → θ as ρ ↓ 0, and similarly for S₀ with ω_m ρ^m.
4. (Density of S at t + y.) Let t ∈ L, y ∈ L^⊥, and let Θ₀ satisfy HasMassDensity S₀ y Θ₀ (it exists by hypothesis). Substituting s = t − ρσ (σ ∈ B^L_1(0), dλ_L(s) = ρ^d dλ_L(σ)) in step 1: (ω_n ρ^n)^{−1} μ(B_ρ(t + y)) = ω_n^{−1} ∫_{B^L_1(0)} f_ρ(σ) (1 − |σ|²)^{m/2} dλ_L(σ), where f_ρ(σ) := μ₀(B_{ρ(1−|σ|²)^{1/2}}(y)) / (ρ(1 − |σ|²)^{1/2})^m. As ρ ↓ 0, f_ρ(σ) → ω_m Θ₀ for each σ ∈ B^L_1(0) (step 3 with radius ρ(1 − |σ|²)^{1/2} ↓ 0). Since s^{−m} μ₀(B_s(y)) → ω_m Θ₀ < ∞, there is s₀ > 0 with C := sup_{0<s≤s₀} s^{−m} μ₀(B_s(y)) < ∞; for ρ ≤ s₀, 0 ≤ f_ρ ≤ C, and (1 − |σ|²)^{m/2} ≤ 1 on the finite-measure set B^L_1(0). By dominated convergence, (ω_n ρ^n)^{−1} μ(B_ρ(t + y)) → ω_n^{−1} ω_m Θ₀ ∫_{B^L_1(0)} (1 − |σ|²)^{m/2} dλ_L(σ) = Θ₀, using ω_m ∫_{|σ|<1, σ ∈ ℝ^d} (1 − |σ|²)^{m/2} dσ = ω_n (Fubini for the unit ball of ℝ^n = ℝ^d × ℝ^m: its slice over σ is an m-ball of radius (1 − |σ|²)^{1/2}). Hence HasMassDensity S (t + y) Θ₀ (Θ₀ ≥ 0).
5. (Equivalence.) Densities are unique: two limits of the same function along the nontrivial filter 𝓝[>] 0 in ℝ≥0∞ coincide, and ofReal is injective on [0, ∞). If HasMassDensity S (t + y) θ, then θ = Θ₀ by step 4, so HasMassDensity S₀ y θ. If HasMassDensity S₀ y θ, then θ = Θ₀ (uniqueness for S₀), so HasMassDensity S (t + y) θ by step 4. This proves HasMassDensity S (t + y) θ ⟺ HasMassDensity S₀ y θ for every θ.

## Key steps

1. Orthogonality and μ₀(ℝ^P ∖ L^⊥) = 0 turn the product identity into μ(B_ρ(t + y)) = ∫_{|s−t|<ρ, s∈L} μ₀(B_{(ρ²−|t−s|²)^{1/2}}(y)) ds.
2. Two-sided ball estimates give μ charges every ball at t + y iff μ₀ charges every ball at y; im_mass_measure (b) converts this to supports.
3. Rescaling s = t − ρσ and dominated convergence (bounded ratios of μ₀ near y) give Θ^n(μ, t + y) = Θ^{n−d}(μ₀, y), using ω_{n−d}∫_{B^d}(1 − |σ|²)^{(n−d)/2} = ω_n.
4. Uniqueness of densities turns this into the stated equivalence for every θ.

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
