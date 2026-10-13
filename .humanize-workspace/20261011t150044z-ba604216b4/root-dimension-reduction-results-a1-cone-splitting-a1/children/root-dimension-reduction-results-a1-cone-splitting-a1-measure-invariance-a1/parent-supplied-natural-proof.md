# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.measure_invariance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 2 of the parent proof (μ = Θ·H^n; T6 invariance of μ), citing Simon Ch. 3, Theorem 1.9 and Ch. 4, Remark 1.8(2) for densities of rectifiable measures, and Simon Ch. 1, Theorem 3.6 with Remark 3.7(2) for the upper-density estimate; the arguments are written out. Notation (all children): ℝ^P = Euclid P; H^k = μHE[k] (Mathlib's normalized k-dimensional Hausdorff measure, equal to Lebesgue measure on k-planes); ω_k = unitBallVolume k ∈ (0, ∞); for an IMRep R = (M, θ, ξ) (carrier, mult, orient) μ_R = R.measure = θ·H^k⌞M; T_x = approxTangentPlane k M x and p_x its orthogonal projection (starProjection). The parent node's dependency im_mass_measure (DAG node root.dimension_reduction_results-a1.im_mass_measure-a1, declaration dimred_im_mass_measure) gives, for an open U and R representing T in U: (a) M_W(T) = T.massOn W = μ_R(W) for open W ⊆ U; (b) x ∈ spt T iff μ_R(B_ε(x)) ≠ 0 for all ε > 0 (x ∈ U); (c) all representations of T have the same measure.
1. (The density function and its invariance.) For each x choose Θ(x) with HasMassDensity S x Θ(x); thus Θ(x) ≥ 0 and S.massOn(B_ρ(x))/(ω_n ρ^n) → ofReal Θ(x) as ρ ↓ 0. By im_mass_measure (a) (U = ℝ^P, W = B_ρ(x) open), S.massOn(B_ρ(x)) = μ(B_ρ(x)), so μ(B_ρ(x))/(ω_n ρ^n) → Θ(x). Densities are unique: if HasMassDensity S x θ and HasMassDensity S x θ', the two limits along the nontrivial filter 𝓝[>] 0 in the Hausdorff space ℝ≥0∞ agree, so ofReal θ = ofReal θ', and θ, θ' ≥ 0 give θ = θ'. Consequently, for y ∈ L, λ > 0 and w ∈ ℝ^P, the hypothesis applied to HasMassDensity S w Θ(w) gives HasMassDensity S (y + λw) Θ(w), whence Θ(y + λw) = Θ(w).
2. (Preliminaries on μ.) μ = θ·H^n⌞M is a Borel measure, finite on compact sets (field locallyIntegrable_mult), hence outer regular. As θ ≥ 1 on M, H^n(M ∩ K) ≤ μ(K) < ∞ for compact K, so ν := H^n⌞M is also locally finite, and μ and ν have the same null sets inside M. For r > 0 and x ∈ ℝ^P let η_{x,r}(z) := r^{−1}(z − x) (Chapter03.blowUpMap). H^n is invariant under isometries (Isometry.euclideanHausdorffMeasure_image) and H^n(cE) = c^n H^n(E) for c > 0 (MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ / hausdorffMeasure_smul₀; equivalently the accepted DAG lemma euclid_hausdorff_dilation_change_of_variables), so H^n(η_{x,r}(E)) = r^{−n} H^n(E).
3. (Θ = θ for H^n-a.e. x ∈ M.) Let G be the set of x ∈ M such that (α) M has an approximate tangent space Q at x (HasApproximateTangentSpaceAt n M x Q; then dim Q = n), and (β) ν(B̄_ρ(x))^{−1} ∫_{M ∩ B̄_ρ(x)} |θ − θ(x)| dH^n → 0 as ρ ↓ 0. Property (α) holds for H^n-a.e. x ∈ M by the field orients of R. Property (β) holds for ν-a.e. x by the Lebesgue–Besicovitch differentiation theorem for the locally finite measure ν on ℝ^P and the locally ν-integrable function θ (Simon Ch. 1, §4; Mathlib Besicovitch.vitaliFamily with VitaliFamily.ae_tendsto_average_norm_sub, whose sets are closed balls centred at x). So H^n(M ∖ G) = 0. Fix x ∈ G.
(a) r^{−n} H^n(M ∩ B_r(x)) → ω_n as r ↓ 0. For ε ∈ (0, 1) choose continuous compactly supported f_−, f_+ : ℝ^P → [0, 1] with f_− = 1 on B̄_{1−ε}(0), f_− = 0 off B_1(0), f_+ = 1 on B̄_1(0), f_+ = 0 off B_{1+ε}(0). Since η_{x,r}(M) ∩ B_1(0) = η_{x,r}(M ∩ B_r(x)), step 2 gives ∫_{η_{x,r}(M)} f_− dH^n ≤ r^{−n} H^n(M ∩ B_r(x)) ≤ ∫_{η_{x,r}(M)} f_+ dH^n. By (α) the outer terms converge to ∫_Q f_∓ dH^n, which lie in [ω_n(1 − ε)^n, ω_n(1 + ε)^n] because H^n restricted to the n-dimensional subspace Q is n-dimensional Lebesgue measure (AffineSubspace.euclideanHausdorffMeasure_coe_image; μHE[n] = volume on Euclid n), so H^n(Q ∩ B_s(0)) = ω_n s^n. Letting ε ↓ 0 proves (a). The same argument with B̄ gives r^{−n} ν(B̄_r(x)) → ω_n.
(b) μ(B̄_ρ(x)) = ∫_{M ∩ B̄_ρ(x)} θ dH^n = θ(x) ν(B̄_ρ(x)) + e(ρ) with |e(ρ)| ≤ ∫_{M ∩ B̄_ρ(x)} |θ − θ(x)| dH^n = o(ν(B̄_ρ(x))) = o(ρ^n) by (β) and (a). Hence μ(B̄_ρ(x))/(ω_n ρ^n) → θ(x). For every ε > 0, μ(B_ρ(x)) ≤ μ(B̄_ρ(x)) ≤ μ(B_{(1+ε)ρ}(x)), so the open-ball limit Θ(x) satisfies Θ(x) ≤ θ(x) ≤ (1 + ε)^n Θ(x); thus Θ(x) = θ(x).
4. (Θ = 0 for H^n-a.e. x ∉ M.) Let t > 0, R' > 0 and A := {x ∈ B_{R'}(0) ∖ M : Θ(x) > t}. Then μ(A) = 0 because μ is concentrated on M. Let ε, δ ∈ (0, 1). By outer regularity there is an open U' ⊇ A with μ(U') < ε. For each x ∈ A, μ(B_ρ(x))/(ω_n ρ^n) → Θ(x) > t, so there is ρ ∈ (0, δ) with B̄_ρ(x) ⊆ U' and μ(B_ρ(x)) > t ω_n ρ^n. By the Vitali 5r-covering lemma for closed balls of radii ≤ δ (Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall) there is a countable pairwise disjoint subfamily (B̄_{ρ_i}(x_i)) with A ⊆ ⋃_i B̄_{5ρ_i}(x_i). Each B̄_{5ρ_i}(x_i) has diameter ≤ 10ρ_i ≤ 10δ, so the 10δ-approximating sum of the unnormalized Hausdorff measure μH[n] satisfies μH[n]_{10δ}(A) ≤ Σ_i (10ρ_i)^n ≤ 10^n (t ω_n)^{−1} Σ_i μ(B_{ρ_i}(x_i)) ≤ 10^n (t ω_n)^{−1} μ(U') ≤ 10^n ε/(t ω_n). Letting ε ↓ 0 and then δ ↓ 0 gives μH[n](A) = 0, hence H^n(A) = 0 since μHE[n] is a finite multiple of μH[n] (euclideanHausdorffMeasure_def). Taking the union over R' ∈ ℕ and t = 1/k (k ∈ ℕ) shows H^n({x ∉ M : Θ(x) > 0}) = 0.
5. (μ = Θ·H^n.) By steps 3 and 4 and Θ ≥ 0, ofReal ∘ Θ = θ·1_M H^n-a.e. Therefore for every Borel A, ∫_A ofReal Θ dH^n = ∫_{A ∩ M} θ dH^n = μ(A); i.e. μ(A) = (H^n.withDensity (ofReal ∘ Θ))(A).
6. (Translation invariance, (i).) Let y ∈ L and A Borel; (fun x => y + x)⁻¹' A = A − y. The map z ↦ z + y is an isometry of ℝ^P, so it preserves H^n (IsometryEquiv.measurePreserving_euclideanHausdorffMeasure). By step 1 applied with the vector −y ∈ L and λ = 1, Θ((−y) + 1·x) = Θ(x) for every x, i.e. Θ(x − y) = Θ(x). Using step 5 and the change of variables x = z + y: μ(A − y) = ∫_{A − y} ofReal Θ(z) dH^n(z) = ∫_A ofReal Θ(x − y) dH^n(x) = ∫_A ofReal Θ(x) dH^n(x) = μ(A).
7. (Homogeneity, (ii).) Let λ > 0 and A Borel; λA = (fun x => λ • x) '' A is Borel (image under a homeomorphism). By step 2, for every Borel g ≥ 0, ∫_{λA} g dH^n = λ^n ∫_A g(λw) dH^n(w): the image of the measure H^n⌞A under w ↦ λw is λ^{−n}·H^n⌞(λA), because H^n(A ∩ λ^{−1}E) = λ^{−n} H^n(λA ∩ E) (H^n(λF) = λ^n H^n(F) for every F) (the accepted DAG lemma euclid_hausdorff_dilation_change_of_variables states this change of variables). By step 1 with y = 0 ∈ L, Θ(λw) = Θ(w). Hence, by step 5, μ(λA) = ∫_{λA} ofReal Θ dH^n = λ^n ∫_A ofReal Θ(λw) dH^n(w) = λ^n ∫_A ofReal Θ dH^n = λ^n μ(A), i.e. μ((fun x => λ • x) '' A) = ofReal(λ^n)·μ(A).
(If P < n then H^n = 0 on ℝ^P, μ = 0 and (i), (ii) hold trivially; the argument above covers this case as well.)

## Key steps

1. Densities are unique (limits in ℝ≥0∞, θ ≥ 0), so the hypothesis gives Θ(y + λw) = Θ(w) for the density function Θ, and im_mass_measure (a) turns mass ratios into μ-ratios.
2. At H^n-a.e. x ∈ M (approximate tangent space and Besicovitch–Lebesgue point of θ) the density is θ(x); hence Θ = θ a.e. on M.
3. A Vitali 5r-covering with μ(A) = 0 shows H^n{x ∉ M : Θ(x) > 0} = 0.
4. Therefore μ = Θ·H^n, and translation invariance and n-homogeneity of H^n with the invariance of Θ give μ(A − y) = μ(A) for y ∈ L and μ(λA) = λ^n μ(A).

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
