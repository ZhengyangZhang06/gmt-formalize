# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1`
- Child DAG node: `root.dimension_reduction_results-a1.regular_point_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the regularity facts "x ∈ reg T, T = m[[M]] near x, μ_T = |m|H^n⌞M, hence Θ^n(μ_T, x) = |m|" used in the parent proof (steps B2, C4, C5, G(c)); the details are supplied. H^n := μHE[n]; |α| is the Euclidean coefficient norm of covectors (covectorEuclideanNorm); ω_n := unitBallVolume n.
1. (Data.) Unfold y ∈ regularSet T: y ∈ spt T, ρ₀ > 0 with B_{ρ₀}(y) ⊆ U, m₀ ∈ ℤ ∖ {0}, M with y ∈ M, IsEmbeddedSubmanifold 1 n M, ξ with IsOrientation n M ξ (ξ continuous on M and, for every x ∈ M, ξ(x)(α) = ±α(τ_1, …, τ_n) for an orthonormal basis τ of the tangent space T_xM), H^n(M ∩ K) < ∞ for compact K ⊆ B_{ρ₀}(y), and T(ω) = m₀∫_M ξ(x)(ω(x)) dH^n for ω ∈ 𝒟^n(U) with tsupport ω ⊆ B_{ρ₀}(y). Put m := |m₀| ∈ ℕ, so m ≥ 1.
2. (Local closedness.) Let (V, W, ψ) be the chart of M at y given by IsEmbeddedSubmanifold 1 n M: W is open with y ∈ W, ψ(V) = W ∩ M, ψ is C¹ and injective on the open set V ⊆ ℝ^n with injective differential, and V ∩ ψ^{−1}(K) is compact for every compact K ⊆ W. Choose ρ₁ ∈ (0, ρ₀/2) with closedBall y (2ρ₁) ⊆ W. Then M ∩ closedBall y (2ρ₁) = ψ(V ∩ ψ^{−1}(closedBall y (2ρ₁))) is compact, so M ∩ B_{2ρ₁}(y) is relatively closed in B_{2ρ₁}(y).
3. (Mass of T on small balls.) Let z ∈ ℝ^P and s > 0 with B_s(z) ⊆ B_{ρ₀}(y). Claim: M_{B_s(z)}(T) = m·H^n(M ∩ B_s(z)). (≤) For admissible ω (tsupport ω ⊆ B_s(z), |ω| ≤ 1), the pointwise duality |ξ(x)(α)| ≤ |α| for a unit simple orientation (Cauchy–Binet: α(τ_1, …, τ_n) = Σ_I α(e_I)det(τ^I) with Σ_I det(τ^I)² = 1) gives T(ω) ≤ m∫_{M∩B_s(z)} |ω| dH^n ≤ m·H^n(M ∩ B_s(z)). (≥) Let β(x) := sign(m₀)·Σ_I ξ(x)(dx^I)dx^I for x ∈ M; β is continuous on M, |β| = 1 and m₀·ξ(x)(β(x)) = m. Let K ⊆ M ∩ B_s(z) be compact and ε > 0; since H^n⌞M is finite on compact subsets of B_{ρ₀}(y) (outer regularity), choose an open V' with K ⊆ V', closure V' ⊆ B_s(z) compact and m·H^n(M ∩ V' ∖ K) < ε. Extend β|_K continuously to ℝ^P (Tietze, coordinatewise), compose with the retraction α ↦ α/max(1, |α|), multiply by χ ∈ C_c(V'; [0, 1]) with χ = 1 on K, and mollify: this gives smooth admissible forms ω_j (tsupport in V', |ω_j| ≤ 1) converging uniformly to a continuous γ with γ = β on K, |γ| ≤ 1 and γ = 0 off V'. By dominated convergence T(ω_j) → m₀∫_M ξ(γ) dH^n ≥ m·H^n(K) − m·H^n(M ∩ V' ∖ K) ≥ m·H^n(K) − ε. As K and ε are arbitrary, inner regularity of the finite measure H^n⌞(M ∩ B_s(z)) gives M_{B_s(z)}(T) ≥ m·H^n(M ∩ B_s(z)).
4. (Density of a C¹ submanifold.) Let z ∈ M ∩ B_{2ρ₁}(y). If n = 0, M is discrete near z (V ⊆ Euclid 0 is a point, so W ∩ M is a single point) and H^0(M ∩ B_s(z)) = 1 = ω_0s^0 for small s > 0 (μHE[0] is counting measure); assume n ≥ 1. Near z, M is the graph {z + v + u(v)} of a C¹ map u from a neighbourhood of 0 in the n-plane T_zM into (T_zM)^⊥ with u(0) = 0 and Du(0) = 0: write z = ψ(v_z) with v_z ∈ V; by properness and injectivity of ψ on V, points of M sufficiently close to z are images of points of V close to v_z (if ψ(v_j) → z then, V ∩ ψ^{−1}(closedBall z ε) being compact, every subsequence of (v_j) has a further subsequence converging to some v'' ∈ V with ψ(v'') = z, i.e. v'' = v_z), and by the inverse function theorem ψ maps a neighbourhood of v_z onto such a C¹ graph over T_zM = Dψ(v_z)(ℝ^n). By the area formula (μHE[n] restricted to an n-dimensional affine plane is its Lebesgue measure), H^n(M ∩ B_s(z)) = ∫_{G_s} J_u dL^n, where G_s := {v : |v|² + |u(v)|² < s²} and J_u(v) = (det(I + Du(v)ᵀDu(v)))^{1/2} → 1 as v → 0. Since |u(v)| = o(|v|), (T_zM ∩ B_{s(1−o(1))}(0)) ⊆ G_s ⊆ T_zM ∩ B_s(0), so H^n(M ∩ B_s(z)) = ω_n s^n(1 + o(1)) as s ↓ 0.
5. (Conclusion.) Put ρ := ρ₁. Let z ∈ spt T ∩ B_ρ(y). First, z ∈ M: otherwise, since M ∩ closedBall y (2ρ₁) is compact and z ∈ B_{ρ₁}(y), there is s ∈ (0, ρ₁) with B_s(z) ∩ M = ∅, and then T(ω) = m₀∫_M ξ(ω) dH^n = 0 for all ω with tsupport ω ⊆ B_s(z); since closure B_s(z) is a compact subset of B_{ρ₀}(y) ⊆ U, z would lie in zeroRegion(T), contradicting z ∈ spt T. So z ∈ M ∩ B_{ρ₁}(y). For 0 < s < ρ₀/2 we have B_s(z) ⊆ B_{ρ₀}(y), so by steps 3 and 4, M_{B_s(z)}(T)/(ω_n s^n) = m·H^n(M ∩ B_s(z))/(ω_n s^n) → m as s ↓ 0. Since m ≥ 0, this is HasMassDensity T z m.

## Key steps

1. Unfold regularSet: T = m₀[[M]] on B_{ρ₀}(y) with M an embedded C¹ n-submanifold through y and m := |m₀| ≥ 1.
2. M is relatively closed near y, so spt T ∩ B_ρ(y) ⊆ M for small ρ.
3. M_{B_s(z)}(T) = m·H^n(M ∩ B_s(z)) by the duality |ξ(α)| ≤ |α| and smooth approximation of the dual covector field of ξ.
4. A C¹ embedded submanifold has H^n-density 1 at each of its points (graph and area formula), so Θ^n(μ_T, z) = m on spt T ∩ B_ρ(y).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n 'μHE\|euclideanHausdorffMeasure' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (same file)`
- `grep -rn 'theorem massOn_le_liminf\|theorem boundary_affinePushforward\|exp_normalizedBallMass_monotoneOn\|theorem bvVariationOn_le_liminf_of_locallyL1\|theorem cone_simonsDefect_lower_bound' simongmt/Poincare`
- `grep -n 'def support\|zeroRegion\|def massOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn dimred --include=*.lean GMT .lake/packages/simongmt/Poincare; grep -c dimred dag.json; grep -rln dimred_ .swarm-worktrees/*/gmt-ch07/GMT (no match anywhere)`
- `python3 inspection of dag.json: sibling lean_statements (abstract_dimension_reduction, density_and_tangent_cones, density_one_implies_regular, compactness_of_minimizing_currents, minimizing_implies_stationary) and similar lemma nodes in other branches (dtc_mass_eq_measure, dor_imrep_massOn_eq_measure_and_support, dtc_dim_zero_eq_zero, imrep_measure_eq_of_represents_same_current, rsd_massOn_eq_measure)`
- `lean -R /tmp/dr-v2-check/src /tmp/dr-v2-check/src/CheckV2Types.lean (private olean of GMT.Ch07.Submission; 12 child types declared as Submission.X in namespace GMT.Ch07 with the contract opens; assembly ⟨A, B, C⟩; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-review-receipt-v1.json`
- `/tmp/dr-v2-check/src/CheckV2Types.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD), mathlib 25730c7c and simongmt 2b36630. The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean; its only sorry is the frozen main_theorem.

Normalization (decides correction R1). Mathlib defines μHE[d] = addHaarScalarFactor(volume, μH[d]) • μH[d] (Measure.lean, lines 68–101). The scalar is in ℝ≥0 and nonzero (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero), so μ_A = ϑ_A·μHE[n] gives ∫_K ϑ_A dμH[n] = c_n⁻¹·μ_A(K).

SimonGMT definitions used:
- massOn is the sSup over admissible forms with Euclidean coefficient norm ≤ 1 (Mass.lean).
- support = U \ zeroRegion (CurrentLocalEquality.lean, lines 108–117).
- WeaklyConvergesOn.massOn_le_liminf (Mass.lean:100) gives the lower semicontinuity used for the new mass bounds.

Other cited library facts exist:
- GeometricCurrentOn.boundary_affinePushforward (AffineCurrentPushforward.lean:188);
- HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn (Chapter04/MeanCurvature.lean:361);
- bvVariationOn_le_liminf_of_locallyL1 (Chapter02/BV.lean:225);
- cone_simonsDefect_lower_bound (AppendixB/ConeDefect.lean:228).

The library provides none of the following for the contract's IMRep currents: the mass–measure identity, product currents, Federer–Fleming compactness, or Appendix A.4. These are children or sibling prerequisites.

Lean check. All twelve child types elaborate after import GMT.Ch07.Submission, in namespace GMT.Ch07 with the contract opens, with only the stub sorry warnings. The assembly ⟨A, B, C⟩ proves IntegerDensityAndTangentPlanes ∧ SingularSetSmallWhereDensityBelowTwo ∧ CodimensionOneRegularity, and the conditional assembly depends only on propext, Classical.choice and Quot.sound.

Names. No dimred_ identifier occurs in the workspace, SimonGMT, any speculative worktree or dag.json. Similar lemmas in other branches have different types and names, so there is neither reuse nor collision.
