# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1`
- Child DAG node: `root.dimension_reduction_results-a1.one_dim_cones-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step T8 (Simon 7.3.3(2), formula (10), chapter-07.txt lines 547–555: "it is easy to check that such a 1-dimensional minimizing cone necessarily has the form m[[ℓ]]"), proof supplied. μ := μ_C (= R.measure for every representation R of C, and M_W(C) = μ(W) for open W, spt C = spt μ: sibling child im_mass_measure (c), (a), (b)). ω_1 = unitBallVolume 1 = 2. [[b, a]] denotes the oriented segment from b to a, [[b, a]](ω) = ∫_0^1 ω(b + t(a − b))(a − b) dt, an integer multiplicity 1-current with ∂[[b, a]] = [[a]] − [[b]] and mass |a − b|.
0. If P = 0, every 1-covector on ℝ^0 vanishes, so C = 0; take e := 0, m := 0 (spt 0 = ∅ ⊆ {0}, and HasMassDensity 0 0 0 holds because all masses of the zero current vanish). Assume P ≥ 1 and C ≠ 0 (if C = 0 take any e with |e| = 1 and m := 0).
1. (Monotonicity.) ℝ^P is an embedded C² P-dimensional submanifold (identity chart), closure ℝ^P ∖ ℝ^P = ∅ and spt C ⊆ ℝ^P, so the sibling child monotonicity applies with U = N = ℝ^P, n = 1, d = P: ρ ↦ ρ^{−1}μ(B_ρ(y)) is nondecreasing on (0, ∞) for every y, Θ(y) := Θ^1(μ, y) exists for every y, and Θ ≥ 1 on spt C.
2. (Cone measure.) For λ > 0, η_{0,λ#}C = C, and masses scale as M_W(η_{0,λ#}C) = λ^{−1}M_{λW}(C) (η_{0,λ}^#ω(w) = λ^{−1}ω(w/λ)); so μ(λW) = λμ(W) for open W and hence μ(λA) = λμ(A) for all Borel A. In particular μ(B_ρ(0)) = ρμ(B_1(0)) → 0, so μ({0}) = 0, and spt C is invariant under dilations.
3. (Finitely many rays.) For Borel Ω ⊆ ∂B_1(0) put ν(Ω) := μ({x : 0 < |x| < 1, x/|x| ∈ Ω}); ν is a finite Borel measure (ν(∂B_1) ≤ μ(B_1) < ∞). For 0 ≤ a < b, the function t ↦ g(t) := μ({0 < |x| < t, x/|x| ∈ Ω}) satisfies g(λt) = λg(t) (step 2), so g(t) = t·ν(Ω) and μ({a < |x| < b, x/|x| ∈ Ω}) = (b − a)ν(Ω). Let Σ := spt C ∩ ∂B_1(0); by step 2, rω' ∈ spt C for all ω' ∈ Σ, r > 0, and x/|x| ∈ Σ for every x ∈ spt C ∖ {0}. For ω' ∈ Σ and small ρ, every x ∈ B_ρ(ω') satisfies ||x| − 1| < ρ and |x/|x| − ω'| ≤ ||x| − 1| + |x − ω'| < 2ρ, so μ(B_ρ(ω')) ≤ 2ρ·ν(∂B_1 ∩ B_{2ρ}(ω')); dividing by ω_1ρ = 2ρ and letting ρ ↓ 0, 1 ≤ Θ(ω') ≤ ν({ω'}). Since ν is finite, Σ is a finite set {e_1, …, e_q} of distinct unit vectors, and ν(∂B_1 ∖ Σ) = 0. With a_i := ν({e_i}) ≥ 1: μ = Σ_i a_i H^1⌞ray(e_i), ray(e) := {te : t > 0} (both sides agree on the sets {a < |x| < b, x/|x| ∈ Ω}, on ℝ^P ∖ spt C, and give 0 mass to {0}).
4. (Constancy on rays.) Fix i and let V_i be an open neighbourhood of ray(e_i) disjoint from 0 and from the other rays (e.g. a thin open cone around ray(e_i) with the vertex removed). In V_i, C is an integer multiplicity current with ∂C = 0 and support in the connected 1-dimensional submanifold ray(e_i) ∩ V_i; by the constancy theorem (Simon Ch. 6, 2.34, applied in coordinates in which ray(e_i) is an open half-axis, together with 2.35/2.36 for currents supported in a smooth submanifold), C⌞V_i = m_i[[ray(e_i)]]⌞V_i for some m_i ∈ ℤ, where [[ray(e)]](ω) := ∫_0^∞ ω(te)(e) dt; comparing mass measures, |m_i| = a_i ≥ 1. Hence C(ω) = Σ_i m_i∫_0^∞ ω(te_i)(e_i) dt for every ω ∈ 𝒟^1(ℝ^P) with 0 ∉ tsupport ω, and, since μ({0}) = 0 and |C(χ_εω)| ≤ sup|ω|·μ(B_{2ε}(0)) → 0 for cut-offs χ_ε supported in B_{2ε}(0), for every ω ∈ 𝒟^1(ℝ^P). Testing ∂C = 0 with f ∈ C^∞_c(ℝ^P), f(0) = 1: 0 = C(df) = Σ_i m_i∫_0^∞ (d/dt)f(te_i) dt = −Σ_i m_i, so Σ_i m_i = 0.
5. (Pairing argument.) By step 4, ∂(C⌞B_1(0))(f) = Σ_i m_i∫_0^1 (d/dt)f(te_i) dt = Σ_i m_i f(e_i), i.e. ∂(C⌞B_1(0)) = Σ_i m_i[[e_i]]. Let N₊ := Σ_{m_i>0} m_i = Σ_{m_i<0} |m_i| ≥ 1 (C ≠ 0 and Σm_i = 0). List the points e_i with m_i > 0, each repeated m_i times, as a_1, …, a_{N₊}, and the points e_i with m_i < 0, each repeated |m_i| times, as b_1, …, b_{N₊}. For any bijective pairing (a_j, b_j) put C' := C⌞(ℝ^P ∖ B_1(0)) + Σ_j [[b_j, a_j]]. Then C' is integer multiplicity (C⌞(ℝ^P ∖ B_1(0)) is represented by the representation of C restricted to the complement of B_1(0); segments are integer multiplicity; sums are integer multiplicity, Ch. 6, 3.2(1)); ∂C' = −∂(C⌞B_1(0)) + Σ_j([[a_j]] − [[b_j]]) = −Σ_i m_i[[e_i]] + Σ_i m_i[[e_i]] = 0 = ∂C; and spt(C' − C) ⊆ closedBall 0 1 is compact and contained in W := B_2(0), an open set with compact closure. By minimality, M_W(C) ≤ M_W(C'). Now M_W(C) = μ(B_2(0)) = 2Σ_i|m_i| = 4N₊, while M_W(C') ≤ μ(B_2(0) ∖ B_1(0)) + Σ_j|a_j − b_j| = 2N₊ + Σ_j|a_j − b_j| (subadditivity of M_W and im_mass_measure for the two summands). Hence 2N₊ ≤ Σ_j|a_j − b_j| ≤ 2N₊, because |a_j − b_j| ≤ 2 for unit vectors; so |a_j − b_j| = 2, i.e. a_j = −b_j, for every j and every pairing.
6. (Conclusion.) Since every pairing is antipodal, any positive point equals the negative of any negative point; so all positive points coincide with one unit vector a and all negative points with −a: the rays are ray(a) with multiplicity m := N₊ and ray(−a) with multiplicity −m. As [[ray(−a)]](ω) = ∫_0^∞ ω(−ta)(−a) dt = −∫_{−∞}^0 ω(sa)(a) ds, C(ω) = m∫_ℝ ω(sa)(a) ds = m[[ℝa]](ω). Put e := a, so |e| = 1 and m ≥ 1. Then spt C = ℝe = span{e}, μ = m·H^1⌞ℝe, and for y ∈ ℝe and every ρ > 0, μ(B_ρ(y)) = 2mρ = m·ω_1ρ; hence M_{B_ρ(y)}(C)/(ω_1ρ) = m for all ρ > 0 and HasMassDensity C y m.

## Key steps

1. Monotonicity (stationary, Λ = 0) gives Θ ≥ 1 on spt C; the cone property gives μ(λA) = λμ(A).
2. Polar decomposition: every point of Σ = spt C ∩ ∂B_1 is an atom of ν of mass ≥ Θ ≥ 1, so spt C is a finite union of rays.
3. Constancy on each ray gives C = Σ m_i[[ray e_i]] with Σ m_i = 0 from ∂C = 0 at the vertex.
4. Replacing C⌞B_1 by segments joining the boundary points shows by minimality that every pairing of positive and negative points is antipodal.
5. Hence C = m[[ℝe]] (or C = 0), with density m along the whole line.

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
