# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.regular_component_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2 ('reg T is relatively open in spt T, and every z ∈ reg T has a ball B_r(z) with spt T ∩ B_r(z) = M' ∩ B_r(z) a connected C¹ graph …; (a) closure(M₁) ∖ M₁ ⊆ sing T; (b) …; on M₁, H^n(M₁ ∖ M) = 0 and ξ orients T_xM₁ a.e.'), Simon 7.4.1 (chapter-07.txt lines 590–612). The parent deduces T₁ = T near M₁ from θ = 1 a.e. (5.2(‡)); here only T₁ = |m_z|⁻¹·T near each z ∈ M₁ is proved, by uniqueness of the representation on a regular sheet, which is all the cut-off argument needs; 5.2(‡) is not used.
Notation: S := spt T = U ∖ Z(T), where Z(T) (zeroRegion) is the union of the open sets with compact closure in U on which T vanishes; Z(T) is open, so S is Borel and closure(S) ∩ U ⊆ S. reg := reg T ⊆ S and sing T = S ∖ reg. For z ∈ reg fix data (ρ_z, m_z, M_z, ξ_z) from the definition: ball(z, ρ_z) ⊆ U, m_z ∈ ℤ ∖ {0}, M_z an embedded C¹ n-submanifold with z ∈ M_z, oriented by ξ_z (continuous on M_z, each ξ_z(x) a unit orientation of T_xM_z), H^n(M_z ∩ K) < ∞ for compact K ⊆ ball(z, ρ_z), and T(ω) = m_z ∫_{M_z} ξ_z(ω) dH^n whenever tsupport ω ⊆ ball(z, ρ_z). For an orthonormal n-frame τ let β_τ ∈ Λ^n be β_τ(v_1, …, v_n) := det(⟨τ_i, v_j⟩) (the wedge of the covectors ⟨τ_i, ·⟩; SimonGMT Chapter06.wedgeCovectors_apply_det), so β_τ(τ) = 1; a unit orientation ε·ev_τ (ε = ±1, ev_τ(α) = α(τ)) satisfies |ε ev_τ(α)| ≤ ‖α‖ for all α and ε ev_τ(ε β_τ) = 1; in particular it is nonzero.

1. (Facts on an embedded C¹ n-submanifold M with a chart (V, W, ψ) at x ∈ M: V ⊆ ℝ^n and W ⊆ ℝ^P open, x ∈ W, ψ C¹ and injective on V with injective differential, ψ(V) = W ∩ M, and V ∩ ψ⁻¹(K) compact for every compact K ⊆ W.)
 (F1) ψ : V → W ∩ M is a homeomorphism, W ∩ M is relatively closed in W, and closure(M) ∩ W = M ∩ W. Proof: let F ⊆ V be relatively closed and let w ∈ W be a limit of ψ(f_j), f_j ∈ F. K := {ψ(f_j)} ∪ {w} is a compact subset of W, so the f_j lie in the compact set V ∩ ψ⁻¹(K); a subsequence converges to some v ∈ V; then v ∈ F and ψ(v) = w by continuity. So ψ maps relatively closed subsets of V to relatively closed subsets of W; with F = V, W ∩ M is relatively closed in W, and a continuous closed bijection V → W ∩ M is a homeomorphism. If x' ∈ closure(M) ∩ W, points of M converging to x' eventually lie in the open set W, so x' ∈ closure(W ∩ M) ∩ W = W ∩ M.
 (F2) H^n(ψ(B)) > 0 for every nonempty open B ⊆ V. Proof: fix v ∈ B, let L := Dψ(v) (injective), p the orthogonal projection onto L(ℝ^n), and Π := L⁻¹ ∘ p : ℝ^P → ℝ^n (linear, Lipschitz with constant ‖Π‖). Π ∘ ψ is C¹ near v with D(Π ∘ ψ)(v) = Id, so by the inverse function theorem it maps some open B' ⊆ B containing v onto a nonempty open set O ⊆ ℝ^n. Then 0 < L^n(O) = H^n(O) = H^n(Π(ψ(B'))) ≤ ‖Π‖^n H^n(ψ(B')) ≤ ‖Π‖^n H^n(ψ(B)). (μHE[n] = c_n·μH[n] with a constant c_n ∈ (0, ∞) depending only on n, so the Lipschitz image bound μH[n](Π(A)) ≤ Lip(Π)^n μH[n](A) (Mathlib LipschitzWith.hausdorffMeasure_image_le) carries over to H^n = μHE[n]; on ℝ^n, μHE[n] is Lebesgue measure, which is positive on nonempty open sets.)
 (F3) M is Borel: each x ∈ M has a chart set W_x with W_x ∩ M relatively closed in W_x (F1); countably many W_{x_i} cover M (Lindelöf), and M = ⋃_i (W_{x_i} ∩ closure(W_{x_i} ∩ M)).

2. (Local sheets.) For every z ∈ reg there is an open O_z with z ∈ O_z ⊆ ball(z, ρ_z) such that (a) S ∩ O_z = M_z ∩ O_z, (b) M_z ∩ O_z is connected, (c) S ∩ O_z ⊆ reg. Write ρ, m, M, ξ' for ρ_z, m_z, M_z, ξ_z.
 2.1 (S ∩ ball(z, ρ) ⊆ closure(M).) If x ∈ ball(z, ρ) ∖ closure(M), pick s > 0 with closedBall(x, s) ⊆ ball(z, ρ) ∖ closure(M). For tsupport ω ⊆ ball(x, s), T(ω) = m ∫_M ξ'(ω) dH^n = 0 since ω vanishes on M. So ball(x, s) (open, with compact closure in U) is a region where T vanishes: x ∈ Z(T), x ∉ S.
 2.2 (M ∩ ball(z, ρ) ⊆ S.) Let x ∈ M ∩ ball(z, ρ) and suppose x ∉ S; as x ∈ U, x ∈ Z(T), so T vanishes on some open W' ∋ x. Write ξ'(x) = ε ev_{τ'} and β := ε β_{τ'}, so ξ'(x)(β) = 1; by continuity of ξ' on M there is s > 0 with ξ'(x')(β) > 1/2 for all x' ∈ M ∩ ball(x, s). Take a chart (V_x, W_x, ψ_x) of M at x and O := ball(x, s) ∩ W' ∩ ball(z, ρ) ∩ W_x (open, x ∈ O). Let g ∈ C_c^∞(ℝ^P) with tsupport g ⊆ O, g ≥ 0, g(x) > 0, and ω := g β ∈ 𝒟^n(U). Then T(ω) = 0 because tsupport ω ⊆ W'. On the other hand V_x ∩ ψ_x⁻¹(O ∩ {g > 0}) is an open neighbourhood of ψ_x⁻¹(x) in ℝ^n (ψ_x is continuous on the open set V_x), so it contains a nonempty open ball B, and ψ_x(B) ⊆ M ∩ O ∩ {g > 0} has H^n(ψ_x(B)) > 0 by (F2). The integrand g ξ'(β) is ≥ 0 on M (g = 0 off ball(x, s)), > 0 on ψ_x(B), and integrable for H^n⌞M (bounded, vanishing off tsupport g, and H^n(M ∩ tsupport g) < ∞); M is Borel (F3), so the integral of a nonnegative integrable function that is positive on a set of positive measure is positive (Mathlib integral_pos_iff_support_of_nonneg_ae). Hence T(ω) = m ∫_M g ξ'(β) dH^n ≠ 0, a contradiction.
 2.3 (Construction of O_z.) Let (V, W, ψ) be a chart of M at z and v₀ := ψ⁻¹(z). Choose t > 0 with ball(v₀, t) ⊆ V and ψ(ball(v₀, t)) ⊆ ball(z, ρ). By (F1), ψ(ball(v₀, t)) is relatively open in W ∩ M, i.e. ψ(ball(v₀, t)) = O'' ∩ W ∩ M for some open O''. Put O_z := O'' ∩ W ∩ ball(z, ρ), an open set containing z. Then M ∩ O_z = ψ(ball(v₀, t)), the continuous image of a ball, hence connected: (b). By 2.1 and (F1), S ∩ O_z ⊆ closure(M) ∩ W ∩ O_z = M ∩ O_z, and M ∩ O_z ⊆ S by 2.2: (a).
 2.4 ((c).) Let x ∈ S ∩ O_z = M ∩ O_z and ρ' := ρ − |x − z| > 0. Then ball(x, ρ') ⊆ ball(z, ρ) ⊆ U, x ∈ M, and the same m, M, ξ' satisfy the local finiteness and representation requirements on ball(x, ρ') (compact subsets of ball(x, ρ') lie in ball(z, ρ), and forms supported in ball(x, ρ') are supported in ball(z, ρ)). Together with x ∈ S this gives x ∈ reg.

3. (Topology of M₁; (i), (iii), (iv).)
 3.1 If z ∈ M₁, then reg ∩ O_z = S ∩ O_z = M_z ∩ O_z (by 2(c), reg ⊆ S and 2(a)) is connected and contains z, so it is contained in the connected component of reg through z, which is M₁. Hence M₁ ∩ O_z = S ∩ O_z = M_z ∩ O_z.
 3.2 (i) With O := ⋃_{z ∈ M₁} O_z (open), M₁ = S ∩ O: '⊆' because z ∈ O_z and M₁ ⊆ S, '⊇' by 3.1. As S is Borel, M₁ is Borel.
 3.3 (iv) With O' := ⋃_{z ∈ reg} O_z, reg = S ∩ O' by 2(c); so sing T = S ∖ O' = U ∖ (Z(T) ∪ O'). For compact K ⊆ U, sing T ∩ K = K ∖ (Z(T) ∪ O') is a closed subset of K, hence compact.
 3.4 (iii) Let x ∈ closure(M₁) ∩ U. Then x ∈ closure(S) ∩ U ⊆ S. If x ∈ reg, the open set O_x meets M₁; reg ∩ O_x is connected (2(a), 2(b), 2(c)), contains x and meets M₁, so M₁ ∪ (reg ∩ O_x) is a connected subset of reg containing y; hence it is contained in M₁ and x ∈ M₁. Otherwise x ∈ S ∖ reg = sing T.

4. (Identification of R on a sheet.) Fix z ∈ M₁, write m, M, ξ', ρ for its data and G := O_z ⊆ ball(z, ρ). Claim: (B) H^n((M ∖ C) ∩ G) = 0; (C) for H^n-a.e. x ∈ C ∩ M ∩ G, θ(x) = |m| and ξ(x) = sign(m) ξ'(x). (The symmetric statement H^n((C ∖ M) ∩ G) = 0 also follows from F = 0 below, but is not needed.)
 Let ν := H^n⌞((C ∪ M) ∩ G) and F(x) := θ(x) 1_C(x) ξ(x) − m 1_M(x) ξ'(x) ∈ Λ_n = (Λ^n)*. M is Borel (F3), ξ' is continuous on M and ξ is a.e. strongly measurable on C, so for each α ∈ Λ^n the function x ↦ F(x)(α) is ν-a.e. strongly measurable; moreover |F(x)(α)| ≤ (θ(x) 1_C(x) + |m| 1_M(x)) ‖α‖ ν-a.e., which is ν-integrable on every compact K ⊆ G (∫_{C∩K} θ dH^n < ∞, and H^n(M ∩ K) < ∞ since K ⊆ ball(z, ρ)). For g ∈ C_c^∞(ℝ^P) with tsupport g ⊆ G and α ∈ Λ^n, ω := g α ∈ 𝒟^n(U) has tsupport ω ⊆ G ⊆ ball(z, ρ), hence ∫ g(x) F(x)(α) dν(x) = ∫_C θ ξ(ω) dH^n − m ∫_M ξ'(ω) dH^n = T(ω) − T(ω) = 0. By the fundamental lemma of the calculus of variations on the open set G (Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero), F(x)(α) = 0 for ν-a.e. x ∈ G; letting α run through a finite basis of Λ^n, F(x) = 0 for ν-a.e. x ∈ G.
 (B) For H^n-a.e. x ∈ (M ∖ C) ∩ G, m ξ'(x) = 0, impossible since m ≠ 0 and ξ'(x) ≠ 0 for every x ∈ M. Hence H^n((M ∖ C) ∩ G) = 0. (C) For H^n-a.e. x ∈ C ∩ M ∩ G, θ(x) ξ(x) = m ξ'(x), where ξ(x) = ε₁ ev_τ and ξ'(x) = ε₂ ev_{τ'} for orthonormal n-frames τ, τ' and ε₁, ε₂ ∈ {1, −1}. With B_{ij} := ⟨τ_i, τ'_j⟩, β_τ(τ') = det B and β_{τ'}(τ) = det Bᵀ = det B. Evaluating at β_τ and at β_{τ'} gives θ ε₁ = m ε₂ det B and θ ε₁ det B = m ε₂. Hence θ = |m| |det B| and |m| = θ |det B|, so θ = θ (det B)²; as θ ≥ 1, (det B)² = 1 and θ = |m|. Then ξ(x) = (m/θ) ξ'(x) = sign(m) ξ'(x).

5. ((v) and (ii).) (v): for z ∈ M₁ take G := O_z and c := 1/|m_z|. If tsupport ω ⊆ G then, by 3.1 (M₁ ∩ G = M_z ∩ G), (B), (C) and the local representation of T on ball(z, ρ_z) ⊇ G: T₁(ω) = ∫_{M₁∩G} ξ(ω) dH^n = ∫_{M_z∩G} ξ(ω) dH^n = sign(m_z) ∫_{M_z} ξ_z(ω) dH^n = (sign(m_z)/m_z) T(ω) = c·T(ω). Here the integrand of T₁(ω) vanishes off G (ω = 0 there) and, by (B) and (C), coincides H^n-a.e. on M₁ ∩ G = M_z ∩ G with sign(m_z) ξ_z(ω), which is continuous on M_z, bounded, and vanishes off tsupport ω (a compact subset of ball(z, ρ_z), meeting M_z in a set of finite H^n-measure); so all integrals are absolutely convergent and the equalities hold. (ii): M₁ ⊆ ⋃_{z ∈ M₁} O_z, and by the Lindelöf property of ℝ^P there are z_1, z_2, … ∈ M₁ with M₁ ⊆ ⋃_i O_{z_i}. Then M₁ ∖ C ⊆ ⋃_i ((M₁ ∩ O_{z_i}) ∖ C) = ⋃_i ((M_{z_i} ∩ O_{z_i}) ∖ C), and each of these sets is H^n-null by (B); hence H^n(M₁ ∖ C) = 0.

## Key steps

1. Charts of embedded C¹ submanifolds are homeomorphisms onto relatively closed pieces, and nonempty open pieces have positive H^n-measure.
2. Every z ∈ reg T has an open O_z with spt T ∩ O_z = M_z ∩ O_z connected and contained in reg T; hence M₁ is relatively open in spt T and Borel, its frontier in U lies in sing T, and sing T is relatively closed in U.
3. Uniqueness of the representation on O_z (fundamental lemma for H^n⌞((C ∪ M_z) ∩ O_z), normalised by determinant covectors) gives M_z ⊆ C a.e., θ = |m_z| and ξ = sign(m_z)ξ_z a.e. there.
4. Hence T₁ = |m_z|⁻¹·T on O_z, and H^n(M₁ ∖ C) = 0 by a countable subcover.

## Reference use

### local-project

Queries:
- `cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 summary of lean_name fields in dag.json; grep -rl regcomp_ in the run directory (no match)`
- `grep -n 'def GeometricCurrentOn.massOn|massAdmissibleOn|covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep -n 'GeometricCurrentOn.support|zeroRegion|restrictDomain' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono, countablyRectifiable_iUnion, aemeasurable_starProjection_of_approximateTangentField)`
- `grep -rn 'simon_theorem_3_6|simon_remark_3_7' simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `grep -n 'wedgeCovectors_apply_det' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean (exp_normalizedBallMass_monotoneOn and the sign-convention remark)`
- `read simongmt/Poincare/SimonGMT/Chapter07/Basic.lean (minimizing_summands, minimizing_summands_source)`
- `grep -rln 'Cauchy-Binet|CauchyBinet|cauchyBinet|cauchy_binet' Mathlib (no match)`
- `grep -rn 'IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|nullSingletonClass_hausdorff|hausdorffMeasure_zero_singleton|Set.Finite.measure_zero|exists_isSubordinate|hausdorffMeasure_image_le|integral_pos_iff_support_of_nonneg_ae|norm_integral_le_lintegral_norm|norm_alternatizeUncurryFin_le|withDensity_apply|setLIntegral_mono|ae_tendsto_measure_inter_div' Mathlib`
- `grep -n 'μHE\[|euclideanHausdorffMeasure' Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `lake build GMT.Ch07.Submission in scratch copy /tmp/regcomp-proj; lake env lean /tmp/regcomp-proj/Check.lean (nine child types + conditional parent assembly + #print axioms)`
- `lake env lean /tmp/regcomp-proj/Axioms.lean (#print axioms of reused SimonGMT lemmas)`
- `lake env lean /tmp/regcomp-proj/Inst.lean (#synth Norm (Covector (Euclid 3) 2); #synth Sub (GeometricCurrentOn univ 2))`
- `grep -n for book line ranges: chapter-07.txt (1.4, 4.1, 5.1–5.2, 5.11), chapter-06.txt (3.1, 3.2), chapter-04.txt (3.1–3.17), chapter-03.txt (1.5, 1.6), chapter-01.txt (3.6, 3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter07/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/regcomp-proj/Check.lean`
- `/tmp/regcomp-proj/Axioms.lean`
- `/tmp/regcomp-proj/Inst.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean, and the DAG reserves no regcomp_ names. The children cite these library facts, all using only propext, Classical.choice and Quot.sound: SimonGMT Chapter01.simon_theorem_3_6 and simon_remark_3_7_of_openSigmaFinite (Upper Density Theorem, for approx_tangent_locality); Chapter06.wedgeCovectors_apply_det (determinant covectors, used for the normalisations); Chapter03.HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono and countablyRectifiable_iUnion; and Chapter07.minimizing_summands_source (the 1.4 chain over abstract groups). That chain cannot be instantiated directly, because the contract gives GeometricCurrentOn no AddCommGroup instance, so minimizing_summand restates it. SimonGMT's monotonicity (Chapter04 RectifiableVarifold.HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn) is stated for its own varifold structure, which assumes a measurable tangent projection. monotonicity_mass_bound therefore proves the bound for IMRep directly, including measurability of the tangential divergence. From Mathlib the children use: IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (needs only LocallyIntegrableOn), SmoothPartitionOfUnity.exists_isSubordinate, nullSingletonClass_hausdorff, hausdorffMeasure_zero_singleton, μHE[0] = μH[0], LipschitzWith.hausdorffMeasure_image_le and norm_alternatizeUncurryFin_le. The search found no Cauchy–Binet theorem in Mathlib, so the multilinear arguments use slotwise Parseval and determinant covectors instead. All nine child types elaborate after import GMT.Ch07.Submission. The conditional assembly of RegularComponentsAreMinimizing from them, MinimizingImpliesStationary and CodimensionOneRegularity compiles, using the standard axioms plus sorryAx from the child stubs only.
