# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1 (Simon 7.5, chapter-07.txt lines 746–780: the class 𝒪 and T = ∂[[E]] (5.1)); for n = 0 the parent's remark 'minimizing 0-currents vanish' is proved here in the form needed, reg T = ∅. Notation: H^d = μHE[d]; tsupport ω is the closed support of a form; Z(T) (zeroRegion) is the union of the open sets with compact closure in U on which T vanishes, and spt T = U ∖ Z(T); M_W is the mass of the contract (supremum of T(ω) over ω ∈ 𝒟^n(U) with tsupport ω ⊆ W and Euclidean coefficient norm ≤ 1 everywhere).

1. (k ≥ 1.) By InClassO, N ∩ U ≠ ∅; pick y ∈ N. The embedded-submanifold property of N (dimension n+1) at y gives V ⊆ ℝ^{n+1} open, W ∋ y open and ψ with ψ(V) = W ∩ N and Dψ(z) injective for every z ∈ V. As y ∈ W ∩ N = ψ(V), V ≠ ∅. For z ∈ V the injective linear map Dψ(z) : ℝ^{n+1} → ℝ^{n+k} forces n + 1 ≤ n + k (the dimension of the domain of an injective linear map is at most that of the codomain), so k ≥ 1.

2. (spt T ⊆ N.) Let x ∈ spt T, so x ∈ U, and suppose x ∉ N. Because (N̄∖N) ∩ U = ∅ and x ∈ U, x ∉ N̄. Since U is open and N̄ is closed, choose r > 0 with closedBall(x, r) ⊆ U ∖ N̄ and put W₀ := ball(x, r): W₀ is open and its closure is a compact subset of U. If ω ∈ 𝒟^n(U) has tsupport ω ⊆ W₀, then tsupport(dω) ⊆ tsupport ω ⊆ W₀ (exterior differentiation does not enlarge the topological support), and E ⊆ N is disjoint from W₀; so dω(z) = 0 for every z ∈ E and T(ω) = ∫_E ξ_N(z)(dω(z)) dH^{n+1}(z) = ∫_E ξ_N(z)(0) dH^{n+1}(z) = 0. Thus T vanishes on W₀, so x ∈ Z(T), contradicting x ∈ spt T = U ∖ Z(T). Hence spt T ⊆ N.

3. (∂T = 0.) If n = 0, BoundaryVanishes T is True by definition. If n = m + 1 and φ ∈ 𝒟^m(U), then ∂T(φ) = T(dφ) = ∫_E ξ_N(z)(d(dφ)(z)) dH^{n+1}(z) = 0, because d(dφ) = 0 for a smooth form φ (Simon (6.1.12); SimonGMT exteriorDerivative_sq) and ξ_N(z) is linear. Hence T.boundary = 0.

4. (n = 0 implies reg T = ∅.) Let n = 0 and suppose, for a contradiction, that y ∈ reg T. As T is minimizing it is integer multiplicity; fix an IMRep R of T with carrier C, multiplicity θ (θ ≥ 1 on C) and orientation ξ_R. Facts in dimension 0: H^0 = μHE[0] = μH[0] and H^0({x}) = 1, so H^0(F) = #F for finite F (additivity over measurable singletons), a set of finite H^0-measure is finite, and an H^0-null set is empty. Let ε₀ be the 0-covector with ε₀() = 1; every 0-covector α equals α()·ε₀; the Euclidean coefficient norm of a 0-covector α is |α()| (the only index map Fin 0 → Fin P is the empty one, which is strictly monotone); a unit orientation ξ' of a 0-dimensional space (empty orthonormal frame) satisfies ξ'(α) = ±α() for all α.
 4.1 (Local form of T.) By the definition of reg T there are ρ > 0 with ball(y, ρ) ⊆ U, m ∈ ℤ ∖ {0}, a 0-dimensional embedded C¹ submanifold M ∋ y with orientation ξ, and T(ω) = m ∫_M ξ(x)(ω(x)) dH^0(x) whenever tsupport ω ⊆ ball(y, ρ). Since ℝ^0 is a single point, a chart (V_M, W_M, ψ) of M at y has W_M ∩ M = ψ(V_M) ⊆ {ψ(0)}, hence W_M ∩ M = {y}. Choose r ∈ (0, ρ) with ball(y, r) ⊆ W_M; then M ∩ ball(y, r) = {y}. Writing ξ(y)(α) = s·α() with s ∈ {1, −1}, we get, for every ω with tsupport ω ⊆ ball(y, r) (the integrand vanishes on M ∖ {y}, which lies outside ball(y, r), so it is supported on the single point y, of H^0-measure 1, and is integrable):
 (*) T(ω) = m·ξ(y)(ω(y)) = m s ω(y)().
 4.2 (C is locally finite and oriented at every point.) For compact K ⊆ U, H^0(C ∩ K) ≤ ∫_{C∩K} θ dH^0 < ∞, so C ∩ K is finite. The set of points of C where the orientation condition of R fails is H^0-null, hence empty: for every x ∈ C, ξ_R(x)(α) = s_x α() for all α, with s_x ∈ {1, −1}.
 4.3 (C ∩ ball(y, r) ⊆ {y}.) Let x ∈ C ∩ ball(y, r) with x ≠ y. By 4.2 choose s' > 0 with closedBall(x, s') ⊆ ball(y, r) ∖ {y} and C ∩ closedBall(x, s') = {x}. Let g ∈ C_c^∞(ball(x, s')) with 0 ≤ g ≤ 1 and g(x) = 1, and ω := g ε₀ ∈ 𝒟^0(U). By (*), T(ω) = m s g(y) = 0. By the representation, T(ω) = ∫_C θ ξ_R(g ε₀) dH^0 = θ(x) s_x g(x) H^0({x}) = ±θ(x) ≠ 0 (the integrand vanishes on C off the single point x, since g = 0 off ball(x, s') and C ∩ closedBall(x, s') = {x}; so it is integrable). Contradiction.
 4.4 (y ∈ C.) Otherwise C ∩ ball(y, r) = ∅ by 4.3, so T(ω) = 0 whenever tsupport ω ⊆ ball(y, r); but for g ∈ C_c^∞(ball(y, r)) with g(y) = 1, (*) gives T(g ε₀) = m s ≠ 0.
 4.5 (The competitor S.) Let W := ball(y, r/2): it is open and its closure lies in closedBall(y, r/2), a compact subset of ball(y, r) ⊆ U. Define D ∈ 𝒟_0(U) by D(ω) := θ(y) ξ_R(y)(ω(y)); D is linear and sequentially continuous (if ω_j → 0 in 𝒟^0(U) then ω_j(y) → 0). Let S := T − D. Using y ∈ C and H^0({y}) = 1, S(ω) = ∫_C θ ξ_R(ω) dH^0 − θ(y) ξ_R(y)(ω(y)) = ∫_{C∖{y}} θ ξ_R(ω) dH^0 (the integrand is supported on the finite set C ∩ tsupport ω, by 4.2, hence integrable, and the integral over C splits as the integral over C ∖ {y} plus the atom at y). The triple R_S := (C ∖ {y}, θ, ξ_R) is an IMRep in U: C ∖ {y} is Borel and ⊆ U; it is countably 0-rectifiable as a subset of C (CountablyRectifiable.mono); θ is measurable, positive and locally integrable on it; ξ_R is a.e. strongly measurable for the restricted measure; and for every x ∈ C ∖ {y} the sets C and C ∖ {y} have the same approximate tangent spaces at x: if f ∈ C_c(ℝ^P) has spt f ⊆ B_R(0) and 0 < λ < |x − y|/R, then η_{x,λ}(C) and η_{x,λ}(C ∖ {y}) differ only by the point (y − x)/λ, whose norm exceeds R, so f vanishes there and the integrands f·1_{η_{x,λ}(C)} and f·1_{η_{x,λ}(C∖{y})} coincide pointwise; hence the integrals in Definition 1.4 of Ch. 3 coincide for all small λ and have the same limits. Hence the orientation condition of R at x transfers to R_S, and S is integer multiplicity.
 4.6 (Minimality applies.) S − T = −D as currents. If x ∈ U ∖ {y}, a ball around x whose closure is a compact subset of U ∖ {y} is a region on which D, hence S − T, vanishes; so spt(S − T) ⊆ {y}, a compact set contained in (N ∩ U) ∩ W, because y ∈ spt T ⊆ N (step 2), y ∈ U and y ∈ W. For n = 0, SameBoundary S T holds by definition. By minimality of T in N ∩ U: M_W(T) ≤ M_W(S).
 4.7 (M_W(S) = 0.) Let tsupport ω ⊆ W ⊆ ball(y, r). For z ∈ C ∖ {y} we have z ∉ ball(y, r) by 4.3, so ω(z) = 0 and S(ω) = 0. Every admissible value is ofReal 0, so M_W(S) = 0.
 4.8 (M_W(T) ≥ 1.) Take g ∈ C_c^∞(W) with 0 ≤ g ≤ 1 and g(y) = 1, and ω := σ g ε₀ with σ := sign(m s) ∈ {1, −1}. The Euclidean coefficient norm of ω(z) is g(z) ≤ 1 and tsupport ω ⊆ W, so ω is admissible for M_W(T), and by (*) T(ω) = m s σ = |m| ≥ 1. Hence M_W(T) ≥ 1 > 0 = M_W(S), contradicting 4.6. Therefore reg T = ∅ when n = 0.

## Key steps

1. An injective chart differential ℝ^{n+1} → ℝ^{n+k} gives k ≥ 1.
2. T vanishes near points off N̄ because dω vanishes on E there; with (N̄∖N) ∩ U = ∅ this gives spt T ⊆ N.
3. ∂T(φ) = ∫_E ⟨ddφ, ξ_N⟩ dH^{n+1} = 0.
4. For n = 0 a regular point y is an isolated atom of T: removing y from the carrier gives an integer multiplicity competitor S with spt(S − T) = {y} ⊆ N ∩ U ∩ W and M_W(S) = 0 < 1 ≤ M_W(T), contradicting minimality.

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
