# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.constancy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, Theorem 4.1 and its printed proof (pp. 213–214), with the documented erratum. ERRATUM (README; SimonGMT ConstancyDomainCounterexample.counterexample_constancy_printed_hypotheses): the printed hypothesis “M connected” is insufficient (U = ℝ ∖ {0}, M = ℝ, V = v((0,∞)) is stationary in U with spt ⊆ M but is not a constant multiple of v(M ∩ U)); the corrected hypothesis is that M ∩ U is (pre)connected, which is exactly what the last line of the printed proof uses. The conclusion V = θ0 v(M) is read in U, i.e. V = θ0 v(M ∩ U) with T_x M the classical tangent plane, and θ0 = 0 is allowed. Notation: μ = μ_V, H^n = μHE[n], G = Grassmannian N n, classicalTangentSpace M x = {γ'(0) : γ C¹ on (−1,1), γ((−1,1)) ⊆ M, γ(0) = x}.

Hypotheses: V is stationary in U (δV(X) = 0 for all X ∈ K(U;ℝ^N)); M is an n-dimensional C² submanifold of ℝ^N in Simon's sense (Ch. 2 §4: Chapter02.IsSimonSubmanifold (E := Euclidean n) 2 M — every point of M lies in an open W with a C², injective, relatively proper parametrization φ : D → W ∩ M, D ⊆ ℝ^n open, Dφ injective); U ∩ spt μ ⊆ M; M ∩ U is preconnected. Claim: ∃ θ0 ≥ 0 with V(A) = θ0 · H^n({x ∈ M ∩ U : (x, T_xM) ∈ A}) for all Borel A ⊆ ℝ^N × G, where T_xM ∈ G is the plane with plane = classicalTangentSpace M x.

0. Trivial case. If M ∩ U = ∅ then U ∩ spt μ = ∅, so μ(U) ≤ μ(U ∩ spt μ) + μ(ℝ^N ∖ spt μ) = 0 and μ(Uᶜ) = 0 (V.supported), hence V = 0 and θ0 = 0 works (both sides are 0). Assume M ∩ U ≠ ∅ below (this also covers n > N vacuously: then no injective Dφ exists, so M = ∅).

1. Classical tangent spaces. For x ∈ M and a local parametrization φ : D → W ∩ M with x = φ(a): classicalTangentSpace M x = range Dφ(a), an n-dimensional subspace, which we denote T_xM. (⊇) For v = Dφ(a)w take γ(t) = φ(a + g(t)w) with g smooth, bounded by r/|w| where B_r(a) ⊆ D, g(0) = 0, g'(0) = 1: γ is C¹ on (−1,1), lands in M, γ(0) = x, γ'(0) = v. (⊆) If γ is C¹ into M with γ(0) = x, then near t = 0, γ(t) ∈ W ∩ M = φ(D), and by the relative properness and the inverse function theorem (φ is a C² immersion and a homeomorphism onto W ∩ M) γ = φ ∘ β with β C¹ near 0, β(0) = a, so γ'(0) = Dφ(a)β'(0) ∈ range Dφ(a). Since a Grassmannian point is determined by its plane, T_xM ∈ G is well defined, and x ↦ T_xM is continuous on M (C¹ dependence of range Dφ).

2. Printed step (1)–(2): p_S(∇f) = 0 on spt V. Take any f ∈ C²_c(U) with f = 0 on M ∩ U (the printed “M ⊂ {x ∈ U : f(x) = 0}”, read in U). For such f, X := f∇f ∈ K(U;ℝ^N) and by 2.3, div_S(f∇f) = ∇^S f·∇f + f div_S∇f = |p_S(∇f)|² + f div_S ∇f; on spt μ ∩ U ⊆ M we have f = 0, so δV(f∇f) = ∫|p_S(∇f(x))|² dV(x,S) (V is carried by Gₙ(U ∩ spt μ)). Stationarity gives ∫|p_S(∇f(x))|² dV = 0, hence (by continuity of (x,S) ↦ |p_S(∇f(x))|²) p_S(∇f(x)) = 0 for all (x,S) ∈ spt V.

3. Printed step (3): S = T_xM on spt V. Let ξ ∈ M ∩ U. There are an open W ∋ ξ and C²_c(U) functions f_1,…,f_k (k = N − n) vanishing on M ∩ W such that ∇f_1(x),…,∇f_k(x) span (T_xM)^⊥ for every x ∈ M ∩ W (locally M ∩ W is the zero set of a C² submersion — straighten M by a C² chart around ξ and multiply the normal coordinates by a cutoff; one checks such W, f_j exist; SimonGMT ConstancyNormalCharts.exists_local_normal_defining_map, Chapter08/ConstancyNormalCharts.lean:90). Step 2 applied to each f_j gives p_S((T_xM)^⊥) = 0 for all (x,S) ∈ Gₙ(W) ∩ spt V, i.e. (T_xM)^⊥ ⊆ S^⊥; as dim S = dim T_xM = n, S = T_xM. Since ξ is arbitrary, V is carried by the graph {(x, T_xM) : x ∈ M ∩ U}:
 (4) ∫ f(x,S) dV(x,S) = ∫_{M∩U} f(x, T_xM) dμ(x) for f ∈ C_c(Gₙ(U)); equivalently V = μ.map(x ↦ (x, T_xM)) on Borel sets (μ is carried by M ∩ U).

4. Printed step (5): μ = θ H^n ⌞ (M ∩ U) with θ = Θ^n(μ,·). Since V is stationary in every open ball B°_ρ(x) ⊆ U, the monotonicity identity 3.4 (sibling monotonicity_density, second conjunct StationaryMonotonicityIdentity; the printed proof cites 3.3) shows θ(x) := Θ^n(μ, x) exists and is finite at every x ∈ U. Work on one chart sheet M ∩ W (W as in the definition of a Simon submanifold, W ∩ U ∩ M ≠ ∅); by Lindelöf countably many sheets cover M ∩ U. On a sheet, λ := H^n ⌞ (M ∩ W) is locally finite in W ∩ U (area formula for the C² chart) and Θ^n(λ, x) = 1 for every x ∈ M ∩ W (the chart is asymptotically linear at each point). (i) μ⌞(W∩U) ≪ λ: if Z ⊆ M ∩ W ∩ U and H^n(Z) = 0, write Z = ∪_k Z_k, Z_k := {x ∈ Z : θ(x) ≤ k}; for δ, η > 0 let Z_{k,δ} := {x ∈ Z_k : μ(B_ρ(x)) ≤ (k+η)ω_nρ^n for 0 < ρ ≤ δ} (Z_k = ∪_{δ} Z_{k,δ}); any cover of Z_{k,δ} by sets C_i of diameter d_i < δ meeting Z_{k,δ} at x_i satisfies Z_{k,δ} ⊆ ∪B_{d_i}(x_i), so μ(Z_{k,δ}) ≤ (k+η)Σω_n d_i^n = 2^n(k+η)Σω_n(d_i/2)^n, whence μ(Z_{k,δ}) ≤ 2^n(k+η)H^n_δ(Z_k) = 0; so μ(Z) = 0. Also μ is carried by M ∩ U (U ∩ spt μ ⊆ M). (ii) By the differentiation theorem (Ch. 1, 3.23–3.24; Radon measures on open subsets of ℝ^N have the symmetric Vitali property), μ⌞(W∩U) = (D_λ μ) λ with D_λμ(x) = lim μ(B_ρ(x))/λ(B_ρ(x)) = θ(x)/Θ^n(λ,x) = θ(x) for x ∈ M ∩ W ∩ U. Patching the sheets,
 (5) ∫ f(x,S) dV(x,S) = ∫_{M∩U} f(x, T_xM) θ(x) dH^n(x), f ∈ C_c(Gₙ(U)),
 i.e. V = v(M ∩ U, θ), θ locally H^n-integrable on M ∩ U.

5. θ is constant on M ∩ U (printed last paragraph). Fix a Simon chart φ : D → W ∩ M (D ⊆ ℝ^n open, φ C², Jφ := (det Dφᵀ Dφ)^{1/2} > 0 and C¹) with φ(D) ⊆ U, and put θ̃ := θ ∘ φ, which is locally L^n-integrable on D (area formula: ∫_{φ(K)} θ dH^n = ∫_K θ̃ Jφ dL^n < ∞ for compact K ⊆ D). For Y ∈ C¹_c(D;ℝ^n), the tangential field Z := (Dφ·Y) ∘ φ⁻¹ on M ∩ W extends to some X ∈ K(U;ℝ^N) with X = Z on M ∩ U (extend in the normal directions using a C² normal chart and a cutoff; M is C²), and div_M X ∘ φ = Jφ⁻¹ Σ_i ∂_i(Jφ Y_i) (divergence in local coordinates). By (5) and 2.3, 0 = δV(X) = ∫_{M∩U} div_M X θ dH^n = ∫_D Σ_i ∂_i(Jφ Y_i) θ̃ dL^n. Given ζ ∈ C¹_c(D) and i, choose Y_i := ζ/Jφ and Y_l := 0 (l ≠ i): ∫_D (∂ζ/∂x_i) θ̃ dL^n = 0 (printed display). Thus θ̃ has vanishing distributional gradient, so (mollification) θ̃ is a.e. equal to a constant on every ball contained in D. Consequently every point of M ∩ U has a neighbourhood in M ∩ U on which θ is H^n-a.e. constant; for c ∈ [0,∞) the set of points of M ∩ U near which θ = c H^n-a.e. is relatively open, these sets for different c are disjoint, and they cover M ∩ U. Because M ∩ U is connected (CORRECTED hypothesis), exactly one of them is nonempty: θ = θ0 H^n-a.e. on M ∩ U for a constant θ0 ∈ [0,∞).

6. Conclusion. From (5) with θ ≡ θ0: for every Borel A ⊆ ℝ^N × G, V(A) = θ0 H^n({x ∈ M ∩ U : (x, T_xM) ∈ A}) (if θ0 = 0 both sides vanish); by step 1, {x ∈ M ∩ U : (x,T_xM) ∈ A} = {x ∈ M ∩ U : ∃ S, S.plane = classicalTangentSpace M x ∧ (x,S) ∈ A} (S is unique since a Grassmannian point is determined by its plane, Grassmannian.eq_of_plane_eq). This is ConstancyTheorem with θ0 ≥ 0.

7. Formal route (pinned SimonGMT, kernel-checked, already proves steps 2–5 in substance). Varifold.Stationary.exists_const_tangentGraph_connectedCarrier (Chapter08/ConstancyCorrected.lean:103) — hypotheses: V.Stationary, IsSimonSubmanifold 2 M, U ∩ spt μ ⊆ M, M.Nonempty, IsPreconnected (M ∩ U) — gives c ∈ [0,∞), a measurable T : ℝ^N → G with V.measure = (c • H̃^n ⌞ (M ∩ U)).map (x ↦ (x, T x)) where H̃^n = Chapter01.simonHausdorffMeasureReal n, and (T(φ a)).plane = range (fderiv φ a) for every Simon chart φ at points φ a ∈ U when c ≠ 0. Translate: H̃^n = μHE[n] by simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (Chapter02/AreaLiteral.lean:42); range(fderiv φ a) = classicalTangentSpace M (φ a) by step 1; take θ0 := c.toReal; the case M = ∅ is step 0 (SimonGMT needs M.Nonempty); if c = 0 both sides are 0. Then Measure.map_apply on measurable A and restrict_apply give the contract's formula.

## Key steps

1. If M ∩ U = ∅ then V = 0 and θ0 = 0.
2. classicalTangentSpace M x = range Dφ(a) for a Simon chart φ with φ(a) = x (curves φ(a + g(t)w); conversely lift curves through the chart).
3. Printed (1)–(3): for f ∈ C²_c(U) vanishing on M ∩ U, δV(f∇f) = ∫|p_S∇f|² dV = 0; local defining functions give S = T_xM on spt V.
4. Printed (4)–(5): V = μ_V.map(x ↦ (x,T_xM)), and μ_V = θ H^n⌞(M∩U) with θ = Θ^n(μ_V,·) (exists everywhere by 3.4; differentiation w.r.t. H^n on chart sheets).
5. θ has zero distributional gradient in charts (δV(X) = ∫ div_M X θ dH^n = 0 for tangential X), hence is locally constant, hence constant by connectedness of M ∩ U.
6. Formal: SimonGMT Stationary.exists_const_tangentGraph_connectedCarrier + simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure + the chart/classical tangent identification.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean workspace GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -l -i 'varifold' mathlib/Mathlib (0 files)`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem ae_tendsto_rnDeriv' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem hausdorffMeasure_image_le' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n 'theorem withDensity_rnDeriv_eq' mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `rg -n 'ext_of_integral_eq_on_compactlySupported' mathlib/Mathlib`
- `rg -n 'theorem measure_toMeasurable_inter_of_sFinite|theorem restrict_toMeasurable_of_sFinite' mathlib/Mathlib`
- `rg -n 'theorem addHaar_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `grep -n '^theorem|^def' simongmt Chapter03/{Rectifiable,SubmanifoldCover,DisjointCover,Differential}.lean`
- `grep -n '^theorem' simongmt Chapter02/{Area,AreaLipschitz,AreaNoninjective,AreaMultiplicity,AreaLiteral}.lean`
- `grep -n '^theorem' simongmt Chapter01/{DensityComparison,Densities,HausdorffDensityBounds,InfiniteDensitySet}.lean`
- `grep -rn 'theorem <name>' simongmt for hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity, aemeasurable_imageMap, measurable_imageMap_domain, pushforwardMeasure_apply_of_contDiffOn, imageMap_preimage_cylinder_ae_of_fixed, eq_of_plane_eq, hasDerivAt_normalized_weightedCutoffMass, simonHausdorffMeasureReal_toOuterMeasure, volume_euclidean_ball_eq, mul_simonHausdorff_le_of_le_dimensionalUpperDensity, measurable_dimensionalUpperDensity`
- `lake env lean Scratch/Final.lean (import GMT.Ch08.Submission + comparator scope replay; 12 child statements + parent assembly + example : type_of% GMT.Ch08.main_theorem)`
- `lake env lean Scratch/Axioms.lean (#print axioms for 13 cited SimonGMT lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/InfiniteDensitySet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`

Snapshot = project 63436ae6 + Mathlib 25730c7c; its project/GMT/Ch08/Contract.lean is byte-identical to the workspace Contract and Submission. Mathlib has no varifold theory (0 files), so every Ch. 8 result is proved in the DAG. Pinned SimonGMT Chapter03 has no Theorem 1.6/1.9 (no rectifiable ⇒ approximate tangents / density one) and no area formula on rectifiable carriers (Chapter02 area formulas have a Euclidean parameter domain) — the reason v1 was rejected — so the new decomposition avoids both: density one and the 5.9 mass/fibre comparison are proved with Lipschitz graphs of small slope from the new sibling tangent_graph_cover, using only Mathlib LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733/745), Isometry.euclideanHausdorffMeasure_image + EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:131,187), Besicovitch.ae_tendsto_measure_inter_div / ae_tendsto_rnDeriv (Covering/Besicovitch.lean:1105,1078), withDensity_rnDeriv_eq (RadonNikodym.lean:60), LipschitzOnWith.extend_real (Lipschitz.lean:308), measure_toMeasurable_inter_of_sFinite (SFinite.lean:477), and SimonGMT simon_theorem_3_3 / simon_theorem_3_6 / measurable_dimensional{Upper,Lower}Density (Chapter01). The first-variation derivative is the kernel-checked Varifold.hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity (DeformationIntegral.lean:266), whose hypotheses match the contract. #print axioms for the 13 newly cited SimonGMT lemmas shows only propext, Classical.choice, Quot.sound. In a scratch copy importing GMT.Ch08.Submission with the comparator's replayed scope, all 12 child lean_statements elaborate and pass validate_lean_statement, and the parent assembly term checks against type_of% GMT.Ch08.main_theorem with no sorry of its own. The active DAG contains only root, so no name reservations conflict; all lean_names are fresh bare identifiers.
