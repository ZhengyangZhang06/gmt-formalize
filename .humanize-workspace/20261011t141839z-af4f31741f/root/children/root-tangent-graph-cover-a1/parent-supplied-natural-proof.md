# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.tangent_graph_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this is the cone/Lipschitz-graph argument of Simon's printed proof of Ch. 3, Theorem 1.6 “⇐” (the definitions (1)–(3), estimate (9), claim (10) and the graph construction following it, printed pp. 72–74), which the printed proof of Ch. 8, Theorem 1.2 invokes through “1.9 of Ch. 3” (Ch. 3, 1.9 is derived from 1.6 via Remark 1.8). Here it is run directly for the weight measure of a varifold at its tangent points in the sense of Ch. 8, Def. 1.1, with two adaptations: (a) Egoroff's theorem (printed (8)) is replaced by a countable decomposition into classes with uniform constants, so that EVERY admissible tangent point (not only almost every one) is covered; (b) the aperture of the cones is adapted to an arbitrary prescribed slope L ∈ (0,1] relative to a fixed reference plane P (the printed proof uses a fixed aperture and slope ≤ 4 relative to finitely many reference planes). Notation: μ := μ_V = V.weight; G := Grassmannian N n; for S ∈ G, p_S := Grassmannian.project S (the orthogonal projection onto S.plane: symmetric and idempotent, so |v|² = |p_S v|² + |v − p_S v|²) and q_S := I − p_S; p := p_P, q := q_P; B_r(y) := closedBall y r; H^n := μHE[n]; ω_n := unitBallVolume n ∈ (0,∞) (ω_0 = 1); V_{x,t} := rescaledMeasure V x t; v(T) := planeVarifoldMeasure T. “Γ is an L-graph over P” means |q(y − z)| ≤ L|p(y − z)| for all y, z ∈ Γ — in Lean notation ‖(y − z) − Grassmannian.project P (y − z)‖ ≤ L * ‖Grassmannian.project P (y − z)‖; “‖p_T − p‖ ≤ L/4” means |p_T v − p v| ≤ (L/4)|v| for every v ∈ ℝ^N.

Statement. Let N, n ∈ ℕ, 0 < L ≤ 1, U ⊆ ℝ^N open, V an n-varifold on U and P ∈ G. Then there are closed sets Γ_0, Γ_1, … ⊆ ℝ^N, each an L-graph over P, such that every x ∈ ℝ^N for which there are T ∈ G and θ ∈ ℝ with HasTangentPlane V x T θ and ‖p_T − p‖ ≤ L/4 belongs to some Γ_i.

1. Consequences of Def. 1.1 at a point. Let HasTangentPlane V x T θ: x ∈ U, θ > 0, and ∫ f dV_{x,t} → θ∫ f dv(T) as t ↓ 0 for every f ∈ C_c(ℝ^N × G).
 (1.1) Weight blow-ups. For g ∈ C_c(ℝ^N) the function f(y,S) := g(y) lies in C_c(ℝ^N × G), because G is compact (tsupport f ⊆ tsupport g × G). By the definitions (V_{x,t} = ofReal(t^{−n}) • V.measure.map((z,S) ↦ (t^{−1}(z − x), S)), integral_map, and V.weight = V.measure.map Prod.fst), ∫ f dV_{x,t} = t^{−n}∫ g((z − x)/t) dμ(z) (for small t the integrand is supported in the compact set x + t·tsupport g ⊆ U, where μ is finite), and ∫ f dv(T) = ∫_{T.plane} g dH^n (v(T) = (H^n⌞T.plane).map(y ↦ (y,T))). Writing ν_t(A) := t^{−n}μ(x + tA), this says ∫ g dν_t → θ∫_{T.plane} g dH^n as t ↓ 0, for every g ∈ C_c(ℝ^N).
 (1.2) Normalisation. T.plane has dimension n (Grassmannian.finrank_plane), so there is a linear isometry ι of ℝ^n = EuclideanSpace ℝ (Fin n) onto T.plane (an orthonormal basis), and H^n(ι(A)) = L^n(A) for every A ⊆ ℝ^n (Mathlib Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume). Hence H^n(T.plane ∩ B_κ(0)) = L^n(B^n_κ(0)) = ω_nκ^n for κ > 0 (Measure.addHaar_closedBall; closed and open balls have the same volume).
 (1.3) Lower mass bound. For κ ∈ (0,1) take g ∈ C_c(ℝ^N) with 0 ≤ g ≤ 1, g = 1 on B_κ(0) and tsupport g ⊆ B_1(0). Then t^{−n}μ(B_t(x)) = ν_t(B_1(0)) ≥ ∫ g dν_t → θ∫_{T.plane} g dH^n ≥ θH^n(T.plane ∩ B_κ(0)) = θω_nκ^n. Letting κ ↑ 1: liminf_{t↓0} t^{−n}μ(B_t(x)) ≥ θω_n.
 (1.4) Cone decay (n ≥ 1). For α ∈ (0,1) let K_α(T) := {v ∈ ℝ^N : |p_T v| ≤ α|v|}, a closed cone (invariant under v ↦ sv, s > 0). Then t^{−n}μ((x + K_α(T)) ∩ B_t(x)) → 0 as t ↓ 0. Indeed C := K_α(T) ∩ B_1(0) is compact, C ∩ T.plane = {0} (for v ∈ T.plane, p_T v = v, and |v| ≤ α|v| forces v = 0), and (x + K_α(T)) ∩ B_t(x) = x + tC, so the quantity equals ν_t(C). For κ ∈ (0,1] let C_κ := {v : dist(v, C) ≤ κ} (compact) and choose g ∈ C_c(ℝ^N), 0 ≤ g ≤ 1, g = 1 on C, tsupport g ⊆ C_κ (Urysohn). Then limsup_t ν_t(C) ≤ lim_t ∫ g dν_t = θ∫_{T.plane} g dH^n ≤ θH^n(T.plane ∩ C_κ). As κ ↓ 0 the sets T.plane ∩ C_κ decrease to T.plane ∩ C = {0} (C is closed), and H^n(T.plane ∩ C_1) < ∞ by (1.2), so H^n(T.plane ∩ C_κ) → H^n({0}) = 0 (n ≥ 1). Hence ν_t(C) → 0.

2. Degenerate dimensions. If n > N there is no P ∈ G (a symmetric idempotent N × N matrix has trace ≤ N), and the claim is vacuous. If n = 0, G has exactly one element, the zero projection (a symmetric idempotent matrix of trace 0 is 0), so p = p_T = 0, q = I, and an L-graph over P is a set with at most one point. If HasTangentPlane V x T θ, then (1.3) with t^0 = 1 and ω_0 = 1 gives liminf_{t↓0} μ(B_t(x)) ≥ θ > 0; since x ∈ U, μ(B_t(x)) < ∞ for small t (V.finite_on_compact), so by continuity from above μ({x}) = lim_{t↓0} μ(B_t(x)) ≥ θ > 0: x is an atom of μ. The measure μ is σ-finite (Varifold.weight.instSigmaFinite), so it has at most countably many atoms a_0, a_1, …; put Γ_i := {a_i} (and Γ_i := ∅ for unused indices). Singletons and ∅ are closed L-graphs, and every point in question is an atom, hence some a_i. This proves the claim for n = 0. Assume 1 ≤ n ≤ N from now on. (For n = N the claim is also trivial — then P is the identity, q = 0 and Γ_0 := ℝ^N works — but the argument below covers it.)

3. Linear algebra. Put c := L/4, γ := c/2 = L/8 and α := (1 − c²/16)^{1/2} = (1 − L²/256)^{1/2} ∈ (0,1). Let T ∈ G with ‖p_T − p‖ ≤ L/4; then also |q_T v − q v| = |p v − p_T v| ≤ (L/4)|v|.
 (3.1) If v ∈ ℝ^N and |q v| > L|p v|, then v ≠ 0 and |q_T v| > c|v|. Indeed |q v|² > L²|p v|² = L²(|v|² − |q v|²) gives |q v| > L|v|/(1 + L²)^{1/2} ≥ L|v|/√2 (as L ≤ 1), so |q_T v| ≥ |q v| − (L/4)|v| > (1/√2 − 1/4)L|v| ≥ (L/4)|v|.
 (3.2) If moreover w ∈ ℝ^N with |w − v| ≤ γ|v|, then w ∈ K_α(T) and 0 < |w| ≤ 2|v|. Indeed |w| ≤ (1 + γ)|v| ≤ 2|v| and |w| ≥ (1 − γ)|v| > 0; |q_T w| ≥ |q_T v| − |q_T(w − v)| ≥ |q_T v| − |w − v| > (c − γ)|v| = (c/2)|v| ≥ (c/4)|w|; hence |p_T w|² = |w|² − |q_T w|² ≤ (1 − c²/16)|w|², i.e. |p_T w| ≤ α|w|.

4. Uniform classes (replacing Egoroff, printed (7)–(9)). For m ≥ 1 put ε_m := (2m)^{−1}(γ/2)^n/2 > 0. For m, k ≥ 1 let E_{m,k} be the set of x ∈ ℝ^N for which there are T ∈ G and θ ∈ ℝ with HasTangentPlane V x T θ, ‖p_T − p‖ ≤ L/4, θ ≥ 1/m, and, for every t ∈ (0, 1/k],
 (i) μ(B_t(x)) ≥ (2m)^{−1}ω_n t^n, and (ii) μ((x + K_α(T)) ∩ B_t(x)) ≤ ε_m ω_n t^n.
 Every x with HasTangentPlane V x T θ and ‖p_T − p‖ ≤ L/4 lies in some E_{m,k}: choose m with θ ≥ 1/m (θ > 0); by (1.3), liminf_t t^{−n}μ(B_t(x)) ≥ θω_n ≥ ω_n/m > (2m)^{−1}ω_n, and by (1.4), t^{−n}μ((x + K_α(T)) ∩ B_t(x)) → 0 < ε_mω_n; so (i) and (ii) hold for all t ∈ (0, 1/k] once k is large enough.

5. Graph property (printed (10)). CLAIM: if x, x' ∈ E_{m,k} and |x' − x| ≤ 1/(2k), then |q(x' − x)| ≤ L|p(x' − x)|. Suppose not, and put v := x' − x, s := |v|; then |q v| > L|p v|, so v ≠ 0 by (3.1) and 0 < s ≤ 1/(2k). Let T be a plane witnessing x ∈ E_{m,k}. For z ∈ B_{γs}(x') the vector w := z − x satisfies |w − v| = |z − x'| ≤ γs = γ|v|, so by (3.2) w ∈ K_α(T) and |w| ≤ 2s; that is, B_{γs}(x') ⊆ (x + K_α(T)) ∩ B_{2s}(x). Since 0 < γs ≤ 2s ≤ 1/k, (i) at x' (with t = γs) and (ii) at x (with t = 2s) give
 (2m)^{−1}ω_n(γs)^n ≤ μ(B_{γs}(x')) ≤ μ((x + K_α(T)) ∩ B_{2s}(x)) ≤ ε_mω_n(2s)^n = (2m)^{−1}ω_nγ^ns^n/2,
 which is impossible because ω_nγ^ns^n > 0. (This is the printed contradiction between (9) at the base point and the ball around the point y in (10), with the cone aperture adapted to L.)

6. Closed graph pieces (printed paragraph after (10)). Let D ⊆ ℝ^N be countable and dense (points with rational coordinates). For m, k ≥ 1 and d ∈ D put Γ_{m,k,d} := closure(E_{m,k} ∩ B_{1/(4k)}(d)). If y, z ∈ E_{m,k} ∩ B_{1/(4k)}(d), then |y − z| ≤ 1/(2k), so |q(y − z)| ≤ L|p(y − z)| by step 5; since (y,z) ↦ L|p(y − z)| − |q(y − z)| is continuous, the inequality persists on the closure. Hence each Γ_{m,k,d} is a closed L-graph over P. Every x ∈ E_{m,k} lies in B_{1/(4k)}(d) for some d ∈ D (density of D). Enumerate the countable family (Γ_{m,k,d})_{m,k ≥ 1, d ∈ D} as (Γ_i)_{i ∈ ℕ}. By step 4, every x with HasTangentPlane V x T θ and ‖p_T − p‖ ≤ L/4 lies in some E_{m,k}, hence in some Γ_i. Together with step 2 this proves the statement: ∃ Γ : ℕ → Set ℝ^N with every Γ i closed, every Γ i an L-graph over P (‖(y − z) − Grassmannian.project P (y − z)‖ ≤ L‖Grassmannian.project P (y − z)‖ for y, z ∈ Γ i), and every such tangent point in some Γ i.

## Key steps

1. Testing Def. 1.1 with f(y,S) = g(y): weight blow-ups t^{−n}μ_V(x + t·) → θH^n⌞T; lower mass bound liminf t^{−n}μ_V(B_t(x)) ≥ θω_n; cone decay t^{−n}μ_V((x + K_α(T)) ∩ B_t(x)) → 0 for n ≥ 1 (K_α(T) = {|p_T v| ≤ α|v|}, C ∩ T = {0}).
2. n > N is vacuous; for n = 0 every tangent point is an atom of the σ-finite μ_V, and singletons are L-graphs.
3. Linear algebra: if |q v| > L|p v| and ‖p_T − p‖ ≤ L/4 then |q_T v| > (L/4)|v|, and every w with |w − v| ≤ (L/8)|v| lies in K_α(T), α = (1 − L²/256)^{1/2}.
4. Classes E_{m,k} (θ ≥ 1/m, μ(B_t) ≥ (2m)^{−1}ω_nt^n and cone mass ≤ ε_mω_nt^n for t ≤ 1/k) cover every admissible tangent point (replacing Egoroff).
5. Printed (10): two points of E_{m,k} within 1/(2k) violating the L-graph inequality would put a ball of mass ≥ (2m)^{−1}ω_n(γs)^n inside a cone region of mass ≤ ε_mω_n(2s)^n — contradiction.
6. Closures of E_{m,k} ∩ B_{1/(4k)}(d), d in a countable dense set, are closed L-graphs over P covering all admissible tangent points; enumerate them by ℕ.

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
