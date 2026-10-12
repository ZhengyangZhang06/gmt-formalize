# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.monotonicity_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 8, 3.1–3.4 (printed pp. 210–211), “by essentially the same computation as in §4 of Ch. 4”, i.e. Ch. 4, 3.1–3.10 and 4.7, with the radial test field X_y = γ(r)(y − x), γ(r) = φ(r/ρ). Errata/normalisations: (i) the printed 3.3 is a subtraction; the contract states it additively in [0,∞], which is equivalent because every term is finite (B_ρ(x) is compact in U); (ii) 3.4 needs no locally-bounded-first-variation hypothesis, only stationarity in B_{ρ0}(x); (iii) the sign of δV(X) in the radial identity is “−δV(X)” (SimonGMT WeightedRadialIdentity.lean, header), which is irrelevant below because only |δV(X)| is used or δV(X) = 0. Notation: μ = μ_V = V.weight, ‖δV‖ = variationMeasure V, B_ρ(x) = closedBall x ρ (closed), B°_ρ(x) = ball x ρ (open), r = |y − x|, ω_n = unitBallVolume n ∈ (0,∞) (ω_0 = 1), densityRatio n μ x ρ = μ(B_ρ(x))/(ω_n ρ^n) (note ofReal ρ ^ n = ofReal (ρ^n) for ρ ≥ 0), and for (y,S) ∈ ℝ^N × G: p_{S⊥}(v) = v − p_S(v); the contract's normalDefect V x A = ∫_{Gₙ(A)} |p_{S⊥}(y − x)|²/|y − x|^{n+2} dV with the Lean convention 0/0 = 0 at y = x.

COMMON COMPUTATION (3.2). Let x ∈ U, R > 0 with B_R(x) ⊆ U, ε ∈ (0,1) and φ ∈ C¹(ℝ) with φ' ≤ 0, φ = 1 on (−∞,1], φ = 0 on [1+ε, ∞). For 0 < ρ with (1+ε)ρ < R put X_ρ(y) = φ(|y−x|/ρ)(y − x); X_ρ is C¹ (φ is constant near 0), with support in B_{(1+ε)ρ}(x) ⊆ B°_R(x), so X_ρ ∈ K(U;ℝ^N). Put I(ρ) = ∫φ(r/ρ) dμ and J(ρ) = ∫ φ(r/ρ) |p_{S⊥}((y−x)/r)|² dV(y,S) (integrand 0 at y = x).
C1. For S ∈ G and y ≠ x: div_S X_ρ = nφ(r/ρ) + r ∂_r[φ(r/ρ)] (1 − |p_{S⊥}((y−x)/r)|²), because trace p_S = n and ∇^S r = p_S((y−x)/r) (this is 3.2: Σ e_S^{ij}(x^i−y^i)(x^j−y^j)/r² = 1 − |p_{S⊥}((y−x)/r)|²); at y = x, div_S X_ρ = n = nφ(0).
C2. r ∂_r[φ(r/ρ)] = (r/ρ)φ'(r/ρ) = −ρ ∂_ρ[φ(r/ρ)]. I and J are C¹ in ρ (differentiation under the integral, dominated by sup|φ'|·(1+ε)/ρ times the finite mass of B_R(x)), and integrating C1 against V gives δV(X_ρ) = nI(ρ) − ρI'(ρ) + ρJ'(ρ), i.e.
   d/dρ (ρ^{-n} I(ρ)) = ρ^{-n} J'(ρ) − ρ^{-n-1} δV(X_ρ).        (★)
   (Formal: SimonGMT Varifold.hasDerivAt_normalized_weightedCutoffMass, WeightedRadialIdentity.lean:200, with h ≡ 1, which uses the squared-radius profile t ↦ φ(t/ρ²) — any such C¹ profile works identically; the gradient term vanishes for h ≡ 1.)
C3. J'(ρ) ≥ 0 since ∂_t[φ(r/t)] = −(r/t²)φ'(r/t) ≥ 0. Moreover ∂_t[φ(r/t)] vanishes unless 1 ≤ r/t ≤ 1+ε, i.e. r/(1+ε) ≤ t ≤ r, where r^{-n} ≤ t^{-n} ≤ (1+ε)^n r^{-n}; hence (Fubini, g := |p_{S⊥}((y−x)/r)|² ∈ [0,1]) for 0 < σ ≤ ρ: ∫ r^{-n}(φ(r/ρ) − φ(r/σ)) g dV ≤ ∫_σ^ρ t^{-n} J'(t) dt ≤ (1+ε)^n ∫ r^{-n}(φ(r/ρ) − φ(r/σ)) g dV (this is Ch. 4, 3.5, with the inequalities written in the direction forced by t ≤ r on the support). Take a family φ = φ_ε decreasing as ε ↓ 0 to the indicator of (−∞,1]. Then φ(r/ρ) → 1_{r≤ρ}, φ(r/ρ) − φ(r/σ) → 1_{σ<r≤ρ} pointwise, I(ρ) → μ(B_ρ(x)), and (dominated convergence: for ε ≤ ε0 with (1+ε0)ρ < R the integrands are bounded by σ^{-n}·1_{B_{(1+ε0)ρ}(x)}, which has finite V-mass because B_{(1+ε0)ρ}(x) ⊆ B_R(x) ⊆ U) both bounds converge to ∫_{Gₙ(B_ρ(x)∖B_σ(x))} r^{-n}|p_{S⊥}((y−x)/r)|² dV = normalDefect V x (B_ρ(x) ∖ B_σ(x)) (note r^{-n}|p_{S⊥}((y−x)/r)|² = |p_{S⊥}(y−x)|²/r^{n+2}).

PART A: MonotonicityFormula (3.3). Hypotheses: V has locally bounded first variation, 0 < ρ0, B°_{ρ0}(x) ⊆ U, Λ ≥ 0, and (3.1) ‖δV‖(B_ρ(x)) ≤ Λ μ(B_ρ(x)) for 0 < ρ < ρ0.
A1. Open balls. For 0 < s ≤ ρ0: B°_s(x) = ∪_{s'<s} B_{s'}(x), so by continuity from below ‖δV‖(B°_s(x)) ≤ Λ μ(B°_s(x)).
A2. Bound on δV(X_ρ) (uses 2.6 from the sibling first_variation: δV(X) = −∫ν·X d‖δV‖ with |ν| = 1 ‖δV‖-a.e., ‖δV‖ = variationMeasure V). Hence |δV(X_ρ)| ≤ ∫|X_ρ| d‖δV‖ ≤ (1+ε)ρ ∫φ(r/ρ) d‖δV‖. By the layer-cake formula and since {y : φ(|y−x|/ρ) > s} = B°_{ρ a_s}(x) with a_s ∈ (1, 1+ε] for s ∈ (0,1) (φ is continuous, non-increasing, = 1 on [0,1]), A1 gives, when (1+ε)ρ ≤ ρ0: ∫φ(r/ρ) d‖δV‖ = ∫_0^1 ‖δV‖(B°_{ρa_s}(x)) ds ≤ Λ ∫_0^1 μ(B°_{ρa_s}(x)) ds = Λ I(ρ). So |δV(X_ρ)| ≤ Λ_ε ρ I(ρ), Λ_ε := (1+ε)Λ.
A3. Integrating factor. From (★) and A2: d/dρ(ρ^{-n}I) ≥ ρ^{-n}J' − Λ_ε ρ^{-n} I, hence d/dρ(e^{Λ_ε ρ} ρ^{-n} I(ρ)) = e^{Λ_ερ}(d/dρ(ρ^{-n}I) + Λ_ε ρ^{-n}I) ≥ e^{Λ_ερ}ρ^{-n}J'(ρ) ≥ ρ^{-n}J'(ρ) ≥ 0, for 0 < ρ < ρ0/(1+ε).
A4. Integrate over [σ, ρ] (0 < σ ≤ ρ < ρ0/(1+ε)): e^{Λ_ερ}ρ^{-n}I(ρ) − e^{Λ_εσ}σ^{-n}I(σ) ≥ ∫_σ^ρ e^{Λ_εt}t^{-n}J'(t) dt ≥ ∫_σ^ρ t^{-n}J'(t) dt ≥ ∫ r^{-n}(φ(r/ρ) − φ(r/σ))|p_{S⊥}((y−x)/r)|² dV (A3, e^{Λ_εt} ≥ 1, J' ≥ 0, C3). Given 0 < σ ≤ ρ < ρ0, every small ε satisfies (1+ε)ρ < ρ0; letting ε ↓ 0 (C3) yields, with all terms finite (B_ρ(x) ⊆ B°_{ρ0}(x) ⊆ U compact):
   e^{Λσ}σ^{-n}μ(B_σ(x)) + normalDefect V x (B_ρ(x) ∖ B_σ(x)) ≤ e^{Λρ}ρ^{-n}μ(B_ρ(x)).        (3.3)
A5. Conclusions. Dividing (3.3) by ω_n gives the second inequality of the contract. Since the defect is ≥ 0, ρ ↦ e^{Λρ}μ(B_ρ(x))/ρ^n is monotone on (0,ρ0) (the contract's MonotoneOn, in ℝ≥0∞). A monotone function has a limit at 0+, so θ := lim_{σ↓0} e^{Λσ}densityRatio n μ x σ exists, and since e^{Λσ} → 1, HasDensity n μ x θ holds (Tendsto densityRatio (𝓝[>]0) (𝓝 θ)); θ ≤ e^{Λσ}densityRatio(σ) for every σ ∈ (0,ρ0) (monotone limit from above), and θ ≠ ∞ because densityRatio(σ) < ∞ (μ(B_σ(x)) < ∞, ω_n σ^n > 0). This is MonotonicityFormula. (For n = 0 all statements hold as well: ω_0 = 1, ρ^0 = 1, and the defect integrand equals 1 off y = x.)

PART B: StationaryMonotonicityIdentity (3.4). Hypotheses: 0 < ρ0, B°_{ρ0}(x) ⊆ U, δV(X) = 0 for every X ∈ K(U;ℝ^N) with tsupport X ⊆ B°_{ρ0}(x). No first-variation bound is used.
B1. For (1+ε)ρ < ρ0, X_ρ is such a field, so δV(X_ρ) = 0 and (★) reads d/dρ(ρ^{-n}I) = ρ^{-n}J'. Integrating and letting ε ↓ 0 with the two-sided bounds C3 gives, for 0 < σ ≤ ρ < ρ0, the identity
   σ^{-n}μ(B_σ(x)) + normalDefect V x (B_ρ(x) ∖ B_σ(x)) = ρ^{-n}μ(B_ρ(x)).
   (Formal: SimonGMT StationaryOn.stationaryMonotonicity, StationaryMonotonicity.lean:131, applied with any R ∈ (ρ, ρ0): closedBall x R ⊆ ball x ρ0 ⊆ U and V is StationaryOn (ball x R); its normalizedBallMass is μ(B_ρ)/ofReal(ρ^n) and its annularMonotonicityDefect equals normalDefect on the annulus because |p_{S⊥}(y−x)|²/r^{n+2} = radialNormalSq/r^n off y = x, via Grassmannian.normalProject_eq_sub and norm_normalProject_radial_sq, RadialFirstVariation.lean:81,123.)
B2. In particular σ ↦ σ^{-n}μ(B_σ(x)) is non-decreasing on (0,ρ0), so L := lim_{σ↓0} σ^{-n}μ(B_σ(x)) exists (StationaryOn.tendsto_normalizedBallMass_atRight) and θ := L/ω_n satisfies HasDensity n μ x θ.
B3. Fix ρ ∈ (0,ρ0). As σ ↓ 0 the sets B_ρ(x) ∖ B_σ(x) increase to B_ρ(x) ∖ {x}; by monotone convergence normalDefect V x (B_ρ(x)∖B_σ(x)) → normalDefect V x (B_ρ(x) ∖ {x}) = normalDefect V x (B_ρ(x)), the centre contributing 0 because the integrand there is ofReal(0/0) = 0. Passing to the limit in B1 and dividing by ω_n: θ + ω_n^{-1} normalDefect V x (B_ρ(x)) = densityRatio n μ x ρ, which is StationaryMonotonicityIdentity (all terms finite). (Again valid for n = 0: then the integrand is 1 off the centre and the identity reads μ({x}) + μ(B_ρ(x)∖{x}) = μ(B_ρ(x)).)

PART C: DensityExistsAE (3.6). Source: Simon, Ch. 8, Lemma 3.6 and its printed proof (p. 211). No erratum; one detail is filled in: the printed claim “μ_V(B_ρ(x)) ≥ limsup_{y→x} μ_V(B_ρ(y))” (which needs finiteness of μ_V on a slightly larger ball) is replaced, for the Borel measurability of x ↦ μ_V(B_ρ(x)), by Tonelli's theorem, which holds for every x. Notation: μ = μ_V = V.weight, ‖δV‖ = variationMeasure V, B_ρ(x) = closedBall x ρ, densityRatio n μ x ρ = μ(B_ρ(x))/(ω_n ρ^n). Hypothesis: V has locally bounded first variation in U.

L1. A.e. ball bound (the parenthetical remark of 3.6, from Ch. 1 3.23). By 2.7 (sibling first_variation, second conjunct of FirstVariationRepresentation), for μ-a.e. x the ratio ‖δV‖(B_ρ(x))/μ(B_ρ(x)) converges as ρ ↓ 0 to the finite value D(x) := variationDensity V x. Also μ(Uᶜ) = 0 (V.supported) and μ(ℝ^N ∖ spt μ) = 0. Fix such an x with x ∈ U ∩ spt μ. Choose ρ1 > 0 with B_{ρ1}(x) ⊆ U (U open) and Λ' > D(x) finite; for small ρ the ratio is < Λ', i.e. ‖δV‖(B_ρ(x)) ≤ Λ' μ(B_ρ(x)) for 0 < ρ < ρ2. Hence there are ρ0 ∈ (0, min(ρ1,ρ2)) and Λ(x) ≥ 0 with ball x ρ0 ⊆ U and ‖δV‖(B_ρ(x)) ≤ Λ(x) μ(B_ρ(x)) for 0 < ρ < ρ0, which is hypothesis 3.1 at x. (Formal shortcut: SimonGMT Varifold.ae_exists_ballFirstVariationBound_inside, Chapter08/BallVariationBound.lean:66, gives μ-a.e. R > 0, Λ ≥ 0 with closedBall x R ⊆ U and the bound for 0 < r < R, stated with firstVariationRieszMeasure, which is variationMeasure V by dif_pos.)

L2. Existence and finiteness (first part of 3.6, “follows directly from the monotonicity formula 3.3”). At every x as in L1, Part A above (MonotonicityFormula, applied with ρ0 and Λ := Λ(x)) gives θ_x ∈ [0,∞) with HasDensity n μ x θ_x. Thus for μ-a.e. x, Θ^n(μ, x) exists and is finite.

L3. Borel measurability of the ball mass. μ is σ-finite (V.measure is σ-finite: Varifold.measure.instSigmaFinite, and μ is its image under Prod.fst, finite on the compact exhaustion of U and zero off U). For fixed ρ > 0 the set {(x,y) : |y − x| ≤ ρ} is closed in ℝ^N × ℝ^N, so by Tonelli (measurability of x ↦ ∫ 1_{|y−x|≤ρ} dμ(y) for s-finite μ; Mathlib Measurable.lintegral_prod_right'), x ↦ μ(B_ρ(x)) is Borel measurable on ℝ^N with values in [0,∞]. Hence x ↦ densityRatio n μ x ρ = μ(B_ρ(x)) · (ω_n ρ^n)^{-1} is Borel for every fixed ρ > 0.

L4. Borel representative. Define Θ(x) := liminf_{k→∞} densityRatio n μ x (1/(k+1)) ∈ [0,∞]. As a liminf of a sequence of Borel functions with values in ℝ≥0∞, Θ is Borel measurable (Measurable.liminf).

L5. Agreement a.e. If HasDensity n μ x θ_x holds (Tendsto densityRatio n μ x along 𝓝[>]0 to θ_x), then along the particular sequence 1/(k+1) → 0+ the ratios converge to θ_x, so Θ(x) = θ_x. By L2 this holds for μ-a.e. x, and there θ_x ≠ ∞. Hence for μ-a.e. x: Θ x ≠ ∞ ∧ HasDensity n μ x (Θ x). This is DensityExistsAE (“Θ^n(μ_V,·) is μ_V-measurable”, in the strong form that it agrees μ_V-a.e. with a Borel function).

Combining Parts A, B and C proves MonotonicityFormula ∧ StationaryMonotonicityIdentity ∧ DensityExistsAE.

## Key steps

1. Radial field X_ρ = φ(|y−x|/ρ)(y−x): div_S X_ρ = nφ + r∂_rφ·(1 − |p_{S⊥}((y−x)/r)|²) (3.2).
2. Integrate: d/dρ(ρ^{-n}I) = ρ^{-n}J' − ρ^{-n-1}δV(X_ρ) with I = ∫φ dμ_V, J = ∫φ|p_{S⊥}|² dV, J' ≥ 0 (SimonGMT hasDerivAt_normalized_weightedCutoffMass, h ≡ 1).
3. With 2.6 (|δV(X)| ≤ ∫|X| d‖δV‖), layer cake and 3.1 extended to open balls: |δV(X_ρ)| ≤ (1+ε)Λρ I(ρ).
4. Integrating factor e^{Λ_ερ}: d/dρ(e^{Λ_ερ}ρ^{-n}I) ≥ ρ^{-n}J' ≥ 0; integrate on [σ,ρ], two-sided Ch. 4 3.5 bounds, let φ ↓ 1_{(−∞,1]}: additive form of 3.3.
5. Read off monotonicity, the density limit θ (monotone limit, e^{Λσ} → 1), θ ≤ e^{Λσ}densityRatio(σ), θ ≠ ∞; divide by ω_n.
6. Stationary case: δV(X_ρ) = 0 gives the annular identity (SimonGMT StationaryOn.stationaryMonotonicity with R ∈ (ρ,ρ0)); let σ ↓ 0 by monotone convergence, the centre contributing 0.
7. By 2.7 (first_variation), for μ_V-a.e. x ∈ U ∩ spt μ_V there are ρ0, Λ(x) with ball x ρ0 ⊆ U and ‖δV‖(B_ρ(x)) ≤ Λ(x)μ_V(B_ρ(x)), 0 < ρ < ρ0 (3.1).
8. At such x MonotonicityFormula gives a finite density θ_x.
9. x ↦ μ_V(B_ρ(x)) is Borel for each ρ (Tonelli for the σ-finite μ_V), so Θ(x) := liminf_k densityRatio n μ_V x (1/(k+1)) is Borel.
10. Where the density exists, Θ(x) equals it; hence Θ x ≠ ∞ ∧ HasDensity n μ_V x (Θ x) μ_V-a.e.

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
