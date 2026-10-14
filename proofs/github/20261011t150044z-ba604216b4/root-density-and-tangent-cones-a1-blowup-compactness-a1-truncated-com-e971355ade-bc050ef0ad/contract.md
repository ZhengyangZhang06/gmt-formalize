<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1.pointwise-a1 -->

## Theorem `Submission.dtc_bc_tc_cl_ci_pointwise_tangent_integer`

Hypothesis names: (REP) and (CT) = (T1) ∧ (T2) ∧ (MM) are the first two conjuncts of the frozen type of the parent's dependency foundations (character-for-character the frozen types of the DAG theorems cmc_exists_massRepresentation and cbr_measure_convergence_tools); (SL) is the frozen type of the parent's dependency slicing (cmc_slice_mass_bounds); (RU) is the frozen type of the parent's dependency restrict_unique (cbr_setIntegral_eq_of_integral_eq); (MR) is the parent's first hypothesis (type of cmc_massOn_eq_imRep_measure); (RECT) is the frozen type of the parent's dependency rectifiable (character-for-character that of cbr_rectifiable_of_approx_tangent). Whichever are needed appear verbatim as hypotheses of the Lean statement; the parent discharges them. In words: (REP) a current T ∈ 𝒟_n(U), U open, with M_W(T) < ∞ for open W ⊂⊂ U has a mass representation (μ, ξ): μ(ℝ^P∖U) = 0, μ(K) < ∞ for compact K ⊆ U, μ(W) = M_W(T) for open W, ξ μ-a.e. strongly measurable with |ξ(x)(α)| ≤ |α| for all x, α, T(ω) = ∫ξ(ω)dμ, and μ(E) = 0 whenever Hⁿ(E) = 0 provided also M_W(∂T) < ∞ (boundaryMassOn) for open W ⊂⊂ U; (MR) M_W(T) = R.measure(W) for an IMRep R of T in an open U and open W; (SL) for T ∈ 𝒟_{k+1}(U) with admissible representations (μ, ξ) of T and (μ', ξ') of ∂T and an L-Lipschitz f there are currents A_t, B_t with A_t(ω) = ∫_{f<t}ξ(ω)dμ, B_t(η) = ∫_{f<t}ξ'(η)dμ', ∂A_t = B_t on forms supported off {f = t}, M_W(∂A_t − B_t) ≤ L·liminf_{h↓0}h⁻¹μ(W ∩ {t−h < f < t}) and ∫⁻_{(a,b)}M_W(∂A_t − B_t)dt ≤ Lμ(W ∩ {a < f < b}) for open W; (RU) an identity ∫ξ₁(ω)dμ₁ = ∫ξ₂(ω)dμ₂ + ∫ξ₃(ω)dμ₃ between admissible pairs, valid for all test forms on an open U, remains valid with all integrals restricted to any Borel set; (T1) measures μ_j with sup_jμ_j(K) < ∞ on compacts have a subsequence converging to a Borel μ finite on compacts (against continuous compactly supported functions; limsup on compacts ≤ μ; liminf on open sets ≥ μ); (T2) if X_j ⇀ X with admissible representations (μ_j, ξ_j), (μ_X, ξ_X), limsup_jμ_j(K) ≤ μ(K) on compacts for a Borel μ finite on compacts, f continuous and μ{f = t} = 0, then ∫_{f<t}ξ_j(ω)dμ_j → ∫_{f<t}ξ_X(ω)dμ_X for every ω; (MM) if μ_j(G ∩ {a < f < b}) < ∞ and Z_j(t) ≤ L·liminf_{h↓0}h⁻¹μ_j(G ∩ {t−h < f < t}) for t ∈ (a, b), then some measurable g has liminf_jZ_j(t) ≤ g(t) for a.e. t ∈ (a, b) and ∫⁻_{(a,b)}g ≤ L·liminf_jμ_j(G ∩ {a < f < b}); (RECT) a Borel M with Hⁿ(M) < ∞ having approximate tangent spaces Q(x) at Hⁿ-a.e. x ∈ M with x ↦ p_{Q(x)} Hⁿ⌞M-a.e. strongly measurable is countably n-rectifiable. Notation: Hⁿ = μHE[n], ω_n = unitBallVolume n, |α| = covectorEuclideanNorm α for covectors; an admissible representation (μ, ξ) of a current X in ℝ^P is a Borel measure μ finite on compact sets and a μ-a.e. strongly measurable ξ with |ξ(x)(α)| ≤ |α| μ-a.e., X(ω) = ∫ξ(x)(ω(x))dμ(x) for every test form. ISP (integer slice property) of Y ∈ 𝒟_{d+1}(ℝ^P): for all admissible representations (μ, ξ) of Y and (μ', ξ') of ∂Y and every Lipschitz f : ℝ^P → ℝ, for L¹-a.e. t, all A ∈ 𝒟_{d+1}(ℝ^P), B ∈ 𝒟_d(ℝ^P) with A(ω) = ∫_{f<t}ξ(ω)dμ and B(η) = ∫_{f<t}ξ'(η)dμ' for all test forms have ∂A − B integer multiplicity. SLIM_{P,d}: if X_i, X ∈ 𝒟_{d+1}(ℝ^P), every X_i has ISP, sup_i(M_W(X_i) + M_W(∂X_i)) < ∞ for every open W with compact closure, and X_i ⇀ X, then X has ISP (hypothesis of the parent). LD_{P,d}: there is η₀ > 0 such that for every C ∈ 𝒟_{d+1}(ℝ^P) with ∂C = 0 and ISP, every Borel μ finite on compacts with μ(W) = M_W(C) for open W and every μ-a.e. strongly measurable ξ with |ξ(α)| ≤ |α| μ-a.e. and C(ω) = ∫ξ(ω)dμ, liminf_{r↓0}μ(B_r(x))/(ω_{d+1}r^{d+1}) ≥ η₀ for μ-a.e. x (hypothesis of the parent). For a ∈ ℝ^P and λ > 0 let η(y) := dilation a λ y = λ⁻¹(y − a); X' ∈ 𝒟_m(ℝ^P) is a dilation of X ∈ 𝒟_m(ℝ^P) if X'(ω) = λ^{−m}X(ω') for all test m-forms ω, ω' with ω'(y) = ω(η(y)) for every y. Assume (REP), (MR), (SL), (RU), (CT). Let P, d ∈ ℕ, n := d+1, and assume SLIM_{P,d} (if X_i ⇀ X in 𝒟_n(ℝ^P), each X_i has ISP and sup_i(M_W(X_i) + M_W(∂X_i)) < ∞ for open W with compact closure, then X has ISP; hypothesis of the parent) and LD_{P,d} (there is η₀ > 0 such that for every C ∈ 𝒟_n(ℝ^P) with ∂C = 0 and ISP, every Borel μ finite on compacts with μ(W) = M_W(C) for open W and every μ-a.e. strongly measurable ξ with |ξ(α)| ≤ |α| μ-a.e. and C(ω) = ∫ξ(ω)dμ, liminf_{r↓0}μ(B_r(x))/(ω_nrⁿ) ≥ η₀ for μ-a.e. x; hypothesis of the parent). Let Γ ∈ 𝒟_n(ℝ^P) with ∂Γ = 0 and ISP; μ a finite Borel measure with μ(W) = M_W(Γ) for open W; M Borel with Hⁿ(M) < ∞; θ Borel and ζ strongly measurable with μ = (Hⁿ⌞M) with density ofReal∘θ, θ > 0 on M, |ζ(x)(α)| ≤ |α| for all x, α, and for each x ∈ M some β with |β| ≤ 1 and ζ(x)(β) = 1; Γ(ω) = ∫_Mθζ(ω)dHⁿ for all ω. Let a ∈ M and η₁ > 0 with liminf_{r↓0}μ(B_r(a))/(ω_nrⁿ) ≥ η₁, limsup_{r↓0}Hⁿ(M ∩ B̄_r(a))/(ω_nrⁿ) ≤ 1 and (∫⁻_{M∩B̄_r(a)}‖θζ − θ(a)ζ(a)‖dHⁿ)/(ω_nrⁿ) → 0 as r ↓ 0. Then there is a subspace Q such that M has approximate tangent space Q at a (HasApproximateTangentSpaceAt n M a Q, in particular dim Q = n), ζ(a) is a unit orientation of Q, and θ(a) is a natural number.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1.pointwise-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8070

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8582, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5624, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5640, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5674

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_tc_cl_ci_pointwise_tangent_integer`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ((∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ (φ : ℕ → ℕ) (μ : Measure (Euclid P)), StrictMono φ ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs (φ j) K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs (φ j) G) atTop)) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) ∧ (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop)) → ∀ (P d : ℕ), (∀ (Xs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), (∀ i, (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Xs i ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (Xs i).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B))) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W univ → ⨆ i, ((Xs i).massOn W + (Xs i).boundary.massOn W) < ∞) → WeaklyConvergesOn Xs X → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B))) → (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)), C.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ W : Set (Euclid P), IsOpen W → C.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∀ᵐ x ∂μ, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0)) → ∀ (Γ : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P (d + 1)) (a : Euclid P) (η₁ : ℝ), Γ.boundary = 0 → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (Γ).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → μ univ < ∞ → (∀ W : Set (Euclid P), IsOpen W → Γ.massOn W = μ W) → MeasurableSet M → μHE[(d + 1)] M < ∞ → Measurable θ → StronglyMeasurable ζ → μ = (μHE[(d + 1)].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, 0 < θ x) → (∀ (x : Euclid P) (α : Covector (Euclid P) (d + 1)), |ζ x α| ≤ covectorEuclideanNorm α) → (∀ x ∈ M, ∃ β : Covector (Euclid P) (d + 1), covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μHE[(d + 1)]) → a ∈ M → 0 < η₁ → ENNReal.ofReal η₁ ≤ liminf (fun r : ℝ => μ (ball a r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0) → limsup (fun r : ℝ => μHE[(d + 1)] (M ∩ closedBall a r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0) ≤ 1 → Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[(d + 1)]) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0) (𝓝 0) → ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt (d + 1) M a Q ∧ IsUnitOrientationOf (ζ a) Q ∧ ∃ m : ℕ, θ a = m
```

### Frozen project context

`GMT/Ch07/Contract.lean` at `b4d606db1da5da8fa2c0292ad4924d97de8b3c4b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 7 "Area Minimizing Currents"
(printed pp. 181–204)

Frozen contract.  Currents, boundary, mass, support and weak convergence are the clean SimonGMT
objects of `Poincare.SimonGMT.Chapter06`: `GeometricCurrentOn U n` (Simon 6.2.1), `T.boundary`
(6.2.3), `T.massOn W` = `M_W(T)` (6.2.5, Euclidean coefficient norm), `T.mass` (6.2.4),
`T.support` (6.2.11), `WeaklyConvergesOn` (6.2.13), and the proper affine push-forward
`GeometricCurrentOn.affinePushforward` (6.2.23).  Everything else (integer multiplicity currents,
minimizing currents, densities, blow-ups, tangent cones, `reg T`, `sing T`, the associated
varifold) is defined below from primitive data.  `Hⁿ` is Mathlib's normalized `μHE[n]`; null-set
statements use Mathlib's `μH[s]` (same null sets as Simon's `Hˢ`).

**Conventions.**  The ambient space is `ℝ^{n+k}` (`Euclid (n + k)`); when a submanifold `N` is
present it has dimension `n + ℓ`, `ℓ ≤ k` (Simon writes `N^{n+ℓ} ⊂ ℝ^{n+ℓ}`, `ℓ ≤ k`, a
misprint for `ℝ^{n+k}`; `N = ℝ^{n+k}` is the case `ℓ = k`).  For an `n`-current, `∂T = 0`,
`∂S = ∂T`, `spt ∂T`, `M_W(∂T)` are read with Simon's convention `∂T = 0` if `n = 0` (6.2.3).
-/

open Filter Function Set MeasureTheory Metric
open scoped ENNReal Topology

namespace GMT.Ch07

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)

noncomputable section

/-- Euclidean space `ℝᴾ`. -/
abbrev Euclid (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Multivectors and integer multiplicity currents (Simon Ch. 6, §1 and 3.1) -/

/-- `n`-vectors `Λₙ(ℝᴾ)`, realized as the dual of `n`-covectors (Simon 6.1, `Λₙ ≅ (Λⁿ)*`);
`ξ α` is the pairing `⟨α, ξ⟩` of Simon (6.1.7). -/
abbrev MultiVector (P n : ℕ) := Covector (Euclid P) n →L[ℝ] ℝ

/-- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of the subspace `Q`, i.e.
`⟨α, ξ⟩ = ±α(τ₁, …, τₙ)` (Simon 6.1.1, 6.1.7; 6.2.2).  The sign matters only for `n = 0`. -/
def IsUnitOrientationOf {n : ℕ} (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) : Prop :=
  ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (range τ) = Q ∧
    ((∀ α : Covector (Euclid P) n, ξ α = α τ) ∨ ∀ α : Covector (Euclid P) n, ξ α = -α τ)

/-- Simon Ch. 6, Definition 3.1 (p. 146): a triple `(M, θ, ξ)` in `U`.  `M ⊆ U` is
`Hⁿ`-measurable (taken Borel; this loses nothing, `Hⁿ⌞M` being σ-finite) and countably
`n`-rectifiable; `θ` is positive integer-valued on `M` and locally `Hⁿ`-integrable in `U`; `ξ` is
`Hⁿ`-measurable and, `Hⁿ`-a.e. on `M`, orients the approximate tangent space `TₓM`
(Ch. 3, 1.4). -/
structure IMRep (U : Set (Euclid P)) (n : ℕ) where
  carrier : Set (Euclid P)
  mult : Euclid P → ℕ
  orient : Euclid P → MultiVector P n
  measurableSet_carrier : MeasurableSet carrier
  carrier_subset : carrier ⊆ U
  rectifiable : CountablyRectifiable n carrier
  measurable_mult : Measurable mult
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  locallyIntegrable_mult : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
    ∫⁻ x in carrier ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞
  aestronglyMeasurable_orient : AEStronglyMeasurable orient (μHE[n].restrict carrier)
  orients : ∀ᵐ x ∂(μHE[n].restrict carrier), ∃ Q : Submodule ℝ (Euclid P),
    HasApproximateTangentSpaceAt n carrier x Q ∧ IsUnitOrientationOf (orient x) Q

variable {U : Set (Euclid P)} {n : ℕ}

/-- `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)` (Simon 6.3.1 (‡)). -/
def IMRep.action (R : IMRep U n) (ω : DifferentialForm (Euclid P) n) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]

/-- `T = τ(M, θ, ξ)` in `U`. -/
def IMRep.Represents (R : IMRep U n) (T : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, T ω = R.action (ω : DifferentialForm (Euclid P) n)

/-- The weight `μ_V = θ Hⁿ⌞M` of the associated varifold `V = v(M, θ)`; it equals the mass
measure `μ_T` of `T = τ(M, θ, ξ)` (Simon 6.3.2(3), 4.1.1). -/
def IMRep.measure (R : IMRep U n) : Measure (Euclid P) :=
  (μHE[n].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞)

/-- Simon 6.3.1: `T` is an integer multiplicity (rectifiable) current. -/
def IsIntegerMultiplicity (T : GeometricCurrentOn U n) : Prop :=
  ∃ R : IMRep U n, R.Represents T

/-- Difference of currents (needed for `spt(S − T)` in 7.1.1). -/
instance : Sub (GeometricCurrentOn U n) where
  sub S T :=
    { toCurrent := S.toCurrent - T.toCurrent
      continuous' := fun ωs h => by
        simpa using (S.continuous' ωs h).sub (T.continuous' ωs h) }

/-! ## Boundary conventions in arbitrary degree -/

/-- `∂S = ∂T` in `U` (vacuous for `n = 0`, where `∂ = 0`). -/
def SameBoundary : {n : ℕ} → GeometricCurrentOn U n → GeometricCurrentOn U n → Prop
  | 0, _, _ => True
  | _ + 1, S, T => S.boundary = T.boundary

/-- `∂T = 0` in `U`. -/
def BoundaryVanishes : {n : ℕ} → GeometricCurrentOn U n → Prop
  | 0, _ => True
  | _ + 1, T => T.boundary = 0

/-- `spt ∂T` (empty for `n = 0`). -/
def boundarySupport : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P)
  | 0, _ => ∅
  | _ + 1, T => T.boundary.support

/-- `M_W(∂T)` (zero for `n = 0`). -/
def boundaryMassOn : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P) → ℝ≥0∞
  | 0, _, _ => 0
  | _ + 1, T, W => T.boundary.massOn W

/-! ## Minimizing currents (Simon 7.1.1) -/

/-- `W ⊂⊂ U`: `closure W` is a compact subset of `U`. -/
def CompactlyContained (W U : Set (Euclid P)) : Prop :=
  IsCompact (closure W) ∧ closure W ⊆ U

/-- **Simon 7.1.1 (p. 181).**  The integer multiplicity `T ∈ 𝒟ₙ(U)` is *minimizing in `A`*
(`A ⊆ U`): `M_W(T) ≤ M_W(S)` whenever `W ⊂⊂ U` is open, `S ∈ 𝒟ₙ(U)` is integer multiplicity,
`∂S = ∂T` in `U` and `spt(S − T)` is a compact subset of `A ∩ W`.  Competitors are integer
multiplicity, as required by Remark 7.2.2(1) and the proofs of 7.1.4 and 7.2.4. -/
def IsMinimizingIn (T : GeometricCurrentOn U n) (A : Set (Euclid P)) : Prop :=
  IsIntegerMultiplicity T ∧
    ∀ (W : Set (Euclid P)) (S : GeometricCurrentOn U n), IsOpen W → CompactlyContained W U →
      IsIntegerMultiplicity S → SameBoundary S T → IsCompact (S - T).support →
        (S - T).support ⊆ A ∩ W → T.massOn W ≤ S.massOn W

/-! ## Densities, blow-ups, tangent cones (Simon 7.3) -/

/-- `ωₙ`, the Lebesgue measure of the unit ball of `ℝⁿ`. -/
def unitBallVolume (n : ℕ) : ℝ≥0∞ := volume (ball (0 : Euclid n) 1)

/-- `Θⁿ(μ_T, x) = θ`: `(ωₙρⁿ)⁻¹ μ_T(B_ρ(x)) → θ` as `ρ ↓ 0`, with `μ_T(B_ρ(x)) = M_{B_ρ(x)}(T)`
for small `ρ` (Simon 6.2.8; open and closed balls give the same limit). -/
def HasMassDensity (T : GeometricCurrentOn U n) (x : Euclid P) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ Tendsto (fun ρ : ℝ => T.massOn (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ))

/-- Value of a current in `U` on an ambient form: `T(ω)` if `ω ∈ 𝒟ⁿ(U)`, else `0`.  Used for
convergence of currents on varying domains (Simon: "`η_{x,λⱼ#}T ⇀ C` in `ℝ^{n+ℓ}`"). -/
def currentEval (T : GeometricCurrentOn U n) (ω : DifferentialForm (Euclid P) n) : ℝ := by
  classical
  exact if h : IsTestForm ω ∧ tsupport ω ⊆ U then T ⟨ω, h⟩ else 0

/-- `Tⱼ ⇀ T` in `V`, for currents `Tⱼ ∈ 𝒟ₙ(Uⱼ)` whose domains eventually contain every compact
subset of `V` (as for blow-ups): `Tⱼ(ω) → T(ω)` for every `ω ∈ 𝒟ⁿ(V)` (Simon 6.2.13). -/
def ConvergesWeakly {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ ω : TestFormOn V n,
    Tendsto (fun j => currentEval (Ts j) (ω : DifferentialForm (Euclid P) n)) atTop (𝓝 (T ω))

/-- `μ_{Tⱼ} → μ_T` as Radon measures in `V` (Simon 7.2.4, Remark 7.2.5(1)): for all integer
multiplicity representations of the `Tⱼ` and of `T`, `∫ f dμ_{Tⱼ} → ∫ f dμ_T` for every
continuous `f` with compact support in `V`. -/
def MassMeasuresConverge {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ Rs : (j : ℕ) → IMRep (Us j) n, (∀ j, (Rs j).Represents (Ts j)) →
    ∀ R : IMRep V n, R.Represents T →
      ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ V →
        Tendsto (fun j => ∫ x, f x ∂(Rs j).measure) atTop (𝓝 (∫ x, f x ∂R.measure))

/-- The linear part `y ↦ λ⁻¹y` of the dilation `η_{x,λ}`. -/
def dilationCLM (P : ℕ) (lam : ℝ) : Euclid P →L[ℝ] Euclid P :=
  lam⁻¹ • ContinuousLinearMap.id ℝ (Euclid P)

/-- Simon's dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, written `y ↦ −λ⁻¹x + λ⁻¹y`. -/
def dilation (x : Euclid P) (lam : ℝ) : Euclid P → Euclid P :=
  fun y => -(lam⁻¹ • x) + dilationCLM P lam y

/-- The blow-up `η_{x,λ#}T ∈ 𝒟ₙ(η_{x,λ}(U))`, `η_{x,λ#}T(ω) = T(η_{x,λ}^# ω)` (Simon 6.2.23 for
the proper affine diffeomorphism `η_{x,λ}`, `λ ≠ 0`). -/
def blowUp (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : lam ≠ 0) :
    GeometricCurrentOn (dilation x lam '' U) n :=
  (T.restrictDomain (show (fun y => -(lam⁻¹ • x) + dilationCLM P lam y) ⁻¹'
      (dilation x lam '' U) ⊆ U by
    rintro y ⟨z, hz, hzy⟩
    have hzy' : lam⁻¹ • z = lam⁻¹ • y := by
      simpa [dilation, dilationCLM] using hzy
    rwa [← smul_right_injective (Euclid P) (inv_ne_zero hlam) hzy'])).affinePushforward
    (dilationCLM P lam) (-(lam⁻¹ • x)) (by
      convert ((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam)).trans
        (Homeomorph.addLeft (-(lam⁻¹ • x)))).isProperMap using 1
      funext y
      simp [dilationCLM])

/-- `C ∈ 𝒟ₙ(ℝᴾ)` is a cone: `η_{0,λ#}C = C` for every `λ > 0` (Simon 7.3.1(2)). -/
def IsConeCurrent (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam) (ω : TestFormOn (univ : Set (Euclid P)) n),
    currentEval (blowUp C 0 lam hlam.ne') (ω : DifferentialForm (Euclid P) n) = C ω

/-- Simon 7.3.2(1): `C` is a tangent cone of `T` at `x`, i.e. `η_{x,λⱼ#}T ⇀ C` in `ℝᴾ` for some
sequence `λⱼ > 0`, `λⱼ → 0`. -/
def IsTangentConeAt (T : GeometricCurrentOn U n) (x : Euclid P)
    (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∃ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) ∧
    ConvergesWeakly (fun j => blowUp T x (lams j) (hlams j).ne') C

/-- Simon 7.3.2(1): `T` has a (multiplicity `m`) tangent plane at `x`: some tangent cone has
support an `n`-dimensional subspace. -/
def HasTangentPlaneAt (T : GeometricCurrentOn U n) (x : Euclid P) : Prop :=
  ∃ C : GeometricCurrentOn (univ : Set (Euclid P)) n, IsTangentConeAt T x C ∧
    ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ C.support = (Q : Set (Euclid P))

/-! ## Submanifolds, `reg T`, `sing T` (Simon Ch. 2, §4 and 7.4.1) -/

/-- Simon Ch. 2, §4, (4.1) (p. 55): `M ⊂ ℝᴾ` is a `d`-dimensional (embedded) `Cʳ` submanifold:
each `y ∈ M` has an open `W ∋ y` and a 1:1 `Cʳ` map `ψ : V → W`, `V ⊆ ℝᵈ` open, with
`ψ(V) = W ∩ M`, `ψ` proper, and `Dψ` of rank `d` on `V`. -/
def IsEmbeddedSubmanifold (r d : ℕ) (M : Set (Euclid P)) : Prop :=
  ∀ y ∈ M, ∃ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧
      ∀ z ∈ V, Injective (fderiv ℝ ψ z)

/-- Simon Ch. 2, §4 (p. 55): `T_yM = {γ'(0) : γ ∈ C¹((−1,1); ℝᴾ), γ((−1,1)) ⊆ M, γ(0) = y}`. -/
def tangentSpace (M : Set (Euclid P)) (y : Euclid P) : Set (Euclid P) :=
  {v | ∃ γ : ℝ → Euclid P, ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧ MapsTo γ (Ioo (-1) 1) M ∧
    γ 0 = y ∧ HasDerivAt γ v 0}

/-- An orientation of the `d`-dimensional submanifold `M` (Simon 6.2.2): `ξ` is continuous on
`M` and `ξ(y) = ±τ₁ ∧ ⋯ ∧ τ_d` for an orthonormal basis `τ` of `T_yM`, for every `y ∈ M`. -/
def IsOrientation (d : ℕ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P d) : Prop :=
  ContinuousOn ξ M ∧ ∀ y ∈ M, ∃ Q : Submodule ℝ (Euclid P),
    (Q : Set (Euclid P)) = tangentSpace M y ∧ IsUnitOrientationOf (ξ y) Q

/-- **Simon 7.4.1 (p. 193)**: `reg T` is the set of `y ∈ spt T` such that, for some `ρ > 0`
(with `B_ρ(y) ⊆ U`), `m ∈ ℤ \ {0}` and embedded `n`-dimensional oriented `C¹` submanifold `M`
(of locally finite `Hⁿ`-measure in `B_ρ(y)`, as `[[M]]` requires, 6.2.2), `T = m[[M]]` in
`B_ρ(y)` (6.2.16), i.e. `T(ω) = m ∫_M ⟨ω, ξ_M⟩ dHⁿ` whenever `spt ω ⊆ B_ρ(y)`.
The point `y` itself must lie on `M` (as in 4.4(8) and the proof of 5.8): otherwise a singular
point could be declared regular by deleting it from `M`, e.g. the vertex of the Simons cone. -/
def regularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  {y | y ∈ T.support ∧ ∃ ρ : ℝ, 0 < ρ ∧ ball y ρ ⊆ U ∧
    ∃ (m : ℤ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P n), m ≠ 0 ∧ y ∈ M ∧
      IsEmbeddedSubmanifold 1 n M ∧ IsOrientation n M ξ ∧
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ ball y ρ → μHE[n] (M ∩ K) ≠ ∞) ∧
      ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball y ρ →
        T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]}

/-- **Simon 7.4.1**: `sing T = spt T \ reg T`. -/
def singularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  T.support \ regularSet T

/-! ## The associated varifold `V = v(M, θ)` (Simon Ch. 4, 2.3–2.7 and 3.14) -/

/-- The approximate tangent plane `TₓM` (Ch. 3, 1.4; unique when it exists), `⊥` otherwise. -/
def approxTangentPlane (n : ℕ) (M : Set (Euclid P)) (x : Euclid P) :
    Submodule ℝ (Euclid P) := by
  classical
  exact if h : ∃ Q, HasApproximateTangentSpaceAt n M x Q then h.choose else ⊥

/-- `div_M X(x) = Σⱼ eⱼ · ∇^M Xʲ = trace(p_{TₓM} ∘ DX(x))` (Simon Ch. 4, 2.3). -/
def tangentialDivergence (n : ℕ) (M : Set (Euclid P)) (X : Euclid P → Euclid P)
    (x : Euclid P) : ℝ :=
  LinearMap.trace ℝ (Euclid P)
    ((approxTangentPlane n M x).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)

/-- First variation `δV(X) = ∫_M div_M X dμ_V` of `V = v(M, θ)` (Simon Ch. 4, 2.2). -/
def IMRep.firstVariation (R : IMRep U n) (X : Euclid P → Euclid P) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * tangentialDivergence n R.carrier X x ∂μHE[n]

/-- Simon Ch. 4, 2.6 (computed form, p. 88): `V` is stationary in `U ∩ N`: `δV(X) = 0` for all
`X ∈ C¹_c(U; ℝᴾ)` with `X(x) ∈ TₓN` for every `x ∈ N ∩ U`. -/
def IMRep.IsStationaryAlong (R : IMRep U n) (N : Set (Euclid P)) : Prop :=
  ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → R.firstVariation X = 0

/-- Simon Ch. 4, 3.14: `V` has generalized mean curvature `H` in `U`
(`∫ div_M X dμ_V = −∫ X · H dμ_V`, `X ∈ C¹_c(U; ℝᴾ)`), with `H` bounded on compact subsets. -/
def IMRep.HasLocallyBoundedMeanCurvature (R : IMRep U n) : Prop :=
  ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧
    (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ᵐ x ∂R.measure, x ∈ K → ‖H x‖ ≤ Λ) ∧
    ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure

/-! ## Codimension one (Simon 7.5) -/

/-- Simon 7.5 (p. 197): `N ∈ 𝒪`, an oriented embedded `C²` submanifold of dimension `n + 1` with
`(N̄ \ N) ∩ U = ∅` and `N ∩ U ≠ ∅`, with chosen orientation `ξN`. -/
def InClassO (n : ℕ) (U N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  IsEmbeddedSubmanifold 2 (n + 1) N ∧ IsOrientation (n + 1) N ξN ∧ (closure N \ N) ∩ U = ∅ ∧
    (N ∩ U).Nonempty

/-- Simon 7.5.1: `T = ∂[[E]]` in `U`, where `[[E]](ω) = ∫_E ⟨ω, ξ_N⟩ dH^{n+1}`. -/
def IsBoundaryOfRegion (T : GeometricCurrentOn U n) (E : Set (Euclid P))
    (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  ∀ ω : TestFormOn U n,
    T ω = ∫ x in E, ξN x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]

/-! ## Headline results -/

/-- **Simon 7.1.2 (Lemma, pp. 181–182).**  Let `N` be an embedded `C²` `(n+ℓ)`-dimensional
submanifold of `ℝ^{n+k}`, `(N̄ \ N) ∩ U = ∅`.  If `T ∈ 𝒟ₙ(U)` is minimizing in `N ∩ U`,
`spt T ⊆ N` and `∂T = 0` in `U`, then the associated varifold `V = v(M, θ)` (for any
representation `T = τ(M, θ, ξ)`) is stationary in `N ∩ U` (Ch. 4, 2.6) and has locally bounded
generalized mean curvature in `U` (Ch. 4, 3.14).
*Correction*: `spt T ⊆ N` and `(N̄ \ N) ∩ U = ∅` are implicit in the book (they are part of the
setting of Ch. 4, 2.5–2.6 and of §3); without `spt T ⊆ N` the lemma is false. -/
def MinimizingImpliesStationary : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    T.support ⊆ N → IsMinimizingIn T (N ∩ U) → BoundaryVanishes T →
    ∀ R : IMRep U n, R.Represents T → R.IsStationaryAlong N ∧ R.HasLocallyBoundedMeanCurvature

/-- **Simon 7.2.1 (Lemma, p. 183).**  Let `S ∈ 𝒟_{n−1}(ℝ^{n+ℓ})` be integer multiplicity with
`spt S` compact and `∂S = 0`.  Then there is an integer multiplicity `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`spt T` compact, `∂T = S`, and `M(T) ≤ M(R)` for every integer multiplicity `R` with `spt R`
compact and `∂R = S`.  Here `n = m + 2`: integer multiplicity currents have dimension `≥ 1`
(Ch. 6, §3).  *Correction*: the printed statement omits the conclusion `∂T = S` (proved: `T ∈ 𝓘_S`);
without it `T = 0` would do. -/
def ExistenceOfMinimizingFilling : Prop :=
  ∀ (m ℓ : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 1)),
    IsIntegerMultiplicity S → IsCompact S.support → S.boundary = 0 →
    ∃ T : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity T ∧ IsCompact T.support ∧ T.boundary = S ∧
      ∀ R : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
        IsIntegerMultiplicity R → IsCompact R.support → R.boundary = S → T.mass ≤ R.mass

/-- **Simon 7.2.4 (Theorem, p. 184).**  If `Tⱼ` are minimizing in `U`,
`supⱼ (M_W(Tⱼ) + M_W(∂Tⱼ)) < ∞` for each open `W ⊂⊂ U`, and `Tⱼ ⇀ T ∈ 𝒟ₙ(U)`, then `T` is
(integer multiplicity, Remark 7.2.5(1), and) minimizing in `U`, and `μ_{Tⱼ} → μ_T` as Radon
measures in `U`. -/
def CompactnessOfMinimizingCurrents : Prop :=
  ∀ (n k : ℕ) (U : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n),
    IsOpen U → (∀ j, IsMinimizingIn (Ts j) U) →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U →
      ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) →
    WeaklyConvergesOn Ts T → IsMinimizingIn T U ∧ MassMeasuresConverge (Us := fun _ => U) Ts T

/-- **Simon 7.3.1 (Theorem, p. 187).**  `N` as in 7.1.2 (`C²`).  If `T ∈ 𝒟ₙ(U)` is minimizing in
`U ∩ N` and `spt T ⊆ U ∩ N`, then (1) `Θⁿ(μ_T, x)` exists at every `x ∈ U \ spt ∂T` and is upper
semicontinuous there; (2) for `x ∈ spt T \ spt ∂T` and `λⱼ ↓ 0` (any `λⱼ > 0`, `λⱼ → 0`) there
are a subsequence `λⱼ'` and an integer multiplicity `C ∈ 𝒟ₙ(ℝ^{n+k})`, minimizing in `ℝ^{n+k}`,
with `η_{x,λⱼ'#}T ⇀ C`, `μ_{η_{x,λⱼ'#}T} → μ_C`, `η_{0,λ#}C = C` (`λ > 0`) and
`Θⁿ(μ_C, 0) = Θⁿ(μ_T, x)`.
*Correction*: the printed hypothesis "`x ∈ spt T \ spt ∂T`" and "(1) … everywhere in `U`" are
garbled; the monotonicity proof gives (1) on `U \ spt ∂T`, which is what is stated. -/
def DensityAndTangentCones : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N →
    (∃ Θ : Euclid (n + k) → ℝ, (∀ x ∈ U \ boundarySupport T, HasMassDensity T x (Θ x)) ∧
        UpperSemicontinuousOn Θ (U \ boundarySupport T)) ∧
    ∀ x ∈ T.support \ boundarySupport T, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j),
      Tendsto lams atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧
        ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        IsMinimizingIn C univ ∧ IsConeCurrent C ∧
        ∃ θ : ℝ, HasMassDensity T x θ ∧ HasMassDensity C 0 θ

/-- **Simon 7.3.3 (Theorem, p. 189).**  `N` as in 7.3.1.  If `T` is minimizing in `U ∩ N`,
`spt T ⊆ U ∩ N` and `∂T = 0` in `U`, then (1) `Θⁿ(μ_T, x) ∈ ℤ` for all `x ∈ U \ E`, where
`H^{n−3+α}(E) = 0` for all `α > 0`; (2) there is `F ⊇ E` with `H^{n−2+α}(F) = 0` for all `α > 0`
such that `T` has a tangent plane at each `x ∈ spt T \ F`.
*Correction*: printed "`F ⊂ E`" must read `F ⊃ E` (non-integer density excludes tangent planes). -/
def IntegerDensityAndTangentPlanes : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∃ E F : Set (Euclid (n + k)), E ⊆ F ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 3 + α] E = 0) ∧
      (∀ x ∈ U \ E, ∃ m : ℤ, HasMassDensity T x m) ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] F = 0) ∧
      ∀ x ∈ T.support \ F, HasTangentPlaneAt T x

/-- **Simon 7.4.2 (Theorem, p. 194).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity and minimizing in
`U ∩ N` (`N` an embedded `C²` `(n+ℓ)`-submanifold, `(N̄ \ N) ∩ U = ∅`), `spt T ⊆ U ∩ N` and
`∂T = 0` in `U`, then `reg T` is dense in `spt T`. -/
def RegularSetDense : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    T.support ⊆ closure (regularSet T)

/-- **Simon 7.4.3 (Theorem, p. 194)**, for a fixed `N` (`Nᵢ = N`).  Let `Tᵢ, T` be minimizing in
`U ∩ N`, `spt Tᵢ, spt T ⊆ N`, `∂Tᵢ = ∂T = 0` in `U`, `Tᵢ ⇀ T`, with
`supᵢ M_W(Tᵢ) < ∞` for `W ⊂⊂ U`.  If `y ∈ N ∩ U`, `Θⁿ(μ_T, y) = 1`, `y = lim yⱼ`, `yⱼ ∈ spt Tⱼ`,
then `y ∈ reg T` and `yⱼ ∈ reg Tⱼ` for all large `j`.
*Deviations*: the book allows `Nᵢ → N` "in the `C²` sense" (not defined at this point of the
book); we take `Nᵢ = N`.  The local mass bound is the hypothesis of 7.2.4, which the proof uses
for `μ_{Tⱼ} → μ_T`; it is added explicitly. -/
def DensityOneImpliesRegular : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n) (ys : ℕ → Euclid (n + k)) (y : Euclid (n + k)),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    (∀ j, IsMinimizingIn (Ts j) (U ∩ N)) → IsMinimizingIn T (U ∩ N) →
    (∀ j, (Ts j).support ⊆ N) → T.support ⊆ N →
    (∀ j, BoundaryVanishes (Ts j)) → BoundaryVanishes T →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U → ⨆ j, (Ts j).massOn W < ∞) →
    WeaklyConvergesOn Ts T → y ∈ N ∩ U → HasMassDensity T y 1 →
    Tendsto ys atTop (𝓝 y) → (∀ j, ys j ∈ (Ts j).support) →
    y ∈ regularSet T ∧ ∀ᶠ j in atTop, ys j ∈ regularSet (Ts j)

/-- **Simon 7.4.4 (Theorem, p. 194).**  If `T` is as in 7.4.2 and `ξ ∈ spt T` has
`Θⁿ(μ_T, ξ) < 2`, then there is `ρ > 0` with `H^{n−2+α}(sing T ∩ B_ρ(ξ)) = 0` for all `α > 0`. -/
def SingularSetSmallWhereDensityBelowTwo : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∀ ξ ∈ T.support, ∀ θ : ℝ, HasMassDensity T ξ θ → θ < 2 →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] (singularSet T ∩ ball ξ ρ) = 0

/-- **Simon 7.4.5 (Theorem, p. 195).**  If `C ∈ 𝒟ₙ(ℝ^{n+k})` is minimizing in `ℝ^{n+k}`, `∂C = 0`,
`C` is a cone, and `spt C ⊆ H̄` for an open half-space `H = {x : v · x > 0}` (`v ≠ 0`, so
`0 ∈ ∂H`), then `spt C ⊆ ∂H`. -/
def HalfSpaceConeLiesInBoundary : Prop :=
  ∀ (n k : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (v : Euclid (n + k)),
    IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → v ≠ 0 →
    C.support ⊆ closure {x | 0 < inner ℝ v x} → C.support ⊆ frontier {x | 0 < inner ℝ v x}

/-- **Simon 7.5.8 (Theorem, p. 200).**  Let `N ∈ 𝒪` (oriented by `ξN`), `E ⊆ N ∩ U`
`H^{n+1}`-measurable, `T = ∂[[E]] ∈ 𝒟ₙ(U)` integer multiplicity and minimizing in `N ∩ U`.  Then
`sing T = ∅` if `n ≤ 6`; `sing T` is locally finite in `U` (finite on compact subsets of `U`) if
`n = 7`; `H^{n−7+α}(sing T) = 0` for all `α > 0` if `n > 7`.  (`N = ℝ^{n+1}` is the case `k = 1`.)
-/
def CodimensionOneRegularity : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    (n ≤ 6 → singularSet T = ∅) ∧
    (n = 7 → ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ U → (singularSet T ∩ K).Finite) ∧
    (7 < n → ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 7 + α] (singularSet T) = 0)

/-- **Simon 7.5.11 (Corollary, p. 202).**  If `T` is as in 7.5.8, `T = τ(M, θ, ξ)`, and
`T₁ ∈ 𝒟ₙ(U)` is obtained by equipping a connected component `M₁` of `reg T` with multiplicity
`1` and the orientation `ξ` of `T`, then `∂T₁ = 0` in `U` and `T₁` is minimizing in `U ∩ N`. -/
def RegularComponentsAreMinimizing : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    ∀ R : IMRep U n, R.Represents T → ∀ y ∈ regularSet T, ∀ T₁ : GeometricCurrentOn U n,
      (∀ ω : TestFormOn U n, T₁ ω = ∫ x in connectedComponentIn (regularSet T) y,
        R.orient x ((ω : DifferentialForm (Euclid (n + k)) n) x) ∂μHE[n]) →
      BoundaryVanishes T₁ ∧ IsMinimizingIn T₁ (U ∩ N)

end

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1.pointwise-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Porting note (not a proof step): this proposition is, character for character, the frozen type of the DAG nodes cbr_ci_pointwise_tangent_integer and dmcbr_ci_pointwise_tangent_integer of the parallel branches, which were not accepted in the 10:46:01Z snapshot against which this decomposition's Lean names are checked (cbr_ci_pointwise_tangent_integer was still being compared at 12:11Z) and are not prerequisites of this leaf. Their compiled speculative draft (commit 9e7eb961) derives this type from the same four sibling types plus four helper facts; steps 2, 3(b), 3(f) and 5 below prove those facts inline. The draft calls Submission.cbr_ci_blowup_limit; here that is the sibling Submission.dtc_bc_tc_cl_ci_blowup_limit, which has the identical type. The helper facts are comparator-accepted with identical frozen types: cbr_ci_pw_span_eq_of_covector_eval_eq (candidate 96759ef5, with cbr_ci_pw_pu_inner_det_covector and cbr_ci_pw_pu_span_le_of_inner_det_eq; step 2), cbr_ci_pw_blowup_lower_density (6df8182a; step 3(b)), cbr_ci_pw_single_plane_of_unit_weights (7bb4b37b; step 3(f)) and cbr_ci_pw_approxTangent_of_subseq (9a38b806; step 5). Their Lean text and the draft may be inlined as local `have`s inside this leaf's single theorem. Measured with #count_heartbeats, they use about 45 000 heartbeats in total, below the default 200 000. The proof base of this leaf contains the candidate histories of the accepted siblings constant_planes, plane_integer and weight_ge_one (the latter with all its cbr_ci_pw_* sub-lemmas), and of blowup_limit once accepted. Among other things these include cbr_ci_cp_pr_inner_det_covector (the covector u ↦ det(⟨g_b, u_a⟩)), regcomp_covector_eval_orthonormal_le, regcomp_exists_covector_eval_orthonormal_eq_one and cbr_cipi_affine_plane_measure.
Source: parent proof, Step 9 (approximate tangent plane; parent V12) with the plane-uniqueness remark at the end of Step 6, assembling Steps 5–8 and 10, which are supplied by the siblings blowup_limit (BL), constant_planes (CP), weight_ge_one (WG) and plane_integer (PI). The hypotheses (REP), (MR), (SL), (RU), (CT) and SLIM_{P,d} of this statement are passed to the siblings that require them ((BL) needs (SL), (RU), (CT), SLIM_{P,d}; (WG) needs (REP), (SL), (CT); (PI) needs (MR), (SL)); LD_{P,d} is used in step 3(b).
1. Notation. n := d + 1, θ₀ := θ(a) > 0 (a ∈ M), ζ₀ := ζ(a), ω_n := unitBallVolume n; η₀' > 0 is the constant provided by LD_{P,d}.
2. Plane uniqueness (parent Step 6, final remark). If v, v' are orthonormal n-families in ℝ^P with β(v) = β(v') for every n-covector β, then span v = span v'. For n = 0 both spans are {0}. Let n ≥ 1. For w ∈ ℝ^P and an (n−1)-covector α (a scalar if n = 1) let w^♭∧α be the n-covector (u_1, …, u_n) ↦ Σ_j(−1)^{j−1}⟨w, u_j⟩α(u_1, …, û_j, …, u_n) (multilinear and alternating; in Lean ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ w).smulRight α), whose value is Σ_j(−1)^j⟨w, u_j⟩α(Fin.removeNth j u) with 0-based j). Then (w^♭∧α)(v) = ⟨Σ_j(−1)^{j−1}α(v^{(j)})v_j, w⟩ with v^{(j)} := (v_1, …, v̂_j, …, v_n), and likewise for v'. As the two evaluations agree for every w, Σ_j(−1)^{j−1}α(v^{(j)})v_j = Σ_j(−1)^{j−1}α(v'^{(j)})v'_j for every α. Take α := β_{v^{(i)}}, β_{v^{(i)}}(u) := det(⟨u_s, v^{(i)}_r⟩)_{s,r} (an (n−1)-covector, e.g. from cbr_ci_cp_pr_inner_det_covector; for n = 1 it is the constant 0-covector 1): β_{v^{(i)}}(v^{(j)}) = δ_{ij} (for j ≠ i the family v^{(j)} contains v_i, orthogonal to every member of v^{(i)}, so the Gram matrix has a zero row; for j = i it is the identity). Hence (−1)^{i−1}v_i ∈ span v' for every i, so span v ⊆ span v', and by symmetry span v = span v'.
3. Claim. For every sequence (λ_i) with λ_i > 0 and λ_i → 0 there are a strictly increasing φ and an orthonormal v = (v_1, …, v_n) such that ζ₀(β) = β(v) for all n-covectors β, ∫_{blowUpMap a λ_{φ(k)} '' M}f dHⁿ → ∫_{span v}f dHⁿ for every continuous compactly supported f, and θ₀ is a natural number.
 (a) Apply (BL) to Γ, μ, M, θ, ζ, a, η₁ and (λ_i) (its hypotheses are among ours): φ, ν, C, Γ_k, μ_k, ξ_k with ν finite on compacts, ν(B_R(0)) ≤ ω_nRⁿ and ν(B_R(0)) > 0 for R > 0, C(ω) = ∫θ₀ζ₀(ω(y))dν(y), ∂C = 0, M_W(C) = ofReal(θ₀)ν(W) for open W, C has ISP, Γ_k ⇀ C, ∂Γ_k = 0, μ_k finite on compacts, admissible representations (μ_k, ξ_k) of Γ_k, limsup_kμ_k(K) ≤ θ₀ν(K) for compact K and, for N_k := blowUpMap a λ_{φ(k)} '' M, μ_k(ℝ^P∖N_k) = 0, limsup_kHⁿ(N_k ∩ K) ≤ ν(K) for compact K and ∫_{N_k}f dHⁿ → ∫f dν for every continuous compactly supported f.
 (b) Lower density of ν (parent Step 7(b)). Apply LD_{P,d} to C with the measure θ₀ν := ofReal(θ₀)·ν and the constant field ζ₀: ∂C = 0; θ₀ν is finite on compacts; M_W(C) = θ₀ν(W) for open W; the constant field is strongly measurable with |ζ₀(α)| ≤ |α|; C(ω) = θ₀∫ζ₀(ω)dν = ∫ζ₀(ω)d(θ₀ν) (integral_smul_measure, (ofReal θ₀).toReal = θ₀); C has ISP. So liminf_{r↓0}θ₀ν(B_r(y))/(ω_nrⁿ) ≥ ofReal(η₀') for θ₀ν-a.e. y, equivalently, since ofReal(θ₀) ≠ 0, for ν-a.e. y (Measure.ae_ennreal_smul_measure_iff). Writing (ofReal(θ₀)·ν)(B)/D = ofReal(θ₀)·(ν(B)/D) (Measure.smul_apply, mul_div_assoc), and using that multiplication by the finite positive constant ofReal(θ₀) commutes with liminf in [0, ∞] (ENNReal.liminf_const_mul_of_ne_zero_of_ne_top), we get ofReal(η₀') ≤ ofReal(θ₀)·liminf_{r↓0}ν(B_r(y))/(ω_nrⁿ), hence liminf_{r↓0}ν(B_r(y))/(ω_nrⁿ) ≥ ofReal(η₀'/θ₀) for ν-a.e. y (ENNReal.ofReal_div_of_pos, ENNReal.div_le_of_le_mul').
 (c) Boundary condition. For a test d-form φ: 0 = ∂C(φ) = C(dφ) = θ₀∫ζ₀(dφ(y))dν(y), so ∫ζ₀(dφ(y))dν(y) = 0 (θ₀ ≠ 0).
 (d) Apply (CP) with ν, ζ₀ (|ζ₀(β)| ≤ |β|, and ζ₀(β₁) = 1 for some |β₁| ≤ 1 because a ∈ M), c := η₀'/θ₀ > 0 and (a)–(c): an orthonormal v with ζ₀(β) = β(v) for all β, N ∈ ℕ, pairwise distinct w_1, …, w_N orthogonal to every v_j, reals α_i ≥ c > 0 with Σ_iα_i ≤ 1, some w_{i₁} = 0, and ν = Σ_iofReal(α_i)·Hⁿ⌞{y : y − w_i ∈ V₀}, V₀ := span v. Consequently C(ω) = θ₀∫ω(y)(v)dν(y).
 (e) Apply (WG) with v, θ₀, N, w, α, ν, C, (Γ_k), (μ_k), (ξ_k) and the sets N_k: its hypotheses are (REP), (SL), (CT), 0 < θ₀ (a ∈ M), 0 < α_i (from α_i ≥ c > 0), and the facts in (a) and (d). Hence α_i ≥ 1 for every i.
 (f) N ≥ 1 (the index i₁ exists) and N ≤ Σ_iα_i ≤ 1, so N = 1, α_1 = 1 and w_1 = 0 (the only index is i₁); substituting into the sum over Fin 1 with ofReal(1) = 1 and y − 0 = y gives ν = μHE[n].restrict (span v : Set (Euclid P)) = Hⁿ⌞V₀.
 (g) By (a) and (f), ∫_{N_k}f dHⁿ → ∫f dν = ∫_{V₀}f dHⁿ for every continuous compactly supported f.
 (h) C(ω) = θ₀∫_{V₀}ω(y)(v)dHⁿ(y) for every ω, θ₀ > 0, v is orthonormal and C has ISP, so (PI) gives θ₀ ∈ ℕ. This proves the claim.
4. The plane. Apply the claim to λ_i := 1/(i + 1); let v be the resulting orthonormal family and Q := span v. finrank Q = n (finrank_span_eq_card; orthonormal families are linearly independent). ζ₀ is a unit orientation of Q (IsUnitOrientationOf with the frame v and the + sign: ζ₀(α) = α(v) for all α), and θ(a) = θ₀ is a natural number.
5. Approximate tangent space (parent Step 9). Let f ∈ C_c(ℝ^P), F(r) := ∫_{blowUpMap a r '' M}f dHⁿ and L₀ := ∫_Qf dHⁿ. Since 𝓝[>]0 is countably generated, by Filter.tendsto_of_subseq_tendsto it suffices that every sequence r_j tending to 0 within (0, ∞) has a subsequence along which F → L₀. Given such (r_j), choose j₀ with r_j > 0 for all j ≥ j₀ and apply the claim to λ_i := r_{i+j₀} (positive, tending to 0): a strictly increasing φ and an orthonormal v' with ζ₀(β) = β(v') for all β and F(λ_{φ(k)}) → ∫_{span v'}f dHⁿ. Since β(v') = ζ₀(β) = β(v) for all β, step 2 gives span v' = Q. Thus F(r_{φ(k)+j₀}) → L₀ along the index map k ↦ φ(k) + j₀. Hence F(r) → L₀ as r → 0⁺ for every f ∈ C_c(ℝ^P), which together with finrank Q = n is HasApproximateTangentSpaceAt n M a Q. With step 4, Q has all the asserted properties. ∎

## Key steps

1. Plane uniqueness: β(v) = β(v') for all n-covectors forces span v = span v' (compare the vectors determined by w ↦ (w^♭∧α)(v) and test with α = β_{v^{(i)}}).
2. For any blow-up sequence, (BL) gives a limit C = θ(a)ζ(a)ν with ISP; LD_{P,d} applied to (θ(a)ν, ζ(a)) gives the lower density of ν.
3. (CP) makes ν a finite sum of parallel planes with ζ(a) = evaluation on v; (WG) gives every weight ≥ 1, so ν = Hⁿ⌞span v; (PI) gives θ(a) ∈ ℕ.
4. Plane uniqueness and the subsequence criterion give HasApproximateTangentSpaceAt n M a (span v) and the unit orientation.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (identical)`
- `grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div|theorem ae_tendsto_average_norm_sub' mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean; grep -n 'def vitaliFamily|theorem tendsto_filterAt' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; grep -n 'theorem exists_disjoint_subfamily_covering_enlargement' mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean; grep -n 'theorem tendsto_of_subseq_tendsto' mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean (all found)`
- `grep -n 'def GeometricCurrentOn.massOn|def GeometricCurrentOn.mass|theorem GeometricCurrentOn.massOn_mono' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (mass = massOn U; massOn monotone)`
- `python3 -I over dag.json: status, candidate commit and accepted-candidate.json mtime of every reused name and of the twins cbr_ci_*/dmcbr_ci_* (good_points, blowup_limit, pointwise and their sub-lemmas); lean_name collision scan for dtc_bc_tc_cl_ci_* (no match)`
- `git show <candidate>:GMT/Ch07/Submission.lean | grep '^theorem Submission.' for 5ab64315, dccef30a, 0d17fe48, 64b1a25a, 12814c0b, 1acc4c76, 6f17e241, e548bab6, 2a731a5a, 77a22fd9 (history contents of the reused and twin candidates)`
- `sed of /runtime/flows/gmt-claude-73516a26825a/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _decompose, _overlay_accepted_children, _install_parent_supplied_child_handoff), store.py (refresh, update, ensure), leaf_verification.py (check_source_delta), inherited.py`
- `lake env lean /tmp/ci_dec_v2/lean/Types.lean (12 frozen child types, only sorry warnings); /tmp/ci_dec_v2/lean/Assembly.lean (parent type from 4 child + 4 dependency types; #print axioms: propext, Classical.choice, Quot.sound); /tmp/ci_dec_v2/lean/ChildChain.lean (good_points and pointwise drafts compile from stubbed accepted types); /tmp/ci_dec_v2/hb/HB_GP.lean, HB_DB.lean, HB_RB.lean, HB_PW.lean (#count_heartbeats of the accepted proofs to be inlined)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on all 12 lean_statements (all valid)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-f25b09cc66/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-73516a26825a/_recursive_lean/runtime.py`
- `/tmp/ci_dec_v2/lean/Assembly.lean`
- `/tmp/ci_dec_v2/lean/ChildChain.lean`
- `/tmp/ci_dec_v2/lean/Types.lean`

The snapshot (local-project; project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean and Submission.lean byte-identical to the workspace. It contains no proved closure, density or tangent-plane theorem. Every Mathlib lemma named in the child proofs exists in the snapshot: Besicovitch differentiation (Besicovitch.vitaliFamily, tendsto_filterAt, VitaliFamily.ae_tendsto_lintegral_enorm_sub_div), Vitali.exists_disjoint_subfamily_covering_enlargement and tendsto_of_subseq_tendsto. SimonGMT's Mass.lean gives mass = massOn U and massOn_mono, which the parent assembly uses. The nine reused declarations are accepted in dag.json with candidate commits and byte-identical frozen types, all accepted before the current validator snapshot. The three new names are unused in dag.json, and their types equal the frozen types of the twins cbr_ci_ae_good_points, cbr_ci_blowup_limit and cbr_ci_pointwise_tangent_integer, none of which was accepted in that snapshot. Lean confirms that the 12 types elaborate, that the parent type follows from them and the four dependency types with standard axioms only, and that each new leaf follows, by the twins' compiled drafts, from its siblings and accepted Lean text within the default heartbeat limit.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
