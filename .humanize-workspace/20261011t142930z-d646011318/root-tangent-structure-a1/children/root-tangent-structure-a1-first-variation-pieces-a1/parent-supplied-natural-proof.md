# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1`
- Child DAG node: `root.tangent_structure-a1.first_variation_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, steps 7–10 (Simon Ch. 4, 2.1–2.2 with the area formula of Ch. 3 §2, 2.4–2.5, and the computation of Ch. 2 §5, 5.2–5.3). The parent's references to its steps 4–6 ("T_i(x) = T_x for Hⁿ-a.e. x ∈ M_i", "x ↦ p_x is μ-a.e. strongly measurable", "dim T_x = n a.e.") are replaced by the hypotheses of this theorem (step 0 below). No errata apply.

Conventions. n ≥ 1, ℓ ≥ 0; E := Ambient n ℓ; ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ; Hⁿ := μHE[n]; B_ρ(z) := closedBall z ρ. a = (M, θ) is an admissible pair (IsRectifiablePair: M countably n-rectifiable and Hⁿ-null-measurable, θ > 0 on M, θ integrable on M ∩ K for every compact K), V := mk a, μ := V.weight, T_x := V.tangentSpace x, p_x := T_x.starProjection, div_M X(x) := V.tangentialDiv X x = trace(DX(x) ∘ p_x). For a subspace P ⊆ E with inclusion ι_P and Λ ∈ L(E, E) put J^P(Λ) := normDet(Λ ∘ ι_P) ≥ 0 (Mathlib LinearMap.normDet of Λ.domRestrict P); for an orthonormal basis e_1, …, e_k of P, J^P(Λ)² = det[⟨Λe_a, Λe_b⟩]_{a,b≤k} (Mathlib LinearMap.normDet_sq_eq_det_gram), J^{0}(Λ) = 1, and J^P(Λ)² = det S_P(Λ) with S_P(Λ) := p_P Λ*Λ p_P + I − p_P ∈ L(E, E) (Λ* = ContinuousLinearMap.adjoint Λ). Proof of the last identity: take an orthonormal basis e_1, …, e_{n+ℓ} of E with e_1, …, e_k a basis of P and e_{k+1}, …, e_{n+ℓ} a basis of P^⊥ (k = dim P). Since p_P is self-adjoint, p_Pe_a = e_a for a ≤ k and p_Pe_b = 0 for b > k, the matrix ⟨S_P(Λ)e_a, e_b⟩ has entries ⟨Λe_a, Λe_b⟩ for a, b ≤ k, entries δ_{ab} for a, b > k, and 0 in the mixed blocks (for a ≤ k < b: ⟨p_PΛ*Λe_a, e_b⟩ = ⟨Λ*Λe_a, p_Pe_b⟩ = 0 and ⟨S_P(Λ)e_b, e_a⟩ = ⟨Λ*Λp_Pe_b, p_Pe_a⟩ + ⟨e_b − p_Pe_b, e_a⟩ = 0 + ⟨e_b, e_a⟩ = 0); hence det S_P(Λ) = det[⟨Λe_a, Λe_b⟩]_{a,b≤k} = J^P(Λ)² by LinearMap.normDet_sq_eq_det_gram (for k = 0 both sides are 1). Consequently J^P(Λ) = (det S_P(Λ))^{1/2} is a continuous function of the pair (Λ, p_P) (polynomial in the entries, followed by the square root of a nonnegative number). For G: ℝⁿ → E, JG(v) := (fderiv ℝ G v).normDet (SimonGMT Chapter02.areaJacobianAt).
Hypotheses: (h1) N₀ ⊆ E Borel with Hⁿ(N₀) = 0; (h2) for each i ∈ ℕ, (C_i, F_i) is a Lipschitz piece: C_i ⊆ ℝⁿ compact, F_i: ℝⁿ → E Lipschitz, F_i differentiable at each w ∈ C_i with injective DF_i(w), DF_i continuous on C_i, c_i|v − w| ≤ |F_i(v) − F_i(w)| on C_i with c_i > 0; (h3) M ⊆ N₀ ∪ ⋃_i F_i(C_i); (h4) for Hⁿ-a.e. x ∈ M: for all i and all w ∈ C_i with F_i(w) = x, T_x = range DF_i(w); (h5) x ↦ p_x is a.e.-strongly measurable for Hⁿ⌞M; (h6) IsCompactVariation φ ε K: ε > 0, K compact, Φ(t, y) := φ t y is C^∞ on U := (−ε, ε) × E, for t ∈ (−ε, ε) φ_t := φ t is bijective with C^∞ inverse Function.invFun φ_t, φ_0 = id, and φ_t(y) = y for t ∈ (−ε, ε), y ∉ K. X(y) := deriv (t ↦ φ t y) 0.
Results used (pinned; standard axioms only): (R2a) SimonGMT Chapter02.weighted_area_formula_lipschitz_injOn (∫⁻_{G(B)} u dHⁿ = ∫⁻_B ofReal(JG(v))·u(G(v)) dLⁿ(v) for Lipschitz G, Borel B, G injective on B, any u: E → [0, ∞]); (R2b) SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn; Mathlib LinearMap.normDet_comp (normDet(Λ ∘ A') = normDet(Λ restricted to range A')·normDet(A'); also SimonGMT Chapter02.areaJacobian_comp_eq_parametrization_mul_tangential), LinearMap.normDet_sq_eq_det_gram, ContDiffAt.isSymmSndFDerivAt (symmetry of second derivatives), hasDerivAt_integral_of_dominated_loc_of_deriv_le (differentiation under the integral sign), lintegral_iUnion₀, integral_withDensity_eq_integral_toReal_smul₀, ofReal_integral_eq_lintegral_ofReal, withDensity_absolutelyContinuous, AEStronglyMeasurable.mono_ac, LinearMap.finrank_range_of_inj.

Proof.

0. Consequences of the hypotheses.
(0a) For Hⁿ-a.e. x ∈ M, dim T_x = n: Hⁿ-a.e. x ∈ M lies outside N₀ (h1), hence (h3) x = F_i(w) for some i and w ∈ C_i; by (h4) T_x = range DF_i(w), whose dimension is dim ℝⁿ = n because DF_i(w) is injective (LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin).
(0b) μ = (Hⁿ⌞M).withDensity(ofReal ∘ θ) (definition of the weight on the class mk a). θ is a.e.-strongly measurable for Hⁿ⌞M (it is integrable on each M ∩ B_k(0)); μ(S) = ∫⁻_{M∩S} ofReal θ dHⁿ for Borel S, so μ is finite on compact sets; μ ≪ Hⁿ⌞M (withDensity_absolutelyContinuous); and for every Borel S and every g: E → ℝ, ∫_S g dμ = ∫_{M∩S} gθ dHⁿ (integral_withDensity_eq_integral_toReal_smul₀ — no integrability assumption is needed — together with (ofReal θ(z)).toReal = θ(z) for z ∈ M, which holds Hⁿ⌞M-a.e. by ae_restrict_mem₀).
(0c) By (h5) and μ ≪ Hⁿ⌞M, x ↦ p_x is also μ-a.e. strongly measurable (AEStronglyMeasurable.mono_ac).

1. The variation (parent step 7).
(a) Φ is C^∞ on the open set U. X(y) = DΦ(0, y)(1, 0) (chain rule for t ↦ (t, y)), so X is C^∞ on E. For y ∉ K, Φ(t, y) = y for all t ∈ (−ε, ε), hence X(y) = 0; since E ∖ K is open (K is compact, hence closed), DX = 0 on E ∖ K, and therefore div_M X(x) = trace(0 ∘ p_x) = 0 for every x ∉ K.
(b) Let t ∈ (−ε, ε). φ_t = Φ(t, ·) is C^∞, bijective, with C^∞ inverse ψ_t := Function.invFun φ_t, which is a two-sided inverse (Function.leftInverse_invFun / rightInverse_invFun for the bijection φ_t). Differentiating ψ_t ∘ φ_t = id gives Dψ_t(φ_t(y)) ∘ Dφ_t(y) = I, so Dφ_t(y) is invertible for every y; φ_t is a homeomorphism. On the open set E ∖ K, φ_t = id, so Dφ_t(y) = I there; y ↦ Dφ_t(y) is continuous, hence bounded on K, so sup_y ‖Dφ_t(y)‖ < ∞ and φ_t is Lipschitz (mean value inequality on the convex set E). By (R2b), Hⁿ(φ_t(Z)) = 0 whenever Hⁿ(Z) = 0; images of Borel sets under the homeomorphism φ_t are Borel. Consequently φ_t maps Hⁿ-null-measurable sets to Hⁿ-null-measurable sets (a null-measurable set is a Borel set plus a subset of a null set).
(c) The partial derivative (t, y) ↦ Dφ_t(y) is C^∞ on U, and by the symmetry of the second derivative of Φ at (0, y) (ContDiffAt.isSymmSndFDerivAt), ∂_t Dφ_t(y)|_{t=0} = D_y(∂_tΦ(0, ·))(y) = DX(y). Also Dφ_0(y) = I since φ_0 = id.

2. Area formula on M (parent step 8; Simon Ch. 3, 2.4–2.5). For t ∈ (−ε, ε) and x ∈ E let J_t(x) := J^{T_x}(Dφ_t(x)). Claim: imageMass a φ_t K = ∫⁻_{M∩K} ofReal(θ(x)·J_t(x)) dHⁿ(x).
(2.1) By definition imageMass a φ_t K = ∫⁻_{φ_t(M∩K)} u_t dHⁿ with u_t(y) := ofReal(θ(ψ_t(y))), and u_t(φ_t(x)) = ofReal(θ(x)).
(2.2) Decomposition. Let D_i := F_i(C_i) ∖ (N₀ ∪ ⋃_{j<i} F_j(C_j)) (Borel: the F_j(C_j) are compact) and M_i := M ∩ K ∩ D_i (Hⁿ-null-measurable). The M_i are pairwise disjoint and, by (h3), M ∩ K = (M ∩ K ∩ N₀) ∪ ⋃_i M_i. As φ_t is injective, φ_t(M ∩ K) = φ_t(M ∩ K ∩ N₀) ∪ ⋃_i φ_t(M_i) with pairwise disjoint pieces; by 1(b) they are Hⁿ-null-measurable and Hⁿ(φ_t(M ∩ K ∩ N₀)) = 0. By countable additivity of the lintegral over disjoint null-measurable sets (lintegral_iUnion₀) and since null sets do not contribute:
imageMass a φ_t K = Σ_i ∫⁻_{φ_t(M_i)} u_t dHⁿ and ∫⁻_{M∩K} ofReal(θJ_t) dHⁿ = Σ_i ∫⁻_{M_i} ofReal(θJ_t) dHⁿ.
It therefore suffices to prove ∫⁻_{φ_t(M_i)} u_t dHⁿ = ∫⁻_{M_i} ofReal(θJ_t) dHⁿ for each i.
(2.3) Fix i. Choose a Borel set A with M_i ⊆ A ⊆ D_i and Hⁿ(A ∖ M_i) = 0 (a Borel hull of the null-measurable M_i, intersected with the Borel D_i). Let B := C_i ∩ F_i⁻¹(A): B is Borel, F_i(B) = A (A ⊆ F_i(C_i)), and F_i is injective on B (by the lower bound on C_i). Let ψ_i: F_i(C_i) → C_i be the inverse of F_i on C_i and, for y ∈ F_i(C_i), T_i(y) := range DF_i(ψ_i(y)).
(2.4) G := φ_t ∘ F_i is Lipschitz (composition of Lipschitz maps) and injective on B. For v ∈ B, F_i is differentiable at v and φ_t is differentiable at F_i(v), so DG(v) = Dφ_t(F_i(v)) ∘ DF_i(v) (chain rule), and by LinearMap.normDet_comp (normDet(Λ ∘ A') = J^{range A'}(Λ)·normDet(A')),
JG(v) = J^{range DF_i(v)}(Dφ_t(F_i(v)))·JF_i(v) = J^{T_i(F_i(v))}(Dφ_t(F_i(v)))·JF_i(v).
(2.5) Define h: E → [0, ∞] by h(y) := ofReal(J^{T_i(y)}(Dφ_t(y)))·u_t(φ_t(y)) for y ∈ F_i(C_i) and h(y) := 0 otherwise. Applying (R2a) to G on B and then to F_i on B (no measurability of the integrands is needed):
∫⁻_{φ_t(A)} u_t dHⁿ = ∫⁻_{G(B)} u_t dHⁿ = ∫⁻_B ofReal(JG(v))·u_t(G(v)) dv = ∫⁻_B ofReal(JF_i(v))·h(F_i(v)) dv = ∫⁻_{F_i(B)} h dHⁿ = ∫⁻_A h dHⁿ,
using ofReal(αβ) = ofReal(α)ofReal(β) for α, β ≥ 0 and (2.4).
(2.6) Since Hⁿ(A ∖ M_i) = 0 and, by 1(b), Hⁿ(φ_t(A ∖ M_i)) = 0, we get ∫⁻_{φ_t(M_i)} u_t dHⁿ = ∫⁻_{φ_t(A)} u_t dHⁿ and ∫⁻_A h dHⁿ = ∫⁻_{M_i} h dHⁿ. For Hⁿ-a.e. x ∈ M_i we have x = F_i(ψ_i(x)) with ψ_i(x) ∈ C_i, so (h4) gives T_x = range DF_i(ψ_i(x)) = T_i(x), and then h(x) = ofReal(J_t(x))·ofReal(θ(x)) = ofReal(θ(x)J_t(x)) (θ(x) > 0, J_t(x) ≥ 0). Hence ∫⁻_{φ_t(M_i)} u_t dHⁿ = ∫⁻_{M_i} ofReal(θJ_t) dHⁿ, and summing over i (2.2) proves the claim.

3. The Jacobian (parent step 9; Simon Ch. 2, 5.2–5.3).
(3.1) On the compact set [−ε/2, ε/2] × K the maps (t, y) ↦ Dφ_t(y), ∂_tDφ_t(y) and Dφ_t(y)⁻¹ are continuous (1(b), 1(c); inversion is continuous on invertible operators), hence bounded in operator norm by some Λ_1 ≥ 1.
(3.2) Fix x ∈ K and an n-dimensional subspace P with orthonormal basis e_1, …, e_n. For t ∈ (−ε, ε) let Gram_t := [⟨Dφ_t(x)e_a, Dφ_t(x)e_b⟩]_{a,b=1}^n, so J^P(Dφ_t(x)) = (det Gram_t)^{1/2} (LinearMap.normDet_sq_eq_det_gram). By 1(c), t ↦ Gram_t is C¹, Gram_0 = I, and ∂_tGram_t|_{t=0} = [⟨DX(x)e_a, e_b⟩ + ⟨e_a, DX(x)e_b⟩]_{a,b}, whose trace is 2Σ_a⟨DX(x)e_a, e_a⟩ = 2·trace(DX(x) ∘ p_P) (compute the trace of DX(x) ∘ p_P in an orthonormal basis of E extending (e_a): p_P fixes the e_a and kills the other basis vectors).
(3.3) For |t| ≤ ε/2: ⟨Gram_t ξ, ξ⟩ = |Dφ_t(x)(Σ_a ξ_a e_a)|² ≥ Λ_1⁻²|ξ|², so the symmetric matrix Gram_t is positive definite, det Gram_t > 0, ‖Gram_t⁻¹‖ ≤ Λ_1², ‖Gram_t‖ ≤ Λ_1², ‖∂_tGram_t‖ ≤ 2Λ_1², and det Gram_t ≤ ‖Gram_t‖ⁿ ≤ Λ_1^{2n}. Jacobi's formula: writing det(G + H) = det G·det(I + G⁻¹H) and expanding det(I + Y) = 1 + trace Y + O(|Y|²) by the Leibniz formula, d/dt det Gram_t = det Gram_t·trace(Gram_t⁻¹∂_tGram_t). Since det Gram_t > 0, t ↦ J^P(Dφ_t(x)) = (det Gram_t)^{1/2} is differentiable on (−ε/2, ε/2) with
∂_tJ^P(Dφ_t(x)) = ½·J^P(Dφ_t(x))·trace(Gram_t⁻¹∂_tGram_t);
at t = 0 this equals ½·trace(∂_tGram_t|_{t=0}) = trace(DX(x) ∘ p_P). Using |trace Y| ≤ n‖Y‖ for n×n matrices: |∂_tJ^P(Dφ_t(x))| ≤ ½·Λ_1ⁿ·n·Λ_1²·2Λ_1² = nΛ_1^{n+4} =: C_1, uniformly for |t| < ε/2, x ∈ K and n-dimensional P. Also 0 ≤ J^P(Dφ_t(x)) ≤ Λ_1ⁿ.
(3.4) Measurability. For each t ∈ (−ε, ε), x ↦ J_t(x) = (det(p_x Dφ_t(x)*Dφ_t(x) p_x + I − p_x))^{1/2} is a continuous function of (Dφ_t(x), p_x); x ↦ Dφ_t(x) is continuous and x ↦ p_x is a.e.-strongly measurable for Hⁿ⌞M (h5), so x ↦ J_t(x) is a.e.-strongly measurable for Hⁿ⌞M. Likewise x ↦ div_M X(x) = trace(DX(x) ∘ p_x) is a.e.-strongly measurable for Hⁿ⌞M and (0c) for μ; it vanishes off K (1(a)) and |div_M X(x)| ≤ (n + ℓ)·sup_K‖DX‖ (|trace Y| ≤ dim E·‖Y‖, ‖p_x‖ ≤ 1), so it is μ-integrable (μ(K) < ∞).

4. Conclusion (parent step 10).
(4.1) For |t| < ε/2 put m(t) := ∫_{M∩K} θ(x)J_t(x) dHⁿ(x). By (0a) and (3.3), for Hⁿ-a.e. x ∈ M ∩ K, 0 ≤ J_t(x) ≤ Λ_1ⁿ; θ is integrable on M ∩ K; so θJ_t is integrable on M ∩ K with nonnegative values, and by step 2 and ofReal_integral_eq_lintegral_ofReal, imageMass a φ_t K = ofReal(m(t)) < ∞. Hence (imageMass a (φ t) K).toReal = m(t) for |t| < ε/2.
(4.2) Differentiation under the integral sign (hasDerivAt_integral_of_dominated_loc_of_deriv_le, on the ball |t| < ε/2 and the measure Hⁿ⌞(M ∩ K)): for each such t the integrand x ↦ θ(x)J_t(x) is a.e.-strongly measurable (3.4) and θJ_0 = θ is integrable (J_0 = J^{T_x}(I) = 1); for Hⁿ-a.e. x ∈ M ∩ K (those with dim T_x = n, (0a)) the map t ↦ θ(x)J_t(x) is differentiable at every t with |t| < ε/2, with derivative θ(x)∂_tJ_t(x) bounded by C_1θ(x) (an integrable bound) by (3.3) with P = T_x, and its derivative at t = 0 is θ(x)·trace(DX(x) ∘ p_x) = θ(x)·div_M X(x), which is a.e.-strongly measurable. Therefore m has derivative ∫_{M∩K} θ·div_M X dHⁿ at t = 0.
(4.3) By (0b) with S = K and since div_M X = 0 off K (1(a)) and is μ-integrable (3.4): ∫_{M∩K} θ·div_M X dHⁿ = ∫_K div_M X dμ = ∫ div_M X dμ = ∫ V.tangentialDiv X x dμ_V(x).
(4.4) The function t ↦ (imageMass a (φ t) K).toReal coincides with m on the neighbourhood (−ε/2, ε/2) of 0 (4.1), so it has the same derivative at 0 (HasDerivAt.congr_of_eventuallyEq): HasDerivAt (fun t ↦ (imageMass a (φ t) K).toReal) (∫ x, (mk a).tangentialDiv (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∂(mk a).weight) 0. ∎

Implementation note (not part of the argument): the statement elaborates with the frozen imports; the proof needs, e.g., Mathlib.Analysis.InnerProductSpace.NormDet, Mathlib.Analysis.InnerProductSpace.Adjoint, Mathlib.Analysis.Calculus.ParametricIntegral, Mathlib.Analysis.Calculus.FDeriv.Symmetric and Poincare.SimonGMT.Chapter02.AreaLipschitz (built in the pinned packages); the frozen child types elaborate unchanged with them. Natural sub-lemmas for a further split are step 2 (area formula for φ_t on M) and steps 3–4 (Jacobian derivative and differentiation under the integral sign).

## Key steps

1. From the hypotheses: dim T_x = n Hⁿ-a.e. on M, μ_V = θHⁿ⌞M ≪ Hⁿ⌞M, and x ↦ p_{T_x} is μ_V-a.e. strongly measurable
2. Variation facts: X is smooth, X = DX = div_M X = 0 off K; φ_t is a Lipschitz homeomorphism with invertible Dφ_t; ∂_tDφ_t|_{t=0} = DX
3. Area formula through the disjointified pieces and normDet_comp: imageMass a φ_t K = ∫⁻_{M∩K} ofReal(θ J^{T_x}(Dφ_t(x))) dHⁿ
4. Jacobi's formula: ∂_tJ^{T_x}(Dφ_t(x))|_{t=0} = trace(DX(x)∘p_x), with a uniform bound C_1 on [−ε/2, ε/2] × K
5. Differentiation under the integral sign, dominated by C_1θ, then ∫_{M∩K} θ div_M X dHⁿ = ∫ div_M X dμ_V

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD`
- `grep -n 'HasWeightedApproximateTangentSpaceAt\|def CountablyRectifiable\|def blowUpMap' -r .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/`
- `grep -n '^theorem\|^def' Chapter04/{WeightedBlowUp,TangentDensity,FirstVariation,Basic}.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|euclideanHausdorffMeasure_image_le_of_lipschitzOn|ae_dimensionalUpperDensity_eq_zero_outside|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|exists_isClosed_continuousOn_of_measurable|areaJacobian_comp_eq_parametrization_mul_tangential|def areaJacobianAt|planeMeasure_unit_closedBall|hausdorff_blowUp_image' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'continuous.*normDet|measurable_areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem .*[Ll]usin|lusin' <snapshot>/mathlib/Mathlib`
- `rg -n 'measure_eq_zero_iff_ae_notMem|ofReal_le_enorm|Regular.smul|exists_isClosed_sdiff_lt' <snapshot>/mathlib/Mathlib`
- `grep -rn 'InnerProductSpace.volume_closedBall|hasDerivAt_integral_of_dominated_loc_of_deriv_le|isSymmSndFDerivAt|inverse_continuousAt|normDet_comp|def normDet|euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem integral_withDensity_eq_integral_toReal_smul₀' <snapshot>/mathlib/Mathlib`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-ts-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-ts-decomp/olean lean /tmp/ch04-ts-decomp/{T0,T1,T5}.lean (statement-scope availability of LinearMap.range/normDet/adjoint; instance #synth)`
- `python3 /tmp/ch04-ts-decomp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/ch04-ts-decomp/gen/Challenge_*.lean`
- `lean /tmp/ch04-ts-decomp/T6.lean (parent assembly from sorry'd children and sibling)`
- `lake env lean /tmp/ch04-ts-decomp/Axioms.lean (#print axioms of the cited lemmas)`
- `lean /tmp/ch04-ts-decomp/gen2/WithImports.lean /tmp/ch04-ts-decomp/gen2/Synth.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/CantorScheme.lean`
- `/tmp/ch04-ts-decomp/T6.lean`
- `/tmp/ch04-ts-decomp/Axioms.lean`
- `/tmp/ch04-ts-decomp/gen2/WithImports.lean`

Contract and pinned packages:
- The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean.
- SimonGMT is at the pinned revision 2b3663083f3fe399b6296fb8eaee52169170e197.

What can appear in a child type:
- In the frozen statement scope (`import GMT.Ch04.Submission` plus the contract opens), LinearMap.normDet, ContinuousLinearMap.adjoint and LinearMap.adjoint are unknown constants. So no child type mentions Jacobians or adjoints.
- `LinearMap.range (fderiv ℝ F w)` does not elaborate; `LinearMap.range (fderiv ℝ F w).toLinearMap` does, and the child types use that form.

Lusin's theorem:
- The snapshot Mathlib has no Lusin theorem: `rg 'theorem .*[Ll]usin'` only hits a docstring in Topology/MetricSpace/CantorScheme.lean.
- SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable is cited instead.

Cited library results — each exists with the stated meaning, and #print axioms shows only propext, Classical.choice, Quot.sound:
- SimonGMT Chapter04: map_inverse_blowUp_carrier, hausdorff_blowUp_image, planeMeasure_unit_closedBall, tangentDensityCutoff_eq_one, RectifiableVarifold.integral_weighted_blowUp.
- SimonGMT Chapter02: continuous_normDet, measurable_areaJacobianAt, weighted_area_formula_lipschitz_injOn, euclideanHausdorffMeasure_image_le_of_lipschitzOn, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, areaJacobian_comp_eq_parametrization_mul_tangential.
- SimonGMT Chapter01: exists_isClosed_continuousOn_of_measurable, ae_dimensionalUpperDensity_eq_zero_outside, measure_toOuterMeasure_isBorelRegular.
- SimonGMT Chapter03: regular_euclideanHausdorffMeasure_restrict_submodule, support_euclideanHausdorffMeasure_restrict_submodule.
- Mathlib: Besicovitch.ae_tendsto_measure_inter_div, Measure.ext_of_integral_eq_on_compactlySupported, hasDerivAt_integral_of_dominated_loc_of_deriv_le, ContDiffAt.isSymmSndFDerivAt, NormedRing.inverse_continuousAt, InnerProductSpace.volume_closedBall, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, LinearMap.normDet_sq_eq_det_gram, LinearMap.normDet_comp, MeasurableSet.exists_isClosed_sdiff_lt, Measure.Regular.smul.
- integral_withDensity_eq_integral_toReal_smul₀ is a root-namespace lemma in MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean.

Elaboration checks:
- All seven child types pass the verifier's validate_lean_statement.
- Each compiles as a comparator-generated NodeChallenge file, with only the expected sorry warning.
- They still elaborate when the implementation imports are added, with the same instances; for example, volume on EuclideanSpace stays measureSpaceOfInnerProductSpace.

Parent assembly:
- T6.lean declares the seven children and the sibling rectifiable_lipschitz_piece_cover as sorry'd theorems, then gives a full proof of Submission.tangent_structure_first_variation with exactly the frozen type.
- It compiles with only the eight sorry warnings.
