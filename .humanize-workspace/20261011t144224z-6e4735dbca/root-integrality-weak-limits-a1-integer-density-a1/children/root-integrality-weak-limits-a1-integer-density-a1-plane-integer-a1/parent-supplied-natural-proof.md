# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 5–8 of the parent proof, which are the printed displays (8)–(10) of the Proof of 8.2 (pp. 178–179) with the documented corrections. The final BV step is the top-dimensional case (Remark 3.12): hypothesis (TOP), followed by the sibling ind_const_multiple_integer. Here Y_k plays the role of η_{x,λ_k#}T_{j(k)}, and c[[Q]] that of σθ(x)[[L_0]].

Two presentational changes from the parent proof, neither changing the argument:
- No rotation Q_0. We work with the plane Q = span τ itself, the distance d to Q and the coordinates p with respect to τ.
- The localized currents live on the bounded cylinder W′ = {|p| < 1, d < 3/4} rather than on the infinite cylinder Ω = B_1ⁿ × ℝ^{P−n}. Their supports lie in {d ≤ γ} with γ < 3/4, so they are the restrictions to W′ of the printed Ω-currents.

Hypotheses.
- (ST) SlicingTheorem and (LPF) LipschitzPushforwardIntegerMultiplicity.
- (RWL), (SPF), (TOP): the frozen Lean types of iwl_restriction_weak_limit, iwl_smooth_pushforward and iwl_top_dim_integrality, exactly as they appear as antecedents of this theorem.
- τ : Fin n → ℝ^P orthonormal, n := m + 1, and c ∈ ℝ.
- Y_k ∈ D_n(ℝ^P) integer multiplicity with ∂Y_k = 0 and C_0 := sup_k M_B(Y_k) < ∞, where B := B_2(0) ⊆ ℝ^P.
- Y_k(ω) → c∫_Q ω(z)(τ) dHⁿ(z) for every ω ∈ D^n(ℝ^P) with tsupport ω ⊆ B, where Q := span τ and Hⁿ := μHE[n].
Goal: c ∈ ℤ.

Conventions.
- V := B_1(0) ⊆ ℝⁿ = Eucl n, and e := (e_1, …, e_n), e_i := EuclideanSpace.single i 1.
- M_W(·) := massOn W, and "i.m." means IsIntegerMultiplicity.
- (R1), (R2) denote the uniqueness and mass-measure/restriction parts of the comparator-accepted declaration Submission.iwl_restriction_theory.

0. Geometry.
 (0a) The coordinate map. p : ℝ^P → ℝⁿ, p(y) := (⟪τ_1,y⟫, …, ⟪τ_n,y⟫), packaged as a continuous linear map, e.g. (EuclideanSpace.equiv _ ℝ).symm ∘L ContinuousLinearMap.pi (fun i => innerSL ℝ (τ i)). It is C^∞ with fderiv ℝ p y = p. By Bessel's inequality (Mathlib Orthonormal.sum_inner_products_le) ‖p(y)‖ ≤ ‖y‖, so ‖p‖ ≤ 1 (opNorm_le_bound). Also p(τ_i) = e_i.
 (0b) The distance to Q. π(y) := Σ_i ⟪τ_i,y⟫τ_i ∈ Q and d(y) := ‖y − π(y)‖.
  - y − π(y) ⊥ Q, so ‖y‖² = ‖π(y)‖² + d(y)², and ‖π(y)‖ = ‖p(y)‖.
  - d is 1-Lipschitz: d(y) − d(y′) ≤ ‖(y − y′) − π(y − y′)‖ ≤ ‖y − y′‖. It is continuous, and it vanishes on Q because π(z) = z for z ∈ Q = span τ. Q is a finite-dimensional subspace, hence closed and measurable.
  - Hence ‖fderiv ℝ d y‖ ≤ 1 for every y (Mathlib norm_fderiv_le_of_lipschitz; fderiv = 0 where d is not differentiable).
 (0c) The parametrization of Q. ι : ℝⁿ → ℝ^P, ι(a) := Σ_i a_i τ_i, is a linear isometry with range Q, and p∘ι = id. By Mathlib Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ∫_Q h dHⁿ = ∫_{ℝⁿ} h(ι(a)) da for every h : ℝ^P → ℝ, with Lebesgue measure da. In particular Hⁿ(Q ∩ K) < ∞ for bounded K, so Hⁿ⌞Q is locally finite.
 (0d) The cylinder. W′ := {y : ‖p(y)‖ < 1, d(y) < 3/4}.
  - W′ is open and bounded, since ‖y‖² < 1 + 9/16.
  - closure W′ ⊆ {‖p(y)‖ ≤ 1, d(y) ≤ 3/4} ⊆ B̄_{5/4}(0) ⊆ B, so W′ ⊂⊂ B (CompactlyContainedOpen W′ B), and p(W′) ⊆ V.
  - For γ < 3/4 and compact K ⊆ V, the set K′ := p⁻¹(K) ∩ {d ≤ γ} is closed and bounded (‖y‖² ≤ 1 + γ²), hence compact, and K′ ⊆ W′.

1. The limit currents.
 (1a) X(ω) := c∫_Q ω(z)(τ) dHⁿ(z) defines a current X ∈ D_n(B).
  - Hⁿ⌞Q is finite on compact sets (IsFiniteMeasureOnCompacts), by (0c). So z ↦ ω(z)(τ), continuous with compact support, is Hⁿ⌞Q-integrable, and X is linear.
  - If ω_i → 0 in D^n(B), the supports lie in one compact K ⊆ B. The k = 0 clause of TestFormOnConverges together with norm_iteratedFDeriv_zero gives sup_z‖ω_i(z)‖ → 0. Hence |X(ω_i)| ≤ |c|·Hⁿ(Q ∩ K)·sup_z‖ω_i(z)‖ → 0, using |α(τ)| ≤ ‖α‖∏_j‖τ_j‖ = ‖α‖.
 (1b) Let μ_Q := Hⁿ⌞Q and let v(z) := c·simpleNVector τ (constant). For ω ∈ D^n(B), z ↦ v(z)(ω(z)) = c·ω(z)(τ) is continuous with compact support, hence μ_Q-integrable by (0c), and its integral is X(ω). So (μ_Q, v) is a measure representation of X (IsMeasureRepresentation X μ_Q v).
 (1c) Likewise S′(ω) := c∫_V ω(a)(e) da defines a current S′ ∈ D_n(V), by the same argument with Lebesgue measure on ℝⁿ.

2. Restriction of the domain to B. Let X_k := Y_k.restrictDomain (B ⊆ ℝ^P) ∈ D_n(B), so X_k(ω) = Y_k(ω).
 (2a) X_k ⇀ X in B, by the convergence hypothesis (tsupport ω ⊆ B).
 (2b) M_W(X_k) ≤ M_W(Y_k) ≤ C_0 for W ⊆ B: an admissible form for X_k gives an admissible form for Y_k with the same value.
 (2c) ∂X_k = 0, since ∂X_k(ω) = Y_k(dω) = ∂Y_k(ω) = 0.
 (2d) X_k is i.m. Write Y_k = τ(M_k, θ_k, ξ_k) with a rectifiable triple in ℝ^P and θ_k ∈ ℕ on M_k.
  - For ω ∈ D^n(B), ω = 0 off B, so X_k(ω) = tauAction(M_k ∩ B, θ_k, ξ_k)(ω). This uses Mathlib setIntegral_eq_of_subset_of_ae_sdiff_eq_zero, which needs only that M_k is null-measurable, together with the vanishing of the integrand on M_k ∖ B.
  - (M_k ∩ B, θ_k, ξ_k) is a rectifiable triple in B with integer θ_k: subset, null-measurability, countable rectifiability (mono), positivity, integrability on compact K ⊆ B (⊆ M_k ∩ K) and AE-strong measurability are inherited.
  - The orients property at a.e. y ∈ M_k ∩ B is inherited as well. B is open, y ∈ B, and (M_k ∩ B) Δ M_k does not meet B. So by the comparator-accepted declaration Submission.br_weightedTangent_congr (V := B, θ′ := θ_k), every weighted approximate tangent space of (M_k, θ_k) at y is one of (M_k ∩ B, θ_k).
  - Equivalently, (2d) is an instance of the comparator-accepted Submission.br_restrictDomain_isIntegerMultiplicity: restrictDomain to an open set preserves integer multiplicity.

3. Slicing (parent Step 5). For each k apply (ST) with U := B, T := X_k, f := d and L := 1. The hypotheses hold: for W ⊂⊂ B, M_W(X_k) ≤ C_0 < ∞ and M_W(∂X_k) = 0; and d is 1-Lipschitz. This gives slices S^k_t ∈ D_m(B), t ∈ ℝ, with the following properties.
 (3a) Slices are boundaries. IsSlice X_k d t S^k_t: there are restrictions A^k_t of X_k and Bc^k_t of ∂X_k = 0 to {y ∈ B : d(y) < t} with S^k_t = ∂A^k_t − Bc^k_t. That set is measurable: this is the first component of the IsRestriction for Bc^k_t, and also follows since the set is open. The zero current has the measure representation (0, 0), through which 0 is a restriction of the zero current to every measurable set. By (R1), Bc^k_t = 0, so S^k_t = ∂A^k_t.
 (3b) Mass bound. By (R2) there are a restriction R^k of X_k to the open set {y ∈ B : 1/4 < d(y) < 1/2} and a measure μ_k with IsMassMeasure X_k μ_k; note M_W(X_k) < ∞ for W ⊂⊂ B. Apply the slicing mass bound with W := W′ (open, ⊆ B), L_W := 1 (allowed by (0b)) and (a, b) := (1/4, 1/2). It gives a measurable g_k : ℝ → [0, ∞] with M_{W′}(S^k_t) ≤ g_k(t) for t ∈ (1/4, 1/2) and
  ∫⁻_{(1/4,1/2)} g_k ≤ M_{W′}(R^k) = μ_k(W′ ∩ {1/4 < d < 1/2}) ≤ μ_k(W′) = M_{W′}(X_k) ≤ C_0,
 by the mass identity of (R2) and IsMassMeasure, since W′ ⊂⊂ B. The slicing clause needs the derivative bound in the form ∀ᵐ y ∂volume, y ∈ W′ → ‖fderiv ℝ d y‖₊ ≤ 1. It holds for every y by norm_fderiv_le_of_lipschitz with constant 1, coerced to ℝ≥0.
 (The slices are also i.m. for a.e. t, but this is not needed below.)

4. Restriction limits (parent Step 5). Apply (RWL) with U := B, the sequence (X_k)_k, the limit X, W := W′ and φ := d. Its hypotheses hold: X_k ⇀ X by (2a), W′ is open and ⊆ B, sup_k M_{W′}(X_k) ≤ C_0 < ∞, and d is continuous. It gives a strictly increasing ψ and a countable E ⊆ ℝ with the following property: for every s ∉ E and all restrictions R_j of X_{ψ(j)} and R of X to {y ∈ B : d(y) < s}, R_j(ω) → R(ω) for every ω ∈ D^n(B) with tsupport ω ⊆ W′.

5. Choice of γ.
 (5a) By Fatou (Mathlib lintegral_liminf_le), ∫⁻_{(1/4,1/2)} liminf_k g_{ψ(k)} ≤ liminf_k ∫⁻_{(1/4,1/2)} g_{ψ(k)} ≤ C_0 < ∞. Hence liminf_k g_{ψ(k)}(t) < ∞ for a.e. t ∈ (1/4, 1/2).
 (5b) Existence of γ.
  - t ↦ liminf_k g_{ψ(k)}(t) is measurable (Measurable.liminf), and its lower integral over (1/4,1/2) is finite. So it is < ∞ for (volume⌞(1/4,1/2))-a.e. t (ae_lt_top).
  - E is countable, hence Lebesgue-null.
  - volume⌞(1/4,1/2) is not the zero measure, so a property holding for a.e. t under it holds for some t.
  Hence there is γ ∈ (1/4, 1/2) ∖ E with G₀ := liminf_k g_{ψ(k)}(γ) < ∞.
 (5c) By Filter.frequently_lt_of_liminf_lt, infinitely many k satisfy g_{ψ(k)}(γ) < G₀ + 1 =: G. So there is a strictly increasing σ with g_{ψ(σ(k))}(γ) ≤ G for all k (Mathlib Filter.extraction_of_frequently_atTop).
 (5d) Put κ := ψ∘σ, A_γ := {y ∈ B : d(y) < γ} (open) and R_k := A^{κ(k)}_γ from (3a). R_k is a restriction of X_{κ(k)} to A_γ, with ∂R_k = S^{κ(k)}_γ and M_{W′}(∂R_k) ≤ g_{κ(k)}(γ) ≤ G.

6. Properties of R_k (parent Steps 5 and 6(a)–(d)).
 (6a) X is a restriction of itself to A_γ. A_γ is measurable (open). With the representation (1b), ∫_{A_γ} v(ω) dμ_Q = ∫ v(ω) dμ_Q = X(ω) for ω ∈ D^n(B). Indeed μ_Q-a.e. z lies in Q (Q is closed; ae_restrict_mem), and every z ∈ Q ∖ A_γ lies outside B (d(z) = 0 < γ), where ω(z) = 0.
 (6b) Convergence. Apply step 4 with s := γ ∉ E to the restrictions R′_j := A^{ψ(j)}_γ of X_{ψ(j)} (from (3a)) and R := X (by (6a)). It gives R′_j(ω) → X(ω) for every ω ∈ D^n(B) with tsupport ω ⊆ W′. Along the subsequence σ, R_k(ω) = R′_{σ(k)}(ω) → X(ω).
 (6c) Mass. By the mass identity of (R2) for X_{κ(k)}, M_{W′}(R_k) = μ_{κ(k)}(W′ ∩ A_γ) ≤ μ_{κ(k)}(W′) = M_{W′}(X_{κ(k)}) ≤ C_0.
 (6d) Formula. Write X_{κ(k)} = τ(M′_k, θ′_k, ξ′_k) on D^n(B), with M′_k ⊆ B (step 2).
  - (Hⁿ⌞M′_k, θ′_kξ′_k) is a measure representation of X_{κ(k)}: for ω ∈ D^n(B), x ↦ θ′_k(x)ξ′_k(x)(ω(x)) is Hⁿ⌞M′_k-integrable (comparator-accepted Submission.ltg_tau_integrable) with integral X_{κ(k)}(ω).
  - R_k is given by some representation (μ₁, v₁) of X_{κ(k)}. The comparator-accepted declaration Submission.slicing_representation_unique says that two representations agreeing on all ω ∈ D^n(B) have equal integrals over every measurable set, for all such ω. With W := B and A := A_γ it gives
   R_k(ω) = ∫_{A_γ} θ′_kξ′_k(ω) d(Hⁿ⌞M′_k) = tauAction(M′_k ∩ A_γ, θ′_k, ξ′_k)(ω) for all ω ∈ D^n(B).
 (6e) Vanishing. If ω ∈ D^n(B) vanishes on A_γ, then R_k(ω) = 0 by (6d). In particular R_k(ω) = 0 whenever tsupport ω ⊆ {d > γ}.

7. Localization to W′ (parent Step 6, with W′ in place of Ω). Let Z_k := R_k.restrictDomain (W′ ⊆ B) ∈ D_n(W′).
 (7a) Z_k is i.m.
  - By (6d), Z_k = τ(M′_k ∩ A_γ ∩ W′, θ′_k, ξ′_k) on D^n(W′), since forms in D^n(W′) vanish off W′.
  - The triple is rectifiable in W′ with integer multiplicity: subset, null-measurability, countable rectifiability, positivity, integrability on compact K ⊆ W′ (a compact subset of B) and measurability are inherited.
  - Orients property at a.e. y ∈ M′_k ∩ A_γ ∩ W′: the open set A_γ ∩ W′ contains y and does not meet (M′_k ∩ A_γ ∩ W′) Δ M′_k. So Submission.br_weightedTangent_congr transfers the weighted tangent spaces of (M′_k, θ′_k) at y.
  - Equivalently: the same argument with the open set A_γ shows that R_k = τ(M′_k ∩ A_γ, θ′_k, ξ′_k) is i.m. on B. Then Z_k = R_k.restrictDomain is i.m. by Submission.br_restrictDomain_isIntegerMultiplicity.
 (7b) M_{W″}(Z_k) ≤ M_{W′}(R_k) ≤ C_0 for every W″: an admissible form for Z_k on W″ is admissible for R_k on W′; then use (6c).
 (7c) ∂Z_k = (∂R_k)|_{W′} = S^{κ(k)}_γ|_{W′}, so M_{W″}(∂Z_k) ≤ M_{W′}(S^{κ(k)}_γ) ≤ G for every W″ (5d).
 (7d) Z_k(ω) = R_k(ω) → X(ω) for every ω ∈ D^n(W′), by (6b).
 (7e) spt Z_k ⊆ W′ ∩ {d ≤ γ}. Every y ∈ W′ with d(y) > γ has a ball around it whose closure lies in the open set W′ ∩ {d > γ}. Z_k vanishes on all forms supported in that ball, by (6e). So y lies in the zero region of Z_k.

8. Projection (parent Step 7). For each k apply (SPF), with (LPF), to U := W′, V := B_1(0) ⊆ ℝⁿ, X := Z_k (i.m. by (7a)) and f := p. Its hypotheses hold:
 - p is C^∞ (linear) and p(W′) ⊆ V (0d).
 - Properness. Let K ⊆ V be compact and K′ := p⁻¹(K) ∩ {d ≤ γ}, compact and ⊆ W′ by (0d). Since spt Z_k = W′ ∖ zeroRegion(Z_k) ⊆ {d ≤ γ} (7e) and K′ ⊆ W′, we get p⁻¹(K) ∩ spt Z_k = K′ ∩ (zeroRegion Z_k)ᶜ. This is a closed subset (GeometricCurrentOn.isOpen_zeroRegion) of the compact set K′, hence compact.
 (SPF) gives i.m. currents S′_k ∈ D_n(V) such that:
 (8a) S′_k(ω) = Z_k(η) whenever η ∈ D^n(W′) agrees with p^#ω, (p^#ω)(y) = ω(p(y))∘p, on an open N ⊇ spt Z_k;
 (8b) for every W″ ⊆ ℝⁿ, with c := 1 ≥ ‖fderiv p‖: M_{W″}(S′_k) ≤ M_{p⁻¹(W″)∩W′}(Z_k) ≤ C_0 and M_{W″}(∂S′_k) ≤ M_{p⁻¹(W″)∩W′}(∂Z_k) ≤ G.
 Hence sup_k (M_{W″}(S′_k) + M_{W″}(∂S′_k)) ≤ C_0 + G < ∞ for every W″.

9. The limit of S′_k (parent Step 7). Fix ω ∈ D^n(V), let K := tsupport ω (a compact subset of V) and let K′ be as in (0d).
 (9a) Cutoff (smooth Urysohn lemma).
  - Choose δ > 0 with cthickening (2δ) K′ ⊆ W′ (Mathlib IsCompact.exists_cthickening_subset_open).
  - Apply Mathlib exists_contDiff_zero_iff_one_iff_of_isClosed to the disjoint closed sets s := (thickening (2δ) K′)ᶜ and t := cthickening δ K′. It gives ζ ∈ C^∞(ℝ^P) with values in [0, 1], ζ = 1 exactly on t and ζ = 0 exactly on s.
  - Put N₀ := thickening δ K′, an open set containing K′ with ζ = 1 on N₀.
  - tsupport ζ ⊆ cthickening (2δ) K′, which is compact and contained in W′.
  - Put η := ζ·p^#ω. It is smooth with tsupport η ⊆ tsupport ζ, so η ∈ D^n(W′).
 (9b) Agreement near the support. N := N₀ ∪ (W′ ∖ p⁻¹(K)) is open. It contains spt Z_k ⊆ W′ ∩ {d ≤ γ} (7e): if p(y) ∈ K then y ∈ K′ ⊆ N₀. On N₀, η = p^#ω; on W′ ∖ p⁻¹(K), p^#ω = 0 = η.
 (9c) By (8a) and (7d), S′_k(ω) = Z_k(η) → X(η) = c∫_Q ζ(z)·ω(p(z))(pτ_1, …, pτ_n) dHⁿ(z).
 (9d) For z ∈ Q we have pτ_i = e_i. Either p(z) ∉ K, so ω(p(z)) = 0, or z ∈ K′ (since d(z) = 0 ≤ γ), so ζ(z) = 1. Hence, using (0c), p∘ι = id, and ω = 0 off V,
  X(η) = c∫_Q ω(p(z))(e) dHⁿ(z) = c∫_{ℝⁿ} ω(a)(e) da = c∫_V ω(a)(e) da = S′(ω).
 Thus S′_k ⇀ S′ in V.

10. Top-dimensional integrality (parent Step 8). Apply (TOP) with m, U := V (open), T_j := S′_k (i.m.) and T := S′ (by (1c)). Its hypotheses are the bound of step 8 and S′_k ⇀ S′ (step 9). It gives: S′ is i.m.

11. Conclusion. Apply the sibling ind_const_multiple_integer with U := V = B_1(0) ⊆ ℝ^{m+1} (open and nonempty), X := S′ (i.m.) and S′(ω) = c∫_V ω(a)(e) da. It gives c = k for some k ∈ ℤ. ∎

Accepted declarations used (reuse by name, identical frozen type): Submission.iwl_restriction_theory, Submission.br_weightedTangent_congr (or Submission.br_restrictDomain_isIntegerMultiplicity), Submission.slicing_representation_unique, Submission.ltg_tau_integrable. Sibling: ind_const_multiple_integer. The unaccepted parent-level results iwl_restriction_weak_limit, iwl_smooth_pushforward and iwl_top_dim_integrality enter only as the hypotheses (RWL), (SPF) and (TOP).

## Key steps

1. Geometry: coordinates p (‖p‖ ≤ 1, pτ_i = e_i), the 1-Lipschitz distance d to Q, the isometry ι : ℝⁿ → Q, and the cylinder W′ ⊂⊂ B_2(0).
2. Limit currents X = c[[Q]] on B and S′ = c[[B_1ⁿ]] on V; (Hⁿ⌞Q, c·simpleNVector τ) represents X.
3. X_k := Y_k|_B are i.m. cycles with M_W(X_k) ≤ C_0 and X_k ⇀ X.
4. SlicingTheorem with f = d: slices = ∂(X_k⌞{d<t}) by (R1), with ∫⁻_{(1/4,1/2)} M_{W′}(slice) ≤ C_0.
5. Hypothesis (RWL) and Fatou give γ ∈ (1/4,1/2) and a subsequence with X_{κ(k)}⌞{d<γ} → X on forms in W′ and boundary masses ≤ G.
6. Z_k := (X_{κ(k)}⌞{d<γ})|_{W′} are i.m. with M + M(∂) bounded, spt Z_k ⊆ {d ≤ γ} and Z_k ⇀ X|_{W′}.
7. Hypothesis (SPF) with f = p gives S′_k := p_#Z_k ∈ D_n(B_1ⁿ), i.m. with bounded M + M(∂); S′_k ⇀ S′ via a cutoff ζ and the isometry ι.
8. Hypothesis (TOP) gives S′ i.m., and ind_const_multiple_integer gives c ∈ ℤ.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical; imports Densities, Rectifiable, Mass, FormsDuality, CurrentLocalEquality only)`
- `python3 scans of dag.json: lean_name/status/depends_on of all nodes (262 now); no ind_* names; statuses of iwl_*, br_weightedTangent_congr, br_restrictDomain_isIntegerMultiplicity, cmb_*, rectifiability_density_comparison, slicing_representation_unique, ltg_tau_integrable, lpf_wtc_blowup_setIntegral_image, fiw_ims_tt_unit_bound`
- `grep -n 'def \|theorem ' simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward,FormsDuality,FormSupNorm}.lean`
- `sed -n 1,130p; 270,370p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasWeightedApproximateTangentSpaceAt)`
- `grep dimensionalUpperDensity|dimensionalDensityQuotient|realUnitBallVolume|simon_theorem_4_16_compact_metrizable|finiteMeasure_tendsto_subseq_of_compact_metrizable|simon_theorem_3_3 simongmt/Poincare/SimonGMT/Chapter01`
- `grep -rn ae_tendsto_average_norm_sub|Besicovitch.tendsto_filterAt|vitaliFamily mathlib/Mathlib/MeasureTheory/Covering`
- `grep -n euclideanHausdorffMeasure_homothety_image|euclideanHausdorffMeasure_smul₀|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|Isometry.map_euclideanHausdorffMeasure mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn isCompact_setOfPred_finiteMeasure_le_of_isCompact|FiniteMeasure.limsup_measure_closed_le_of_tendsto|lintegral_liminf_le|IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|norm_fderiv_le_of_lipschitz|AlternatingMap.eq_smul_basis_det|exists_contDiff_zero_iff_one_iff_of_isClosed|IsCompact.exists_cthickening_subset_open|setIntegral_eq_of_subset_of_ae_sdiff_eq_zero|extraction_of_frequently_atTop|frequently_lt_of_liminf_lt|OrthonormalBasis.det_to_matrix_orthonormalBasis_real|MeasurableEmbedding.integrable_map_iff|aestronglyMeasurable_iUnion_iff|ae_restrict_iff'₀ mathlib/Mathlib`
- `sed -n 2400,2500p book/chapter-06.txt (printed Proof of 8.2, displays (7)-(10))`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') + lean_contract.validate_lean_statement on the 7 child statements`
- `lake env lean /tmp/ind-decomp-scratch/{Stmts,ScopeCheck,Assembly}.lean (#print axioms IndAssemblyCheck.parent)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ind-decomp-scratch/Stmts.lean`
- `/tmp/ind-decomp-scratch/ScopeCheck.lean`
- `/tmp/ind-decomp-scratch/Assembly_checked.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 Contract and a byte-identical Submission. Its imports are Mass, FormsDuality, CurrentLocalEquality, Densities and Rectifiable, but not AffineCurrentPushforward. So no child statement mentions affinePushforward; the child ind_rescaled_current states the push-forward through its action on pulled-back test forms.

Scratch Lean checks of the frozen project:
- All 7 child statements pass the comparator's validate_lean_statement and elaborate in the contract_scope replay at main_theorem.
- `exact Submission.<name>` resolves for each child.
- IndAssemblyCheck.parent derives the exact frozen iwl_integer_density type from the child types plus the frozen types of iwl_restriction_weak_limit, iwl_smooth_pushforward and iwl_top_dim_integrality. Its only axioms are propext, Classical.choice and Quot.sound.

SimonGMT supplies GeometricCurrentOn.affinePushforward (with boundary_affinePushforward, affinePullbackForm_isTestForm, TestFormOnConverges.affinePullback), restrictDomain, massOn_mono and le_massOn, blowUpMap, the definition of HasWeightedApproximateTangentSpaceAt, dimensionalUpperDensity with realUnitBallVolume, and finiteMeasure_tendsto_subseq_of_compact_metrizable / simon_theorem_4_16_compact_metrizable.

Mathlib supplies Besicovitch.vitaliFamily, VitaliFamily.ae_tendsto_average_norm_sub, Besicovitch.tendsto_filterAt, euclideanHausdorffMeasure_homothety_image, euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure, FiniteMeasure.limsup_measure_closed_le_of_tendsto, lintegral_liminf_le, IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, norm_fderiv_le_of_lipschitz, AlternatingMap.eq_smul_basis_det, exists_contDiff_zero_iff_one_iff_of_isClosed, IsCompact.exists_cthickening_subset_open, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero and extraction_of_frequently_atTop. Mathlib proves metrizability of the weak topology only for probability measures.

Accepted DAG declarations reused by the child proofs: iwl_restriction_theory, rectifiability_density_comparison, br_weightedTangent_congr, br_restrictDomain_isIntegerMultiplicity, cmb_exists_countable_dense_testForms, cmb_abs_apply_le_of_massOn_le, slicing_representation_unique, ltg_tau_integrable and lpf_wtc_blowup_setIntegral_image. iwl_restriction_weak_limit, iwl_smooth_pushforward and iwl_top_dim_integrality are unaccepted and enter only as hypotheses.

The printed Proof of 8.2 (book chapter-06 lines 2400–2500) matches the supplied Step 11. No ind_* names exist in the DAG or the libraries. These checks do not certify the analytic child proofs.
