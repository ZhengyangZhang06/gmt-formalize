# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6–8 of the parent proof. This is the comparison (8)–(9) in Simon's proof of 7.2.4 (chapter-07.txt lines 222–246), with the competitor projected into N by π (README erratum 5, N_i = N). It uses Simon Ch. 6, 2.23–2.24 and 3.3–3.9 for push-forward (chapter-06.txt lines 408–440 and 763–860); Ch. 3, 1.2–1.6 and 2.3–2.6 (C¹ covers of rectifiable sets, approximate tangent spaces, area formula; chapter-03.txt lines 1–143 and 330–410); (C1); and the siblings int_combination and tangent_locality.
Correction of Simon 3.9, used in step 5(c): the multiplicity N of f_#τ(M, θ, ξ) in 3.8 is only a non-negative integer, because oppositely oriented sheets with the same image cancel. For example, an oriented rectangle boundary projected onto a line has zero push-forward, although its image has positive H¹-measure. So Simon's triple (f(M), ζ, N) need not have positive multiplicity on its carrier, as IMRep.mult_pos requires. Step 5(c) chooses Borel versions and restricts the carrier to {N ≥ 1}.
Notation: F := B̄_t(y), G := B_{3ρ}(y), Λ := 1 + 3cρ, μ_Z := μ_{RZ}, μ_Y := μ_{RY}. Write RZ = (M_Z, θ_Z, ξ_Z), RY = (M_Y, θ_Y, ξ_Y), and fix a representation RX = (M_X, θ_X, ξ_X) of X. Dπ(x) is the Fréchet derivative (fderiv) of π at x, and ‖·‖ is the operator norm.
Multilinear algebra:
- For an n-covector α and a linear map L, α∘L is the covector (v₁, …, vₙ) ↦ α(Lv₁, …, Lvₙ).
- An n-vector is a linear functional ζ on n-covectors (MultiVector), and (∧ₙL)ζ is the n-vector α ↦ ζ(α∘L).
- For increasing I = (i₁ < ⋯ < iₙ), dx^I is the coordinate covector (v₁, …, vₙ) ↦ det[(v_j)_{i_k}], and e_I := (e_{i₁}, …, e_{iₙ}). Then α = Σ_I α(e_I)dx^I, and the coordinates ζ(dx^I) determine ζ.
- |α|_E := (Σ_I α(e_I)²)^{1/2} is the Euclidean coefficient norm used in M_W, and |ζ| := (Σ_I ζ(dx^I)²)^{1/2}.
- A unit orientation of an n-dimensional subspace Π is an n-vector ζ with ζ(α) = ±α(σ₁, …, σₙ) for all α, for an orthonormal basis σ of Π (IsUnitOrientationOf).
Four facts are used below.
 (L1) |α(v₁, …, vₙ)| ≤ |α|_E·Π_j|v_j|. This follows from α(v) = Σ_I α(e_I)det[(v_j)_I], Cauchy–Schwarz, Cauchy–Binet (Σ_I det[(v_j)_I]² = det(v_i·v_j)) and Hadamard (det(v_i·v_j) ≤ Π_j|v_j|²). Also |α(v)| ≤ ‖α‖·Π_j|v_j| for the operator norm ‖α‖.
 (L2) A unit orientation ζ of Π has |ζ| = 1, by Cauchy–Binet. For every n-vector ζ, |ζ(α)| ≤ |ζ||α|_E, by Cauchy–Schwarz in the coordinates.
 (L3) Two unit orientations of the same Π differ by a sign: orthonormal bases of Π differ by an orthogonal matrix O, and α(σO) = det(O)α(σ) with det(O) = ±1.
 (L4) Let ζ(α) = ±α(τ₁, …, τₙ) for an orthonormal basis τ of an n-plane P₀, and let L be linear. Then (∧ₙL)ζ(α) = ±α(Lτ₁, …, Lτₙ) and |(∧ₙL)ζ| = det(Lτ_i·Lτ_j)^{1/2} ≤ ‖L‖ⁿ. If |(∧ₙL)ζ| = 0, then (∧ₙL)ζ = 0. If |(∧ₙL)ζ| > 0, then L is injective on P₀ and L(P₀) is an n-plane. Writing Lτ_j = Σ_l B_{lj}σ_l for an orthonormal basis σ of L(P₀) gives (∧ₙL)ζ(α) = ±det(B)α(σ) with |det B| = |(∧ₙL)ζ|. So (∧ₙL)ζ/|(∧ₙL)ζ| is a unit orientation of L(P₀).
If t < 0 then F = ∅ and the claim is trivial, so assume t ≥ 0. Then F ⊆ B_{2ρ}(y) ⊆ G, and Ḡ = B̄_{3ρ}(y) ⊆ B_r(y) ∩ U is compact.
1. Lipschitz bounds and π(F).
 (a) For 0 < s < r the closed ball B̄_s(y) ⊆ B_r(y) is convex, π is differentiable on it, and ‖Dπ‖ ≤ 1 + cs there. By the mean value inequality (Mathlib Convex.norm_image_sub_le_of_norm_fderiv_le), |π(x) − π(x')| ≤ (1 + cs)|x − x'| for x, x' ∈ B̄_s(y). In particular π is Λ-Lipschitz on B̄_{2ρ}(y), since 2ρ < r and 1 + 2cρ ≤ Λ. Hence Hⁿ(π(A)) ≤ ΛⁿHⁿ(A) for every A ⊆ B̄_{2ρ}(y).
 (b) π(y) = y, since y ∈ N ∩ B_r(y).
 (c) For x ∈ F: |π(x) − y| ≤ (1 + ct)t ≤ (1 + 2cρ)t < (3/2)(2ρ) = 3ρ, using 4cρ ≤ 1. Also π(x) ∈ N, since F ⊆ B_r(y). So K' := π(F) is a compact subset of N ∩ G ⊆ U.
 (d) Let p₀ be the nearest point projection of ℝ^P onto the closed convex ball B̄_{2ρ}(y); it is 1-Lipschitz. Then π̃ := π∘p₀ is Λ-Lipschitz on ℝ^P and agrees with π on B̄_{2ρ}(y) ⊇ F.
2. Consequences of (C1).
 (a) μ_X(ℝ^P ∖ F) = 0. U ∖ F is open, and X vanishes on every form admissible for M_{U∖F}(X), since such a form has support disjoint from F. So μ_X(U ∖ F) = M_{U∖F}(X) = 0, and μ_X(ℝ^P ∖ U) = 0. Since θ_X ≥ 1, Hⁿ(M_X ∖ F) = 0.
 (b) μ_Z(U ∖ N) = 0. By (C1), U ∩ spt μ_Z = spt Z ⊆ N. So U ∖ N ⊆ ℝ^P ∖ spt μ_Z, which is μ_Z-null (Mathlib measure_compl_support). Hence Hⁿ(M_Z ∖ N) = 0.
 (c) For every open V ⊆ U ∖ F we have Y(ω) = Z(ω) + X(ω) = Z(ω) when spt ω ⊆ V. Hence μ_Y(V) = M_V(Y) = M_V(Z) = μ_Z(V).
 (d) μ_Z(G) = M_G(Z) < ∞, μ_Y(G) < ∞ and ∫_{M_X∩F} θ_X dHⁿ < ∞. These follow from local integrability on the compact sets Ḡ ⊆ U and F ⊆ U.
3. Tangent inclusion. Claim: for Hⁿ-a.e. x ∈ M_Z, x ∈ N, T_xM_Z =: Q exists, ξ_Z(x) orients Q, and Q ⊆ tangentSpace N x. The first three hold a.e. by 2(b) and the IMRep property. Fix such an x, a chart ψ : V → W of N at x with x = ψ(v_x), and put L := range Dψ(v_x).
 (a) L ⊆ tangentSpace N x. Let w ∈ ℝ^d and choose δ > 0 with B̄_δ(v_x) ⊆ V. Let κ(s) := (δ/(1 + |w|)) tanh(s(1 + |w|)/δ). Then γ(s) := ψ(v_x + κ(s)w) is C¹ on ℝ, γ(ℝ) ⊆ ψ(V) ⊆ N, γ(0) = x and γ'(0) = Dψ(v_x)w.
 (b) Flatness of N at x. ψ|_V is a homeomorphism onto N ∩ W and Dψ(v_x) is injective. So for z ∈ N near x, z = ψ(v) with v near v_x, |v − v_x| ≤ C|z − x|, and dist(z − x, L) = o(|z − x|) as z → x.
 (c) Q ⊆ L. Suppose p ∈ Q ∖ L. Choose δ' > 0 with B_{3δ'}(p) ∩ L = ∅. By (b), for small λ > 0 every z ∈ N with (z − x)/λ ∈ B_{δ'}(p) has dist((z − x)/λ, L) < δ', which is impossible. So η_{x,λ}(N) ∩ B_{δ'}(p) = ∅, and η_{x,λ}(M_Z) ∩ B_{δ'}(p) ⊆ η_{x,λ}(M_Z ∖ N), an Hⁿ-null set.
 (d) Contradiction. Take f ∈ C_c(ℝ^P) with 0 ≤ f ≤ 1, f = 1 on B_{δ'/2}(p) and spt f ⊆ B_{δ'}(p). Then ∫_{η_{x,λ}(M_Z)} f dHⁿ = 0 for small λ, whereas its limit must be ∫_Q f dHⁿ ≥ Hⁿ(Q ∩ B_{δ'/2}(p)) > 0. Hence Q ⊆ L ⊆ tangentSpace N x.
4. π fixes Z. For Hⁿ-a.e. x ∈ M_Z ∩ G we have x ∈ N ∩ B_r(y) and π(x) = x. Write ξ_Z(x)(α) = ±α(τ) with τ an orthonormal basis of Q ⊆ tangentSpace N x. Then Dπ(x)τᵢ = τᵢ, so ξ_Z(x)(α∘Dπ(x)) = ξ_Z(x)(α) for every n-covector α. In particular ξ_Z(x)(ω(x)) = ξ_Z(x)(ω(π(x))∘Dπ(x)) for ω ∈ 𝒟ⁿ(U).
5. The projected cycle Q_π := π_#X. Define Q_π(ω) := ∫_{M_X∩F} θ_X ξ_X(ω(π(x))∘Dπ(x)) dHⁿ(x) for ω ∈ 𝒟ⁿ(U). This is Simon 2.24(2), 3.3–3.6 for the C¹ map π, which is proper on the compact F; μ_X is carried by F by 2(a).
 (a) Current. The integrand is Hⁿ⌞(M_X ∩ F)-a.e. strongly measurable, since x ↦ ω(π(x))∘Dπ(x) is continuous on B_r(y) ⊇ F. For Hⁿ-a.e. x ∈ M_X, ξ_X(x) is a unit orientation. So by (L1) and ‖Dπ‖ ≤ Λ on F, |ξ_X(x)(α∘Dπ(x))| ≤ ‖α‖Λⁿ. Hence |Q_π(ω)| ≤ Λⁿ·sup_x‖ω(x)‖·∫_{M_X∩F} θ_X dHⁿ, which is finite by 2(d). Q_π is linear. If ω_j → 0 in 𝒟ⁿ(U), then sup‖ω_j‖ → 0, so Q_π(ω_j) → 0. Thus Q_π is a GeometricCurrentOn U n.
 (b) Support. If ω ∈ 𝒟ⁿ(U) vanishes on K' = π(F), then Q_π(ω) = 0. Every z ∈ U ∖ K' has a ball B_s(z) whose closure is a compact subset of the open set U ∖ K'. Q_π vanishes on forms supported in B_s(z), so z lies in the zero region of Q_π. Hence spt Q_π ⊆ K'. As spt Q_π is relatively closed in U and contained in the compact K' ⊆ U, it is compact. It is contained in K' ⊆ (U ∩ N) ∩ G.
 (c) Integer multiplicity. We construct an IMRep R_Q = (C, N', ζ') in U representing Q_π. This is Simon 3.3–3.9 with the correction stated at the top.
  (c1) Set-up. Put M := M_X ∩ F and θ := θ_X. M is Borel and countably n-rectifiable, being a subset of M_X (SimonGMT CountablyRectifiable.mono). By 2(d), Hⁿ(M) ≤ ∫_M θ dHⁿ < ∞. Fix a Borel map ξ̃ : ℝ^P → Λ_n with ξ̃ = ξ_X Hⁿ-a.e. on M. Call x ∈ M oriented if T_xM exists and ξ̃(x) is a unit orientation of it. Hⁿ-a.e. x ∈ M is oriented: a.e. on M, T_xM_X exists and is oriented by ξ_X(x) = ξ̃(x) (IMRep), and tangent_locality with (A, B) = (M, M_X) gives T_xM = T_xM_X. Define the Borel function J(x) := |(∧ₙDπ(x))ξ̃(x)| on M. By (L4), at an oriented x, J(x) is the Jacobian J^M_π(x) of Simon Ch. 3, 2.3, and J(x) ≤ ‖Dπ(x)‖ⁿ ≤ Λⁿ. Let M₊ := {x ∈ M : J(x) > 0}, a Borel set. For x ∈ M ∖ M₊ the n-vector (∧ₙDπ(x))ξ̃(x) is 0, since its norm is 0.
  (c2) C¹ pieces on which π is injective. By Simon Ch. 3, Lemma 1.2 and Remark 1.3, M = ⋃_{j≥0} M_j disjointly, with M_j Borel, Hⁿ(M₀) = 0, and M_j ⊆ N_j for embedded C¹ n-submanifolds N_j (j ≥ 1). SimonGMT simon_remark_1_3 gives the disjoint Borel pieces: the N_j are Borel (SimonGMT measurableSet_of_isSimonSubmanifold), and a Borel null N₀ ⊇ M₀ exists because Hⁿ is Borel regular. By Remark 1.5(2), T_xM = T_xN_j for Hⁿ-a.e. x ∈ M_j.
   Let x₀ ∈ N_j ∩ B_{2ρ}(y) with Dπ(x₀) injective on T_{x₀}N_j. Take a C¹ parametrization φ of N_j near x₀, with φ(v₀) = x₀ and Dφ(v₀) an isomorphism onto T_{x₀}N_j. Then π∘φ is C¹ with injective derivative at v₀. By the inverse function theorem, in the form of the local immersion theorem (Simon Ch. 6, 3.4), there is an open set O ∋ x₀ with O ⊆ B_{2ρ}(y) such that:
   - π is injective on N_j ∩ O;
   - Σ := π(N_j ∩ O) is an embedded C¹ n-submanifold with Hⁿ(Σ) < ∞ (take N_j ∩ O = φ(V'') with V'' bounded, of compact closure in the domain of φ);
   - T_{π(z)}Σ = Dπ(z)(T_zN_j) for z ∈ N_j ∩ O.
   By Lindelöf's theorem, for each j countably many such O cover {x ∈ N_j ∩ B_{2ρ}(y) : Dπ(x) is injective on T_xN_j}. Enumerate all of them, over all j, as (j(k), O_k, Σ_k), k = 1, 2, …. Put A_k := (M₊ ∩ M_{j(k)} ∩ O_k) ∖ ⋃_{k'<k} A_{k'}; these are Borel and pairwise disjoint.
   Let x ∈ M₊ ∩ M_j (j ≥ 1) be oriented with T_xM = T_xN_j. Then Dπ(x) is injective on T_xN_j, by (L4) as J(x) > 0, and x ∈ F ⊆ B_{2ρ}(y); so x ∈ ⋃_k A_k. Hence Hⁿ(M₊ ∖ ⋃_k A_k) = 0. Moreover, π is injective on each A_k, π(A_k) ⊆ Σ_k, and Dπ(x)(T_xM) = T_{π(x)}Σ_k for Hⁿ-a.e. x ∈ A_k.
  (c3) Compact pieces and the image set. Hⁿ⌞M is a finite Borel measure on ℝ^P, hence inner regular. For each k choose compact sets K_{k,1}, K_{k,2}, … with K_{k,i} ⊆ A_k ∖ (K_{k,1} ∪ ⋯ ∪ K_{k,i−1}) and Hⁿ(A_k ∖ (K_{k,1} ∪ ⋯ ∪ K_{k,i})) < 2^{−i}. Enumerate all K_{k,i} as K₁, K₂, …; they are pairwise disjoint, with K_m ⊆ A_{k(m)}.
   Put M' := ⋃_m K_m ⊆ M₊, a Borel set with Hⁿ(M₊ ∖ M') = 0, and E := π(M') = ⋃_m π(K_m). Each π(K_m) is compact, so E is σ-compact, hence Borel. Also E ⊆ K' ⊆ G ⊆ U, E ⊆ ⋃_k Σ_k, and Hⁿ(E) ≤ ΛⁿHⁿ(M) < ∞ by 1(a). Since π|K_m is a continuous injection of a compact set, x_m := (π|K_m)⁻¹ : π(K_m) → K_m is continuous.
   Countable rectifiability: M ⊆ M₀'' ∪ ⋃_i F_i(ℝⁿ) with Hⁿ(M₀'') = 0 and F_i Lipschitz. So E ⊆ π̃(M) ⊆ π̃(M₀'') ∪ ⋃_i (π̃∘F_i)(ℝⁿ), where Hⁿ(π̃(M₀'')) = 0 by 1(d) and each π̃∘F_i is Lipschitz. Hence every subset of E is countably n-rectifiable.
   Call x ∈ M' good if x is oriented, x ∈ M_{j(k)} with T_xM = T_xN_{j(k)}, and Dπ(x)(T_xM) = T_{π(x)}Σ_k; here k := k(m) for the m with x ∈ K_m. By (c1) and (c2), Hⁿ(M' ∖ good) = 0.
  (c4) Area formula. Fix m. π is C¹, hence locally Lipschitz, on B_r(y) ⊇ K_m, and π is injective on K_m. By tangent_locality with (A, B) = (K_m, M), T_xK_m = T_xM for Hⁿ-a.e. x ∈ K_m; so the Jacobian J^{K_m}_π equals J Hⁿ-a.e. on K_m. Simon Ch. 3, 2.6 gives ∫_{K_m} hJ dHⁿ = ∫_{π(K_m)} h∘x_m dHⁿ for every Borel h ≥ 0. Sum over m, using monotone convergence (the K_m are disjoint and π is injective on each):
   (A) ∫_{M'} hJ dHⁿ = ∫ Σ_m 1_{π(K_m)}(w)·h(x_m(w)) dHⁿ(w) = ∫ Σ_{x∈π⁻¹(w)∩M'} h(x) dHⁿ(w).
   The integrand on the right is Borel. With h = θ, ∫ Σ_{x∈π⁻¹(w)∩M'} θ(x) dHⁿ(w) = ∫_{M'} θJ dHⁿ ≤ Λⁿ∫_M θ dHⁿ < ∞. So the Borel set E₁ := {w : Σ_{x∈π⁻¹(w)∩M'} θ(x) < ∞} satisfies Hⁿ(ℝ^P ∖ E₁) = 0. For w ∈ E₁ the fibre π⁻¹(w) ∩ M' is finite, as θ ≥ 1.
  (c5) The image integral. For x ∈ M' put ζ̂(x) := J(x)⁻¹(∧ₙDπ(x))ξ̃(x), and ζ̂(x) := 0 elsewhere. Then ζ̂ is Borel and |ζ̂(x)| = 1 on M'. By (L4), ζ̂(x) is a unit orientation of Dπ(x)(T_xM) at every good x.
   Define V(w) := Σ_{x∈π⁻¹(w)∩M'} θ(x)ζ̂(x) = Σ_m 1_{π(K_m)}(w)·θ(x_m(w))·ζ̂(x_m(w)) for w ∈ E₁, and V(w) := 0 for w ∉ E₁. The series converges absolutely on E₁, because |ζ̂(x)(dx^I)| ≤ 1. So each coordinate V(·)(dx^I) is Borel, and V is Borel.
   Let ω ∈ 𝒟ⁿ(U). For Hⁿ-a.e. x ∈ M we have ξ_X(x) = ξ̃(x), hence θ(x)ξ_X(x)(ω(π(x))∘Dπ(x)) = θ(x)((∧ₙDπ(x))ξ̃(x))(ω(π(x))). This is 0 on M ∖ M₊ by (c1), and equals θ(x)J(x)ζ̂(x)(ω(π(x))) on M'. By 2(a) and Hⁿ(M₊ ∖ M') = 0,
   Q_π(ω) = ∫_{M'} θ(x)J(x)ζ̂(x)(ω(π(x))) dHⁿ(x).
   Apply (A) to the positive and negative parts of h(x) := θ(x)ζ̂(x)(ω(π(x))). Both have finite integral against J, since |h| ≤ θ·sup_z|ω(z)|_E by (L2). On the fibre over w we have π(x) = w, so
   (B) Q_π(ω) = ∫ V(w)(ω(w)) dHⁿ(w).
  (c6) Tangent planes of the image. Fix k. Apply tangent_locality, with U := ℝ^P, to (A, B) = (E ∩ Σ_k, E) and to (A, B) = (E ∩ Σ_k, Σ_k). These sets are Borel (Σ_k is locally closed), and Hⁿ(E), Hⁿ(Σ_k) < ∞. The C¹ submanifold Σ_k has approximate tangent space T_wΣ_k at every w ∈ Σ_k, as in the proof of Simon Ch. 3, 1.6. So for Hⁿ-a.e. w ∈ E ∩ Σ_k, T_wE exists and equals T_wΣ_k.
   Let Bad_E be the union of three null sets: these countably many exceptional sets; ℝ^P ∖ E₁; and π(M' ∖ good), which is null by 1(a). Since E ⊆ ⋃_k Σ_k, for every w ∈ E ∖ Bad_E the approximate tangent space Π_w := T_wE exists, and Π_w = T_wΣ_k whenever w ∈ Σ_k.
  (c7) Integer multiplicity in the fibres (Simon 3.7–3.8). Let w ∈ E ∖ Bad_E, and fix a unit orientation ζ_w of Π_w. Every x ∈ π⁻¹(w) ∩ M' is good, since w ∉ π(M' ∖ good). If x ∈ K_m and k := k(m), then w = π(x) ∈ Σ_k, so Dπ(x)(T_xM) = T_wΣ_k = Π_w. By (c5) and (L3), ζ̂(x) = ε(x)ζ_w with ε(x) ∈ {1, −1}. Hence V(w) = m(w)ζ_w, where m(w) := Σ_{x∈π⁻¹(w)∩M'} ε(x)θ(x) ∈ ℤ is a finite sum (w ∈ E₁) and |m(w)| ≤ Σ_{x∈π⁻¹(w)∩M'} θ(x).
  (c8) Borel versions; restriction to positive multiplicity. Let ν(w) := |V(w)|, a Borel function. By (c7) and (L2), ν(w) = |m(w)| for w ∈ E ∖ Bad_E. Define:
   - the Borel function N' : ℝ^P → ℕ, N'(w) := ⌊ν(w) + 1/2⌋, so N'(w) = |m(w)| on E ∖ Bad_E;
   - the Borel map ζ' : ℝ^P → Λ_n, ζ'(w) := ν(w)⁻¹V(w) if ν(w) > 0, and ζ'(w) := 0 otherwise;
   - the carrier C := {w ∈ E : N'(w) ≥ 1}, a Borel set.
   For w ∈ C ∖ Bad_E: m(w) ≠ 0, ζ'(w) = sgn(m(w))ζ_w is a unit orientation of Π_w, and N'(w)ζ'(w) = m(w)ζ_w = V(w). For w ∈ E ∖ (C ∪ Bad_E): m(w) = N'(w) = 0, so V(w) = 0. Off E, V = 0. Hence V = 1_C·N'·ζ' Hⁿ-a.e. The points of E where Simon's multiplicity N = |m| vanishes are thus removed from the carrier.
  (c9) R_Q := (C, N', ζ') is an IMRep in U representing Q_π. We check each field.
   - measurableSet_carrier: C is Borel.
   - carrier_subset: C ⊆ E ⊆ U.
   - rectifiable: C ⊆ E is countably n-rectifiable by (c3).
   - measurable_mult: N' is Borel.
   - mult_pos: N' ≥ 1 on C, by the definition of C.
   - locallyIntegrable_mult: for compact K ⊆ U, ∫_{C∩K} N' dHⁿ ≤ ∫_{E∖Bad_E} |m| dHⁿ ≤ ∫ Σ_{x∈π⁻¹(w)∩M'} θ(x) dHⁿ(w) < ∞, by (c7) and (c4).
   - aestronglyMeasurable_orient: ζ' is Borel with values in the finite-dimensional space Λ_n, hence strongly measurable.
   - orients, on the smaller carrier: apply tangent_locality (U := ℝ^P) to (A, B) = (C, E). This is legitimate, as C ⊆ E are Borel and Hⁿ(E) < ∞. So for Hⁿ-a.e. w ∈ C, C and E have the same approximate tangent spaces at w. For such w outside Bad_E, T_wE = Π_w exists, hence T_wC = Π_w, and ζ'(w) is a unit orientation of Π_w by (c8). So for Hⁿ⌞C-a.e. w there is Q := Π_w with HasApproximateTangentSpaceAt n C w Q and IsUnitOrientationOf (ζ'(w)) Q.
   - Represents, with the action unchanged: for ω ∈ 𝒟ⁿ(U), the integrand N'ζ'(ω) is bounded by N'·sup|ω|_E, which is integrable on C. By (c8) and (B), ∫_C N'(w)ζ'(w)(ω(w)) dHⁿ(w) = ∫ V(w)(ω(w)) dHⁿ(w) = Q_π(ω).
   So Q_π is integer multiplicity.
 (d) ∂Q_π = 0. Fix r'' with t < r'' < 2ρ. Let η ∈ 𝒟^{n−1}(U), and fix χ ∈ C_c^∞(B_{r''}(y)) with χ = 1 near F. Let π_k := π * φ_{1/k} be standard mollifications; they only use the values of π on B_r(y). For large k they are smooth on a neighbourhood of B̄_{r''}(y), and π_k → π, Dπ_k → Dπ uniformly on B̄_{r''}(y), because π is C¹ on B_r(y) ⊋ B̄_{r''}(y). Then χπ_k^#η ∈ 𝒟^{n−1}(U), where (π_k^#η)(x) = η(π_k(x))∘Dπ_k(x), and d(χπ_k^#η) = dχ ∧ π_k^#η + χπ_k^#dη. Now ∂X = 0 gives X(d(χπ_k^#η)) = 0. Also X(dχ ∧ π_k^#η) = 0 by the vanishing hypothesis, since dχ = 0 near F. Hence X(χπ_k^#dη) = 0, i.e. ∫_{M_X∩F} θ_X ξ_X((dη)(π_k(x))∘Dπ_k(x)) dHⁿ = 0. As k → ∞ the integrands converge uniformly on F and are bounded by a constant multiple of θ_X. So Q_π(dη) = 0 by dominated convergence.
6. Competitor and minimality.
 (a) Let Z' := Z + Q_π ∈ 𝒟_n(U). It is integer multiplicity by int_combination, applied to RZ and the representation R_Q of 5(c) with (p₁, p₂) = (1, 1).
 (b) ∂Z' = ∂Z + ∂Q_π = ∂Z, i.e. SameBoundary Z' Z.
 (c) Z' − Z = Q_π, so spt(Z' − Z) = spt Q_π is a compact subset of (U ∩ N) ∩ G.
 (d) G is open and its closure B̄_{3ρ}(y) is a compact subset of U (CompactlyContained). Since Z is minimizing in U ∩ N, M_G(Z) ≤ M_G(Z').
7. Mass of the competitor. Let ω ∈ 𝒟ⁿ(U) with spt ω ⊆ G and |ω(x)|_E ≤ 1 for all x. Define the bounded Borel n-form φ(x) := ω(π(x))∘Dπ(x) for x ∈ G and φ(x) := 0 otherwise; it is supported in the compact Ḡ ⊆ U.
 (a) By step 4 and ω = 0 off G, Z(ω) = ∫_{M_Z} θ_Z ξ_Z(φ) dHⁿ.
 (b) By 2(a) and F ⊆ G, Q_π(ω) = ∫_{M_X} θ_X ξ_X(φ) dHⁿ.
 (c) Y = Z + X on 𝒟ⁿ(U). So the Λ_n-valued Radon measures θ_Yξ_YHⁿ⌞M_Y and θ_Zξ_ZHⁿ⌞M_Z + θ_Xξ_XHⁿ⌞M_X agree on smooth compactly supported forms. Smooth forms are uniformly dense in C_c(U; Λⁿ) (with supports in a fixed compact), and signed Radon measures are determined by C_c(U) (componentwise in the basis dx^I). Hence the two measures coincide and also agree on the bounded Borel form φ with compact support in U:
 Z'(ω) = Z(ω) + Q_π(ω) = ∫_{M_Y} θ_Y ξ_Y(φ) dHⁿ = ∫_{M_Y∩G} θ_Y ξ_Y(x)(ω(π(x))∘Dπ(x)) dHⁿ.
 (d) For Hⁿ-a.e. x ∈ M_Y, ξ_Y(x) = ±τ₁∧⋯∧τₙ with τ orthonormal. Then |ξ_Y(x)(α∘L)| = |α(Lτ₁, …, Lτₙ)| ≤ |α|_E |Lτ₁|⋯|Lτₙ| ≤ |α|_E ‖L‖ⁿ. This uses Cauchy–Binet (α(v) = Σ_I α(e_I) det[(v_j)_I]), Cauchy–Schwarz, and Σ_I det[(v_j)_I]² = det(vᵀv) ≤ Π|v_j|² (Hadamard).
 (e) For x ∈ G, ‖Dπ(x)‖ ≤ 1 + c|x − y| ≤ Λ and |ω(π(x))|_E ≤ 1. So Z'(ω) ≤ Λⁿ ∫_{M_Y∩G} θ_Y dHⁿ = Λⁿ μ_Y(G).
 Taking the supremum over such ω gives M_G(Z') ≤ Λⁿ μ_Y(G).
8. By steps 6, 7 and (C1): μ_Z(G) = M_G(Z) ≤ M_G(Z') ≤ Λⁿ μ_Y(G).
9. Splitting off G ∖ F. G ∖ F is open and contained in U ∖ F, so μ_Y(G ∖ F) = μ_Z(G ∖ F) by 2(c). All quantities are finite by 2(d). Since F ⊆ G,
 μ_Z(F) = μ_Z(G) − μ_Z(G ∖ F)
 ≤ Λⁿ μ_Y(G) − μ_Y(G ∖ F)
 = Λⁿ μ_Y(F) + (Λⁿ − 1) μ_Y(G ∖ F)
 = Λⁿ μ_Y(F) + (Λⁿ − 1) μ_Z(G ∖ F)
 ≤ Λⁿ μ_Y(F) + (Λⁿ − 1) μ_Z(G).
 With Λ = 1 + 3cρ and Λⁿ − 1 ≥ 0, this is the claim. ∎

## Key steps

1. π maps F = B̄_t(y) into N ∩ B_{3ρ}(y), since Lip(π|B̄_s) ≤ 1 + cs, π(y) = y and 4cρ ≤ 1; via (C1), μ_X is carried by F and μ_Z by N.
2. Approximate tangent planes of Z lie in T_xN (blow-up against a C² chart), so π_# fixes Z on G.
3. Q_π = π_#X is a current with compact support in N ∩ G. On disjoint compact pieces where π is injective (C¹ cover, local immersion), the area formula gives Q_π(ω) = ∫ V(ω) dHⁿ with V(w) = m(w)ζ_w, m(w) ∈ ℤ.
4. Borel versions N' = |m| and ζ' = V/|V| on the carrier C = {w : N'(w) ≥ 1} form an IMRep representing Q_π; tangent_locality gives the orientation on C, and the area formula its local integrability.
5. ∂Q_π = 0 by mollifying π; Z + Q_π is an admissible competitor, so M_G(Z) ≤ M_G(Z + Q_π).
6. Z + Q_π = π_#(Y⌞G) as vector measures, so M_G(Z + Q_π) ≤ (1 + 3cρ)ⁿμ_Y(G) by Hadamard; then subtract G ∖ F, where μ_Y = μ_Z.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -c sorry local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (1, the final main_theorem)`
- `rg -l -i 'slice|slicing|flat metric|flat norm|deformation theorem|nearest.point|tubular' simongmt/Poincare/SimonGMT local-references/123e8435b4a2469b/project -t lean`
- `rg -n 'def .*[Pp]ushforward' simongmt/Poincare/SimonGMT -t lean`
- `rg -n -i 'theorem .*area.*rectifiable|rectifiable.*area_formula|areaFormula.*Rectifiable' simongmt/Poincare/SimonGMT -t lean (no match)`
- `grep -n '^theorem|^def' simongmt Chapter02/AreaNoninjective.lean, Chapter03/{SubmanifoldCover,DisjointCover,Rectifiable,Differential}.lean, Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `grep -n 'measure_compl_support|hausdorffMeasure_image_le|norm_image_sub_le_of_norm_fderiv_le|toOpenPartialHomeomorph|exists_isCompact_diff_lt' in snapshot mathlib Support.lean, Hausdorff.lean, MeanValue.lean, InverseFunctionTheorem/ContDiff.lean, Regular.lean`
- `grep -rln 'def compContinuousLinearMap' snapshot mathlib Topology/Algebra/Module/Alternating`
- `dag.json lean_name scan for the eight proposed dor_lmb_* names (164 nodes at 2026-10-12T01:39Z; no collision); git grep dor_lmb over all branches (no match)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope on all eight lean_statement strings`
- `lake env lean /tmp/lmb-decomp-v2/Types.lean (eight child types in the exact comparator scope, each also checked as `example : Prop`)`
- `lake env lean /tmp/lmb-decomp-v2/Assembly.lean (#print axioms Submission.dor_minimizing_limsup_mass_bound)`
- `lake env lean /tmp/lmb-decomp-v2/Inst.lean (implicit volume on ℝ, Measure.le_iff', ENNReal smul of measures)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-audit-v1.json`
- `/tmp/lmb-decomp-v2/v2_subproblems.json`
- `/tmp/lmb-decomp-v2/Types.lean`
- `/tmp/lmb-decomp-v2/Assembly.lean`
- `/tmp/lmb-decomp-v2/Inst.lean`

Snapshot: project b4d606d, mathlib 25730c7c; simongmt is pinned at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Its only sorry is main_theorem.

Reusable facts found:
- SimonGMT Chapter03/Rectifiable.lean: HasApproximateTangentSpaceAt (Simon 1.4, unweighted), .unique, CountablyRectifiable and CountablyRectifiable.mono.
- Chapter03/DisjointCover.lean: simon_remark_1_3 (disjoint Borel pieces).
- Chapter03/SubmanifoldCover.lean: countablyRectifiable_of_submanifold_cover, measurableSet_of_isSimonSubmanifold, countablyRectifiable_image_contDiffOn_open. Its header says the converse direction of Lemma 1.2 "remains a separate theorem".
- Chapter02/AreaNoninjective.lean: weighted_area_formula_lipschitz_fiberSum, a non-injective weighted Lipschitz area formula. It is for maps on a Euclidean domain, not on rectifiable subsets of ℝ^P.
- Chapter06: massOn and massAdmissibleOn (Mass.lean); support as U minus the zero region (CurrentLocalEquality.lean); GeometricCurrentOn with sequential continuity, and boundary (Currents.lean).
- Mathlib: measure_compl_support, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, ContDiffAt.toOpenPartialHomeomorph, MeasurableSet.exists_isCompact_diff_lt, ContinuousAlternatingMap.compContinuousLinearMap, μHE[d].

Not available, so cited from Simon in the child proofs:
- current slicing (6.4) and flat convergence (6.7.2): the keyword hits are only linear co-area slices, product point slices and varifold deformation slices;
- the Deformation Theorem (6.5.3) and completeness (6.3.13);
- C¹ or Lipschitz push-forward of currents: only affinePushforward and varifold push-forwards exist;
- the rectifiable-set area formula (Ch. 3, 2.6), the only-if direction of Lemma 1.2, and a nonlinear tubular-neighbourhood retraction.

Lean checks:
- All eight child types elaborate as Prop in the exact comparator scope and pass validate_lean_statement.
- The conditional assembly of the exact frozen parent type compiles. It depends only on propext, Classical.choice, Quot.sound and the stubs' sorryAx.
- No proposed name collides.
