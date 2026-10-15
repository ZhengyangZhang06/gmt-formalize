# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This child supplies the one conclusion for which the supplied proof of CodimensionOneRegularity cites root theorems that the selected node cannot use: “x ∈ spt T and Θ^n(μ_T, x) < 1 + δ ⇒ x ∈ reg T”.
- In the supplied proof it is used in step 2 (⇐) for T itself, with d = n + 1, and in step 5(α) for the cone factor S₀, with U = N = ℝ^P and d = P.
- There it is derived from DensityAndTangentCones (2), the sibling density_gap and DensityOneImpliesRegular, which are not among this node's resolved dependencies.
Here it is proved by Simon's printed route instead: Allard's theorem 5.2 of Ch. 5 applied at the point itself, as in 7.4.2, 7.4.3 with T_j ≡ T and y_j ≡ y, and 7.4.4 (8) (“by Allard's 5.2 of Ch. 5 there is δ > 0 such that sing S = {Θ ≥ 1 + δ}”), with Lemma 7.1.2 justifying its use. The statement and the proof C0–C8 are those of the previously reviewed child low_density_regular of this node; only the citations of general facts changed.
Explicit departures from the parent text:
(i) No tangent cone, density gap or sequence version is needed. δ is Allard's constant for (n, P − n).
(ii) Stationarity along N and the bound on the generalized mean curvature are derived from minimality, by the printed proof of 7.1.2 together with Ch. 2, 5.6–5.10, instead of citing MinimizingImpliesStationary.
(iii) The mass–weight identity (C1b) is cited from the sibling child oriented_piece_mass instead of im_mass_measure.
No DAG declaration other than the four sibling children below is used.

Sibling children used.
- vanish_off_support (Submission.dtc_vanish_off_support): S(ω) = 0 whenever tsupport ω ∩ spt S = ∅.
- oriented_piece_mass (Submission.codim1_massOn_eq_lintegral_of_oriented_rep): if V ⊆ U is open, M' ⊆ V Borel, θ' ≥ 0 measurable, ξ' a.e. strongly measurable on M' and H^k-a.e. on M' a unit orientation of some subspace, and T(ω) = ∫_{M'} θ'·ξ'(ω) dH^k whenever tsupport ω ⊆ V, then for every open W ⊆ V: M_W(T) ≤ ∫_{M'∩W} θ' dH^k (first conclusion), with equality when the right side is finite (second conclusion).
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual): a continuous linear L : Λ_k → Λ^k such that every unit orientation ξ of a subspace satisfies (a) |ξ(α)| ≤ |α| for every k-covector α, (b) |L(ξ)| ≤ 1, (c) ξ(L(ξ)) = 1.
- orientation_sign (Submission.rsdic_unitOrientation_eq_or_eq_neg): two unit orientations of the same subspace satisfy w = v or w = −v.

Notation.
- H^d := μHE[d]. On a d-dimensional affine plane it is d-dimensional Lebesgue measure, since Hausdorff measure is isometry invariant and μHE[d] = volume on ℝ^d. ω_d := unitBallVolume d is H^d of a unit d-disc.
- B_ρ(y) := ball y ρ.
- For a k-covector α, |α| is the Euclidean coefficient norm (covectorEuclideanNorm).
- For T ∈ 𝒟_k(U), M_W(T) := T.massOn W = sup{ofReal T(ω) : ω ∈ 𝒟^k(U), tsupport ω ⊆ W, |ω| ≤ 1 pointwise}.
- “T vanishes on W” means T(ω) = 0 whenever tsupport ω ⊆ W. Z(T) is the union of the open W with compact closure in U on which T vanishes, and spt T := U ∖ Z(T).
- “Θ^k(μ_T, y) = θ” means HasMassDensity T y θ: θ ≥ 0 and M_{B_ρ(y)}(T)/(ω_kρ^k) → θ as ρ ↓ 0.

General facts. Let U be open, k ∈ ℕ and T ∈ 𝒟_k(U).
(G2) Positive density forces support.
- If T vanishes on an open W, then M_{W'}(T) = 0 for every W' ⊆ W, since every admissible form gives the value 0.
- Let y ∈ U with Θ^k(μ_T, y) = θ > 0, and suppose y ∉ spt T. Then y lies in an open W on which T vanishes, so M_{B_t(y)}(T) = 0 for small t and the density is 0 ≠ θ. Hence y ∈ spt T.
(O1) Orientations of planes. Let f_1, …, f_k ∈ ℝ^P be linearly independent with span Π. Then ξ(α) := α(f_1, …, f_k)/det(f_i·f_j)^{1/2} defines a unit orientation of Π (IsUnitOrientationOf ξ Π).
- Gram–Schmidt writes f = σU, with σ an orthonormal basis of Π and U upper triangular with positive diagonal.
- By multilinearity and alternation, α(f) = det(U)·α(σ). Also det(f_i·f_j)^{1/2} = det(UᵀU)^{1/2} = det U.
- So ξ(α) = α(σ).

Proof (steps C0–C8). Printed sources:
- Simon 7.4.2 (“an immediate consequence of The Allard Theorem 5.2 of Ch. 5 and Lemma 1.2”), chapter-07-source.txt lines 605–615;
- 7.4.3 with T_j ≡ T and y_j ≡ y (lines 617–632);
- 7.4.4 (8), “by Allard's 5.2 of Ch. 5 there is δ > 0 such that sing S = {Θ ≥ 1 + δ}” (lines 673–675);
- Lemma 7.1.2 and its printed proof (lines 29–68);
- Ch. 2, 5.6–5.10 (chapter-02-source.txt lines 1290–1360) and Ch. 4, 2.5–2.7, 3.14 (chapter-04-source.txt lines 160–212, 370–380): stationarity in N and the mean curvature H_N;
- Ch. 5, 5.1–5.2 (Allard; chapter-05-source.txt lines 1008–1031) and 7.1 (lines 1312–1366);
- Ch. 6, 2.34 (constancy; chapter-06-source.txt lines 569–604).
The general facts (G2) and (O1) above are used with k := n.

C0. (Choice of δ.) Fix P and n ≥ 1. If n > P there is no d with n ≤ d ≤ P, so the statement holds vacuously; assume n ≤ P and put ℓ := P − n and p := 2n > n.
- If ℓ = 0, put δ := 1.
- If ℓ ≥ 1, let δ₀, γ ∈ (0, 1) and C_A ≥ 1 be the constants δ₀(n, ℓ, p), γ(n, ℓ, p) and C(n, ℓ, p) of the Allard Regularity Theorem (Simon Ch. 5, 5.2). Put δ := min{δ₀, (2C_A)^{−(2n+2)}} > 0.
- Since δ ≤ δ₀, hypotheses 5.1 with constant δ imply the conclusion of 5.2, and its estimate then gives sup|Du| ≤ C_Aδ^{1/(2n+2)} ≤ 1/2.
δ depends only on P and n.
Now fix d, U, N, T as in the statement, x ∈ spt T and θ with Θ^n(μ_T, x) = θ < 1 + δ.
- T is integer multiplicity (first conjunct of IsMinimizingIn). Fix an IMRep R = (M_R, θ_R, ξ_R) of T, and let μ := μ_R be its weight, μ(A) = ∫_{M_R∩A} θ_R dH^n.
- V := v(M_R, θ_R) is the associated varifold, so μ_V = μ.

C1. (Mass and weight.)
(C1a) μ(K) < ∞ for every compact K ⊆ U (IMRep.locallyIntegrable_mult).
(C1b) For every open W ⊆ U, M_W(T) ≤ μ(W), and M_W(T) = μ(W) if μ(W) < ∞. This is oriented_piece_mass (first and second conclusions) applied with V := U, M' := M_R, θ' := θ_R and ξ' := ξ_R: its hypotheses are IMRep.measurableSet_carrier, IMRep.carrier_subset, IMRep.measurable_mult (θ_R ≥ 0), IMRep.aestronglyMeasurable_orient, IMRep.orients (ξ_R(x) is a unit orientation of the approximate tangent plane for H^n-a.e. x ∈ M_R) and R.Represents T; and ∫_{M_R∩W} θ_R dH^n = μ(W).
(C1c) spt T = U ∩ spt μ, and μ(U ∖ spt T) = 0. Let y ∈ U and let r > 0 with closedBall(y, r) ⊆ U.
- If y ∉ spt T, then T vanishes on an open W ∋ y. For ε ≤ r with B_ε(y) ⊆ W, (C1b) and (G2) give μ(B_ε(y)) = M_{B_ε(y)}(T) = 0.
- If μ(B_ε(y)) = 0 for some ε ≤ r, then M_{B_ε(y)}(T) = 0 by (C1b), so T vanishes on B_ε(y): any ω with tsupport ω ⊆ B_ε(y) and T(ω) ≠ 0 would make ±ω/max|ω| admissible with positive value. Hence y ∉ spt T.
- U ∖ spt T is open and is covered by countably many such balls of μ-measure 0 (second countability). So μ(U ∖ spt T) = 0.
(C1d) For 0 < r with closedBall(x, r) ⊆ U, μ(B_r(x)) = M_{B_r(x)}(T), by (C1a) and (C1b).
(C1e) Tangent planes lie in T_yN.
- By (C1c), μ-a.e. y ∈ M_R lies in spt T ⊆ N. Since θ_R ≥ 1 on M_R, H^n(M_R ∖ N) = 0.
- At μ-a.e. y ∈ M_R ∩ N the approximate tangent space T_yM_R exists, and T_yM_R ⊆ T_yN. Indeed the blow-ups of H^n⌞M_R at y are carried by the blow-ups of N, up to the H^n-null set M_R ∖ N, and these converge to T_yN locally in Hausdorff distance.

C2. (First variation along N; Simon 7.1.2 and its printed proof.) Let X ∈ C¹_c(U; ℝ^P) with X(y) ∈ T_yN for every y ∈ N ∩ U. Then ∫_{M_R} θ_R div_{M_R}X dH^n = 0.
(C2a) N ∩ U is relatively closed in U, because (closure N ∖ N) ∩ U = ∅. Hence N ∩ K is compact for every compact K ⊆ U.
(C2b) By Simon Ch. 2, the discussion preceding 5.8 (= Ch. 4, 2.5–2.6), there is a family φ_t, t ∈ (−1, 1), of diffeomorphisms of U such that:
- (t, y) ↦ φ_t(y) is C²;
- φ_t(U ∩ N) ⊆ U ∩ N and φ_0 = id;
- φ_t = id on U ∖ K for a compact K ⊆ U;
- the initial velocity Y := ∂_tφ_t|_{t=0} is a C¹ vector field with support in K and Y = X on N ∩ U. The book gives the initial velocity X at the points of N ∩ U.
Choose an open W ⊇ K with compact closure in U. Since φ_t is a bijection of U equal to the identity off K ⊆ W, φ_t(K) = K and φ_t(W) = W.
(C2c) The competitor. Put S_t(ω) := ∫_{M_R} θ_R ⟨ω(φ_t(y)), Λ_nDφ_t(y)ξ_R(y)⟩ dH^n(y) for ω ∈ 𝒟^n(U). This is φ_{t#}T (Simon Ch. 6, 3.3), i.e. T acting through its representation on the compactly supported C¹ form φ_t^#ω.
- S_t ∈ 𝒟_n(U). It is linear, and |S_t(ω)| ≤ c_n·sup|Dφ_t|^n·μ(K_ω ∪ K)·sup|ω| whenever tsupport ω ⊆ K_ω with K_ω compact (c_n a constant depending only on n and P), since φ_t^{−1}(K_ω) ⊆ K_ω ∪ K and |ξ_R(y)(α)| ≤ |α| for H^n-a.e. y ∈ M_R (IMRep.orients and unit_orientation_dual (a)). So it is continuous for test-form convergence.
- S_t is integer multiplicity. By the area formula on the countably n-rectifiable set M_R (Simon Ch. 6, 3.3–3.9), S_t = τ(φ_t(M_R), θ_R∘φ_t^{−1}, ξ_t), where ξ_t(φ_t(y)) := Λ_nDφ_t(y)ξ_R(y)/|Λ_nDφ_t(y)ξ_R(y)|. Here φ_t(M_R) is Borel and countably n-rectifiable. Its approximate tangent space at φ_t(y) is Dφ_t(y)(T_yM_R) for H^n-a.e. y. The multiplicity is locally integrable because the Jacobians of φ_t and φ_t^{−1} are bounded on compact sets.
- ∂S_t = 0 = ∂T. Let ψ ∈ 𝒟^{n−1}(U).
  - φ_t^#ψ is a compactly supported C¹ form, and S_t(dψ) = T(φ_t^#dψ) = T(d(φ_t^#ψ)).
  - Mollifications η_j of φ_t^#ψ are test forms supported in a fixed compact subset of U, with dη_j → d(φ_t^#ψ) uniformly.
  - T(dη_j) = 0 because ∂T = 0. By dominated convergence in the representation, T(dη_j) → T(d(φ_t^#ψ)). So S_t(dψ) = 0.
- spt(S_t − T) ⊆ K ∩ N.
  - If tsupport ω ∩ K = ∅, then S_t(ω) = T(ω): near every y ∈ M_R ∖ K the map φ_t is the identity, and ω vanishes at the points φ_t(y) ∈ K for y ∈ M_R ∩ K.
  - If tsupport ω ∩ N = ∅, then T(ω) = 0 by vanish_off_support, since spt T ⊆ N. Also S_t(ω) = 0: μ-a.e. y ∈ M_R lies in spt T ⊆ N by (C1c), so φ_t(y) ∈ N and ω(φ_t(y)) = 0.
  - U ∖ K and U ∖ N are open by (C2a). A smooth partition of unity subordinate to them splits any ω with tsupport ω ⊆ U ∖ (K ∩ N) into two such pieces. So S_t − T vanishes on U ∖ (K ∩ N).
  - Hence spt(S_t − T) is a relatively closed subset of U contained in the compact set K ∩ N ⊆ (U ∩ N) ∩ W, and so it is compact.
- Since T is minimizing in U ∩ N, M_W(T) ≤ M_W(S_t) for all t ∈ (−1, 1).
(C2d) Differentiation.
- By (C1b) for T, and by oriented_piece_mass (second conclusion) for S_t with its representation above (both weights of W are finite by (C1a) and the boundedness of the Jacobians), M_W(T) = μ(W).
- By the area formula, M_W(S_t) = ∫_{φ_t(M_R)∩W} θ_R∘φ_t^{−1} dH^n = ∫_{M_R∩W} θ_R J_t dH^n, where J_t(y) := |Λ_nDφ_t(y)τ(y)| for an orthonormal basis τ(y) of T_yM_R.
- So f(t) := ∫_{M_R∩W} θ_R J_t dH^n has a minimum at t = 0.
- J_t is C¹ in t, with J_0 = 1 and ∂_tJ_t|_{t=0} = div_{M_R}Y. Its t-derivative is bounded uniformly on K, J_t = 1 off K, and μ(W) < ∞. So f'(0) = ∫_{M_R} θ_R div_{M_R}Y dH^n (Simon Ch. 2, 5.1–5.3; Ch. 4, 2.2).
- div_{M_R}Y = div_{M_R}X μ-a.e. By (C1e), μ-a.e. y ∈ M_R lies in N with T_yM_R ⊆ T_yN. The C¹ field Y − X vanishes on the C¹ submanifold N, so its derivative at y vanishes along T_yN, hence along T_yM_R. So f'(0) = ∫_{M_R} θ_R div_{M_R}X dH^n.
- Since the minimum is interior, ∫_{M_R} θ_R div_{M_R}X dH^n = 0.

C3. (Bounded generalized mean curvature; Simon Ch. 2, 5.9–5.10; Ch. 4, 2.7, 3.14.)
(C3a) By (C1e), H^n(M_R ∖ N) = 0, and T_yM_R ⊆ T_yN at μ-a.e. y ∈ M_R.
(C3b) The mean curvature field. Let B^N be the second fundamental form of the C² submanifold N, with Simon's sign convention (Ch. 2, 4.24): B^N_y(τ, η) = −Σ_j (τ·D_ην^j)ν^j for a local orthonormal normal frame (ν^j). It is continuous on N. For y as in (C1e) put H(y) := Σ_{i=1}^n B^N_y(τ_i, τ_i), with τ an orthonormal basis of T_yM_R; put H := 0 elsewhere. H is μ-measurable.
(C3c) The first variation formula. Let X ∈ C¹_c(U; ℝ^P).
- Cover the compact set N ∩ spt X by finitely many open cylinders O_k = {z₀ + v + h : v ∈ Π_k, |v| < r_k, h ∈ Π_k^⊥, |h| < r_k'} ⊆ U, with z₀ ∈ N and Π_k := T_{z₀}N. Choose them so that N ∩ O_k = {z₀ + v + w(v) : v ∈ Π_k, |v| < r_k} is the graph of a C² map w : Π_k ∩ B_{r_k}(0) → Π_k^⊥ with |w| < r_k'.
- Such cylinders exist. Take a chart (V, W, ψ) of N at z₀ (IsEmbeddedSubmanifold 2 d N), so that Dψ(ψ^{−1}(z₀)) is injective with range Π_k (the curve argument shows range ⊆ T_{z₀}N, and the dimensions agree). By the inverse function theorem, p_k∘(ψ − z₀) is a C² diffeomorphism near ψ^{−1}(z₀), where p_k is the orthogonal projection onto Π_k. ψ is proper and injective, hence a homeomorphism onto W ∩ N, which is relatively closed in W. So for small r_k, r_k' with r_k' small relative to r_k, N ∩ O_k is exactly the graph of w := p_k^⊥∘(ψ − z₀)∘(p_k∘(ψ − z₀))^{−1}, and |w| < r_k'.
- Gram–Schmidt applied to the C¹ normal vectors of the graph gives a C¹ orthonormal frame (ν^j) of the normal spaces of N along N ∩ O_k. Extend it to O_k by ν^j(z₀ + v + h) := ν^j(z₀ + v + w(v)), which is C¹. Only derivatives along T_yN at points y ∈ N enter below, so the extension is immaterial.
- Take a C^∞ partition of unity subordinate to {O_k} ∪ {U ∖ N}, and write X = X₀ + Σ_k X_k, with X₀ vanishing on a neighbourhood of N and X_k ∈ C¹_c(O_k).
- div_{M_R}X₀ = 0 at every point of M_R ∩ N. Since H^n(M_R ∖ N) = 0, ∫ θ_R div_{M_R}X₀ dH^n = 0 = −∫ X₀·H dμ.
- For each k put X_k^T := X_k − Σ_j (X_k·ν^j)ν^j. It is C¹ with compact support in O_k and tangent to N on N ∩ O_k, so (C2) gives ∫ θ_R div_{M_R}X_k^T dH^n = 0.
- At μ-a.e. y ∈ M_R ∩ O_k, since ν^j(y) ⊥ T_yM_R, the computation of Simon Ch. 2, 5.9 gives div_{M_R}X_k = div_{M_R}X_k^T + Σ_j (X_k·ν^j)div_{M_R}ν^j = div_{M_R}X_k^T − X_k·H.
- Summing, ∫ θ_R div_{M_R}X dH^n = −∫ X·H dμ for every X ∈ C¹_c(U; ℝ^P).
So V has generalized mean curvature H in U (Simon Ch. 4, 2.7 and 3.14).
(C3d) Bound. For each compact K ⊆ U, |H| ≤ Λ_K := n·max_{N∩K}|B^N| < ∞ μ-a.e. on K. The maximum is finite because N ∩ K is compact (C2a).

C4. (Allard's hypotheses at x.) Assume ℓ ≥ 1. Choose ρ₀ > 0 with closedBall(x, ρ₀) ⊆ U, and put Λ := Λ_{closedBall(x, ρ₀)}.
- θ_R ≥ 1 on M_R, so the density of V is ≥ 1 μ_V-a.e.
- x ∈ spt μ by (C1c), i.e. x ∈ spt V.
- By (C1d), M_{B_r(x)}(T)/(ω_nr^n) = μ(B_r(x))/(ω_nr^n) for r ≤ ρ₀, and this tends to θ < 1 + δ. So there is ρ₁ ∈ (0, ρ₀) with (ω_nr^n)^{−1}μ(B_r(x)) ≤ 1 + δ for 0 < r < ρ₁.
- For such r, (r^{p−n}∫_{B_r(x)} |H|^p dμ)^{1/p} ≤ (r^{p−n}Λ^p(1 + δ)ω_nr^n)^{1/p} ≤ Λ(2ω_n)^{1/p}r.
- Fix ρ ∈ (0, ρ₁) with Λ(2ω_n)^{1/p}ρ ≤ δ. Then, after translating x to 0, the hypotheses 5.1 of Simon Ch. 5 hold for V with radius ρ and constant δ ≤ δ₀.

C5. (Allard's conclusion.)
- If ℓ ≥ 1, Theorem 5.2 of Ch. 5 gives a linear isometry q of ℝ^P = ℝ^n × ℝ^ℓ and u ∈ C^{1,1−n/p}(B^n_{γρ}(0); ℝ^ℓ) with spt μ ∩ B_{γρ}(x) = (x + q(graph u)) ∩ B_{γρ}(x) and sup|Du| ≤ 1/2 (C0).
  - Since x ∈ spt μ, x = x + q(v₀, u(v₀)) with |v₀| ≤ |q(v₀, u(v₀))| = 0. So u(0) = 0, and |u(v)| ≤ |v|/2.
  - By (C1c), spt T ∩ B_{γρ}(x) = (x + q(graph u)) ∩ B_{γρ}(x).
- If ℓ = 0, choose ρ > 0 with closedBall(x, ρ) ⊆ U and set γ := 1, q := id and u :≡ 0 ∈ ℝ^0 on B^n_ρ(0) = B^P_ρ(0). Then x + q(graph u) = B_ρ(x), so spt T ∩ B_{γρ}(x) ⊆ x + q(graph u) trivially; also u(0) = 0 and Du ≡ 0.
In both cases spt T ∩ B_{γρ}(x) ⊆ x + q(graph u), with u(0) = 0 and sup|Du| ≤ 1/2. Only this inclusion is used below.

C6. (The graph piece.) Put σ := γρ/2 and D := B^n_σ(0) ⊆ ℝ^n (identified with Euclid n). Define Γ(v) := x + q(v, u(v)) for v ∈ D, the affine map π(y) := (first n coordinates of q^{−1}(y − x)) from ℝ^P to ℝ^n, and M := Γ(D). Then π∘Γ = id_D and Dπ∘DΓ(v) = I.
(C6a) |v| ≤ |Γ(v) − x| ≤ (3/2)|v|, so M ⊆ B_{3σ/2}(x) ⊆ B_{γρ}(x). Moreover spt T ∩ B_σ(x) ⊆ M: a point y of the left side is Γ(v) with |v| ≤ |y − x| < σ.
(C6b) IsEmbeddedSubmanifold 1 n M, and x = Γ(0) ∈ M.
- Γ is C¹ on D and injective, since π∘Γ = id. DΓ(v)w = q(w, Du(v)w) is injective, since |DΓ(v)w| ≥ |w|.
- For every point of M use the chart (V, W, ψ) := (D, π^{−1}(D), Γ). W is open, and ψ(V) = M = W ∩ M.
- For compact K' ⊆ W, the set D ∩ Γ^{−1}(K') = {v ∈ π(K') : Γ(v) ∈ K'} is closed in the compact set π(K') ⊆ D, hence compact.
(C6c) tangentSpace(M, Γ(v)) = DΓ(v)(ℝ^n) for v ∈ D.
- (⊇) For w ∈ ℝ^n, let ε := (σ − |v|)/(1 + |w|) and h(t) := ε·tanh(t/ε). Then γ(t) := Γ(v + h(t)w) is a C¹ curve on (−1, 1) in M with γ(0) = Γ(v) and γ'(0) = DΓ(v)w.
- (⊆) If γ is a C¹ curve in M with γ(0) = Γ(v), then π∘γ is C¹ with values in D, and γ = Γ∘(π∘γ). So γ'(0) = DΓ(v)(π∘γ)'(0).
(C6d) IsOrientation n M ξ_M.
- For y ∈ M and v := π(y), put ξ_M(y)(α) := α(DΓ(v)e_1, …, DΓ(v)e_n)/J(v), with J(v) := det(DΓ(v)ᵀDΓ(v))^{1/2} > 0. Put ξ_M := 0 off M.
- Gram–Schmidt writes DΓ(v)e = σ'U with σ' an orthonormal basis of DΓ(v)ℝ^n and U upper triangular with positive diagonal, and det U = J(v). So ξ_M(y)(α) = α(σ'), and ξ_M(y) is a unit orientation of tangentSpace(M, y) by (O1).
- ξ_M is continuous on M, because DΓ, π and J are continuous and J > 0.
(C6e) H^n(M) = ∫_D J dL^n ≤ (5/4)^{n/2}ω_nσ^n < ∞, by the area formula and ‖DΓ‖² ≤ 1 + |Du|² ≤ 5/4. In particular H^n(M ∩ K'') < ∞ for every K''.

C7. (Constant integer multiplicity on M; constancy theorem.)
(C7a) μ(B_σ(x) ∖ M) = 0 by (C1c) and (C6a). Since θ_R ≥ 1 on M_R, H^n((M_R ∩ B_σ(x)) ∖ M) = 0.
(C7b) For H^n-a.e. y ∈ M_R ∩ M ∩ B_σ(x), the approximate tangent space of M_R at y is T_yM.
- At H^n-a.e. y ∈ M_R the upper density of H^n⌞(M ∖ M_R) is 0 (Simon Ch. 3, §1).
- Near y ∈ B_σ(x), H^n⌞M_R = H^n⌞M − H^n⌞(M ∖ M_R) by (C7a). So the blow-ups of H^n⌞M_R at such y have the limit H^n⌞T_yM.
- By IMRep.orients, ξ_R(y) is then a unit orientation of T_yM. Two unit orientations of one plane differ by a sign (orientation_sign), so ξ_R(y) = s(y)ξ_M(y) with s(y) ∈ {±1}.
(C7c) Put f := θ_R s on M_R ∩ M ∩ B_σ(x), and f := 0 on M ∖ (M_R ∩ B_σ(x)). f is H^n-measurable and integer valued, and ∫_M |f| dH^n ≤ μ(B_σ(x)) < ∞. By (C7a) and (C7b), every ω ∈ 𝒟^n(U) with tsupport ω ⊆ B_σ(x) satisfies T(ω) = ∫_{M_R} θ_R⟨ω, ξ_R⟩ dH^n = ∫_M f⟨ω, ξ_M⟩ dH^n.
(C7d) Constancy. Put D' := B^n_{σ/2}(0) and let β ∈ 𝒟^{n−1}(D').
- Γ(spt β) ⊆ closedBall(x, 3σ/4) by (C6a).
- Choose χ ∈ C^∞_c(B_σ(x)) with χ = 1 on B_{7σ/8}(x), and put ω_β := χ·π^#β ∈ 𝒟^{n−1}(U).
- dω_β = χπ^#dβ + dχ∧π^#β. Let y ∈ M. If dχ(y) ≠ 0, then |y − x| ≥ 7σ/8, so π(y) ∉ spt β (otherwise y = Γ(π(y)) ∈ closedBall(x, 3σ/4)), and (π^#β)(y) = 0. Also χ(y) = 1 wherever (π^#dβ)(y) ≠ 0. Hence ⟨dω_β, ξ_M⟩ = ⟨π^#dβ, ξ_M⟩ on M.
- ∂T = 0 (n ≥ 1) and (C7c) give 0 = T(dω_β) = ∫_M f⟨π^#dβ, ξ_M⟩ dH^n.
- By the area formula for Γ, and because Dπ∘DΓ(v) = I gives ⟨(π^#dβ)(Γ(v)), ξ_M(Γ(v))⟩ = dβ(v)(e_1, …, e_n)/J(v), this integral equals ∫_D f(Γ(v))·dβ(v)(e_1, …, e_n) dv.
- Hence the n-current S'(α) := ∫_{D'} (f∘Γ)·α(e_1, …, e_n) dv on D' has ∂S' = 0. It is well defined: J ≥ 1 gives ∫_{D'}|f∘Γ| ≤ ∫_M |f| < ∞.
- By the constancy theorem (Simon Ch. 6, 2.34; D' is connected), S' = m[[D']] for a constant m, i.e. f∘Γ = m L^n-a.e. on D'. Since f is integer valued, m ∈ ℤ.
(C7e) Put ρ' := σ/2 and let ω ∈ 𝒟^n(U) with tsupport ω ⊆ B_{ρ'}(x).
- Every y ∈ M ∩ B_{ρ'}(x) has |π(y)| ≤ |y − x| < σ/2, i.e. y ∈ Γ(D').
- f = m H^n-a.e. on Γ(D'), by (C7d) and the area formula.
- So (C7c) gives T(ω) = m∫_{M∩B_{ρ'}(x)} ⟨ω, ξ_M⟩ dH^n = m∫_M ξ_M(y)(ω(y)) dH^n(y).
(C7f) m ≠ 0. Otherwise T vanishes on B_{ρ'}(x), whose closure is a compact subset of U, and x ∉ spt T.

C8. (Conclusion.) We have:
- x ∈ spt T;
- ρ' > 0 with B_{ρ'}(x) ⊆ U;
- m ∈ ℤ ∖ {0} and x ∈ M;
- IsEmbeddedSubmanifold 1 n M (C6b) and IsOrientation n M ξ_M (C6d);
- H^n(M ∩ K'') < ∞ for compact K'' ⊆ B_{ρ'}(x) (C6e);
- T(ω) = m∫_M ξ_M(ω) dH^n whenever tsupport ω ⊆ B_{ρ'}(x) (C7e).
This is x ∈ regularSet T. δ was chosen in C0 depending only on P and n. ∎

## Key steps

1. C0–C1: δ := 1 if P = n, else δ := min{δ₀, (2C_A)^{−(2n+2)}} from Allard's constants (p = 2n); mass equals weight on open sets of finite weight (oriented_piece_mass); spt T = U ∩ spt μ_T and μ_T(U ∖ spt T) = 0; tangent planes of the carrier lie in T_yN.
2. C2–C3: competitors φ_{t#}T for the book's families preserving N (Simon 7.1.2) give first variation zero along N; with Ch. 2, 5.9 the varifold has generalized mean curvature H = Σ B^N(τ_i, τ_i), bounded by n·max|B^N| on compact sets.
3. C4–C5: Θ(x) < 1 + δ and ρΛ small give Allard's hypotheses 5.1 at x; Theorem 5.2 puts spt T ∩ B_{γρ}(x) in the graph of a C¹ map u with u(0) = 0 and |Du| ≤ 1/2.
4. C6–C8: the graph piece M is an oriented embedded C¹ n-submanifold with finite area; T = ∫_M f⟨·, ξ_M⟩ with integer f (orientation_sign); testing ∂T = 0 on χπ^#β and the constancy theorem give f ≡ m ≠ 0 near x; hence x ∈ regularSet T.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A4 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'theorem finrank_add_inf_finrank_orthogonal|theorem IsCompact.tendsto_subseq|theorem isOpen_iUnion_countable' local-references/123e8435b4a2469b/mathlib/Mathlib/{Analysis/InnerProductSpace/Projection/FiniteDimensional,Topology/Sequences,Topology/Bases}.lean`
- `grep -n 'def massOn|massOn_mono|def zeroRegion|def support|Zero (GeometricCurrentOn' simongmt/Poincare/SimonGMT/Chapter06/{Mass,CurrentLocalEquality,Currents}.lean`
- `grep -rn 'theorem <name>' simongmt/Poincare/SimonGMT for bvVariationOn_le_liminf_of_locallyL1, cone_simonsDefect_lower_bound, exists_final_exponent, injective_area_formula_of_injective_derivative, exteriorDerivative_affinePullbackForm, tsupport_exteriorDerivative_subset, exteriorDerivative_sq, simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, WeakDerivativesZero.ae_eq_const`
- `header of simongmt Chapter03/FinitePerimeter.lean and Chapter05/Basic.lean; grep -rln 'Allard|DeGiorgi|BVCompact' simongmt/Poincare/SimonGMT`
- `python3 scan of dag.json: statuses and frozen types of the 8 siblings, the 5 reused names, the 6 new codim1_ names, the root theorems DensityAndTangentCones, DensityOneImpliesRegular, MinimizingImpliesStationary and dor_stationary_cycle_epsilon_regularity; keyword scan for overlapping nodes (regcomp_codim_one_preliminaries, regcomp_cop_region_support_subset, regcomp_cop_region_boundary_vanishes)`
- `for r in $(git for-each-ref refs/heads refs/remotes): git grep -l codim1_ $r -- 'GMT/*.lean' (2056 refs, no match)`
- `lean -DautoImplicit=false /tmp/codim1-v6/check/Types.lean; lean -DautoImplicit=false /tmp/codim1-v6/check/Assembly.lean (LEAN_PATH taken from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `ps -eo pid,lstart,args; max_nodes timeline over .humanize/swarm-configs; /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py _decompose, _solve_children, _existing_lean_name_problem, _install_parent_supplied_child_handoff; store.py ensure`
- `sed -n 560,1000p book/sources/chapter-07-source.txt (7.4–7.5.8); sed -n 1286,1330p book/sources/chapter-02-source.txt (5.6–5.8); sed -n 1300,1370p book/sources/chapter-05-source.txt (Theorem 7.1)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-audit-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/tmp/codim1-v6/check/Types.lean`
- `/tmp/codim1-v6/check/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/33c6cc03ee394bfbb35f84931b68580c.json`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib; the snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…), so the frozen types of this node and of the 8 siblings are unchanged since v5.
Library.
- The snapshot Mathlib has finrank_add_inf_finrank_orthogonal (FiniteDimensional.lean:89), IsCompact.tendsto_subseq (Sequences.lean:298) and isOpen_iUnion_countable (Bases.lean:932); the glue uses all three.
- SimonGMT supplies massOn and massOn_mono, support = U \ zeroRegion and the zero current (Chapter06). It also supplies BV lower semicontinuity (Chapter02/BV.lean:225), the Simons algebra (AppendixB/ConeDefect.lean:228, SimonsInequalities.lean:88), and the area-formula, exterior-derivative and affine-pullback lemmas cited by the children.
- Its headers state that De Giorgi's theorem (Chapter03/FinitePerimeter.lean) and Allard's theorem (Chapter05/Basic.lean) are not provided, and no BV compactness theorem exists. These remain book citations inside the children.
DAG.
- The 5 reused declarations are accepted with byte-identical types.
- DensityAndTangentCones, DensityOneImpliesRegular, MinimizingImpliesStationary and dor_stationary_cycle_epsilon_regularity are not accepted, so they cannot be reused.
- regcomp_codim_one_preliminaries and its children overlap region_support_cycle, but they are unaccepted and have other types.
- The 6 new codim1_ names are free in dag.json, GMT/, SimonGMT and all 2056 refs.
Lean.
- Types.lean elaborates all 11 child types (exit 0, only sorry warnings).
- Assembly.lean proves CodimensionOneRegularity from the 8 sibling and 11 child types taken as axioms (exit 0). Its axioms are propext, Classical.choice, Quot.sound, 5 new children and 7 siblings; no root proposition occurs.
Infrastructure. The current controller (pid 23222) runs with max_nodes = 1000 and dag.json has 457 nodes, so the 6 new nodes can be activated. The accepted v5 was dropped by the old controller, which had max_nodes = 200 loaded.
