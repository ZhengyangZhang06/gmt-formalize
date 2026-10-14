# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.spine_coarea-a1.coarea_of_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–8 and (T4) of the selected node's supplied proof (Federer 3.2.22 for p restricted to M, with coarea factor 1). This is the slicing step behind Simon Ch. 7, Lemma 3.5 (chapter-07.txt lines 407–418, "the proof of which is left to the reader"). (H2) replaces supplied step 1 and the first half of step 2.
Context (not part of the numbered proof). The steps below follow the accepted Lean proof of the identical-type declaration Submission.idtp_fons_cs_sos_spine_coarea (candidate d35a0320a1655c5aa9479b8fdfc9adcba5c25d5b). Its GMT/Ch07/Submission.lean lines 6555–7356 hold an inline `have master` over abstract spaces V, F, B. Taken verbatim, that block proves exactly this child's frozen type in the environment of the accepted candidate 2626c7a (d35a0320 is 2626c7a plus only that theorem), as follows:
  intro P n L M hdn hM hpieces hloc htan
  have master : … := <d35a0320 GMT/Ch07/Submission.lean lines 6555–7356, verbatim>
  exact master (Euclid n) (Euclid P) (Euclid (n - Module.finrank ℝ L)) n (Module.finrank ℝ L)
    (n - Module.finrank ℝ L) L M finrank_euclideanSpace_fin finrank_euclideanSpace_fin rfl hdn rfl
    hM hloc htan hpieces (Submission.ptd_piece_image_measurable_ae_pullback P n)
    (fun G Y K hG hY hYl => Submission.idtp_fons_cs_sos_lipschitz_approx_tangent P n G Y K
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hdn) hG hY hYl)
    (fun G Y K hG hY hYl => Submission.idtp_fons_cs_sos_lipschitz_approx_tangent P _ G Y K
      (Nat.sub_pos_of_lt hdn) hG hY hYl)
    (Submission.dpf_itt_ae_of_ae_pieces P _)
The argument is uniform in d ≥ 0. For d = 0, L = {0}, p = 0, M_0 = M and H^0⌞L is the unit mass at 0.
Imports. The area formula (A1), (A2) and LinearMap.normDet live in Poincare.SimonGMT.Chapter02.AreaLipschitz and Mathlib.Analysis.InnerProductSpace.NormDet. Both are outside the contract import closure. This leaf gets them through the dependency merge of its sibling tangent_along_lipschitz, whose accepted candidate 2626c7a33b0710ef02dabb5fabccd7f228531ad1 has `import Poincare.SimonGMT.Chapter02.AreaLipschitz` and already contains the other reused declarations. Everything else below is in scope after `import GMT.Ch07.Submission`.

Notation. V := ℝ^n, W := ℝ^P, B := ℝ^m (m = n − d ≥ 1, so n = d + m), H^k := μHE[k], p := L.starProjection, q := I − p = Lᗮ.starProjection, M_t := M ∩ p⁻¹(t). For a linear map D between finite-dimensional inner-product spaces, J(D) := normDet D = det(D*D)^{1/2} ≥ 0. For a map G, JG(u) := J(DG(u)) (SimonGMT areaJacobianAt) and Reg G := {u : G is differentiable at u and DG(u) is injective}.
Siblings used.
- (S1) piece_pullback, in dimension n. Let G : ℝ^n → ℝ^P be Lipschitz, S ⊆ ℝ^n Borel, c > 0 with c|a − a'| ≤ |G(a) − G(a')| on S. Then G(S) is Borel, and every property that holds H^n⌞G(S)-a.e. holds at G(b) for L^n-a.e. b ∈ S.
- (S2) ae_transfer, in dimension m. Let S ⊆ ℝ^P be Borel, G_q : ℝ^m → ℝ^P Lipschitz and T_q ⊆ ℝ^m (q ∈ ℕ) with H^m(S ∖ ⋃_q G_q(T_q)) = 0. If a property π satisfies π(G_q(b)) for L^m-a.e. b ∈ T_q, for every q, then π holds H^m-a.e. on S.
- (S3) tangent_along_lipschitz, for k = n and k = m (both ≥ 1). Let G : ℝ^k → ℝ^P be Lipschitz and Y ⊆ ℝ^P Borel with H^k(Y ∩ C) < ∞ for every compact C. Then for L^k-a.e. u: if G(u) ∈ Y, G is differentiable at u and DG(u) is injective, then HasApproximateTangentSpaceAt k Y (G u) (DG(u)(ℝ^k)).
Library facts.
- (A1) Area formula, SimonGMT weighted_area_formula_lipschitz_injOn. Let G : E → E' be Lipschitz between finite-dimensional inner-product spaces, S ⊆ E Borel with G injective on S, and g ≥ 0 any function. Then ∫_{G(S)} g dH^{dim E} = ∫_S JG(u) g(G(u)) du. Also u ↦ JG(u) is measurable (measurable_areaJacobianAt).
- (A2) Sard-type statement, SimonGMT area_image_compl_regularSet_eq_zero: H^{dim E}(G(S ∖ Reg G)) = 0 for G Lipschitz.
- (A3) Lipschitz image bound, euclideanHausdorffMeasure_image_le_of_lipschitzOn: H^k(G(A)) ≤ Lip(G)^k H^k(A).
- (A4) Mathlib NormDet:
 - J(f∘g) = J(f)J(g) if dim(source g) = dim(target g) (normDet_comp_of_finrank_eq);
 - J of a linear isometry is 1;
 - J(U) = |det U| for an endomorphism U;
 - J(f)² = det Gram(f(b_i)) for an orthonormal basis b of the source (normDet_sq_eq_det_gram).
- (A5) Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt.
- (A6) Lusin–Souslin (MeasurableSet.image_of_continuousOn_injOn); LipschitzOnWith.extend_finite_dimension; uniqueness of approximate tangent spaces (HasApproximateTangentSpaceAt.unique); LinearMap.exists_antilipschitzWith.
- (A7) Fubini/Tonelli (lintegral_prod, Measure.ae_ae_of_ae_prod, MeasurePreserving.lintegral_comp).
- (A8) H^k = Lebesgue measure on a k-dimensional space (InnerProductSpace.euclideanHausdorffMeasure_eq_volume), and the image of Lebesgue measure on L under the inclusion L ⊆ W is H^d⌞L (Isometry.map_euclideanHausdorffMeasure).
- (A9) μHE[k] = c_k μH[k] with 0 < c_k < ∞ (euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero); Measure.hausdorffMeasure_apply; Measure.hausdorffMeasure_le_liminf_tsum; Measure.addHaar_closedBall'; Fatou (lintegral_liminf_le).

0. (Coordinates.)
- dim V = n = dim(L ×₂ B), so there is a linear isometry Θ : V → L ×₂ B (L² product). Put π₁(z) := (Θz)_L. This is a continuous linear map V → W with values in L, so p(π₁ z) = π₁ z.
- Put j(s) := Θ⁻¹(0, s) for s ∈ B. Then j is linear and injective, and Θ⁻¹(t, s) = Θ⁻¹(t, 0) + j(s).
- (t, s) ↦ Θ⁻¹(t, s) carries the product of the Lebesgue measures of L and B to Lebesgue measure on V.
- By (A8), H^n = Lebesgue measure on V and H^m = Lebesgue measure on B, and Lebesgue measure on L is carried by the inclusion to H^d⌞L.

1. (Jacobian identity.) Let D : V → W be linear with p(Dv) = π₁(v) for all v and L ⊆ D(V). Put Y := D∘j : B → W. Claim: J(D) = J(Y) and Y(B) = D(V) ∩ L^⊥.
 (a) For s ∈ B, p(Ys) = π₁(js) = (Θ js)_L = 0. So Y(B) ⊆ L^⊥.
 (b) By linearity, D(Θ⁻¹(t, s)) = D(Θ⁻¹(t, 0)) + Y(s).
 (c) Let τ ∈ L. Pick v with Dv = τ. Then (Θv)_L = π₁(v) = p(τ) = τ. By (b), τ = D(Θ⁻¹(τ, 0)) + Y((Θv)_B), so D(Θ⁻¹(τ, 0)) − τ = Y(−(Θv)_B) ∈ Y(B).
 (d) The linear map τ ↦ D(Θ⁻¹(τ, 0)) − τ, from L to Y(B), therefore lifts through the surjection Y : B → Y(B). This gives a linear β : L → B with Y(βτ) = D(Θ⁻¹(τ, 0)) − τ.
 (e) Let U(t, s) := (t, s + βt). Then U is block unipotent, and det U = 1. Indeed, with N(t, s) := (0, βt), det(I + N) = det(I + (fst)(inr∘β)) = det(I_L + 0) = 1.
 (f) Let D₀(t, s) := t + Y(s). Then D(Θ⁻¹(t, s)) = t + Y(βt) + Y(s) = D₀(U(t, s)), so D∘Θ⁻¹ = D₀∘U.
 (g) Take orthonormal bases (e_a) of L and (f_b) of B; the vectors (e_a, 0), (0, f_b) form an orthonormal basis of L ×₂ B. Then D₀(e_a, 0) = e_a and D₀(0, f_b) = Y f_b ∈ L^⊥. So the Gram matrix of D₀ is block diagonal, diag(I, Gram(Y f_b)), and (A4) gives J(D₀)² = J(Y)². Hence J(D₀) = J(Y), both being ≥ 0.
 (h) By (A4), J(D) = J(D∘Θ⁻¹) = J(D₀∘U) = J(D₀)|det U| = J(Y), since Θ⁻¹ is an isometry between spaces of equal dimension.
 (i) Y(B) ⊆ D(V) ∩ L^⊥ by (a). Conversely, let y = Dv ∈ L^⊥. Then π₁(v) = p(y) = 0, so v = j((Θv)_B) and y = Y((Θv)_B).
2. (Coercivity constant.) For continuous linear A : V → W, let K_A := ker(p∘A) and π_{K_A} its orthogonal projection.
 - The linear map v ↦ (p(Av), π_{K_A} v) is injective: if both components vanish, then v ∈ K_A, so v = π_{K_A} v = 0.
 - Hence (LinearMap.exists_antilipschitzWith) there is C_A > 0 with |v| ≤ C_A·max(|p(Av)|, |π_{K_A} v|) for all v.
3. (One approximately linear piece.) Claim: let F' : V → W be Lipschitz, T ⊆ V Borel, and m' > 0 with m'|a − a'| ≤ |F'(a) − F'(a')| on T. Let A' : V → W be continuous linear with |F'(a) − F'(a') − A'(a − a')| ≤ (2C_{A'})⁻¹|a − a'| on T, and assume L ⊆ A'(V) if T ≠ ∅. Then there are a Lipschitz H' : V → W, a Borel Ω' ⊆ V and c > 0 such that:
 - c|z − z'| ≤ |H'(z) − H'(z')| on Ω';
 - H'(Ω') = F'(T);
 - p(H'(z)) = π₁(z) for every z ∈ V.
 Proof.
 - If T = ∅, take H' := π₁, Ω' := ∅ and c := 1.
 - Otherwise, p∘A' maps V onto L: for ℓ = A'w ∈ L, p(A'w) = ℓ. So dim K := dim K_{A'} = n − d = m. Fix a linear isometry κ : K → B.
 - Put Λ(x, y) := Θ⁻¹(p(x), κ(π_K y)). This is continuous linear W × V → V. Because Θ⁻¹ and κ are isometries, |p(x)| ≤ |Λ(x, y)| and |π_K y| ≤ |Λ(x, y)|.
 - Put Φ(u) := Λ(F'(u), u). Φ is Lipschitz with some constant K_Φ, and Φv − Φw = Λ(F'v − F'w, v − w).
 - Let v, w ∈ T and C := C_{A'}. Since p is 1-Lipschitz, |p(A'(v − w))| ≤ |p(F'v − F'w)| + |F'v − F'w − A'(v − w)| ≤ |Φv − Φw| + (2C)⁻¹|v − w|. Also |π_K(v − w)| ≤ |Φv − Φw|.
 - By step 2, |v − w| ≤ C|Φv − Φw| + |v − w|/2. Hence (★) |v − w| ≤ 2C|Φv − Φw|.
 - By (★), Φ is injective on T. So Ω' := Φ(T) is Borel (A6), and Φ has an inverse ψ : Ω' → T.
 - By (★), F'∘ψ is Lipschitz on Ω' with constant 2C·Lip(F'). Extend it to a Lipschitz h : V → W (A6), and set H'(z) := π₁(z) + q(h(z)). Then H' is Lipschitz and p(H'z) = π₁ z.
 - For u ∈ T, π₁(Φu) = (ΘΦu)_L = p(F'u) and h(Φu) = F'(u). So H'(Φu) = p(F'u) + q(F'u) = F'(u), and H'(Ω') = F'(T).
 - Finally, for u, u' ∈ T we have |Φu − Φu'| ≤ (K_Φ + 1)|u − u'|. So c := m'(K_Φ + 1)⁻¹ gives c|Φu − Φu'| ≤ m'|u − u'| ≤ |H'(Φu) − H'(Φu')|.
4. (Adapted pieces.) Let (F_i, B_i, m_i) be the pieces of (H2).
 (a) Good parameters. Fix i. By (H4) and F_i(B_i) ⊆ M, the property "∃Q with HasApproximateTangentSpaceAt n M x Q and L ⊆ Q" holds H^n⌞F_i(B_i)-a.e. By (S1), it holds at F_i(a) for L^n-a.e. a ∈ B_i.
  - By (S3) with k = n and Y := M (Borel by (H1), locally H^n-finite by (H3)), for a.e. a ∈ B_i, M has approximate tangent space DF_i(a)(V) at F_i(a). Here F_i(a) ∈ M, F_i is differentiable at a and DF_i(a) is injective.
  - By uniqueness, Q = DF_i(a)(V), so L ⊆ DF_i(a)(V) for a.e. a ∈ B_i.
  - Remove a Borel null set containing the exceptional points (toMeasurable). This gives a Borel G_i ⊆ B_i with L^n(B_i ∖ G_i) = 0 and L ⊆ DF_i(a)(V) for all a ∈ G_i.
 (b) Partition. Apply (A5) to F_i on G_i (where F_i is differentiable) with tolerance r(A) := (2C_A)⁻¹ > 0. This gives pairwise disjoint Borel sets t_{i,k} covering G_i and continuous linear maps A_{i,k} such that:
  - |F_i(a) − F_i(a') − A_{i,k}(a − a')| ≤ (2C_{A_{i,k}})⁻¹|a − a'| on G_i ∩ t_{i,k};
  - if G_i ≠ ∅, then A_{i,k} = DF_i(y) for some y ∈ G_i, so L ⊆ A_{i,k}(V) by (a).
 (c) Reparametrize. Index q ↔ (i, k) through Nat.unpair. Step 3 applies with F' := F_i, T := G_i ∩ t_{i,k} ⊆ B_i, m' := m_i and A' := A_{i,k}. It gives H_q Lipschitz, Ω_q Borel and c_q > 0 such that:
  - H_q is c_q-bi-Lipschitz from below on Ω_q;
  - H_q(Ω_q) = F_i(G_i ∩ t_{i,k}) ⊆ F_i(B_i) ⊆ M;
  - p∘H_q = π₁ on V.
 (d) Disjointness. Let q ≠ q'. If i ≠ i', the images lie in the disjoint sets F_i(B_i) and F_{i'}(B_{i'}). If i = i', then k ≠ k'. Since F_i is injective on B_i (lower bound) and t_{i,k} ∩ t_{i,k'} = ∅, the images are disjoint.
 (e) Null remainder. Let Z := M ∖ ⋃_q H_q(Ω_q). If x ∈ Z ∩ F_i(B_i), say x = F_i(a), then a ∉ G_i, since otherwise a ∈ some t_{i,k}. So Z ⊆ (M ∖ ⋃_i F_i(B_i)) ∪ ⋃_i F_i(B_i ∖ G_i).
  - The first set is H^n-null by (H2).
  - By (A3) and (A8), H^n(F_i(B_i ∖ G_i)) ≤ Lip(F_i)^n L^n(B_i ∖ G_i) = 0.
  - Hence H^n(Z) = 0.
5. (One piece.) Fix q and write H := H_q, Ω := Ω_q.
 (a) H is injective on Ω. By (S1) with c := c_q, H(Ω) is Borel and H^n⌞H(Ω)-a.e. properties pull back to L^n-a.e. w ∈ Ω.
 (b) Good points. For L^n-a.e. w ∈ Ω:
  - H is differentiable at w and DH(w) is injective. By (A2), H^n(H(Ω ∖ Reg H)) = 0. Pulling back "x ∉ H(Ω ∖ Reg H)" by (a) gives w ∈ Reg H.
  - M has approximate tangent space R_w := DH(w)(V) at H(w), and L ⊆ R_w. This follows from (S3) with k = n and Y = M, from (H4) pulled back by (a), and from uniqueness, as in 4(a).
 (c) Where H is differentiable, p∘DH(w) = π₁. Indeed p∘H = π₁ is linear, and D(p∘H)(w) = p∘DH(w).
 (d) Slices. For t ∈ L put H_t(s) := H(Θ⁻¹(t, s)) and Ω_t := {s ∈ B : Θ⁻¹(t, s) ∈ Ω}. Since s ↦ Θ⁻¹(t, 0) + j(s) is affine with derivative j:
  - H_t is Lipschitz and Ω_t is Borel;
  - if H is differentiable at w = Θ⁻¹(t, s), then DH_t(s) = DH(w)∘j;
  - H_t is injective on Ω_t;
  - H_t(Ω_t) = H(Ω) ∩ p⁻¹(t). For ⊆: p(H(Θ⁻¹(t, s))) = π₁(Θ⁻¹(t, s)) = t. For ⊇: if z ∈ Ω and p(Hz) = t, then (Θz)_L = t, so Hz = H_t((Θz)_B) with (Θz)_B ∈ Ω_t.
 (e) Fubini. By step 0 and (A7) applied to the full-measure set of w satisfying "w ∈ Ω ⇒ (b)": for L^d-a.e. t ∈ L and L^m-a.e. s, if s ∈ Ω_t, then (b) holds at w = Θ⁻¹(t, s).
 (f) At such (t, s), step 1 applies to D := DH(w). Its hypotheses hold by (c) and (b). It gives:
  - JH_t(s) = J(DH(w)∘j) = JH(w);
  - (DH(w)∘j)(B) = R_w ∩ L^⊥;
  - DH_t(s) = DH(w)∘j is injective.
 (g) Coarea on the piece. Let g ≥ 0 be Borel and f := 1_Ω·JH·(g∘H), a Borel function on V.
  - By (A1) for H on Ω, step 0 and Tonelli: ∫_{H(Ω)} g dH^n = ∫_V f = ∫_L ∫_B f(Θ⁻¹(t, s)) ds dt.
  - For t as in (e), (A1) for H_t on Ω_t (dim B = m) together with (d) and (f) gives ∫_{H(Ω)∩p⁻¹(t)} g dH^m = ∫_{Ω_t} JH_t(s) g(H_t(s)) ds = ∫_B f(Θ⁻¹(t, s)) ds.
  - The middle function of t is measurable by Tonelli.
  - Transport to H^d⌞L by step 0. Then t ↦ ∫_{H(Ω)∩p⁻¹(t)} g dH^m is a.e.-measurable for H^d⌞L, and ∫_{H(Ω)} g dH^n = ∫_L ∫_{H(Ω)∩p⁻¹(t)} g dH^m dH^d(t).
 (h) Record for step 9: for H^d⌞L-a.e. t and L^m-a.e. s ∈ Ω_{q,t}, with w = Θ⁻¹(t, s):
  - H_{q,t} is differentiable at s with injective derivative DH_q(w)∘j;
  - M has approximate tangent space R_w at H_q(w);
  - (DH_q(w)∘j)(B) = R_w ∩ L^⊥.
6. (Null sets have null slices.) Claim: if H^n(Z) = 0, then H^m(Z ∩ p⁻¹(t)) = 0 for H^d⌞L-a.e. t.
 - By (A9), μH[n](Z) = 0. Fix j ∈ ℕ. Since the 1/(j+1)-premeasure of Z is 0 (hausdorffMeasure_apply), there is a cover (C_{j,k})_k of Z with diam C_{j,k} ≤ 1/(j+1) and Σ_k (diam C_{j,k})^n < 1/(j+1); only nonempty C_{j,k} count in the sum.
 - Choose x_{j,k} with p(C_{j,k}) ⊆ closedBall(p(x_{j,k}), diam C_{j,k}); this works because p is 1-Lipschitz. Put ψ_j(t) := Σ_k 1_{closedBall(p(x_{j,k}), diam C_{j,k})}(t)·(diam C_{j,k})^m, a Borel function.
 - For every t, the sets C_{j,k} ∩ p⁻¹(t) cover Z ∩ p⁻¹(t), and their diameters are ≤ 1/(j+1) → 0. A nonempty one has t in the k-th ball and diameter ≤ diam C_{j,k}; an empty one contributes 0 (m ≥ 1). So hausdorffMeasure_le_liminf_tsum gives μH[m](Z ∩ p⁻¹(t)) ≤ liminf_j ψ_j(t).
 - Let c_B be the Lebesgue measure of the unit ball of L. By step 0 and addHaar_closedBall', ∫_L ψ_j dH^d ≤ c_B Σ_k (diam C_{j,k})^d (diam C_{j,k})^m ≤ c_B/(j+1), since d + m = n.
 - Fatou gives ∫_L liminf_j ψ_j dH^d = 0. So liminf_j ψ_j(t) = 0, hence μH[m](Z ∩ p⁻¹(t)) = 0 and H^m(Z ∩ p⁻¹(t)) = 0, for H^d-a.e. t ∈ L.
7. (Summation: proof of (ii).)
 - If A_q ⊆ S are Borel and pairwise disjoint with H^k(S ∖ ⋃_q A_q) = 0, then ∫_S g dH^k = Σ_q ∫_{A_q} g dH^k. This holds by a.e.-equality of S and ⋃_q A_q and countable additivity (lintegral_iUnion).
 - Apply this to S := M, A_q := H_q(Ω_q) and remainder Z (steps 4 and 5(a)). This gives ∫_M g dH^n = Σ_q ∫_{H_q(Ω_q)} g dH^n.
 - By step 6, H^m(Z ∩ p⁻¹(t)) = 0 for a.e. t. For such t, apply it to S := M_t and A_q := H_q(Ω_q) ∩ p⁻¹(t), whose remainder is Z ∩ p⁻¹(t). This gives ∫_{M_t} g dH^m = Σ_q ∫_{H_q(Ω_q)∩p⁻¹(t)} g dH^m.
 - So t ↦ ∫_{M_t} g dH^m is a.e. equal to a countable sum of a.e.-measurable functions (5(g)), and is therefore a.e.-measurable.
 - Finally, by 5(g) and lintegral_tsum, ∫_M g dH^n = Σ_q ∫_L ∫_{H_q(Ω_q)∩p⁻¹(t)} g dH^m dH^d = ∫_L ∫_{M_t} g dH^m dH^d. This is (ii).
8. (Local finiteness of slices.) For j ∈ ℕ, apply (ii) to g := 1_{closedBall(0, j)}. Then ∫_L H^m(M_t ∩ closedBall(0, j)) dH^d = H^n(M ∩ closedBall(0, j)) < ∞, by (H3). So for a.e. t, H^m(M_t ∩ C) < ∞ for every compact C, since each C lies in some closedBall(0, j).
9. (Proof of (i).) Fix t ∈ L with the following properties, which hold together for a.e. t:
 - 5(h) holds for every q;
 - H^m(Z ∩ p⁻¹(t)) = 0 (step 6);
 - M_t is locally H^m-finite (step 8).
 M_t is Borel by (H1).
 - Rectifiability. M_t ⊆ (Z ∩ p⁻¹(t)) ∪ ⋃_q H_{q,t}(B), using 5(d). Each H_{q,t} : ℝ^m → ℝ^P is Lipschitz. So M_t is countably m-rectifiable, with exceptional set Z ∩ p⁻¹(t).
 - Tangent planes. Let q ∈ ℕ. By 5(h), for a.e. s ∈ Ω_{q,t}, H_{q,t} is differentiable at s with injective derivative.
  - By (S3) with k = m, G := H_{q,t} and Y := M_t (Borel, locally H^m-finite), for a.e. s ∈ Ω_{q,t}, M_t has approximate tangent space (DH_q(w)∘j)(B) = R_w ∩ L^⊥ at x = H_{q,t}(s). This uses x ∈ H_q(Ω_q) ∩ p⁻¹(t) ⊆ M_t.
  - By 5(h), M has approximate tangent space R_w at x. Any Q with HasApproximateTangentSpaceAt n M x Q equals R_w by uniqueness. So HasApproximateTangentSpaceAt m M_t x (Q ⊓ L^⊥) holds for every such Q.
  - Apply (S2) with S := M_t, G_q := H_{q,t} and T_q := Ω_{q,t}. Its remainder is M_t ∖ ⋃_q H_{q,t}(Ω_{q,t}) = Z ∩ p⁻¹(t), which is H^m-null. So this property holds for H^m-a.e. x ∈ M_t. This is (i). ∎

## Key steps

1. Coordinates V = ℝ^n ≅ L ×₂ ℝ^m (Θ, π₁, j). Jacobian identity: if p∘D = π₁ and L ⊆ range D, then the shear U (det 1) and the block-diagonal Gram matrix of D₀ give J(D) = J(D∘j) and range(D∘j) = range D ∩ L^⊥.
2. Refine the given pieces to parameters where L ⊆ range DF_i (piece_pullback, tangent_along_lipschitz, uniqueness). Partition with tolerance (2C_A)⁻¹ and reparametrize each part by Φ = Θ⁻¹(pF', κπ_{ker pA'}) as H(Ω), with H Lipschitz, bi-Lipschitz on Ω and p∘H = π₁. The images are disjoint, lie in M and cover it up to a null set.
3. On each piece, the area formula for H and for the slice maps H(Θ⁻¹(t,·)) (whose derivative is DH∘j and Jacobian equals JH), together with Tonelli, gives ∫_{H(Ω)} g dH^n = ∫_L ∫_{H(Ω)∩p⁻¹(t)} g dH^m dH^d with an a.e.-measurable inner function.
4. Eilenberg: an H^n-null Z has H^m-null slices for H^d-a.e. t (fine covers, ψ_j with ∫_L ψ_j ≤ c_B/(j+1), Fatou).
5. Summing over the disjoint pieces gives (ii); (ii) gives local finiteness of slices. The slice maps make M_t countably m-rectifiable, and tangent_along_lipschitz in dimension m with ae_transfer gives Tan(M_t, x) = T_xM ∩ L^⊥ a.e., which is (i).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606d = workspace HEAD; mathlib 25730c7c); diff of 480b1bd:GMT/Ch07/Submission.lean vs the workspace Submission.lean (identical, contract only)`
- `rg -n -i 'coarea|eilenberg|starProjection x = t' <snapshot>/project/GMT --glob '*.lean' (only the unproved Ch02 Contract/Submission Props EilenbergInequality and CoareaFormula); rg -n 'spine_coarea|dimred_cs_sos|idtp_fons' <snapshot>/project (no match)`
- `rg -n in <snapshot>/mathlib/Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, hausdorffMeasure_apply, hausdorffMeasure_le_liminf_tsum, ae_ae_of_ae_prod, normDet_sq_eq_det_gram, normDet_comp_of_finrank_eq, normDet_eq_abs_det, LinearIsometry.normDet_eq_one, LipschitzOnWith.extend_finite_dimension, MeasurableSet.image_of_continuousOn_injOn, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, Isometry.map_euclideanHausdorffMeasure, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, lintegral_liminf_le`
- `grep -n in SimonGMT 2b36630 (lake-packages-25730c7c/simongmt): Chapter02/AreaLipschitz.lean (areaRegularSet, area_image_compl_regularSet_eq_zero, weighted_area_formula_lipschitz_injOn), Chapter02/Area.lean (areaJacobianAt = normDet), Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn), Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique)`
- `lake env lean /tmp/sc-decomp/Probe.lean after import GMT.Ch07.Submission. Unknown: LinearMap.normDet, areaJacobianAt, weighted_area_formula_lipschitz_injOn. In scope: euclideanHausdorffMeasure_image_le_of_lipschitzOn, HasApproximateTangentSpaceAt.unique, Submodule.measurePreserving_measurableEquivProd, AffineSubspace.euclideanHausdorffMeasure_eq_lintegral, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LipschitzOnWith.extend_real, MeasurableSet.image_of_continuousOn_injOn`
- `python3 -I over dag.json: accepted nodes mentioning 'starProjection x = t', coarea, Eilenberg, ApproximatesLinearOn or Matrix.gram give idtp_fons_cs_sos_spine_coarea (byte-identical type) and dtc_bc_lc_sl_cc_critical_null. Also status, candidate commit and type identity of dpf_rectifiable_bilipschitz_pieces, ptd_piece_image_measurable_ae_pullback, dpf_itt_ae_of_ae_pieces, idtp_fons_cs_sos_lipschitz_approx_tangent and dimred_cs_sos_lipschitz_approx_tangent`
- `git show d35a0320:GMT/Ch07/Submission.lean, lines 6460–7367 (accepted lipschitz_tangent and spine_coarea proofs; master block 6555–7356; instantiation 7358–7367)`
- `git show {a2ba78f,bed5b84,bfe4427,2626c7a,a216804,08ae824,2e81485}:GMT/Ch07/Submission.lean | head (imports); git merge-base --is-ancestor checks (a2ba78f, bed5b84 and bfe4427 are ancestors of 2626c7a; a2ba78f and bfe4427 are not ancestors of 08ae824)`
- `sed -n '/^## Proof/,/^## Key steps/p' on the parent-supplied-natural-proof.md of the 4 reused nodes; read the split_off_spine decomposition-v1.json for the reuse precedent and import policy`
- `python3 -I /tmp/sc-decomp/scripts/gen_challenges.py (gmt-compare.py child_modules, contract mode), then lake env lean /tmp/sc-decomp/Challenges.lean (44 s, exit 0)`
- `lake env lean /tmp/sc-decomp/Check1.lean (with the AreaLipschitz import; #print axioms: propext, sorryAx (stubs only), Classical.choice, Quot.sound)`
- `grep 'dimred_cs_sos_sc_' in dag.json, nodes/*/decomposition-v*.json, .humanize/math-wiki and GMT/ (no match)`
- `sed -n 390,425p book/chapter-07.txt (Simon 7.3.5 at lines 407–418, proof left to the reader)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-ac07005b8c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-e483a373f0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-6d6197c93d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-aad3a33660/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/sc-decomp/Challenges.lean`
- `/tmp/sc-decomp/Check1.lean`

Pins. The snapshot is project b4d606d (= workspace HEAD) with mathlib 25730c7c; SimonGMT is 2b36630. The proof base 480b1bd has a contract-identical Submission.lean.

What the snapshot lacks. It has no slicing or coarea theorem for rectifiable sets: its project tree holds only the unproved Ch02 contract Props EilenbergInequality and CoareaFormula, and no spine/dimred/idtp declaration. Every Mathlib lemma the new child uses is present at the cited files. The SimonGMT area formula and LinearMap.normDet lie outside the contract import closure, so the new child inherits them by merging the accepted candidate 2626c7a.

Reuse. The reusable work is in DAG-accepted commits, not in the snapshot. idtp_fons_cs_sos_spine_coarea (d35a0320) has exactly the selected type. Its proof uses the four accepted declarations reused here, whose types are byte-identical.

Lean check. All 5 child types elaborate in the comparator's contract scope. The parent's frozen type follows by a one-line assembly, and the new child is proved by the accepted master block. The new name dimred_cs_sos_sc_coarea_of_pieces is unused.
