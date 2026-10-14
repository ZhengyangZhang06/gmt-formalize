# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of 7.2, (1)–(3): “the main difficulty is to establish the appropriate total boundedness property … an easy consequence of the Deformation Theorem: … 5.3 guarantees that for T ∈ I_{M,W} we can find integer multiplicity P, R, S with (2), (3) … since there are only finitely many currents P as in (2), we have (1)”. It is used in the pigeonhole form of the parent proof's Step 5, with the preliminaries (P3) extension/restriction of domains, (P4) lattice chains and (P5) approximation with control.
- For P = m + 1 (book ℓ = 0), the deformation theorem is replaced by the printed steps (27)–(37) of the proof of 5.1 with Q := T (identity retraction, R = 0).
- For P < m + 1 all currents vanish.
Errata: the printed “Σ_{j=1}^N B_{ε,W̃}(P_j)” in (1) is the union; the integer coefficients are bounded because |β_F| ρ^n ≤ M(P) (P4). Since the conclusion uses global masses on U and arbitrary currents on U, no condition relating ρ to dist(K, ∂U) is needed: the deformation outputs are simply restricted to U.

Notation. n := m + 1; H := μHE[n]; |α| := covectorEuclideanNorm α; ‖ω‖ := sup_x |ω(x)|. M := M_U for currents on U and M := M_{ℝ^P} for currents on ℝ^P (GeometricCurrentOn.mass). “aX + bY” is the current ω ↦ aX(ω) + bY(ω).

0. (P < n.) Every alternating map of degree > P on ℝ^P vanishes, so every test form of degree n or n + 1 is 0 and every current of degree n or n + 1 is the zero current. Take J' := J and, for i, j ∈ J', R := 0 and S := 0 (integer multiplicity by F1). Then T_i − T_j = 0 = ∂0 + 0 and M(0) + M(0) = 0 < ε. From now on P ≥ n.

Preliminary facts.
(F1)–(F3)
   - The zero current is integer multiplicity with zero mass.
   - aX + bY is a current with ∂(aX + bY) = a∂X + b∂Y; it is integer multiplicity when X, Y are and a, b ∈ ℤ (sibling im_lincomb).
   - M_V(X + Y) ≤ M_V(X) + M_V(Y) and M_V(−X) = M_V(X).
   - ofReal |X(η)| ≤ M_V(X) · ofReal ‖η‖ when tsupport η ⊆ V (rescale ±η/‖η‖ and use GeometricCurrentOn.le_massOn).
(F4) Mass formula (sibling im_mass_formula): M_V(τ(M, θ, ξ)) = ∫_{M∩V} θ dH for open V, for every rectifiable triple (M, θ, ξ).
(G1) Support vanishing. If X ∈ D_k(U), η ∈ D^k(U) and tsupport η ∩ spt X = ∅, then X(η) = 0.
   Proof: tsupport η is a compact subset of zeroRegion(X) = ⋃{V open : closure V compact ⊆ U, X vanishes on V}. Choose finitely many such V_1, …, V_N covering tsupport η, and a smooth partition of unity ψ_1, …, ψ_N with tsupport ψ_i ⊆ V_i and Σ_i ψ_i = 1 on tsupport η (SmoothPartitionOfUnity subordinate to the cover). Then η = Σ_i ψ_i η with tsupport(ψ_i η) ⊆ V_i, so X(η) = Σ_i X(ψ_i η) = 0.
   In particular spt ∂X ⊆ spt X, since ∂X(η) = X(dη) and tsupport dη ⊆ tsupport η.
(G2) Let X = τ(M, θ, ξ) be integer multiplicity in U. Then H(M ∖ spt X) = 0, X = τ(M ∩ spt X, θ, ξ), and (M ∩ spt X, θ, ξ) is again an integer multiplicity rectifiable triple.
   Proof: V := U ∖ spt X = zeroRegion(X) is open, and X(η) = 0 whenever tsupport η ⊆ V (G1), so M_V(X) = 0. By F4, ∫_{M∩V} θ dH = 0, and θ > 0 on M, so H(M ∩ V) = 0. Removing an H-null set from M changes neither the integrals defining τ nor the blow-up integrals in HasWeightedApproximateTangentSpaceAt (blowUpMap x r maps H-null sets to H-null sets), and it preserves the other triple conditions.
(G3) Extension (P3). Fix once and for all χ ∈ C^∞(ℝ^P) with 0 ≤ χ ≤ 1, χ = 1 on an open neighbourhood N of K, and tsupport χ compact ⊆ U (smooth Urysohn, exists_contMDiffMap_one_nhds_of_subset_interior, applied to K and a compact neighbourhood of K inside U). For X ∈ D_k(U) with spt X ⊆ K define X̃(ω) := X(χω) for ω ∈ D^k(ℝ^P); note χω ∈ D^k(U). Then:
   (i) X̃ ∈ D_k(ℝ^P): it is linear, and if ω_q → 0 in D^k(ℝ^P) then χω_q → 0 in D^k(U) (supports in tsupport χ; Leibniz rule for iterated derivatives).
   (ii) X̃(ω) = X(ω) for ω ∈ D^k(U): tsupport((1 − χ)ω) ∩ K = ∅, so X((1 − χ)ω) = 0 by G1.
   (iii) If k ≥ 1 then ∂X̃ = (∂X)~, the extension of ∂X with the same χ (spt ∂X ⊆ K by G1). Indeed ∂X̃(ω) = X(χ dω) = X(d(χω)) − X(η) with η := d(χω) − χ dω ∈ D^k(U). By the Leibniz rule for fderiv, η(x) depends linearly on Dχ(x), so η = 0 on the open set N where χ ≡ 1. Hence tsupport η ⊆ ℝ^P ∖ N is disjoint from K, X(η) = 0 by G1, and ∂X̃(ω) = X(d(χω)) = ∂X(χω).
   (iv) M(X̃) ≤ M(X) and M(∂X̃) ≤ M(∂X): if ω is admissible on ℝ^P then χω is admissible on U (|χω| ≤ |ω| ≤ 1).
   (v) spt X̃ ⊆ K: if tsupport ω ∩ K = ∅ then X̃(ω) = X(χω) = 0 by G1.
   (vi) If X = τ(M, θ, ξ) is integer multiplicity in U, then by G2 and χ = 1 on K ⊇ spt X, X̃(ω) = ∫_{M∩spt X} θ ξ(χω) dH = ∫_{M∩spt X} θ ξ(ω) dH. The triple (M ∩ spt X, θ, ξ) is an integer multiplicity rectifiable triple in ℝ^P: integrability on compact subsets of ℝ^P follows from integrability on M ∩ K (K compact ⊆ U), and the tangent data are as in G2. So X̃ is integer multiplicity in ℝ^P.
(G4) Restriction to U (P3). For Y ∈ D_k(ℝ^P) let Y|_U := Y.restrictDomain (subset_univ U) ∈ D_k(U), so Y|_U(ω) = Y(ω). Then ∂(Y|_U) = (∂Y)|_U, and M(Y|_U) ≤ M(Y) since forms admissible on U are admissible on ℝ^P. If Y = τ(M, θ, ξ) is integer multiplicity in ℝ^P, then Y|_U = τ(M ∩ U, θ, ξ) is integer multiplicity in U. Indeed, for x ∈ M ∩ U, f ∈ C_c with spt f ⊆ B_R(0) and r < dist(x, ℝ^P ∖ U)/R, the blow-up integrals of (M ∩ U, θ) and (M, θ) at x coincide, because blowUpMap x r '' (M ∖ U) misses B_R(0). The other conditions are inherited.
(G5) Lattice chains (P4). Let ρ > 0, β : LatticeFaceIndex n P → ℝ and Pc ∈ D_n(ℝ^P) with IsLatticeChain ρ β Pc. For a face index F₀ = (z₀, α₀) let F̊₀ := {x : ρ z₀_i < x_i < ρ(z₀_i + 1) for i ∈ range α₀, x_i = ρ z₀_i otherwise}, the relative interior of latticeFace ρ F₀.
   - For p ∈ F̊₀ and 0 < σ < min(ρ, dist(p, latticeFace ρ F₀ ∖ F̊₀)), the ball B_σ(p) meets no face of direction α₀ other than latticeFace ρ F₀: faces of direction α₀ in the same affine n-plane meet latticeFace ρ F₀ only in its relative boundary, and faces of direction α₀ in other parallel planes are at distance ≥ ρ.
   - Let dx^{α₀} ∈ Λ^n be the covector with dx^{α₀}(e_α) = δ_{αα₀} for increasing α, so |ψ(x) dx^{α₀}| = |ψ(x)|. For ψ ∈ C_c^∞(B_σ(p)) and ω := ψ dx^{α₀}: latticeFaceAction ρ F ω = 0 for every F = (z, α) with α ≠ α₀ (since ω(x)(e_α) = 0), and for every F ≠ F₀ of direction α₀ (since ω vanishes on that face). So the tsum defining Pc(ω) has the single term Pc(ω) = β(F₀) ∫_{latticeFace ρ F₀} ψ dH.
   - The face is the image of [0, ρ]^n ⊆ ℝ^n under the affine isometry y ↦ ρz₀ + Σ_j y_j e_{α₀(j)}. H is preserved by isometries (Isometry.euclideanHausdorffMeasure_image) and equals Lebesgue measure on ℝ^n, so H(latticeFace ρ F₀) = ρ^n, and H⌞F̊₀ charges every nonempty relatively open subset of F̊₀.
   Consequently, if β(F₀) ≠ 0:
   (a) Taking ψ ≥ 0 with ψ(p) > 0 gives Pc(ω) ≠ 0 for forms supported in arbitrarily small balls around p, so p ∈ spt Pc. Hence F̊₀ ⊆ spt Pc and latticeFace ρ F₀ = closure F̊₀ ⊆ closure(spt Pc).
   (b) Take compact sets C_q ↑ F̊₀ and ψ_q ∈ C_c^∞ with 0 ≤ ψ_q ≤ 1, ψ_q = 1 on C_q, and support in a neighbourhood of C_q meeting no other α₀-face. The forms ω_q := sign(β(F₀)) ψ_q dx^{α₀} are admissible, and Pc(ω_q) = |β(F₀)| ∫_{latticeFace ρ F₀} ψ_q dH, where H(C_q) ≤ ∫_{latticeFace ρ F₀} ψ_q dH ≤ H(latticeFace ρ F₀) = ρ^n and H(C_q) ↑ H(F̊₀) = ρ^n. Hence Pc(ω_q) → |β(F₀)| ρ^n, and |β(F₀)| ρ^n ≤ M(Pc).
   (c) For every bounded Y ⊆ ℝ^P, only finitely many face indices F satisfy latticeFace ρ F ∩ Y ≠ ∅: z ranges over a bounded subset of ℤ^P and α over the finite set SimonMultiIndex n P.

1. (Approximation at scale ρ, case P ≥ n + 1: parent (P5) via DeformationTheorem.) Write P = n + ℓ = m + 1 + ℓ with ℓ ≥ 1 (transport all data along this equality of dimensions), and let C = C(m, ℓ) be given by DeformationTheorem. Fix ρ > 0. For each j let X_j := T̃_j (G3 with k = n). Then:
   - X_j ∈ D_n(ℝ^P) is integer multiplicity (G3(vi));
   - ∂X_j = (∂T_j)~ is integer multiplicity, by G3(iii) and G3(vi) applied to the integer multiplicity current ∂T_j, whose support lies in K by G1;
   - spt X_j ⊆ K, and M(X_j) + M(∂X_j) ≤ M(T_j) + M(∂T_j) ≤ B < ∞.
   DeformationTheorem gives Pc_j, β_j, R̃_j ∈ D_{n+1}(ℝ^P) and S̃_j ∈ D_n(ℝ^P) with:
   - IsLatticeChain ρ β_j Pc_j and X_j − Pc_j = ∂R̃_j + S̃_j;
   - M(Pc_j) ≤ C M(X_j) ≤ CB, M(R̃_j) ≤ Cρ M(X_j) ≤ CρB, M(S̃_j) ≤ Cρ M(∂X_j) ≤ CρB;
   - spt Pc_j ⊆ thickening(2√P ρ, spt X_j) ⊆ thickening(2√P ρ, K);
   - all β_j(F) ∈ ℤ, and R̃_j, S̃_j integer multiplicity (since X_j and ∂X_j are).
   Let Y_ρ := cthickening(2√P ρ, K), a bounded set, and 𝓕_ρ := {F : latticeFace ρ F ⊆ Y_ρ}, a finite set by G5(c). By G5(a), β_j(F) ≠ 0 implies latticeFace ρ F ⊆ closure(spt Pc_j) ⊆ Y_ρ, i.e. F ∈ 𝓕_ρ. By G5(b), |β_j(F)| ≤ M(Pc_j)/ρ^n ≤ CB/ρ^n. Hence β_j lies in 𝓑_ρ := {β : β(F) ∈ ℤ ∩ [−CB/ρ^n, CB/ρ^n] for F ∈ 𝓕_ρ, β(F) = 0 for F ∉ 𝓕_ρ}, a finite set independent of j. Put R_j := R̃_j|_U, S_j := S̃_j|_U and Q_j := Pc_j|_U (G4). Then R_j and S_j are integer multiplicity, T_j − Q_j = ∂R_j + S_j on D^n(U) (G3(ii), G4), and M(R_j) + M(S_j) ≤ 2CρB.

2. (Approximation at scale ρ, case P = n: printed (27)–(37) of 5.1 with Q := X, R := 0.) Fix ρ > 0 and let X_j := T̃_j ∈ D_n(ℝ^n) as in step 1: integer multiplicity, spt X_j ⊆ K, M(X_j) + M(∂X_j) ≤ B, and ∂X_j ∈ D_m(ℝ^n).
   (a) (Density; (27)–(28).) Write X_j = τ(M_j, θ_j, ξ_j) with H(M_j ∖ K) = 0 (G2, G3). For H-a.e. x ∈ M_j, ξ_j(x) = ±simpleNVector τ(x) for an orthonormal basis τ(x) of ℝ^n. Moreover simpleNVector τ = det[τ] · e with e := simpleNVector(e_1, …, e_n) and det[τ] = ±1 (multilinearity and alternation). So ξ_j = ε_j e with ε_j(x) ∈ {±1} a.e. on M_j. Put u_j := ε_j θ_j 1_{M_j}. Then u_j is integer-valued and integrable, u_j = 0 a.e. outside K, X_j(ω) = ∫ u_j(x) ω(x)(e_1, …, e_n) dx (H = μHE[n] is Lebesgue measure on ℝ^n), and M(X_j) = ∫ |u_j| dx (F4).
   (b) (Translation estimate.) For h ∈ ℝ^n, ∫ |u_j(x + h) − u_j(x)| dx ≤ |h| M(∂X_j).
   Proof: let g ∈ C_c^∞(ℝ^n) with |g| ≤ 1. By the fundamental theorem of calculus for t ↦ g(y − th) and Fubini (the integrand is bounded by sup|Dg| |h| |u_j|),
   ∫ (u_j(x + h) − u_j(x)) g(x) dx = ∫ u_j(y)(g(y − h) − g(y)) dy = −∫_0^1 ∫ u_j(y) ⟨Dg(y − th), h⟩ dy dt.
   For fixed t, ⟨Dg(y − th), h⟩ = div G_t(y) with G_t(y) := g(y − th) h ∈ C_c^∞(ℝ^n; ℝ^n). Let ω_t ∈ D^{n−1}(ℝ^n) be the (n−1)-form whose coefficient on the increasing (n−1)-tuple omitting e_i is ±G_t^i, with signs chosen so that dω_t(e_1, …, e_n) = div G_t for the convention exteriorDerivative = alternatizeUncurryFin ∘ fderiv. Then |ω_t(y)| = |G_t(y)| ≤ |h|, and ∫ u_j div G_t dy = X_j(dω_t) = ∂X_j(ω_t), so |∫ u_j div G_t dy| ≤ |h| M(∂X_j) (F3). Hence |∫ (u_j(· + h) − u_j) g| ≤ |h| M(∂X_j) for every such g. Approximate sign(u_j(· + h) − u_j) a.e. by such g (Lusin's theorem and mollification, truncated to |g| ≤ 1); dominated convergence gives the claim.
   (c) (Medians and the chain; (31), (35)–(36).) In ℝ^n the faces of 𝓛_n(ρ) are the cubes F_z := latticeFace ρ (z, id) = ρ(z + [0, 1]^n), z ∈ ℤ^n, since SimonMultiIndex n n consists of id only. For each z let β_z be an integer median of u_j on F_z, i.e. |F_z ∩ {u_j ≥ β_z}| ≥ ρ^n/2 and |F_z ∩ {u_j ≤ β_z}| ≥ ρ^n/2. Take β_z := the least integer k with |F_z ∩ {u_j ≤ k}| ≥ ρ^n/2, which exists because u_j is integer-valued and finite a.e. Then:
   - |β_z| ρ^n ≤ 2 ∫_{F_z} |u_j|: if β_z ≥ 1 then |u_j| ≥ β_z on a set of measure ≥ ρ^n/2, and symmetrically if β_z ≤ −1;
   - β_z ≠ 0 forces |F_z ∩ {u_j ≠ 0}| > 0, hence F_z ∩ K ≠ ∅ and F_z ⊆ cthickening(√n ρ, K);
   - since a median minimizes c ↦ ∫_{F_z} |u_j − c|, we have ∫_{F_z} |u_j − β_z| ≤ ∫_{F_z} |u_j − ū_z| ≤ ρ^{−n} ∫_{F_z} ∫_{F_z} |u_j(x) − u_j(y)| dy dx, where ū_z := ρ^{−n} ∫_{F_z} u_j.
   Let β_j(z, id) := β_z (finitely many nonzero), v_j := Σ_z β_z 1_{F̊_z}, and Pc_j(ω) := Σ_z β_z latticeFaceAction ρ (z, id) ω = ∫ v_j(x) ω(x)(e_1, …, e_n) dx (cube boundaries are null). Then:
   - Pc_j ∈ D_n(ℝ^n), IsLatticeChain ρ β_j Pc_j, and M(Pc_j) ≤ Σ_z |β_z| ρ^n ≤ 2 ∫ |u_j| = 2M(X_j) ≤ 2B;
   - Pc_j is integer multiplicity: Pc_j = τ(M_P, |v_j|, sign(v_j) e), where M_P := ⋃_{β_z ≠ 0} F̊_z is open and contained in ℝ^n = range(id) (countably n-rectifiable). At each x ∈ M_P, |v_j| is constant near x, so the blow-ups of (M_P, |v_j|) at x converge to |v_j(x)| H⌞ℝ^n; thus ℝ^n = span(e_1, …, e_n) is the weighted approximate tangent space, and sign(v_j(x)) e = ±simpleNVector(e_1, …, e_n).
   (d) (The Poincaré inequality (32), summed over the cubes.) The cubes overlap only in null sets and diam F_z = √n ρ, so by (c) and (b):
   Σ_z ∫_{F_z} |u_j − β_z| ≤ ρ^{−n} ∫∫_{|x − y| ≤ √n ρ} |u_j(x) − u_j(y)| dy dx = ρ^{−n} ∫_{|h| ≤ √n ρ} ∫ |u_j(x + h) − u_j(x)| dx dh ≤ ρ^{−n} · |B_{√n ρ}| · √n ρ · M(∂X_j) ≤ c_n ρ B,
   with c_n := ω_n n^{(n+1)/2}. (Simon obtains (32) cube by cube from the BV Poincaré inequality of Ch. 2, 2.7; only the summed form is used here, and the translation estimate (b) gives it directly.)
   (e) Put R̃_j := 0 ∈ D_{n+1}(ℝ^n) and S̃_j := X_j − Pc_j, integer multiplicity by the sibling im_lincomb. Then X_j − Pc_j = ∂R̃_j + S̃_j, and M(S̃_j) ≤ ∫ |u_j − v_j| = Σ_z ∫_{F_z} |u_j − β_z| ≤ c_n ρ B, since S̃_j(ω) = ∫ (u_j − v_j) ω(x)(e_1, …, e_n) dx and |ω(x)(e_1, …, e_n)| ≤ |ω(x)|.
   (f) If β_j(z, id) ≠ 0 then F_z ⊆ cthickening(√n ρ, K) (finitely many z) and |β_j(z, id)| ≤ 2B/ρ^n. So β_j lies in a finite set 𝓑_ρ independent of j. Put R_j := 0 ∈ D_{n+1}(U), S_j := S̃_j|_U and Q_j := Pc_j|_U (G4). Then R_j and S_j are integer multiplicity, T_j − Q_j = ∂R_j + S_j on D^n(U), and M(R_j) + M(S_j) ≤ c_n ρ B.

3. (Pigeonhole; parent Step 5.) Let C' := max(2C, c_n), or C' := c_n if P = n. In both cases, for every ρ > 0 and every j:
   - β_j ∈ 𝓑_ρ (a finite set);
   - Q_j(ω) = Σ'_F β_j(F) latticeFaceAction ρ F ω for ω ∈ D^n(U);
   - R_j, S_j are integer multiplicity with T_j − Q_j = ∂R_j + S_j and M(R_j) + M(S_j) ≤ C' ρ B.
   Given ε > 0 and an infinite J ⊆ ℕ, choose ρ > 0 with 2C'ρB < ε (possible since B < ∞). The map j ↦ β_j sends the infinite set J into the finite set 𝓑_ρ, so by the pigeonhole principle some fiber J' := {j ∈ J : β_j = β*} is infinite. For i, j ∈ J', Q_i = Q_j (same coefficients), hence T_i − T_j = ∂(R_i − R_j) + (S_i − S_j) on D^n(U). R := R_i − R_j and S := S_i − S_j are integer multiplicity (sibling im_lincomb with a = 1, b = −1), and M(R) + M(S) ≤ M(R_i) + M(R_j) + M(S_i) + M(S_j) ≤ 2C'ρB < ε (F2). ∎

## Key steps

1. P < m + 1: all currents of degree m + 1 and m + 2 vanish; take R = S = 0.
2. Support, extension and restriction calculus: extend T_j to ℝ^P with a cutoff χ (integer multiplicity, same mass and boundary mass, support in K) and restrict outputs back to U.
3. P ≥ m + 2: DeformationTheorem at scale ρ; lattice-chain facts (β_F ≠ 0 ⇒ face ⊆ closure spt Pc, and |β_F|ρ^n ≤ M(Pc)) put the coefficient vectors in a finite set.
4. P = m + 1: printed (27)–(37) of 5.1 — integer medians on lattice cubes, Pc := Σβ_F[[F]], R := 0, S := X − Pc, M(Pc) ≤ 2M(X), and M(S) ≤ c_nρM(∂X) via the translation estimate.
5. Pigeonhole on the coefficient vectors: T_i − T_j = ∂(R_i − R_j) + (S_i − S_j), integer multiplicity by im_lincomb, with mass ≤ 2C'ρB < ε.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def (flatDistance|FlatConvergenceIffWeakConvergence|DeformationTheorem|SlicingTheorem|BoundaryRectifiability|IsIntegerMultiplicity|IsRestriction|IsSlice|IsLatticeChain|IsMeasureRepresentation|CompactlyContainedOpen)|^structure IsRectifiableTriple' project/GMT/Ch06/Contract.lean`
- `rg -n 'IsIntegerMultiplicity|flatDistance' project/GMT (no match outside Contract.lean/Submission.lean)`
- `rg -n 'theorem ae_tendsto_measure_inter_div \(μ|theorem ae_tendsto_lintegral_enorm_sub_div \{|theorem exists_contMDiffMap_zero_one_of_isClosed|theorem tendsto_of_subseq_tendsto|theorem lintegral_liminf_le \{|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀|theorem hasProd_prod_of_ne_finset_one|theorem IsometryEquiv.measurePreserving_euclideanHausdorffMeasure' mathlib/Mathlib`
- `grep -n '^theorem|^def|^structure|^abbrev' over SimonGMT Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,FormsDuality,FormSupNorm}.lean and Chapter03/Rectifiable.lean (GeometricCurrentOn, massOn, massOn_mono, le_massOn, WeaklyConvergesOn.massOn_le_liminf, restrictDomain, zeroRegion/support, HasWeightedApproximateTangentSpaceAt and .unique, CountablyRectifiable.mono, simpleNVector, testFormEuclideanSupNorm)`
- `rg -n -i 'flat (norm|distance|metric)|integer multiplicity|approximate tangent.*(local|subset)' SimonGMT Chapter06 Chapter03 (no integer-multiplicity calculus or flat-norm lemmas)`
- `grep Cauchy–Binet / det-of-minors in Mathlib and SimonGMT (no match; proved inline in the children)`
- `python3 listing of dag.json lean_names and nodes/*/decomposition-v1.json (no fiw_* names reserved)`
- `lake build GMT.Ch06.Submission in /tmp/fiw_check (git archive of the frozen commit d8d46c9, .lake/packages linked to the shared tree, which was left unchanged)`
- `gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement on the 8 statements; lake env lean Scratch/Ch_fiw_*.lean (0 errors)`
- `lake env lean Scratch/AssemblyExact.lean (#print axioms assembly_exact: propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/LincombExact.lean (#print axioms lincomb_exact: propext, Classical.choice, Quot.sound)`
- `book/chapter-06.txt §7 (7.1–7.3, proof of 7.2), 3.1–3.2, 3.13, 4.4–4.5, 5.1 (27)–(37); chapter-03.txt 1.4–1.9; chapter-02.txt 2.6–2.9`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/fiw_check/Scratch/AssemblyExact.lean`
- `/tmp/fiw_check/Scratch/LincombExact.lean`
- `/tmp/fiw_check/Scratch/Ch_fiw_localization.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract. It defines flatDistance, IsIntegerMultiplicity, IsRestriction, IsSlice and IsLatticeChain, plus the three sibling Props this node uses (SlicingTheorem, DeformationTheorem, BoundaryRectifiability).

Neither the project nor SimonGMT has any integer-multiplicity calculus (restriction, sums, 3.13), the mass formula 3.2(3), a flat-norm lemma, or Cauchy–Binet. These are therefore introduced as children, or proved inline (Cauchy–Binet).

Mathlib in the snapshot supplies the tools cited in the child proofs:
- Besicovitch.ae_tendsto_measure_inter_div;
- VitaliFamily.ae_tendsto_lintegral_enorm_sub_div with Besicovitch.vitaliFamily;
- exists_contMDiffMap_zero_one_of_isClosed (smooth Urysohn);
- tendsto_of_subseq_tendsto;
- lintegral_liminf_le;
- euclideanHausdorffMeasure_smul₀ and IsometryEquiv.measurePreserving_euclideanHausdorffMeasure;
- hasSum_sum_of_ne_finset_zero (to_additive of hasProd_prod_of_ne_finset_one).
SimonGMT supplies massOn_mono, le_massOn, restrictDomain, zeroRegion/support and HasWeightedApproximateTangentSpaceAt.unique.

Scratch build of the frozen commit:
- all 8 child types elaborate in the comparator's exact challenge text;
- FlatConvergenceIffWeakConvergence is kernel-checked from fiw_flat_to_weak, fiw_localization, fiw_total_boundedness, fiw_flat_cauchy_limit and the three root siblings;
- fiw_im_lincomb is kernel-checked from fiw_im_series and fiw_im_mass_formula.
Both derivations use only [propext, Classical.choice, Quot.sound]. These checks do not certify the analytic child proofs.
