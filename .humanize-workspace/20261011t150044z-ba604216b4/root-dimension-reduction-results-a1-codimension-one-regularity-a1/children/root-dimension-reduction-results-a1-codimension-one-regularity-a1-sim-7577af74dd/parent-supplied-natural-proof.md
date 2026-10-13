# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 5 (β)–(γ) of the supplied proof of CodimensionOneRegularity for the cone factor S₀: Simon Appendix B, B.1, B.2 and the printed proof of B.2 (Simons [Sim68], in the form of Schoen–Simon–Yau; chapter-07-source.txt lines 1256–1539 = chapter-B.txt lines 1–233), together with the verification of the hypotheses of B.2. Supporting book results: Ch. 2, 5.1–5.12, first and second variation (chapter-02.txt lines 1290–1405); Ch. 5, 7.1 (chapter-05.txt lines 1312–1366); Ch. 3, 1.8–1.9, densities (chapter-03.txt lines 298–323); Ch. 6, 3.3–3.9, push-forward of integer multiplicity currents. This is part B of the previously reviewed analytic core of this node, stated as its own theorem.
Explicit departures from the parent text:
(i) The hypothesis “y ∈ reg C and Θ^m(μ_C, y) = 1 for every y ∈ spt C ∖ {0}” is supplied by the parent in step 5(α) (from the sibling children low_density_regular and, at the parent level, regular_point_density).
(ii) Stationarity of M is proved directly from minimality, by the same first-variation competitors that give stability, instead of citing MinimizingImpliesStationary; the vertex density is computed from the multiplicity-one representation instead of the constancy theorem.
(iii) The mass facts are cited from the sibling child oriented_piece_mass instead of the parent's sibling im_mass_measure.

Sibling children used.
- vanish_off_support (Submission.dtc_vanish_off_support): S(ω) = 0 whenever tsupport ω ∩ spt S = ∅.
- cone_pullback_identity (Submission.cone_current_apply_dilation_pullback): for a cone C, λ > 0 and ω ∈ 𝒟^m(ℝ^P) there is ω' ∈ 𝒟^m(ℝ^P) with ω'(y) = λ^{−m}ω(λ^{−1}y) for all y and C(ω') = C(ω).
- oriented_piece_mass (Submission.codim1_massOn_eq_lintegral_of_oriented_rep): if V ⊆ U is open, M' ⊆ V Borel, θ' ≥ 0 measurable, ξ' a.e. strongly measurable on M' and H^m-a.e. on M' a unit orientation of some subspace, and T(ω) = ∫_{M'} θ'·ξ'(ω) dH^m whenever tsupport ω ⊆ V, then for every open W ⊆ V: M_W(T) ≤ ∫_{M'∩W} θ' dH^m (first conclusion), with equality when the right side is finite (second conclusion).
- orientation_sign (Submission.rsdic_unitOrientation_eq_or_eq_neg): two unit orientations of the same subspace satisfy w = v or w = −v.
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual): a continuous linear L : Λ_m → Λ^m such that every unit orientation ξ of a subspace satisfies (a) |ξ(α)| ≤ |α| for all α, (b) |L(ξ)| ≤ 1 and (c) ξ(L(ξ)) = 1.

Notation.
- H^d := μHE[d]; on a d-dimensional affine plane it is d-dimensional Lebesgue measure. ω_d := unitBallVolume d is H^d of a unit d-disc. B_ρ(y) := ball y ρ; r(x) := |x|.
- For a k-covector α, |α| is the Euclidean coefficient norm (covectorEuclideanNorm). M_W(T) := T.massOn W is the supremum of ofReal T(ω) over ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ W and |ω| ≤ 1 pointwise.
- “T vanishes on W” means T(ω) = 0 whenever tsupport ω ⊆ W; Z(T) is the union of the open W with compact closure on which T vanishes, and spt T := ℝ^P ∖ Z(T).
- “Θ^m(μ_T, y) = θ” means HasMassDensity T y θ: θ ≥ 0 and M_{B_ρ(y)}(T)/(ω_mρ^m) → θ as ρ ↓ 0.
- For an IMRep R = (M_R, θ_R, ξ_R), μ_R(A) := ∫_{M_R∩A} θ_R dH^m.
- M := spt C ∖ {0}.

General facts (for a current T ∈ 𝒟_m(U), U open).
(G1) Uniqueness of densities. If Θ^m(μ_T, y) = θ₁ and Θ^m(μ_T, y) = θ₂, then θ₁ = θ₂, because limits in [0, ∞] are unique and ofReal is injective on [0, ∞).
(G2) Positive density forces support. If T vanishes on an open W, then M_{W'}(T) = 0 for every W' ⊆ W. Hence if y ∈ U has Θ^m(μ_T, y) = θ > 0, then y ∈ spt T: otherwise y lies in an open W on which T vanishes, M_{B_t(y)}(T) = 0 for small t, and the density is 0 ≠ θ.
(G7) Density of C¹ submanifolds (Simon Ch. 3, 1.8–1.9). If M' ∩ B_r(w) is a relatively closed embedded C¹ m-submanifold of B_r(w) containing w, then H^m(M' ∩ B_s(w))/(ω_ms^m) → 1 as s ↓ 0: near w, M' is the graph over T_wM' of a C¹ map whose Lipschitz constant on B_s(w) tends to 0 as s ↓ 0, and the area formula gives H^m(M' ∩ B_s(w)) = ω_ms^m(1 + o(1)).

Proof. Fix P, m, C, A₀ satisfying the hypotheses, and let θ satisfy Θ^m(μ_C, 0) = θ.

B0. (Set-up.)
- dim A₀ = m + 1 ≤ P.
- C is integer multiplicity (first conjunct of IsMinimizingIn). Fix an IMRep R = (M_R, θ_R, ξ_R) of C and put μ := μ_R; then μ(K) < ∞ for compact K (IMRep.locallyIntegrable_mult).
- The general facts (G1), (G2), (G7) above hold with U := ℝ^P.
(B0.1) Vertex negligibility. Let χ_ε ∈ C^∞_c(B_{2ε}(0)) with 0 ≤ χ_ε ≤ 1 and χ_ε = 1 on B_ε(0). For every ω ∈ 𝒟^m(ℝ^P), C(χ_εω) → 0 as ε ↓ 0.
- C(χ_εω) = ∫_{M_R} θ_Rχ_ε⟨ω, ξ_R⟩ dH^m.
- For ε ≤ 1/2 the integrand is dominated by θ_R·max|ω|·1_{B_1(0)}, because ξ_R(x) is a unit orientation of a plane for H^m-a.e. x ∈ M_R (IMRep.orients) and then |ξ_R(x)(α)| ≤ |α| by unit_orientation_dual (a); the dominant is integrable since μ(closedBall(0, 1)) < ∞.
- It tends pointwise to θ_R1_{{0}}⟨ω, ξ_R⟩, and H^m({0}) = 0 because m ≥ 1. Dominated convergence gives the limit 0.
- Since (1 − χ_ε)ω ∈ 𝒟^m(ℝ^P) with tsupport ⊆ tsupport ω ∖ B_ε(0), it follows that C(ω) = lim_{ε↓0} C((1 − χ_ε)ω).

B1. (Trivial case M = ∅.) Then spt C ⊆ {0}.
- For every ω, tsupport((1 − χ_ε)ω) is disjoint from {0} ⊇ spt C, so C((1 − χ_ε)ω) = 0 by vanish_off_support.
- By (B0.1), C(ω) = 0 for every ω. Thus C = 0, M_{B_ρ(0)}(C) = 0 for every ρ, and Θ^m(μ_C, 0) = 0.
- By (G1), θ = 0 ≤ 1. From now on assume M ≠ ∅.

B2. (Local structure of M; parent 5(β)(i).) Let y ∈ M. By hypothesis y ∈ regularSet C and Θ^m(μ_C, y) = 1. The definition of regularSet gives:
- ρ_y > 0, m_y ∈ ℤ ∖ {0}, and an embedded C¹ m-dimensional submanifold M_y ∋ y;
- an orientation ξ_y of M_y: continuous on M_y, with ξ_y(w) a unit orientation of tangentSpace(M_y, w);
- H^m(M_y ∩ K) < ∞ for compact K ⊆ B_{ρ_y}(y);
- C(ω) = m_y ∫_{M_y} ⟨ω, ξ_y⟩ dH^m whenever tsupport ω ⊆ B_{ρ_y}(y).
(B2a) Relative closedness.
- Take a chart (V, W_ψ, ψ) of M_y at y. Since ψ(V) = W_ψ ∩ M_y and ψ is proper, W_ψ ∩ M_y is closed in W_ψ.
- Choose ρ' with 0 < ρ' ≤ min(ρ_y, |y|)/2 and B_{2ρ'}(y) ⊆ W_ψ.
- Then M_y ∩ B_{ρ'}(y) is relatively closed in B_{ρ'}(y), and 0 ∉ closedBall(y, ρ').
(B2b) If tsupport ω ⊆ B_{ρ'}(y) ∖ M_y, an open set, then ω = 0 on M_y and C(ω) = 0. So spt C ∩ B_{ρ'}(y) ⊆ M_y.
(B2c) Mass identity. Apply oriented_piece_mass (second conclusion) with θ' :≡ |m_y|, V := B_{ρ'}(y), M' := M_y ∩ B_{ρ'}(y) and ξ' := sign(m_y)ξ_y (extended by 0 off M'). Its hypotheses hold:
- M' is Borel, being relatively closed in the open ball;
- ξ' is continuous on the Borel set M', hence measurable, and sign(m_y)ξ_y(w) is a unit orientation of tangentSpace(M_y, w) for every w ∈ M';
- C(ω) = m_y∫_{M_y}⟨ω, ξ_y⟩ dH^m = |m_y|∫_{M'}⟨ω, sign(m_y)ξ_y⟩ dH^m whenever tsupport ω ⊆ B_{ρ'}(y);
- for open W ⊆ B_{ρ'}(y), ∫_{M'∩W} |m_y| dH^m = |m_y|·H^m(M_y ∩ W) ≤ |m_y|·H^m(M_y ∩ closedBall(y, ρ')) < ∞, since closedBall(y, ρ') is a compact subset of B_{ρ_y}(y).
This gives M_W(C) = |m_y|·H^m(M_y ∩ W) for every open W ⊆ B_{ρ'}(y).
(B2d) Densities.
- By (B2c) and (G7) (C¹ case), Θ^m(μ_C, w) = |m_y| for every w ∈ M_y ∩ B_{ρ'}(y).
- In particular |m_y| = Θ^m(μ_C, y) = 1 by (G1).
- Every such w has density 1 > 0, so w ∈ spt C by (G2).
(B2e) Consequences.
- M ∩ B_{ρ'}(y) = M_y ∩ B_{ρ'}(y), and this set lies in A₀ since spt C ⊆ A₀.
- C(ω) = ∫_M ⟨ω, ξ'_y⟩ dH^m for tsupport ω ⊆ B_{ρ'}(y), where ξ'_y := m_yξ_y is a continuous unit orientation.
- M_W(C) = H^m(M ∩ W) for open W ⊆ B_{ρ'}(y).
- Hence M is an embedded C¹ m-submanifold of ℝ^P contained in the (m+1)-dimensional subspace A₀, i.e. a C¹ hypersurface of A₀ ∖ {0}. It is relatively closed in ℝ^P ∖ {0}, because spt C is closed.

B3. (Global orientation and representation off the vertex.)
(B3a) Agreement on overlaps. If B_{ρ'}(y) ∩ B_{ρ'}(y') ≠ ∅, then ∫_M ⟨ω, ξ'_y − ξ'_{y'}⟩ dH^m = 0 for every ω supported in the overlap. Test with ω = φβ, where φ ranges over C^∞_c and β over a countable dense set of constant covectors. This gives ξ'_y = ξ'_{y'} H^m-a.e. on M in the overlap.
(B3b) A continuous global orientation. The set where ξ'_y ≠ ξ'_{y'} is relatively open in M and H^m-null. A nonempty relatively open subset of a C¹ m-submanifold has positive H^m-measure, so the two orientations agree everywhere on the overlap. This defines a continuous unit orientation ξ_M of M.
(B3c) Representation off the vertex. Let ω have tsupport ω ⊆ ℝ^P ∖ {0}.
- Cover the compact set tsupport ω by finitely many balls B_{ρ'}(y_j), y_j ∈ M, together with the open set ℝ^P ∖ spt C.
- Take a smooth partition of unity subordinate to this cover. On pieces supported in ℝ^P ∖ spt C both sides vanish, by vanish_off_support and because M ∩ (ℝ^P ∖ spt C) = ∅.
- Hence (†) C(ω) = ∫_M ⟨ω, ξ_M⟩ dH^m for every ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ ℝ^P ∖ {0}.
(B3d) Finiteness and mass off the vertex.
- For W open with compact closure in ℝ^P ∖ {0}, H^m(M ∩ W) < ∞, since finitely many balls B_{ρ'}(y_j) cover M ∩ closure(W).
- M is relatively closed in the open set ℝ^P ∖ {0}, hence Borel, and ξ_M (extended by 0 off M) is measurable. By oriented_piece_mass (second conclusion) with θ' :≡ 1, V := ℝ^P ∖ {0}, M' := M and ξ' := ξ_M, using (†): M_W(C) = H^m(M ∩ W) for such W.
- For 0 < ε < ρ, W_ε := B_ρ(0) ∖ closedBall(0, ε) is such a W, and oriented_piece_mass (first conclusion) applied to the representation R gives M_{W_ε}(C) ≤ ∫_{M_R∩W_ε} θ_R dH^m ≤ μ(closedBall(0, ρ)) < ∞. So H^m(M ∩ W_ε) ≤ μ(closedBall(0, ρ)); letting ε ↓ 0 (monotone convergence, 0 ∉ M) gives H^m(M ∩ B_ρ(0)) < ∞ for every ρ.

B4. (Cone structure; parent 5(β)(iii)–(iv).)
- Let t > 0 and let W be an open set with compact closure on which C vanishes. Then C vanishes on tW. Indeed, let tsupport ω ⊆ tW. The sibling child cone_pullback_identity with λ := t^{−1} gives ω' ∈ 𝒟^m(ℝ^P) with ω'(z) = t^{m}ω(tz) and C(ω') = C(ω). Since tsupport ω' = t^{−1}tsupport ω ⊆ W, we get C(ω) = C(ω') = 0.
- closure(tW) = t·closure(W) is compact. Hence Z(C) is invariant under all dilations, and so is spt C = ℝ^P ∖ Z(C). Thus M = tM for all t > 0: M is a cone.
- 0 ∈ closure(M), because ty → 0 as t ↓ 0 for y ∈ M. Also closure(M) ⊆ spt C = M ∪ {0} and 0 ∉ M. Hence closure(M) ∖ M = {0}.

B5. (Competitors and first variation; stationarity.)
(B5a) Deformation. Let Z ∈ C^∞_c(ℝ^P ∖ {0}; ℝ^P), put K_Z := spt Z, and choose an open W with compact closure in ℝ^P ∖ {0} and K_Z ⊆ W.
- For |t| < t₀ := 1/(1 + 2 sup|DZ|), the map Φ_t := id + tZ is a C^∞ diffeomorphism of ℝ^P equal to the identity off K_Z.
- Hence Φ_t(K_Z) = K_Z and Φ_t(W) = W. If Z(w) ∈ A₀ for all w, then also Φ_t(A₀) = A₀.
(B5b) The push-forward is a current. S_t(ω) := C(Φ_t^#ω), the push-forward Φ_{t#}C (Simon 6.2.23).
- Φ_t is proper, so Φ_t^# maps 𝒟^m(ℝ^P) into itself.
- Φ_t^# is sequentially continuous in the test-form topology: supports stay in Φ_t^{−1}(K), and derivatives converge uniformly by the chain rule. So S_t ∈ 𝒟_m(ℝ^P).
(B5c) S_t is an admissible competitor.
- Integer multiplicity. By the area formula on the rectifiable set M_R (Simon Ch. 6, 3.3–3.9), S_t is represented by (Φ_t(M_R), θ_R∘Φ_t^{−1}, ξ_t) with ξ_t(Φ_t x) := Λ_mDΦ_t(x)ξ_R(x)/|Λ_mDΦ_t(x)ξ_R(x)|. Here Φ_t(M_R) is Borel and countably m-rectifiable, its approximate tangent space at Φ_t(x) is DΦ_t(x)(T_xM_R), and the multiplicity is locally integrable since the Jacobians are bounded.
- Same boundary. m ≥ 2, so S_t(dφ) = C(Φ_t^#dφ) = C(d(Φ_t^#φ)) = 0 = C(dφ), using ∂C = 0.
- Compact support of the difference. If tsupport ω ∩ K_Z = ∅, then Φ_t^#ω = ω: at points off K_Z the map Φ_t is the identity nearby, and at points of K_Z both sides vanish because Φ_t(K_Z) = K_Z. So spt(S_t − C) ⊆ K_Z, a compact subset of W.
- Minimality of C in ℝ^P therefore gives M_W(C) ≤ M_W(S_t).
(B5d) Both masses are areas.
- For tsupport ω ⊆ W: S_t(ω) = C(Φ_t^#ω), with tsupport Φ_t^#ω ⊆ W ⊆ ℝ^P ∖ {0}.
- By (†) and the area formula for the injective smooth map Φ_t, S_t(ω) = ∫_{Φ_t(M)} ⟨ω, ξ_{M,t}⟩ dH^m, with ξ_{M,t} the transported unit orientation.
- Φ_t(M) ∩ W = Φ_t(M ∩ W) is Borel with finite H^m-measure (Φ_t is a diffeomorphism with Φ_t(W) = W, and H^m(M ∩ W) < ∞ by (B3d)), and ξ_{M,t} is measurable. By oriented_piece_mass (second conclusion) with θ' :≡ 1, V := W, M' := Φ_t(M) ∩ W and ξ' := ξ_{M,t}, M_W(S_t) = H^m(Φ_t(M) ∩ W) = H^m(Φ_t(M ∩ W)); by (B3d), M_W(C) = H^m(M ∩ W).
- So f_Z(t) := H^m(Φ_t(M ∩ W)) satisfies f_Z(t) ≥ f_Z(0) for |t| < t₀.
(B5e) First variation.
- By the area formula, f_Z(t) = ∫_{M∩W} J_t dH^m with J_t(x) := |(τ_1 + tDZ(x)τ_1)∧⋯∧(τ_m + tDZ(x)τ_m)|, for τ an orthonormal basis of T_xM.
- J_t(x) is smooth in t with derivatives bounded uniformly in x ∈ K_Z, J_t = 1 off K_Z, and ∂_tJ_t|_{t=0} = Σ_i τ_i·DZ(x)τ_i = div_M Z(x) (Simon Ch. 2, 5.1–5.3).
- So f_Z is differentiable at 0 with f_Z'(0) = ∫_M div_M Z dH^m. Since 0 is an interior minimum, ∫_M div_M Z dH^m = 0.
- For X ∈ C¹_c(ℝ^P ∖ {0}; ℝ^P), mollification gives such Z → X in C¹ with supports in a fixed compact set. Since H^m(M ∩ K) < ∞ (B3d), ∫_M div_M X dH^m = 0.
- Hence the varifold V := v(M, 1) is stationary in ℝ^P ∖ {0} (Simon Ch. 2, 5.7–5.8).

B6. (Smoothness and zero mean curvature; parent 5(β)(ii).)
- Apply Simon Ch. 5, Theorem 7.1, last part, in the open set ℝ^P ∖ {0} with N := ℝ^P (C^∞). Its hypotheses hold: V is stationary, θ ≡ 1, and Θ^m(V, y) = 1 at every y ∈ M by (G7).
- So for each y ∈ M and each q there is σ_q > 0 such that, after a rigid motion, spt V ∩ B_{σ_q}(y) = M ∩ B_{σ_q}(y) is the graph of a C^{q+2,α} function. This holds at every y ∈ M and for every q, so M is a C^∞ submanifold.
- Since V is stationary and M is smooth, the first variation formula (Simon Ch. 2, 4.29 and 5.10) gives ∫_M X·H_M dH^m = 0 for all X ∈ C¹_c(ℝ^P ∖ {0}; ℝ^P). So the mean curvature H_M ≡ 0.
- As M ⊆ A₀, M is a smooth minimal hypersurface of A₀ ∖ {0}, with closure(M) ∖ M = {0} (B4).

B7. (Stability B.1; parent 5(β)(v); Simon Ch. 2, 5.11–5.12.)
(B7a) Unit normal. Fix an orientation of A₀ and let ν be the unit normal of M in A₀ determined by ξ_M; ν is smooth on M.
(B7b) The variation field. Let ζ ∈ C^∞_c(M), with support K ⊆ M compact. Let Z ∈ C^∞_c(ℝ^P ∖ {0}; ℝ^P) satisfy Z(w) ∈ A₀ for all w and Z = ζν on M. It exists:
- extend ζν to a smooth A₀-valued map near K, by local extensions and a partition of unity;
- compose with the orthogonal projection onto A₀;
- multiply by a cutoff equal to 1 near K with compact support in ℝ^P ∖ {0}.
(B7c) Minimality at t = 0. With W and Φ_t as in (B5a), Φ_t(A₀) = A₀. By (B5d), f(t) := H^m(Φ_t(M ∩ W)) has a minimum at t = 0. f is C^∞ near 0:
- J_t² is a polynomial in t whose coefficients are bounded on M ∩ K_Z, and J_t² ≥ 1/2 for |t| small.
- So J_t is C^∞ in t with t-derivatives bounded uniformly on M ∩ K_Z, and J_t = 1 off K_Z.
- Since H^m(M ∩ W) < ∞, f may be differentiated under the integral.
Hence f'(0) = 0 and f''(0) ≥ 0.
(B7d) Second variation. Apply the second variation formula (Simon Ch. 2, 5.4 and 5.11) to the smooth stationary M:
- The acceleration ∂²Φ_t/∂t² vanishes. The variation field Z|_M = ζν is normal to M.
- (D_{τ_i}(ζν))^⊥ = (∇_{τ_i}ζ)ν. Indeed D_{τ_i}ν ∈ A₀ is orthogonal to ν, hence tangent to M.
- B(τ_i, τ_j) = h_{ij}ν, where A = (h_{ij}) is the second fundamental form of M in A₀.
- So f''(0) = ∫_M (|∇^Mζ|² − |A|²ζ²) dH^m (Simon 5.12 (‡)).
(B7e) Conclusion. B.1 holds: ∫_M (|∇^Mζ|² − |A|²ζ²) dH^m ≥ 0 for every ζ ∈ C^∞_c(M). By mollification in charts it extends to locally Lipschitz ζ with compact support in M: |A| is continuous on M, and the supports stay in a fixed compact subset of M.

B8. (Simons' theorem B.2: the printed proof.) Identify A₀ with ℝ^{m+1} by a linear isometry. Then M is a smooth m-dimensional cone in ℝ^{m+1} with zero mean curvature, closure(M) ∖ M = {0}, stable in the sense of B.1, and 2 ≤ m ≤ 6. We show |A| ≡ 0 on M.
(B8a) Simons' identity and inequality.
- In a local orthonormal frame, Simons' identity B.8 reads ½Δ_M|A|² = Σ_{i,j,k} h²_{ij;k} − |A|⁴ + h_{ij}H_{;ij} + H h_{mi}h_{mj}h_{ij}. It follows from the symmetry B.4, the Codazzi equations B.5, the Gauss equations B.6 and the commutation formula B.7.
- With H = 0 this is ½Δ_M|A|² = Σ h²_{ij;k} − |A|⁴.
- For a cone, Lemma B.11 gives Σ_{i,j,k} h²_{ij;k} − |∇_M|A||² ≥ 2r^{−2}|A|² wherever |A| > 0. Choose τ_m radial along the ray through x; then h_{mj} = 0 and h_{ij;m} = −r^{−1}h_{ij} by homogeneity. The algebra is SimonGMT AppendixB.simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le and cone_simonsDefect_lower_bound.
- Where |A| = 0, ∇|A| = 0 H^m-a.e. (|A| is locally Lipschitz) and ½Δ|A|² = Σ h²_{ij;k} ≥ 0.
- Hence, H^m-a.e. on M, (1) ½Δ_M|A|² + |A|⁴ ≥ 2r^{−2}|A|² + |∇_M|A||².
(B8b) Basic inequality. Let ψ be locally Lipschitz with compact support in M, and insert ζ := |A|ψ in B.1:
 (2) ∫|A|⁴ψ² ≤ ∫|∇(|A|ψ)|² = ∫(|∇ψ|²|A|² + ψ²|∇|A||² + 2ψ|A|∇ψ·∇|A|).
Integration by parts and (1) give
 2∫ψ|A|∇ψ·∇|A| = ∫∇(ψ²)·∇(½|A|²) = −∫ψ²Δ_M(½|A|²) ≤ ∫ψ²(|A|⁴ − 2r^{−2}|A|² − |∇|A||²).
Combining: (3) 2∫_M r^{−2}ψ²|A|² dH^m ≤ ∫_M |A|²|∇_Mψ|² dH^m.
(B8c) Extension. (3) holds for every locally Lipschitz ψ on M with (4) ∫_M r^{−2}ψ²|A|² < ∞.
- For 0 < κ < 1 let γ_κ be Lipschitz with 0 ≤ γ_κ ≤ 1, γ_κ = 1 for |x| ∈ (κ, κ^{−1}), γ_κ = 0 for |x| < κ/2 or |x| > 2κ^{−1}, and |∇γ_κ| ≤ 3/|x|.
- ψγ_κ has compact support in M, since closure(M) ∖ M = {0}. Apply (3) to it.
- Use |∇(ψγ_κ)|² ≤ (1 + η)|∇ψ|²γ_κ² + (1 + η^{−1})ψ²|∇γ_κ|². By (4), ∫|A|²ψ²|∇γ_κ|² ≤ 9∫_{{κ/2<r<κ}∪{κ^{−1}<r<2κ^{−1}}} r^{−2}ψ²|A|² → 0.
- Let κ ↓ 0:
  - the left side converges by dominated convergence, with dominant r^{−2}ψ²|A|², which is integrable by (4);
  - the first term on the right is at most (1 + η)∫|A|²|∇ψ|², because γ_κ ≤ 1;
  - the second term on the right tends to 0.
  Then let η ↓ 0.
(B8d) Cone integrals.
- Σ := M ∩ ∂B_1(0) is a compact smooth (m−1)-dimensional submanifold. It is closed because closure(M) ∩ ∂B_1(0) = M ∩ ∂B_1(0), and the sphere is transversal to the cone M.
- (5) ∫_M f dH^m = ∫_0^∞ r^{m−1}∫_Σ f(rσ) dH^{m−1}(σ) dr for continuous f ≥ 0 on M.
- |A(x)|² = r^{−2}|A(x/|x|)|² by homogeneity. Put c_Σ := ∫_Σ |A|² dH^{m−1} < ∞.
(B8e) Choice of ψ.
- Choose ε > 0 with (m/2 − 2 + ε)² < 2 and (1 + ε)² < 2. This is possible exactly because 2 ≤ m ≤ 6, e.g. ε = 1/10 (SimonGMT AppendixB.exists_final_exponent).
- Put ψ := r^{1+ε}r₁^{1−m/2−2ε} with r₁ := max{1, r}. Then r^{−2}ψ² = r^{2ε} on {r < 1} and r^{2−m−2ε} on {r > 1}.
- By (5), ∫_M r^{−2}ψ²|A|² = c_Σ(∫_0^1 r^{m−3+2ε} dr + ∫_1^∞ r^{−1−2ε} dr) < ∞. So (4) holds.
- |∇_Mψ| = (1+ε)r^{ε} on {r < 1} and |m/2 − 2 + ε|r^{1−m/2−ε} on {r > 1}, since |∇_Mr| = 1 on a cone.
- So (3) becomes (6): 2∫_{M∩{r<1}} |A|²r^{2ε} + 2∫_{M∩{r>1}} |A|²r^{2−m−2ε} ≤ (1+ε)²∫_{M∩{r<1}} |A|²r^{2ε} + (m/2 − 2 + ε)²∫_{M∩{r>1}} |A|²r^{2−m−2ε}, with all integrals finite.
- Since 2 − (1+ε)² > 0 and 2 − (m/2 − 2 + ε)² > 0, both integrals vanish. As |A| is continuous, |A| ≡ 0 on M.

B9. (Hyperplane.)
- |A| ≡ 0 means ν is locally constant on M. So each connected component M_c of M lies in an affine hyperplane of A₀.
- That hyperplane passes through 0. The ray through a point of M_c is connected, lies in M (B4) and meets M_c, so it lies in M_c. Hence M_c ⊆ H_c for an m-dimensional linear subspace H_c ⊆ A₀.
- M_c is open in H_c, being an m-submanifold of the m-plane H_c. It is closed in H_c ∖ {0}, since M is relatively closed in ℝ^P ∖ {0} and M_c is closed in M. H_c ∖ {0} is connected (m ≥ 2), so M_c = H_c ∖ {0}.
- Suppose two components had H_c ≠ H_{c'}. Then H_c ∩ H_{c'} has dimension m − 1 ≥ 1 and contains some w ≠ 0 lying in both M_c and M_{c'}, which is impossible.
- Hence M = H₀ ∖ {0} for a single m-dimensional linear subspace H₀ ⊆ A₀.

B10. (Density at the vertex.)
(B10a) Constant orientation. H₀ ∖ {0} is connected (m ≥ 2). For y ∈ M, ξ_M(y) is a unit orientation of tangentSpace(M, y) = H₀; fixing one unit orientation ξ_{H₀} of H₀, orientation_sign gives ξ_M(y) ∈ {ξ_{H₀}, −ξ_{H₀}}. A continuous map from a connected set into this two-point set is constant; so ξ_M is constant, say ξ.
(B10b) Global representation. For every ω ∈ 𝒟^m(ℝ^P), (B0.1) and (†) give
 C(ω) = lim_{ε↓0} C((1 − χ_ε)ω) = lim_{ε↓0} ∫_{H₀} (1 − χ_ε)⟨ω, ξ⟩ dH^m = ∫_{H₀} ⟨ω, ξ⟩ dH^m,
by dominated convergence (H^m(H₀ ∩ {0}) = 0).
(B10c) Mass of balls. By oriented_piece_mass (second conclusion) with θ' :≡ 1, V := ℝ^P, M' := H₀ (closed, hence Borel) and the constant ξ' := ξ, and (B10b): M_{B_ρ(0)}(C) = H^m(H₀ ∩ B_ρ(0)) = ω_mρ^m < ∞, because H^m on the m-plane H₀ is m-dimensional Lebesgue measure.
(B10d) Conclusion. (ω_mρ^m)^{−1}M_{B_ρ(0)}(C) ≡ 1, so Θ^m(μ_C, 0) = 1, and by (G1) θ = 1 ≤ 1.
This proves the statement. ∎

## Key steps

1. The vertex is negligible for C; if spt C ⊆ {0} then C = 0 and θ = 0. Otherwise, regularity with density one off the vertex makes C = [[M]] near each point of M = spt C ∖ {0}, with a continuous global orientation; oriented_piece_mass gives M_W(C) = H^m(M ∩ W) away from 0.
2. spt C is a cone (cone_pullback_identity), so M is a C¹ hypersurface cone of A₀ ∖ {0} with closure(M) ∖ M = {0}.
3. The competitors (id + tZ)_#C are admissible; minimality gives first variation zero, Ch. 5, 7.1 makes M smooth and minimal, and the second variation for Z = ζν tangent to A₀ gives stability B.1.
4. Simons' identity B.8 and Lemma B.11 inserted in B.1 with the cut-offs γ_κ and ψ = r^{1+ε}r₁^{1−m/2−2ε} (2 ≤ m ≤ 6) force |A| ≡ 0; so M = H₀ ∖ {0}, C = [[H₀]] (orientation_sign), and θ = Θ^m(μ_C, 0) = 1 ≤ 1.

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
