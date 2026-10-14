# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1.blowup_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Porting note (not a proof step): this proposition is, character for character, the frozen type of the DAG nodes cbr_ci_blowup_limit and dmcbr_ci_blowup_limit of the parallel branches, which are not prerequisites of this leaf. Both were comparator-accepted only after the 10:46:01Z DAG snapshot against which this decomposition's Lean names are checked (accepted-candidate.json at 11:59:58Z and 12:10:48Z), so they cannot be reused by name here. The accepted candidate 2a731a5a contains the complete Lean proof of cbr_ci_blowup_limit (156 lines). It also contains cbr_ci_bl_rescaled_bounds with its sub-lemmas cbr_ci_bl_rb_scale_identities, cbr_ci_bl_rb_null_seq_transfer and cbr_ci_bl_rb_compact_sup_bound, which step 3 below proves inline. That text may be inlined as local `have`s inside this leaf's single theorem, with the call of cbr_ci_bl_rescaled_bounds replaced by the local `have`. Measured with #count_heartbeats, the four rescaled-bounds proofs plus the assembly use about 65 000 heartbeats in total, below the default 200 000.
Lean availability note (not a proof step): the sibling prerequisites density_bounds (DB), constant_limit (CL) and blowup_scale (BS) are comparator-accepted declarations. The runtime merges the accepted candidate commits of a leaf's sibling prerequisites into its Lean base before the leaf starts. Those commits (5ab64315, dccef30a, 0d17fe48) also contain, in GMT/Ch07/Submission.lean, the following comparator-accepted declarations (checked with git show <commit>:GMT/Ch07/Submission.lean). They are therefore available here as Submission.<name>:
(dc) cbr_ci_dilation_calculus. For P, m, a and λ > 0: (1) every X ∈ 𝒟_m(ℝ^P) has a dilation X', i.e. X'(ω) = λ^{−m}X(ω') whenever ω'(y) = ω(dilation a λ y) for all y; (2) if X' is a dilation of X ∈ 𝒟_{m+1}(ℝ^P), then ∂X'(ω) = λ^{−m}∂X(ω') for test m-forms with ω'(y) = ω(dilation a λ y); (4) if X' is a dilation of X ∈ 𝒟_m(ℝ^P) and X(ω) = ∫ξ(x)(ω(x))dμ(x) for all ω, then X'(ω) = ∫ξ(a + λy)(ω(y)) d(ofReal(λ^{−m})·(dilation a λ)_#μ)(y) for all ω; (5) if X' is a dilation of X ∈ 𝒟_m(ℝ^P), then M_{dilation a λ '' W}(X') = ofReal(λ^{−m})·M_W(X) for every W.
(di) cbr_ci_dilation_slice_property. Under (SL) and (RU): if X' is a dilation of X ∈ 𝒟_{d+1}(ℝ^P) by dilation a λ (λ > 0), ∂X = 0, (μ_X, ξ_X) is a representation of X (μ_X finite on compacts, ξ_X μ_X-a.e. strongly measurable, |ξ_X(x)(α)| ≤ |α| μ_X-a.e.), and X has ISP, then X' has ISP.
(cm) cbr_ci_const_vector_massOn. If ν' is finite on compacts, |ζ'(α)| ≤ s|α| for all α, ζ'(β) = s for some |β| ≤ 1, and Ξ(ω) = ∫ζ'(ω(x))dν'(x) for all ω, then M_W(Ξ) = ofReal(s)·ν'(W) for every open W.
(rc) cmcs_restrict_current. If μ' is finite on compact subsets of U, ξ' is μ'-a.e. strongly measurable and |ξ'(x)(α)| ≤ |α| μ'-a.e., then for every set E there is S ∈ 𝒟_m(U) with S(ω) = ∫_Eξ'(x)(ω(x))dμ'(x) for all ω.
(BM) cbr_ci_bl_blowUp_restrict_scaling. For Borel M, Borel θ and λ > 0: (i) blowUpMap a λ '' M is Borel; (ii) Hⁿ⌞(blowUpMap a λ '' M) = ofReal(λ^{−n})·(dilation a λ)_#(Hⁿ⌞M); (iii) ofReal(λ^{−n})·(dilation a λ)_#((Hⁿ⌞M) with density ofReal∘θ) = (Hⁿ⌞(blowUpMap a λ '' M)) with density y ↦ ofReal θ(a + λy).
Source: parent proof, Step 4 (density bounds at a good point; parent V7) and Step 5 (blow-ups; parent V8). The proof uses the siblings (DB), (CL), (BS), the accepted declarations (dc), (di), (cm), (rc), (BM) above, and the hypotheses (SL), (RU), (CT) and SLIM_{P,d} of this statement. (SL) and (RU) are only passed on to (di); (CT) is used through its first conjunct (T1).
0. Notation. n := d + 1; Hⁿ := μHE[n]; ω_n := unitBallVolume n ∈ (0, ∞) and V(r) := ω_n·ofReal(rⁿ), so V(r) ∈ (0, ∞) for r > 0. θ₀ := θ(a) > 0 (a ∈ M), ζ₀ := ζ(a), τ := θ•ζ, τ₀ := τ(a) = θ₀•ζ₀. For i ∈ ℕ: D_i := dilation a λ_i (y ↦ −λ_i⁻¹a + λ_i⁻¹y), which equals blowUpMap a λ_i as a function (unfold; smul_sub). D_i is a homeomorphism ((Homeomorph.smulOfNeZero λ_i⁻¹ _).trans (Homeomorph.addLeft (−(λ_i⁻¹•a)))), hence a measurable embedding, with a + λ_i·D_i(x) = x. Further c_i := ofReal(λ_i^{−n}) = ENNReal.ofReal(λ_i⁻¹ ^ n) ∈ (0, ∞), N_i' := blowUpMap a λ_i '' M, ν_i := Hⁿ⌞N_i' and μ_i' := c_i·(D_i)_#μ. We write o(r) := ∫⁻_{M∩B̄_r(a)}‖τ − τ₀‖ₑdHⁿ, so o(r)/V(r) → 0 as r ↓ 0 by hypothesis.
1. Density bounds at a (parent Step 4). (DB) applies with the hypotheses of this statement (M Borel, θ Borel, ζ strongly measurable, μ = (Hⁿ⌞M) with density ofReal∘θ, θ > 0 on M, |ζ(x)(α)| ≤ |α|, the norming covectors on M, a ∈ M, η₁ > 0, and the lower density, upper density and Lebesgue-point hypotheses at a). It gives r₀ > 0 with ofReal(η₁/(4θ₀))·V(r) ≤ Hⁿ(M ∩ B_r(a)) and Hⁿ(M ∩ B̄_r(a)) ≤ 2V(r) for all 0 < r < r₀.
2. Blow-ups (parent Step 5). For each i, (dc)(1) with m := n and λ := λ_i gives a dilation Γ_i' of Γ by D_i. (dc)(2) with m := d gives (h2): ∂Γ_i'(ω) = λ_i^{−d}∂Γ(ω') whenever ω'(y) = ω(D_i(y)). (dc)(4) and (dc)(5) with m := n give (h4) and (h5). (BS) applied to Γ, Γ_i', μ, M, θ, ζ, a, λ_i has the hypotheses λ_i > 0, ∂Γ = 0, μ(ℝ^P) < ∞, M_W(Γ) = μ(W) for open W, M Borel, θ Borel, ζ strongly measurable, μ = (Hⁿ⌞M) with density ofReal∘θ, θ > 0 on M, Γ(ω) = ∫_Mθζ(ω)dHⁿ, and (h2), (h4), (h5). It yields:
 (P0) Γ(ω) = ∫ζ(x)(ω(x))dμ(x) for every ω;
 (P7) ∂Γ_i' = 0;
 (P1) μ_i'(K) < ∞ for every compact K;
 (P2) M_W(Γ_i') = μ_i'(W) for every open W;
 (P3) ξ_i'(y) := ζ(a + λ_iy) is μ_i'-a.e. strongly measurable;
 (P5) Γ_i'(ω) = ∫ξ_i'(y)(ω(y))dμ_i'(y);
 (P6) μ_i'(ℝ^P∖N_i') = 0;
 (P8) Γ_i'(ω) = ∫_{N_i'}(θ(a + λ_iy)•ζ(a + λ_iy))(ω(y))dHⁿ(y) for every ω.
 Also |ξ_i'(y)(α)| ≤ |α| for all y and α.
3. Rescaled bounds (parent Steps 5(a) and estimate (*)). These are the four statements of cbr_ci_bl_rescaled_bounds; they are proved here. Let (λ'_i) be any sequence with λ'_i > 0 and λ'_i → 0, write D'_i, c'_i, N'_i and ν'_i for the corresponding objects, and let R > 0.
 (3.1) Change of variables. By (BM)(ii), ν'_i = c'_i·(D'_i)_#(Hⁿ⌞M). As D'_i is a measurable embedding, ν'_i(S) = c'_i·Hⁿ(M ∩ D'_i⁻¹S) for Borel S, and ∫⁻_Sg dν'_i = c'_i·∫⁻_{M∩D'_i⁻¹S}g(D'_i(x))dHⁿ(x) for every g : ℝ^P → [0, ∞] (MeasurableEmbedding.map_apply, MeasurableEmbedding.lintegral_map, Measure.restrict_restrict).
 (3.2) Balls and constants. ‖D'_i(y)‖ = λ'_i⁻¹dist(y, a), so D'_i⁻¹(B̄_R(0)) = B̄_{λ'_iR}(a) and D'_i⁻¹(B_R(0)) = B_{λ'_iR}(a). Also c'_i·V(λ'_iR) = V(R), because (λ'_i⁻¹)ⁿ(λ'_iR)ⁿ = Rⁿ.
 (3.3) Small scales. λ'_iR → 0 within (0, ∞), so λ'_iR < r₀ for all large i (step 1).
 (a) sup_iν'_i(K) < ∞ for every compact K. Choose R > 0 with K ⊆ B̄_R(0) (K is bounded; take R := max(R₀, 1)) and N with λ'_iR < r₀ for i ≥ N. Then ν'_i(K) ≤ ν'_i(B̄_R(0)) = c'_i·Hⁿ(M ∩ B̄_{λ'_iR}(a)). This is ≤ c'_i·2V(λ'_iR) = 2V(R) for i ≥ N, and ≤ c'_iHⁿ(M) < ∞ for i < N (Hⁿ(M) < ∞). So the supremum is at most max(2V(R), Σ_{j<N}c'_jHⁿ(M)) < ∞.
 (b) limsup_iν'_i(B̄_R(0)) ≤ V(R). By (3.1)–(3.2), ν'_i(B̄_R(0)) = V(R)·h(λ'_iR) with h(r) := Hⁿ(M ∩ B̄_r(a))/V(r), and limsup_{r↓0}h(r) ≤ 1 by hypothesis. For c > 1, eventually h(r) < c as r ↓ 0, hence eventually h(λ'_iR) < c. So limsup_ih(λ'_iR) ≤ 1, and limsup_iV(R)h(λ'_iR) = V(R)·limsup_ih(λ'_iR) ≤ V(R) (ENNReal.limsup_const_mul_of_ne_top, V(R) < ∞).
 (c) Eventually in i, ofReal(η₁/(4θ₀))·V(R) ≤ ν'_i(B̄_R(0)). For λ'_iR < r₀: ofReal(η₁/(4θ₀))V(R) = c'_i·ofReal(η₁/(4θ₀))V(λ'_iR) ≤ c'_iHⁿ(M ∩ B_{λ'_iR}(a)) = ν'_i(B_R(0)) ≤ ν'_i(B̄_R(0)).
 (d) ∫⁻_{B̄_R(0)}‖τ(a + λ'_iy) − τ₀‖ₑdν'_i(y) → 0. With g(y) := ‖τ(a + λ'_iy) − τ₀‖ₑ we have g(D'_i(x)) = ‖τ(x) − τ₀‖ₑ, so by (3.1)–(3.2) the integral equals c'_io(λ'_iR) = V(R)·o(λ'_iR)/V(λ'_iR). This tends to V(R)·0 = 0, because o(r)/V(r) → 0 as r ↓ 0 and λ'_iR → 0⁺.
4. Compactness (parent Step 5(b)). Apply (T1) with U := ℝ^P to (ν_i), using (3)(a) for λ'_i := λ_i. This gives a strictly increasing φ and a Borel measure ν, finite on compacts, with:
 ∫f dν_{φ(k)} → ∫f dν for every continuous compactly supported f;
 limsup_kν_{φ(k)}(K) ≤ ν(K) for compact K;
 ν(G) ≤ liminf_kν_{φ(k)}(G) for open G.
 Put Γ_k := Γ'_{φ(k)}, μ_k := μ'_{φ(k)}, ξ_k := ξ'_{φ(k)} and N_k := N'_{φ(k)} = blowUpMap a λ_{φ(k)} '' M. Apply step 3 again to λ'_k := λ_{φ(k)} (positive, → 0). It gives (3)(b)–(d) along the subsequence, with ν'_k = ν_{φ(k)}.
5. The limit current (parent Steps 0(g), 5(c)). The measure ofReal(θ₀)·ν is finite on compacts, and the constant field y ↦ ζ₀ is strongly measurable with |ζ₀(α)| ≤ |α|. So (rc) with U := ℝ^P and E := ℝ^P gives C ∈ 𝒟_n(ℝ^P) with C(ω) = ∫ζ₀(ω(y))d(ofReal(θ₀)·ν)(y) = ∫θ₀·ζ₀(ω(y))dν(y) (Measure.restrict_univ, integral_smul_measure, (ofReal θ₀).toReal = θ₀, integral_const_mul). This is C(ω) = ∫θ(a)·ζ(a)(ω(y))dν(y), and also C(ω) = ∫(θ₀•ζ₀)(ω(y))dν(y).
6. Weak convergence and the mass limsup (parent Steps 5(c), 5(d)(ε)). Apply (CL) with X_k := Γ_k, C, ν_k := ν_{φ(k)}, ν, μ_k, τ_k(y) := θ(a + λ_{φ(k)}y)•ζ(a + λ_{φ(k)}y), the constant n-vector θ₀•ζ₀ and s := θ₀. Its hypotheses hold:
 ν_{φ(k)} and ν are finite on compacts (step 3(a), step 4);
 ∫f dν_{φ(k)} → ∫f dν and limsup_kν_{φ(k)}(K) ≤ ν(K) (step 4);
 τ_k is strongly measurable (θ, ζ measurable, composed with y ↦ a + λy), hence a.e. strongly measurable;
 θ₀ ≥ 0, and |(θ₀•ζ₀)(α)| ≤ θ₀|α|;
 ∫⁻_{B̄_R(0)}‖τ_k − θ₀•ζ₀‖ₑdν_{φ(k)} → 0 for R > 0 (step 4, (3)(d));
 Γ_k(ω) = ∫τ_k(ω)dν_{φ(k)} by (P8);
 C(ω) = ∫(θ₀•ζ₀)(ω)dν by step 5;
 M_W(Γ_k) = μ_k(W) for open W by (P2).
 Hence Γ_k ⇀ C and limsup_kμ_k(K) ≤ ofReal(θ₀)·ν(K) for every compact K.
7. Bounds for ν (parent Step 5(d)(α), (β)). For R > 0: ν(B_R(0)) ≤ liminf_kν_{φ(k)}(B_R(0)) ≤ liminf_kν_{φ(k)}(B̄_R(0)) ≤ limsup_kν_{φ(k)}(B̄_R(0)) ≤ V(R). This uses step 4 and (3)(b) along the subsequence. For r > 0: by (3)(c) along the subsequence, ν_{φ(k)}(B̄_{r/2}(0)) ≥ ofReal(η₁/(4θ₀))V(r/2) > 0 for all large k. Hence 0 < ofReal(η₁/(4θ₀))V(r/2) ≤ limsup_kν_{φ(k)}(B̄_{r/2}(0)) ≤ ν(B̄_{r/2}(0)) ≤ ν(B_r(0)) (le_limsup_of_frequently_le, step 4, closedBall_subset_ball).
8. ∂C = 0 (parent Step 5(d)(γ)). For a test d-form φ', ∂Γ_k ⇀ ∂C (WeaklyConvergesOn.boundary), and ∂Γ_k(φ') = 0 by (P7). Hence ∂C(φ') = lim_k∂Γ_k(φ') = 0.
9. Mass of C (parent Step 5(d)(δ)). Take β_a with |β_a| ≤ 1 and ζ₀(β_a) = 1 (a ∈ M). Apply (cm) with m := n, ν' := ν, ζ' := θ₀•ζ₀ and s := θ₀: ν is finite on compacts (step 4), |(θ₀•ζ₀)(α)| ≤ θ₀|α|, (θ₀•ζ₀)(β_a) = θ₀, and C(ω) = ∫(θ₀•ζ₀)(ω)dν. Hence M_W(C) = ofReal(θ₀)·ν(W) for open W.
10. Uniform local mass bound (parent Step 5(e)). Let W be open with CompactlyContained W ℝ^P, so K := closure W is compact. The zero current has zero mass on every set (every admissible value is 0). So M_W(Γ_k) + M_W(∂Γ_k) = μ_k(W) + 0 ≤ μ_k(K), using (P7) and (P2). By step 6, limsup_kμ_k(K) ≤ ofReal(θ₀)ν(K) < ∞. Choose c with limsup_kμ_k(K) < c < ∞; then μ_k(K) < c for k ≥ N. For k < N, μ_k(K) < ∞ by (P1). Therefore sup_k(M_W(Γ_k) + M_W(∂Γ_k)) ≤ c + Σ_{j<N}μ_j(K) < ∞.
11. ISP of C (parent Step 5(e)). For each k apply (di) with (SL), (RU), X := Γ, X' := Γ_k, λ := λ_{φ(k)} and (μ_X, ξ_X) := (μ, ζ). Its hypotheses hold:
 Γ_k is a dilation of Γ by D_{φ(k)} (step 2);
 ∂Γ = 0;
 μ is finite on compacts (μ(ℝ^P) < ∞);
 ζ is strongly measurable with |ζ(x)(α)| ≤ |α| for all x;
 Γ(ω) = ∫ζ(ω)dμ by (P0);
 Γ has ISP.
 So every Γ_k has ISP. With step 10 and Γ_k ⇀ C (step 6), SLIM_{P,d} shows that C has ISP.
12. Conclusion. The objects φ, ν, C, Γs := (Γ_k), μs := (μ_k) and ξs := (ξ_k) satisfy the nineteen asserted properties:
 (1) φ is strictly increasing (step 4);
 (2) ν is finite on compacts (step 4);
 (3)–(4) ν(B_R(0)) ≤ ω_nRⁿ for R > 0 and ν(B_r(0)) > 0 for r > 0 (step 7);
 (5) C(ω) = ∫θ(a)·ζ(a)(ω(y))dν(y) (step 5);
 (6) ∂C = 0 (step 8);
 (7) M_W(C) = ofReal(θ(a))·ν(W) for open W (step 9);
 (8) C has ISP (step 11);
 (9) Γ_k ⇀ C (step 6);
 (10) ∂Γ_k = 0 (P7);
 (11) μ_k(K) < ∞ for compact K (P1);
 (12) M_W(Γ_k) = μ_k(W) for open W (P2);
 (13) ξ_k is μ_k-a.e. strongly measurable (P3);
 (14) |ξ_k(x)(α)| ≤ |α| for all x (step 2);
 (15) Γ_k(ω) = ∫ξ_k(ω)dμ_k (P5);
 (16) limsup_kμ_k(K) ≤ ofReal(θ(a))·ν(K) for compact K (step 6);
 (17) μ_k((blowUpMap a λ_{φ(k)} '' M)ᶜ) = 0 (P6);
 (18) limsup_kHⁿ(blowUpMap a λ_{φ(k)} '' M ∩ K) ≤ ν(K) for compact K: since Hⁿ(N_k ∩ K) = ν_{φ(k)}(K) (Measure.restrict_apply for closed K and inter_comm), this follows from step 4;
 (19) ∫_{blowUpMap a λ_{φ(k)} '' M}f dHⁿ = ∫f dν_{φ(k)} → ∫f dν for every continuous compactly supported f (step 4). ∎

## Key steps

1. Density bounds at a come from the sibling density_bounds. The dilations Γ_i' of Γ come from the accepted cbr_ci_dilation_calculus. The sibling blowup_scale makes each Γ_i' a cycle with mass measure ofReal(λ_i^{−n})·(D_i)_#μ, admissible pair (μ_i', ζ(a + λ_i·)) and Γ_i'(ω) = ∫_{η_i(M)}θζ(a + λ_i·)(ω)dHⁿ.
2. Rescaled bounds, proved inline from cbr_ci_bl_blowUp_restrict_scaling and density_bounds: ν_i = Hⁿ⌞η_i(M) is uniformly bounded on compacts, limsup ν_i(B̄_R) ≤ ω_nRⁿ, an eventual lower bound holds, and θζ(a + λ_i·) → θ(a)ζ(a) in L¹(ν_i⌞B̄_R).
3. (T1) gives φ and ν. The accepted cmcs_restrict_current gives C = ∫θ(a)ζ(a)(ω)dν. The sibling constant_limit gives Γ_k ⇀ C and limsup μ_k(K) ≤ θ(a)ν(K).
4. 0 < ν(B_r) and ν(B_R) ≤ ω_nRⁿ; ∂C = 0 from ∂Γ_k = 0; M_W(C) = θ(a)ν(W) by the accepted cbr_ci_const_vector_massOn.
5. Each Γ_k has ISP by the accepted cbr_ci_dilation_slice_property. The uniform local mass bound and SLIM_{P,d} then give ISP of C.

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
