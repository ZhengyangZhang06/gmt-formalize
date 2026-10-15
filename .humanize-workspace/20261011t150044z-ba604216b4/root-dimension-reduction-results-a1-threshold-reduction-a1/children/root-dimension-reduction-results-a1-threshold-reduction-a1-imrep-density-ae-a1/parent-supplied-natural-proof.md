# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3(iii), "μ_A = ϑ_A·Hⁿ as measures on ℝ^P". That step cites Simon Ch. 3, Remark 1.5(3), Remark 1.8 and Theorem 1.9 (the density equals θ on the carrier) and Ch. 1, Theorem 3.6 with Remark 3.7(2) (the upper density vanishes off the carrier). The printed arguments are reproduced and specialized to integer multiplicities; the level sets of θ replace Lusin's theorem in Remark 1.8(1). The upper density theorem is proved first, as Lemma U in Step 0.


Step 0 (Lemma U; formerly the separate sibling upper_density_zero of attempt 4, merged here because this child is its only user). Within this step the letters below denote the objects of Lemma U only.
Lemma U (Simon Ch. 1, Theorem 3.6 with Remark 3.7(2)). Let P, n ∈ ℕ, let μ be a Borel measure on ℝ^P (Euclid P) with μ(K) < ∞ for every compact K ⊆ ℝ^P, and let A ⊆ ℝ^P be a Borel set with μ(ℝ^P ∖ A) = 0. Then for μHE[n]-almost every x ∈ ℝ^P with x ∉ A, μ(B̄_ρ(x))/ofReal(ρ)ⁿ → 0 in [0, ∞] as ρ ↓ 0, where B̄_ρ(x) is the closed ball.
Proof of Lemma U.
Source: Simon Ch. 1, Theorem 3.6 with Remark 3.7(2), the fact "the upper density vanishes Hⁿ-a.e. off the carrier" cited in parent step 3(iii). The printed proof is reproduced for a locally finite Borel measure: density comparison (Ch. 1, 3.2) via the Vitali covering lemma (Ch. 1, 3.3), inner regularity by closed sets, then localization.

The same argument, written for μ = μHE[n]⌞S with μHE[n](S) < ∞, is the comparator-accepted declaration Submission.regcomp_atl_upper_density_zero of DAG node root.regular_components_are_minimizing-a1.approx_tangent_locality-a1.upper_density_zero-a1 (candidate 031b5125695febe04a82aacb729a15164ef02960). These accepted declarations are reading references only. They are not dependencies of this child and are not in its worktree, and the numbered proof below is self-contained. Their Lean proofs show the same Vitali and comparison steps with μHE[n](S ∩ ·) in place of λ(·); Submission.regcomp_atl_local_density_zero shows the localization by balls. The SimonGMT lemmas simon_theorem_3_6 and simon_remark_3_7_of_openSigmaFinite are not used: they live in Poincare/SimonGMT/Chapter01/DensityComparison.lean, which the frozen header does not import.

Notation. Hⁿ := μHE[n] = c_n·μH[n] with c_n := addHaarScalarFactor(volume, μH[n]) ∈ (0, ∞) (Measure.euclideanHausdorffMeasure_def, Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero). So Hⁿ and μH[n] have the same null sets. For a measure λ, x ∈ ℝ^P and ρ > 0 put r_λ(x, ρ) := λ(B̄_ρ(x))/ofReal(ρ)ⁿ ∈ [0, ∞]; ofReal(ρ)ⁿ ∈ (0, ∞) for ρ > 0.

U1. (Comparison lemma, Simon 3.2 with the crude constant 6ⁿ.) Let λ be a Borel measure, G a Borel set with λ(G) < ∞, t ∈ (0, ∞) and E ⊆ ℝ^P. Assume that for every x ∈ E and every δ > 0 there is ρ ∈ (0, δ) with t·ofReal(ρ)ⁿ ≤ λ(G ∩ B̄_ρ(x)). Then t·μH[n](E) ≤ 6ⁿ·λ(G).
Proof. Fix j ∈ ℕ and put δ_j := 1/(j + 1).
(a) Vitali selection. Consider the family of pairs a = (x_a, ρ_a) with x_a ∈ E, 0 < ρ_a < δ_j and t·ofReal(ρ_a)ⁿ ≤ λ(G ∩ B̄_{ρ_a}(x_a)), with the closed balls B̄_{ρ_a}(x_a) (nonempty) and radii ρ_a ≤ δ_j. Mathlib's Vitali.exists_disjoint_subfamily_covering_enlargement with τ = 2 gives a pairwise disjoint subfamily u_j such that every ball of the family meets some ball b ∈ u_j with ρ_a ≤ 2ρ_b. The balls of u_j are disjoint with nonempty interior, so u_j is countable (Set.PairwiseDisjoint.countable_of_nonempty_interior).
(b) Covering. For x ∈ E the hypothesis with δ = δ_j gives a member a = (x, ρ) of the family. Let b ∈ u_j be a ball meeting B̄_ρ(x) at a point w, with ρ ≤ 2ρ_b. Then |x − x_b| ≤ |x − w| + |w − x_b| ≤ ρ + ρ_b ≤ 3ρ_b. So E ⊆ ⋃_{b∈u_j} B̄_{3ρ_b}(x_b), and diam B̄_{3ρ_b}(x_b) ≤ 6ρ_b ≤ 6δ_j (ediam_le_of_forall_dist_le).
(c) Packing. By disjointness,
t·Σ_{b∈u_j} ofReal(ρ_b)ⁿ ≤ Σ_{b∈u_j} λ(G ∩ B̄_{ρ_b}(x_b)) = λ(⋃_{b∈u_j} G ∩ B̄_{ρ_b}(x_b)) ≤ λ(G)
(measure_biUnion). Hence t·Σ_{b∈u_j} diam(B̄_{3ρ_b}(x_b))ⁿ ≤ 6ⁿ·λ(G) for every j.
(d) Limit. Mathlib's MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum applies to the covers {B̄_{3ρ_b}(x_b) : b ∈ u_j} of E, whose diameters are ≤ 6δ_j → 0. It gives μH[n](E) ≤ liminf_j Σ_{b∈u_j} diam(B̄_{3ρ_b}(x_b))ⁿ ≤ 6ⁿλ(G)/t (ENNReal.le_div_iff_mul_le with t ∉ {0, ∞}). Multiplying by t gives the claim. For n = 0 the same computation holds with every n-th power equal to 1.

U2. (Finite measures.) Let λ be a finite Borel measure and A′ a Borel set with λ(A′ᶜ) = 0. Then for Hⁿ-a.e. x ∉ A′, r_λ(x, ρ) → 0 as ρ ↓ 0.
Proof.
(a) Thresholds. For t ∈ (0, ∞) let N_t := {x : x ∉ A′ and t < r_λ(x, ρ) for ρ frequently in 𝓝[>]0}. Suppose x ∉ A′ and r_λ(x, ·) does not tend to 0. By ENNReal.tendsto_nhds_zero there is ε > 0 with ε < r_λ(x, ρ) frequently. Choosing k with 1/(k + 1) < ε (ENNReal.exists_inv_nat_lt) gives x ∈ N_{1/(k+1)}. By measure_iUnion_null it therefore suffices to show Hⁿ(N_t) = 0 for every t ∈ (0, ∞), and for that it suffices to show μH[n](N_t) = 0.
(b) Fix t and ε′ ∈ (0, ∞). The finite Borel measure λ on the metric space ℝ^P is weakly regular (Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure). MeasurableSet.exists_isClosed_sdiff_lt (the current name of the deprecated exists_isClosed_diff_lt) gives a closed F ⊆ A′ with λ(A′ ∖ F) < t·ε′/6ⁿ. Put G := A′ ∖ F; it is Borel and λ(G) < ∞.
(c) Let x ∈ N_t and δ > 0. Then x ∉ F, since F ⊆ A′. As F is closed, some r₁ > 0 has B_{r₁}(x) ∩ F = ∅. Since the threshold holds frequently and ρ ∈ (0, min(δ, r₁/2)) holds eventually in 𝓝[>]0, pick ρ satisfying both (Frequently.and_eventually). Then B̄_ρ(x) ∩ F = ∅. As λ(A′ᶜ) = 0, λ(B̄_ρ(x)) = λ(A′ ∩ B̄_ρ(x)) = λ(G ∩ B̄_ρ(x)). From t < r_λ(x, ρ) and 0 < ofReal(ρ)ⁿ < ∞ (ENNReal.lt_div_iff_mul_lt) we get t·ofReal(ρ)ⁿ < λ(G ∩ B̄_ρ(x)).
(d) Step U1 with E := N_t gives t·μH[n](N_t) ≤ 6ⁿλ(G) < 6ⁿ·(tε′/6ⁿ) = tε′. Hence μH[n](N_t) < ε′. As ε′ > 0 is arbitrary, μH[n](N_t) = 0, and Hⁿ(N_t) = c_n·0 = 0.

U3. (Localization; the statement.) For j ∈ ℕ let λ_j := μ.restrict (A ∩ B_j(0)), where B_j(0) is the open ball.
- λ_j is finite: λ_j(ℝ^P) = μ(A ∩ B_j(0)) ≤ μ(B̄_j(0)) < ∞, as B̄_j(0) is compact.
- λ_j((A ∩ B_j(0))ᶜ) = 0.
By step U2 for each j and ae_all_iff, Hⁿ-a.e. x satisfies: for every j, if x ∉ A ∩ B_j(0) then r_{λ_j}(x, ρ) → 0.
Fix such an x with x ∉ A. Choose j ∈ ℕ with |x| < j and put ε := (j − |x|)/2 > 0, so B̄_ε(x) ⊆ B_j(0). For 0 < ρ < ε, since μ(Aᶜ) = 0,
μ(B̄_ρ(x)) = μ(A ∩ B̄_ρ(x)) = μ(A ∩ B_j(0) ∩ B̄_ρ(x)) = λ_j(B̄_ρ(x)).
So r_μ(x, ρ) = r_{λ_j}(x, ρ) on (0, ε), a set in 𝓝[>]0. Since x ∉ A ∩ B_j(0), r_{λ_j}(x, ·) → 0, and therefore r_μ(x, ρ) → 0 as ρ ↓ 0 (Tendsto.congr′). This holds for Hⁿ-a.e. x ∉ A, which is the claim. ∎

Main argument.
Notation.
- Hⁿ := μHE[n].
- ω_n := unitBallVolume n = volume(B_1(0) ⊆ Euclid n) ∈ (0, ∞): a nonempty bounded open set under Lebesgue measure; for n = 0 it equals 1.
- M′ := M ∩ W, a Borel set.
- μ := R.measure.restrict W, so μ(B) = R.measure(B ∩ W) = ∫_{M′∩B} θ dHⁿ for Borel B.
- ν := Hⁿ.restrict M′.
- q(x, ρ) := μ(B_ρ(x))/(ω_n·ofReal(ρⁿ)) for ρ > 0.
Since balls are Borel, R.measure(B_ρ(x) ∩ W) = μ(B_ρ(x)) (Measure.restrict_apply). Also 1_{M′}(x)θ(x) = Set.indicator (R.carrier ∩ W) (fun y ↦ (R.mult y : ℝ≥0∞)) x. So the claim is: q(x, ρ) → 1_{M′}(x)θ(x) as ρ ↓ 0 for Hⁿ-a.e. x.

1. (Local finiteness and concentration.)
- μ(K) = R.measure(K ∩ W) < ∞ for every compact K, by hypothesis.
- θ ≥ 1 on M, so ν(B) = Hⁿ(M′ ∩ B) ≤ ∫_{M′∩B} θ dHⁿ = μ(B) for Borel B; in particular ν(K) < ∞ for compact K.
- R.measure = (Hⁿ⌞M).withDensity θ vanishes off M, and μ vanishes off W, so μ(M′ᶜ) = 0. Likewise ν(M′ᶜ) = 0.
- For ρ ≥ 0, ofReal(ρⁿ) = ofReal(ρ)ⁿ (ENNReal.ofReal_pow), and B_ρ(x) ⊆ B̄_ρ(x). Hence, for every measure λ, λ(B_ρ(x))/(ω_n·ofReal(ρⁿ)) ≤ ω_n⁻¹·λ(B̄_ρ(x))/ofReal(ρ)ⁿ.
 (†) So the open-ball ratio, normalized by ω_n, tends to 0 whenever the closed-ball ratio λ(B̄_ρ(x))/ofReal(ρ)ⁿ does.

2. (Off the carrier.) Apply Lemma U (Step 0) to the measure μ and the Borel set M′. Its hypotheses hold by step 1. It gives an Hⁿ-null set E₀ such that for x ∉ M′ ∪ E₀, μ(B̄_ρ(x))/ofReal(ρ)ⁿ → 0. By (†), q(x, ρ) → 0 = 1_{M′}(x)θ(x).

3. (Unit density at approximate-tangent points; Simon Ch. 3, Remark 1.5(3).) By the IMRep field orients, for Hⁿ-a.e. x ∈ M there is a subspace Q with HasApproximateTangentSpaceAt n M x Q (in particular finrank Q = n). By definition this means: ∫_{blowUpMap x ρ '' M} f dHⁿ → ∫_Q f dHⁿ as ρ ↓ 0 for every f ∈ C_c(ℝ^P, ℝ), where blowUpMap x ρ (p) = ρ⁻¹(p − x). Let E′ ⊆ M be the Hⁿ-null set of points of M where this fails. Fix x ∈ M′ ∖ E′, the subspace Q, and δ > 0 with B_{2δ}(x) ⊆ W (W is open). Write η_ρ := blowUpMap x ρ. Claim: ν(B_ρ(x))/(ω_n·ofReal(ρⁿ)) → 1.
(a) Scaling. For every set A, Hⁿ(η_ρ(A)) = ofReal(ρ⁻¹)ⁿ·Hⁿ(A). Indeed η_ρ(A) = ρ⁻¹ • (A − x). The translation y ↦ y − x is an isometry, so it preserves Hⁿ (Isometry.euclideanHausdorffMeasure_image applied to (IsometryEquiv.subRight x).isometry), and Hⁿ(c • B) = ‖c‖₊ⁿ·Hⁿ(B) for c ≠ 0 (Measure.euclideanHausdorffMeasure_smul₀). This combination compiles after import GMT.Ch07.Submission. (MeasureTheory.euclideanHausdorffMeasure_homothety_image concerns y ↦ x + c(y − x) and can also be used after rewriting.)
(b) For 0 < ρ < δ, M ∩ B_{2ρ}(x) = M′ ∩ B_{2ρ}(x). Hence:
 - η_ρ(M) ∩ B_2(0) = η_ρ(M′ ∩ B_{2ρ}(x));
 - Hⁿ(η_ρ(M) ∩ B_1(0)) = ofReal(ρ)⁻ⁿ·ν(B_ρ(x));
 - Hⁿ(η_ρ(M) ∩ B_2(0)) = ofReal(ρ)⁻ⁿ·ν(B_{2ρ}(x)) < ∞.
(c) Fix 0 < ε < 1 and take continuous f^±: ℝ^P → [0, 1] with compact support:
 - f⁺(p) := min(1, max(0, (1 + ε − |p|)/ε)), which is 1 on B̄_1(0) and 0 off B_{1+ε}(0) ⊆ B_2(0);
 - f⁻(p) := min(1, max(0, (1 − |p|)/ε)), which is 1 on B̄_{1−ε}(0) and 0 off B_1(0).
 Both are integrable over η_ρ(M), since they are bounded and supported in B_2(0), which has finite measure by (b). As 1_{B_1(0)} lies between f⁻ and f⁺, the following holds as real numbers. All quantities are finite by (b), and the measure values are compared through toReal.
 ∫_{η_ρ(M)} f⁻ dHⁿ ≤ (Hⁿ(η_ρ(M) ∩ B_1(0))).toReal = (ofReal(ρ)⁻ⁿ·ν(B_ρ(x))).toReal ≤ ∫_{η_ρ(M)} f⁺ dHⁿ.
(d) Hⁿ(Q ∩ B_t(0)) = ω_n·tⁿ for t > 0. Indeed, Q with the induced inner product is an n-dimensional inner product space, and the inclusion Q → ℝ^P is an isometry (Isometry.euclideanHausdorffMeasure_image). Hⁿ on Q is its volume (InnerProductSpace.euclideanHausdorffMeasure_eq_volume with finrank Q = n). An orthonormal basis gives a linear isometry Q ≃ Euclid n, which preserves volume. In Euclid n the ball of radius t > 0 has volume ofReal(tⁿ)·ω_n (Measure.addHaar_ball_of_pos, which needs no nontriviality, so n = 0 is included). Since 1_{B̄_{1−ε}(0)} ≤ f⁻ and f⁺ ≤ 1_{B_{1+ε}(0)},
 ω_n(1 − ε)ⁿ ≤ ∫_Q f⁻ dHⁿ and ∫_Q f⁺ dHⁿ ≤ ω_n(1 + ε)ⁿ.
(e) Let ρ ↓ 0 in (c), using the approximate-tangent convergence for f^±. This gives
 ω_n(1 − ε)ⁿ ≤ liminf ν(B_ρ(x))/ofReal(ρⁿ) ≤ limsup ν(B_ρ(x))/ofReal(ρⁿ) ≤ ω_n(1 + ε)ⁿ.
 Then let ε ↓ 0 and divide by ω_n ∈ (0, ∞); this proves the claim.

4. (Density θ on the carrier; Simon Ch. 3, Remark 1.8.) For m ≥ 1 let M′_m := {p ∈ M′ : θ(p) = m} and A_m := M′ ∖ M′_m; both are Borel. Since θ is ℕ-valued and ≥ 1 on M, M′ = ⋃_{m≥1} M′_m (disjoint union).
Fix m. The measures μ.restrict A_m and ν.restrict A_m are finite on compact sets (step 1) and vanish off A_m. Apply Lemma U (Step 0) to each of them with the set A_m. This gives an Hⁿ-null set E_m such that, for x ∉ A_m ∪ E_m:
 μ(A_m ∩ B̄_ρ(x))/ofReal(ρ)ⁿ → 0 and ν(A_m ∩ B̄_ρ(x))/ofReal(ρ)ⁿ → 0.
By (†), the corresponding open-ball ratios normalized by ω_n also tend to 0.
Now let x ∈ M′_m ∖ (E_m ∪ E′); note M′_m ⊆ ℝ^P ∖ A_m. For ρ ∈ (0, δ) all terms below are finite, and
 μ(B_ρ(x)) = μ(M′_m ∩ B_ρ(x)) + μ(A_m ∩ B_ρ(x))
 = m·ν(M′_m ∩ B_ρ(x)) + μ(A_m ∩ B_ρ(x))
 = m·[ν(B_ρ(x)) − ν(A_m ∩ B_ρ(x))] + μ(A_m ∩ B_ρ(x)).
The first equality holds because μ vanishes off M′ = M′_m ∪ A_m; the second because θ = m on M′_m. Dividing by ω_n·ofReal(ρⁿ) and using step 3 together with the two vanishing ratios gives q(x, ρ) → m·1 − m·0 + 0 = m = θ(x) = 1_{M′}(x)θ(x). This is arithmetic of finite limits, for example after passing to toReal.

5. (Conclusion.) The set E₀ ∪ E′ ∪ ⋃_{m≥1} E_m is Hⁿ-null (countable union). Outside it, q(x, ρ) → 1_{M′}(x)θ(x) as ρ ↓ 0: by step 2 if x ∉ M′, and by step 4 with m = θ(x) if x ∈ M′. ∎

## Key steps

1. Lemma U (Simon 1.3.6, 3.7(2)): Vitali comparison t·μH[n](E) ≤ 6ⁿλ(G), inner regularity by closed sets for finite measures, and localization to balls give vanishing upper density Hⁿ-a.e. off a set carrying a locally finite measure.
2. μ := R.measure⌞W and ν := Hⁿ⌞(M ∩ W) are finite on compact sets (θ ≥ 1 on M) and concentrated on M′ = M ∩ W; open-ball ratios normalized by ω_n are bounded by closed-ball ratios.
3. Off M′: Lemma U applied to (μ, M′) gives zero density Hⁿ-a.e. off M′.
4. At Hⁿ-a.e. x ∈ M′ the carrier has an approximate tangent plane Q. Testing with cut-offs of B_1(0), using Hⁿ(η_{x,ρ}A) = ρ^{−n}Hⁿ(A) and Hⁿ(Q ∩ B_t) = ω_ntⁿ, gives ν(B_ρ(x))/(ω_nρⁿ) → 1.
5. Split M′ into the Borel level sets {θ = m}. Lemma U applied to μ⌞A_m and ν⌞A_m, with A_m = M′ ∖ {θ = m}, makes the other levels negligible, so the ratio tends to m = θ(x) at Hⁿ-a.e. point of {θ = m}.
6. The countable union of exceptional sets is Hⁿ-null.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `sha256sum GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `grep -n 'theorem hausdorffMeasure_image_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'addHaarScalarFactor_volume_hausdorffMeasure_ne_zero\|theorem euclideanHausdorffMeasure_def' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -c dimred_tr_ <snapshot>/project (exit 1, no match); rg -l dimred_tr_ GMT .lake/packages/simongmt/Poincare --glob '*.lean' (exit 1, no match)`
- `grep -n 'def HasApproximateTangentSpaceAt' -A 14 and grep -n 'def blowUpMap' -A 5 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 85,125p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, support)`
- `python3 inspection of dag.json: status, candidate_commit and lean_statement of the selected node, of its registered dependencies im_mass_measure, monotonicity and moving_blowups, of root.abstract_dimension_reduction-a1 and of the six reused nodes; string comparison of the children's leading premises with these frozen types`
- `python3 /tmp/tr-a7/scripts/check_reuse_types.py dag.json (git show <candidate>:GMT/Ch07/Submission.lean, declared type vs dag.json up to whitespace, sorry occurrences); git cat-file -e <candidate>^{commit}; isolated-comparator-result.json and comparator-v1.log of the six reused nodes`
- `python3 /tmp/tr-a7/scripts/graph_check.py decomposition-v6.json dag.json 5000 12 (replica of _dependency_problem, _existing_lean_name_problem and the max_nodes bound)`
- `lake env lean /tmp/tr-a7/lean/Types.lean; lake env lean /tmp/tr-a7/lean/Assembly.lean; lake env lean /tmp/tr-a7/lean/TangentCheck.lean`
- `python3 reading of decomposition-v1..v6.json, decomposition-audit-v*.json, decomposition-review-receipt-v*.json and decomposition-scope-v*.json of the selected node; grep -l 'threshold_reduction' cluster-state/logs/gmt-ch07/*.log; max_nodes in .humanize/swarm-configs/9619fab3de46466e954c3c0e22455dff.json and 53f9bac0ca76443b9b296465895cebc9.json`
- `gh api repos/humanfia/math-lean-flow/contents/_recursive_lean/{runtime,store,github_runtime,decomposition_scope}.py?ref=feature/humanize-api-update-claude; grep -n '_decompose\|_solve_children\|_existing_lean_name_problem\|_overlay_accepted_children\|_reference_use_problem\|def ensure' on the fetched copies`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-review-receipt-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-scope-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-stationary-of-minimizing-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-rep-pushforward-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/9619fab3de46466e954c3c0e22455dff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/53f9bac0ca76443b9b296465895cebc9.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/9619fab3de46466e954c3c0e22455dff.log`
- `/tmp/tr-a7/lean/Types.lean`
- `/tmp/tr-a7/lean/Assembly.lean`
- `/tmp/tr-a7/lean/TangentCheck.lean`
- `/tmp/tr-a7/scripts/graph_check.py`
- `/tmp/tr-a7/scripts/check_reuse_types.py`
- `/tmp/tr7-mlf/runtime.py`

Pins match. The snapshot manifest records project b4d606d and mathlib 25730c7c, equal to the workspace HEAD and to .lake/packages/mathlib; simongmt is 2b36630 as pinned in lakefile.toml. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library facts the children use exist where cited:
- The snapshot mathlib has LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:745), used in the parent assembly.
- It has addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Measure.lean:96), used for the normalization Hⁿ = c_n·μH[n].
- SimonGMT's HasApproximateTangentSpaceAt (Rectifiable.lean:102) and support = U ∖ zeroRegion are as the children's proofs use them. zeroRegion is a union of open sets with compact closure in U on which the current vanishes (CurrentLocalEquality.lean:99–117).

No dimred_tr_ identifier exists in the snapshot project, GMT, SimonGMT or dag.json.

The six reused declarations are accepted, and their candidate commits are present. Their dag.json types equal the children's lean_statements and the candidates' declarations (up to whitespace). Each candidate's only sorry is the frozen main_theorem, and each isolated comparator result passed.

Lean checks:
- All 12 child types elaborate after import GMT.Ch07.Submission.
- The parent assembly compiles from exactly the three registered dependencies, abstract_dimension_reduction and the three new children it uses, with no sorryAx.
- The tangent child compiles from exactly its four reused siblings.

The graph and name replica passes against the current 2327-node DAG, with room for 6 new nodes under max_nodes = 5000.

Attempt 6 was audited acceptable. It failed activation only because the old worker's max_nodes was 1000, below the DAG size, so it is resubmitted unchanged.
