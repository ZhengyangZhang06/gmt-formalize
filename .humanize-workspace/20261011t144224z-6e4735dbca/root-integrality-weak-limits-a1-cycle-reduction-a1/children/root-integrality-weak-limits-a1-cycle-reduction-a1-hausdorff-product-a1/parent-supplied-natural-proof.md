# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the product formula cited in Part I, item 5 of the parent proof: “H^{m+1}⌞((0,1) × M) = L¹⌞(0,1) ⊗ H^m⌞M (product formula for Hausdorff measure on rectifiable sets, Federer 3.2.23)” and “(0,1) × M_0 is H^{m+1}-null”. It is isolated as a named lemma and proved completely here.
- Part (a) is an elementary covering argument.
- Part (b) follows Federer's route to 3.2.23 (H. Federer, Geometric Measure Theory, 1969, 3.2.23; cf. its use in arXiv:2505.11279). Cut the Lipschitz parametrizations of A into injective Lipschitz pieces, apply the area formula for Lipschitz maps in dimensions m and m + 1, and use Tonelli.
- No C¹ chart cover is used, and no DAG declaration is needed (depends_on = []).
- The piece construction of Steps 6–7 is the one in the comparator-accepted proof of rectifiability_weighted_tangent_ae (node root.rectifiability-a1.weighted_tangent_ae-a1, Step 4(a)–(d) of its natural proof; Lean code in commit 2f36576, hypothesis `hpart`), specialized to dimension m.
- Every external input is a theorem of the pinned libraries (Library account below); each has #print axioms = [propext, Classical.choice, Quot.sound].

Library account (pinned Mathlib 25730c7c and SimonGMT 2b36630).
- (L1) Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn (simongmt Poincare/SimonGMT/Chapter02/AreaLipschitz.lean:101).
  - Statement: let E, F be finite-dimensional real inner product spaces with Borel σ-algebras, f : E → F with LipschitzWith K f, s ⊆ E a MeasurableSet with InjOn f s, and g : F → [0, ∞] arbitrary (no measurability is needed). Then ∫⁻_{f '' s} g dμHE[finrank ℝ E] = ∫⁻_{x ∈ s} ENNReal.ofReal(J_f(x))·g(f(x)) dvolume(x).
  - Normalization: the target measure is Mathlib's normalized Hausdorff measure μHE. The source measure is Lebesgue measure volume. J_f(x) := Poincare.SimonGMT.Chapter02.areaJacobianAt f x = (fderiv ℝ f x).normDet (areaJacobianAt_eq_normDet), which is Simon's √det(Df(x)* Df(x)) of (3.3) (areaJacobianAt_eq_sqrt_det_adjoint_comp). For E = Eucl k, finrank ℝ E = k (finrank_euclideanSpace_fin), so the left side is the integral with respect to μHE[k].
  - Provenance: AreaLipschitz.lean derives (L1) from weighted_area_formula_volume_of_injective_derivative (Chapter02/WeightedArea.lean:120). That is the volume-normalized form of weighted_area_formula_of_injective_derivative (WeightedArea.lean:76), the area formula for maps that are injective on s with injective derivative at every point of s. The derivation discards the null images of the Rademacher exceptional set and of the critical set, so no rank or everywhere-differentiability hypothesis remains.
- (L2) Poincare.SimonGMT.Chapter02.areaRegularSet f := {x | DifferentiableAt ℝ f x ∧ Injective (fderiv ℝ f x)}. It is measurable (measurableSet_areaRegularSet, AreaLipschitz.lean:34). For Lipschitz f and every s, μHE[finrank ℝ E](f '' (s ∖ areaRegularSet f)) = 0 (area_image_compl_regularSet_eq_zero, AreaLipschitz.lean:59; Rademacher's theorem and the null critical image).
- (L3) Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt (Chapter02/AreaApproximation.lean:44): x ↦ J_f(x) is Borel.
- (L4) Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Mathlib/MeasureTheory/Function/Jacobian.lean:255), for f : E → F with E finite-dimensional and F second countable.
  - Input: hf′ : ∀ x ∈ s, HasFDerivWithinAt f (f′ x) s x, and r : (E →L[ℝ] F) → ℝ≥0 with r A ≠ 0.
  - Output: pairwise disjoint measurable t_n with s ⊆ ⋃_n t_n, and A_n with ApproximatesLinearOn f (A_n) (s ∩ t_n) (r(A_n)), i.e. ‖f x − f y − A_n(x − y)‖ ≤ r(A_n)‖x − y‖ on s ∩ t_n; moreover s.Nonempty → ∀ n, ∃ y ∈ s, A_n = f′ y.
- (L5) Mathlib MeasurableSet.image_of_continuousOn_injOn (Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:821): the image of a Borel subset of a Polish space under a map that is continuous and injective on it is Borel.
- (L6) Mathlib LinearMap.injective_iff_antilipschitz (Mathlib/Analysis/Normed/Module/FiniteDimension.lean:242), and LinearMap.normDet_sq_eq_det_gram (Mathlib/Analysis/InnerProductSpace/NormDet.lean:303): normDet(L)² = det(⟨L b_i, L b_j⟩)_{i,j} for every orthonormal basis b of the source.
- (L7) Measure theory:
  - Sets and Hausdorff measures: NullMeasurableSet.exists_measurable_subset_ae_eq; Measure.euclideanHausdorffMeasure_def (μHE[k] = c_k • μH[k] with c_k := volume.addHaarScalarFactor μH[k] ∈ ℝ≥0, nonzero by addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, hence 0 < c_k < ∞); Measure.euclideanHausdorffMeasure_zero (μHE[0] = μH[0]); Measure.hausdorffMeasure_zero_singleton (μH[0]{x} = 1); Measure.hausdorffMeasure_apply (the δ-cover formula for μH[d]).
  - Integrals: lintegral_prod; Measurable.lintegral_prod_right'; lintegral_iUnion; lintegral_tsum; setLIntegral_congr.
  - Volume: measurePreserving_piFinSuccAbove; PiLp.volume_preserving_ofLp; PiLp.volume_preserving_toLp.

Conventions.
- E := ℝ^P = Eucl P, E′ := ℝ^{P+1} = Eucl (P+1), and Hᵏ := μHE[k] on the relevant space. vol denotes Lebesgue measure (volume) on ℝ and on Eucl k.
- For s ∈ ℝ and x ∈ E, Φ(s,x) := (s, x_1, …, x_P) ∈ E′ (Lean: (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))). For y ∈ E′, y_0 is its 0-th coordinate and π(y) := (y_1, …, y_P) ∈ E (Lean as in the statement).
- Then π(Φ(s,x)) = x, y = Φ(y_0, π(y)), and ⟨Φ(s,x), Φ(s′,x′)⟩ = ss′ + ⟨x, x′⟩. In particular ‖Φ(s,x) − Φ(s′,x′)‖² = (s − s′)² + ‖x − x′‖².
- For S ⊆ E write Ŝ := {y : π(y) ∈ S} = Φ(ℝ × S). The map S ↦ Ŝ commutes with unions, intersections and differences, and Ŝ is Borel when S is (π is continuous linear).
- By (L7), μHE[k] and μH[k] have the same null sets.

Part (a). Let N ⊆ E with H^m(N) = 0. We show H^{m+1}(N̂) = 0.
1. (m = 0.) μHE[0] = μH[0] and μH[0]({x}) = 1 for every x (L7). So H^0(N) = 0 forces N = ∅, and then N̂ = ∅.
2. (m ≥ 1: what suffices.) N̂ = ⋃_{a ∈ ℤ} Φ([a, a+1] × N), so by countable subadditivity it suffices to show μH[m+1](Φ([a, a+1] × N)) = 0 for each a ∈ ℤ.
   - By hausdorffMeasure_apply, μH[m+1](S) = sup_{r>0} inf Σ_n diam(t_n)^{m+1}, the infimum over countable covers (t_n) of S with diam t_n ≤ r. (For m + 1 ≥ 1 the factor ⨆_{t_n ≠ ∅} is harmless because diam ∅ = 0.)
   - So it suffices: for every r > 0 and ε′ > 0, Φ([a, a+1] × N) has a countable cover by sets of diameter ≤ r with Σ diam^{m+1} ≤ ε′.
   - Given r, fix δ ∈ (0, 1) with √2·δ ≤ r. Steps 3–4 produce, for every ε ∈ (0, (δ/2)^m), such a cover with diameters ≤ √2·δ and Σ diam^{m+1} ≤ 2^{2+(m+1)/2}·ε.
3. (Covering N.) Since μH[m](N) = 0, the infimum in hausdorffMeasure_apply for the radius δ/2 is 0. So there are sets C_i (i ∈ ℕ) with N ⊆ ⋃_i C_i, diam C_i ≤ δ/2 and Σ_i (diam C_i)^m < ε. (Because m ≥ 1, (diam ∅)^m = 0^m = 0, so the factor ⨆_{C_i ≠ ∅} can be dropped. All diameters here are finite, so ediam = diam.)
   - Put d_i := max(diam C_i, (ε·2^{−i−1})^{1/m}).
   - Then 0 < d_i ≤ max(δ/2, ε^{1/m}) < δ < 1, and d_i^m ≤ (diam C_i)^m + ε·2^{−i−1}, so Σ_i d_i^m < 2ε.
4. (Covering the strip.) Let k_i := ⌈1/d_i⌉ ≤ 1/d_i + 1 ≤ 2/d_i.
   - [a, a+1] ⊆ ⋃_{k=0}^{k_i−1} [a + k·d_i, a + (k+1)·d_i], so Φ([a, a+1] × C_i) ⊆ ⋃_{k<k_i} Q_{i,k} with Q_{i,k} := Φ([a + k·d_i, a + (k+1)·d_i] × C_i).
   - By the distance formula, diam Q_{i,k} ≤ √(d_i² + (diam C_i)²) ≤ √2·d_i < √2·δ.
   - The countable family (Q_{i,k}) covers Φ([a, a+1] × N), and Σ_{i,k} (diam Q_{i,k})^{m+1} ≤ Σ_i (2/d_i)(√2·d_i)^{m+1} = 2^{1+(m+1)/2}·Σ_i d_i^m ≤ 2^{2+(m+1)/2}·ε.
   - To apply hausdorffMeasure_apply, index the family by ℕ: send n to Q_{i,k} if n = Nat.pair i k with k < k_i, and to ∅ otherwise. Empty sets contribute 0 because of the factor ⨆_{t_n ≠ ∅}.
   - By Step 2, μH[m+1](Φ([a, a+1] × N)) = 0 for every a, hence H^{m+1}(N̂) = 0.

Part (b). Let A be as in (b) and g : E′ → [0, ∞] measurable.
For B ⊆ E and s ∈ ℝ write:
- LHS(B) := ∫⁻_{B̂} g dH^{m+1};
- φ_B(s) := ∫⁻_{x ∈ B} g(Φ(s,x)) dH^m(x);
- RHS(B) := ∫⁻_ℝ φ_B(s) ds.
The goal is LHS(A) = RHS(A). The function (s, x) ↦ g(Φ(s,x)) is Borel on ℝ × E (Φ is continuous).

5. (Reduction to Borel A.) By NullMeasurableSet.exists_measurable_subset_ae_eq there is a Borel A₀ ⊆ A with H^m(A ∖ A₀) = 0.
   - Â = Â₀ ∪ (A ∖ A₀)^, and H^{m+1}((A ∖ A₀)^) = 0 by Part (a). So Â =ᵐ Â₀ for H^{m+1}, and LHS(A) = LHS(A₀) (setLIntegral_congr).
   - For every s, A =ᵐ A₀ for H^m, so φ_A(s) = φ_{A₀}(s) and RHS(A) = RHS(A₀).
   - A₀ is countably m-rectifiable (CountablyRectifiable.mono) and H^m(A₀ ∩ K) ≤ H^m(A ∩ K) < ∞ for compact K.
   - So we may and do assume that A is Borel.
   - Then H^m⌞A is σ-finite: E = ⋃_k B̄_k(0) and H^m(A ∩ B̄_k(0)) < ∞. Hence H^m⌞A′ is σ-finite (in particular s-finite) for every Borel A′ ⊆ A.
6. (Injective Lipschitz pieces.) By CountablyRectifiable m A, A ⊆ M₀ ∪ ⋃_i F_i(Eucl m) with H^m(M₀) = 0 and F_i : Eucl m → E satisfying LipschitzWith K_i F_i.
   - Fix i and let R_i := areaRegularSet F_i, which is Borel by (L2). For b ∈ R_i, F_i has Fréchet derivative fderiv ℝ F_i b at b, hence HasFDerivWithinAt F_i (fderiv ℝ F_i b) R_i b.
   - For each injective continuous linear L : Eucl m → E, fix by (L6) a constant c_L > 0 with ‖Lv‖ ≥ c_L‖v‖ for all v, and put r(L) := c_L/2. Put r(L) := 1 if L is not injective. Then r(L) ≠ 0 for all L.
   - Apply (L4) to F_i, s := R_i, f′ := fderiv ℝ F_i and r. This gives pairwise disjoint Borel sets t_{i,l} (l ∈ ℕ) with R_i ⊆ ⋃_l t_{i,l}, and continuous linear maps A_{i,l}, with the following properties.
     - Put S_{i,l} := R_i ∩ t_{i,l} (Borel). Then ‖F_i(b) − F_i(b′) − A_{i,l}(b − b′)‖ ≤ r(A_{i,l})·‖b − b′‖ for b, b′ ∈ S_{i,l}.
     - If R_i ≠ ∅, then A_{i,l} = fderiv ℝ F_i y for some y ∈ R_i, which is injective by the definition of R_i.
   - Hence, if S_{i,l} ≠ ∅, A_{i,l} is injective and, with c := c_{A_{i,l}} > 0, for b, b′ ∈ S_{i,l}: ‖F_i(b) − F_i(b′)‖ ≥ ‖A_{i,l}(b − b′)‖ − (c/2)‖b − b′‖ ≥ (c/2)‖b − b′‖. So F_i is injective on S_{i,l} (trivially also if S_{i,l} = ∅).
   - Enumerate the pairs (i, l) by p ∈ ℕ via (i, l) = Nat.unpair p, and write G_p := F_i and S_p := S_{i,l}. Then:
     - G_p is LipschitzWith K_i and S_p is Borel;
     - G_p is injective on S_p and differentiable at every point of S_p (S_p ⊆ R_i);
     - G_p '' S_p is Borel by (L5) (Eucl m is Polish and G_p is continuous).
   - Let N := M₀ ∪ ⋃_i F_i '' (Eucl m ∖ R_i). Then H^m(N) = 0 by (L2) (with s := Eucl m and finrank ℝ (Eucl m) = m) and countable subadditivity.
   - A ⊆ N ∪ ⋃_p G_p '' S_p. Indeed, if x ∈ A ∖ M₀, then x = F_i(b) for some i and b. If b ∉ R_i then x ∈ N. Otherwise b ∈ t_{i,l} for some l, so x ∈ G_p '' S_p for the index p of (i, l).
7. (Disjoint pieces.) Put A_p := (A ∩ G_p '' S_p) ∖ ⋃_{q<p} G_q '' S_q and B_p := S_p ∩ G_p⁻¹(A_p).
   - Both are Borel (Step 5, Step 6, continuity of G_p).
   - The A_p are pairwise disjoint subsets of A.
   - A ∖ ⋃_p A_p ⊆ N: if x ∈ A ∖ N, let p be the least index with x ∈ G_p '' S_p; then x ∈ A_p.
   - G_p maps B_p bijectively onto A_p, because A_p ⊆ G_p '' S_p and G_p is injective on S_p ⊇ B_p.
8. (Area formula in dimension m.) For each p and every function u : E → [0, ∞], (L1) with f := G_p and s := B_p (measurable, InjOn, G_p '' B_p = A_p) gives
   ∫⁻_{A_p} u dH^m = ∫⁻_{b ∈ B_p} J_p(b)·u(G_p(b)) db, where J_p(b) := ENNReal.ofReal(areaJacobianAt G_p b).   (8.1)
9. (The lifted pieces.) For w ∈ Eucl (m+1), let w_0 be its 0-th coordinate and tl(w) ∈ Eucl m its remaining coordinates (Lean: (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m+1)) ℝ w))). Then ‖w − w′‖² = (w_0 − w′_0)² + ‖tl w − tl w′‖².
   Define G̃_p : Eucl (m+1) → E′ by G̃_p(w) := Φ(w_0, G_p(tl w)), and B̃_p := {w : tl w ∈ B_p} (Borel).
   (i) G̃_p is Lipschitz: ‖G̃_p(w) − G̃_p(w′)‖² = (w_0 − w′_0)² + ‖G_p(tl w) − G_p(tl w′)‖² ≤ max(1, K_i)²·‖w − w′‖².
   (ii) G̃_p is injective on B̃_p. If G̃_p(w) = G̃_p(w′), then w_0 = w′_0 and G_p(tl w) = G_p(tl w′). Hence tl w = tl w′, as both lie in B_p ⊆ S_p, and so w = w′.
   (iii) G̃_p '' B̃_p = Â_p.
       - For w ∈ B̃_p, π(G̃_p(w)) = G_p(tl w) ∈ A_p.
       - Conversely, if π(y) ∈ A_p, then π(y) = G_p(b) with b ∈ B_p. The w with w_0 = y_0 and tl w = b satisfies G̃_p(w) = Φ(y_0, π(y)) = y.
   (iv) (Jacobian.) Let w ∈ B̃_p, b := tl w ∈ S_p and L := fderiv ℝ G_p b (G_p is differentiable at b). We show areaJacobianAt G̃_p w = areaJacobianAt G_p (tl w), so J̃_p(w) = J_p(tl w) on B̃_p.
       - By the chain rule G̃_p is differentiable at w with derivative L̃(ω) = ω_0·Φ(1,0) + Φ(0, L(tl ω)).
       - Let (e_0, …, e_m) and (e′_0, …, e′_{m−1}) be the standard orthonormal bases of Eucl (m+1) and Eucl m (0-based, as in Lean's Fin). Then L̃e_0 = Φ(1,0) and L̃e_{j+1} = Φ(0, L e′_j) for 0 ≤ j < m, since (e_{j+1})_0 = 0 and tl e_{j+1} = e′_j (Lean: tl (single j.succ 1) = single j 1).
       - Since ‖Φ(1,0)‖ = 1, ⟨Φ(1,0), Φ(0,v)⟩ = 0 and ⟨Φ(0,u), Φ(0,v)⟩ = ⟨u, v⟩, the Gram matrix (⟨L̃e_i, L̃e_j⟩)_{0≤i,j≤m} has first row and column (1, 0, …, 0). Its entry at (i+1, j+1) is ⟨Le′_i, Le′_j⟩.
       - Expanding along the first row (Matrix.det_succ_row_zero), its determinant is det(⟨Le′_i, Le′_j⟩)_{0≤i,j<m}.
       - By (L6) and areaJacobianAt = normDet ∘ fderiv, (areaJacobianAt G̃_p w)² = (areaJacobianAt G_p b)². Both are ≥ 0, so they are equal.
       - For m = 0 both sides equal 1: the Gram matrices are (1) and the empty matrix.
10. (Area formula in dimension m+1, then Tonelli.) Fix p.
   - By (L1) with f := G̃_p and s := B̃_p (finrank ℝ (Eucl (m+1)) = m+1), using 9(i)–(iv):
     LHS(A_p) = ∫⁻_{Â_p} g dH^{m+1} = ∫⁻_{w ∈ B̃_p} J_p(tl w)·g(Φ(w_0, G_p(tl w))) dw.
   - Ψ(w) := (w_0, tl w) is measure preserving from vol on Eucl (m+1) to vol ⊗ vol on ℝ × Eucl m. It is the composite of PiLp.volume_preserving_ofLp, measurePreserving_piFinSuccAbove at index 0, and PiLp.volume_preserving_toLp on the second factor. Moreover B̃_p = Ψ⁻¹(ℝ × B_p).
   - The function h(s, b) := 1_{B_p}(b)·J_p(b)·g(Φ(s, G_p(b))) is Borel on ℝ × Eucl m, by (L3), Borel g, and continuity of Φ and G_p.
   - The change of variables along Ψ, Tonelli (lintegral_prod) and (8.1) give
     LHS(A_p) = ∫⁻ h d(vol ⊗ vol) = ∫⁻_ℝ ∫⁻_{b ∈ B_p} J_p(b)·g(Φ(s, G_p(b))) db ds = ∫⁻_ℝ φ_{A_p}(s) ds = RHS(A_p).
     The third equality is (8.1) applied, for each fixed s, to u := g(Φ(s, ·)).
11. (Summation.)
   - The sets Â_p are Borel and pairwise disjoint, and ⋃_p Â_p ⊆ Â. Moreover Â ∖ ⋃_p Â_p = (A ∖ ⋃_p A_p)^ ⊆ N̂, which is H^{m+1}-null by Part (a). Hence, by setLIntegral_congr and lintegral_iUnion, LHS(A) = Σ_p LHS(A_p).
   - For every s, A =ᵐ ⋃_p A_p for H^m (the difference lies in N), so φ_A(s) = Σ_p φ_{A_p}(s).
   - Each φ_{A_p} is measurable by Measurable.lintegral_prod_right', applied to the Borel function (s, x) ↦ g(Φ(s,x)) and the s-finite measure H^m⌞A_p (Step 5). So lintegral_tsum gives RHS(A) = Σ_p RHS(A_p).
   - By Step 10, LHS(A) = Σ_p LHS(A_p) = Σ_p RHS(A_p) = RHS(A). ∎

Implementation notes.
- Submission.lean may add imports: Poincare.SimonGMT.Chapter02.AreaLipschitz, Poincare.SimonGMT.Chapter02.AreaApproximation, Mathlib.MeasureTheory.Function.Jacobian, Mathlib.MeasureTheory.Constructions.Polish.Basic, Mathlib.Analysis.InnerProductSpace.NormDet and Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace. The comparator byte-checks only the frozen inputs.
- During this decomposition, two steps were checked in Lean against the frozen project, with only standard axioms. The checks used the definitions of Φ, tl and G̃_p above.
  - Step 9(iv), as `areaJacobianAt (fun w => Φ(w 0, G (tl w))) w = areaJacobianAt G (tl w)` whenever G is differentiable at tl w. The derivative is (EuclideanSpace.proj 0).smulRight e_0 + Φ(0,·) ∘L fderiv G (tl w) ∘L tl. The proof uses LinearMap.normDet_sq_eq_det_gram with EuclideanSpace.basisFun, Matrix.det_succ_row_zero and pow_left_inj₀.
  - The measure preservation of w ↦ (w 0, tl w) in Step 10, via PiLp.volume_preserving_ofLp, measurePreserving_piFinSuccAbove (index 0) and (MeasurePreserving.id).prod (PiLp.volume_preserving_toLp).

## Key steps

1. Φ(s,x) = (s,x) is a linear isometry ℝ × ℝ^P → ℝ^{P+1} with {π ∈ S} = Φ(ℝ × S); μHE[k] and μH[k] have the same null sets.
2. (a) Null sets: for m = 0, N = ∅; for m ≥ 1 cover N by sets C_i with Σ diam^m < ε and each strip [a,a+1] × C_i by ≤ 2/d_i boxes of diameter ≤ √2 d_i, so the (m+1)-dimensional δ-content is O(ε).
3. (b) Reduce to Borel A via (a). Cut the Lipschitz parametrizations into injective Lipschitz pieces G_p|S_p (Rademacher and null critical images by area_image_compl_regularSet_eq_zero, Mathlib's approximately-linear partition, Borel injective images). Disjointify to A_p = G_p(B_p), leaving an H^m-null set N.
4. Apply SimonGMT's injective Lipschitz area formula (weighted_area_formula_lipschitz_injOn) to G_p on B_p and to the lift G̃_p(w) = Φ(w_0, G_p(tl w)) on ℝ × B_p. The two Jacobians agree, since the Gram matrix is block-diagonal diag(1, Gram(DG_p)).
5. The measure-preserving splitting ℝ^{m+1} ≅ ℝ × ℝ^m, Tonelli and the m-dimensional area formula give LHS(A_p) = RHS(A_p). Sum over p with lintegral_iUnion and lintegral_tsum; the remainders are null by (a).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3: read nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/{parent-child-handoff,decomposition-v1,decomposition-audit-v1,decomposition-review-receipt-v1}.json`
- `python3: dag.json statuses and frozen lean_statements of iwl_im_closure, iwl_smooth_pushforward, iwl_cycle_reduction, isoperimetric_apply_eq_zero_of_disjoint_support, cmb_abs_apply_le_of_massOn_le, isoperimetric_abs_covector_apply_le, lpf_countably_rectifiable_c1_cover, lpf_rectifiable_area_formula; scan of dag.json and nodes/*/decomposition-v*.json for iwl_cr_* names`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem MeasurableSet.image_of_continuousOn_injOn|theorem LinearMap.injective_iff_antilipschitz|theorem normDet_sq_eq_det_gram|theorem measurePreserving_piFinSuccAbove|theorem PiLp.volume_preserving_ofLp|theorem PiLp.volume_preserving_toLp|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero|theorem hausdorffMeasure_zero_singleton|theorem hausdorffMeasure_apply|theorem exists_measurable_subset_ae_eq|theorem lintegral_prod |theorem Measurable.lintegral_prod_right'|theorem lintegral_iUnion |theorem lintegral_tsum' mathlib/Mathlib (snapshot)`
- `rg -n 'hausdorffMeasure.*prod|area_formula|areaJacobian' mathlib/Mathlib (snapshot)`
- `grep -rln for hasFDerivAt_integral_of_dominated_of_fderiv_le, norm_iteratedFDeriv_le_of_bilinear, norm_iteratedFDeriv_smul_le, alternatizeUncurryFin_curryLeft, extDeriv_extDeriv, tendsto_integral_filter_of_dominated_convergence, integral_integral_swap, euclideanHausdorffMeasure_homothety_image, det_succ_row_zero in snapshot Mathlib`
- `grep -n '^theorem|^def' simongmt Chapter02/{AreaLipschitz,WeightedArea,Area,AreaApproximation,AreaNoninjective}.lean, Chapter03/{Rectifiable,DisjointCover,SubmanifoldCover}.lean, Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean; rg 'pointSlice_isTestForm|iteratedFDeriv_fixedSupportParameterSlice' simongmt`
- `git show 2f3657605e574458d48b2cd837f262ae2f392816:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, piece construction hpart)`
- `python3 -I /tmp/cr2/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/cr2/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/cr2/Scratch/Assembly.lean, SolutionCheck.lean, LibCheck.lean, JacCheck.lean, SplitCheck.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-density-comparison-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cr2/scripts/gen.py`
- `/tmp/cr2/Scratch/Assembly.lean`
- `/tmp/cr2/Scratch/SolutionCheck.lean`
- `/tmp/cr2/Scratch/LibCheck.lean`
- `/tmp/cr2/Scratch/JacCheck.lean`
- `/tmp/cr2/Scratch/SplitCheck.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

Findings in dag.json:
- The chart-cover and rectifiable-area-formula nodes (lpf_countably_rectifiable_c1_cover, lpf_rectifiable_area_formula) are still speculative-ready, so they cannot be reused.
- No other DAG node supplies a product formula.
- iwl_im_closure and iwl_smooth_pushforward are the parent's frozen sibling dependencies, with the types used in the assembly.
- The reused isoperimetric_apply_eq_zero_of_disjoint_support, cmb_abs_apply_le_of_massOn_le and isoperimetric_abs_covector_apply_le are accepted, with identical types.

Libraries:
- rg in the snapshot Mathlib finds no area formula and no Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real and hausdorffMeasure_prod_real exist.
- The pinned SimonGMT package (lake-packages-25730c7c/simongmt, rev 2b36630) supplies the injective Lipschitz area formula weighted_area_formula_lipschitz_injOn (Chapter02/AreaLipschitz.lean:101). It takes an arbitrary weight, with μHE[finrank E] on the target, volume on the source and J = areaJacobianAt = normDet. It is derived from WeightedArea.lean:76/120. SimonGMT also supplies area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet and measurable_areaJacobianAt.
- Mathlib supplies exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255), MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821), LinearMap.injective_iff_antilipschitz, LinearMap.normDet_sq_eq_det_gram (NormDet.lean:303), measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, lintegral_prod, lintegral_iUnion and lintegral_tsum.
- All of these print only propext, Classical.choice and Quot.sound.
- The accepted rectifiability_weighted_tangent_ae (commit 2f36576) already formalizes the same bi-Lipschitz piece construction (`hpart`).
- These inputs give a complete chart-free proof of the product formula.

Lean checks:
- 12 challenge modules and 12 solution resolutions.
- The parent assembly.
- The lift Jacobian identity and the measure-preserving split (standard axioms only).

These checks certify statements, assembly and library inputs, not the remaining analytic proofs. Those were reviewed in natural language; the v1 audit accepted 11 of them, and an independent reviewer accepted the repaired one in this session.

Public citation: Federer, GMT (1969) 3.2.23, cited for this product formula in arXiv:2505.11279.
