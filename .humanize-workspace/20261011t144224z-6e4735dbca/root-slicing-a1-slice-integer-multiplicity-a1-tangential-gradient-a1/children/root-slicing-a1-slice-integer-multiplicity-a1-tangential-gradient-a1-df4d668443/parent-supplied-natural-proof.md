# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k), |·| Euclidean norm, ⟨·,·⟩ inner product; Lⁿ := volume on ℝⁿ; Hⁿ := μHE[n] on ℝ^Q (translation invariant; Hⁿ(λS) = λⁿHⁿ(S) for λ > 0, Mathlib `MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀`; Hⁿ = Lⁿ on ℝⁿ). B_ρ(y), B̄_ρ(y) are the open and closed balls. η_{y,r}(x) := r⁻¹(x − y) (SimonGMT `blowUpMap y r`), r > 0. By definition, HasWeightedApproximateTangentSpaceAt n M θ y T means: dim T = n and, for every φ ∈ C_c(ℝ^Q), ∫_{η_{y,r}(M)} φ(z) θ(y + rz) dHⁿ(z) → θ(y) ∫_T φ dHⁿ as r ↓ 0; SimonGMT `HasApproximateTangentSpaceAt n S y T` (Simon 1.4) is the same with θ ≡ 1 and S in place of M. Put N := Φ(Ω). This lemma is the existence half of Step 6 of the parent proof, which cites Simon Ch. 3, Remark 1.5(2), the proof of Theorem 1.6 “⟹” and Remark 1.8(1) (weighted version); those printed arguments are copied below, specialised to the single C¹ chart N, with all details filled in. (The parent's parenthetical treats the term θ − θ(y) on M ∩ N via Lebesgue points; following the cited Remark 1.8(1), the same estimate is obtained from compact Lusin pieces C on which θ is continuous, steps 1–4.)

0. Preliminaries on the chart.
 (a) Let w ∈ Ω, s ∈ ℝⁿ. For small |t|, w + ts ∈ Ω (Ω open), so c|t||s| ≤ |Φ(w + ts) − Φ(w)|; dividing by |t| and letting t → 0 gives c|s| ≤ |DΦ(w)s|. Hence DΦ(w) is injective and T_w := DΦ(w)(ℝⁿ) = LinearMap.range (fderiv ℝ Φ w) has dimension n. Φ is injective on Ω (Φ(w) = Φ(w′) forces c|w − w′| ≤ 0). For y ∈ N let w_y denote the unique point of Ω with Φ(w_y) = y; the clause “∀ w ∈ Ω, Φ w = y → …” of the claim only concerns w = w_y. Put T_y := T_{w_y}. The inverse Ψ := (Φ|Ω)⁻¹ : N → Ω is c⁻¹-Lipschitz.
 (b) N is σ-compact (Ω is a countable union of compact sets and Φ is continuous), hence Borel; so M ∩ N is Hⁿ-null-measurable.
 (c) (N is locally Hⁿ-finite.) Let K ⊆ ℝ^Q be compact. Ψ(N ∩ K) has diameter ≤ c⁻¹ diam K, so it lies in a closed ball B̄ ⊆ ℝⁿ. Φ is Λ-Lipschitz on the compact convex set B̄, Λ := max_{B̄}‖DΦ‖ (mean value inequality; Φ is C¹). Hence Hⁿ(N ∩ K) ≤ Hⁿ(Φ(B̄)) ≤ Λⁿ Lⁿ(B̄) < ∞ (SimonGMT `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`).
 (d) (Blow-up change of variables.) η_{y,r} is a translation followed by the dilation by r⁻¹, so for every set S ⊆ ℝ^Q and every g : ℝ^Q → ℝ, ∫_{η_{y,r}(S)} g dHⁿ = r^{−n} ∫_S g(η_{y,r}(x)) dHⁿ(x) (Bochner integrals; this is the accepted DAG lemma `lpf_wtc_blowup_setIntegral_image`), and Hⁿ(η_{y,r}(S) ∩ B̄_R(0)) = r^{−n} Hⁿ(S ∩ B̄_{rR}(y)).
 (e) (C¹ blow-up of N; Simon: “since x ∈ N_j and N_j is a C¹ submanifold, lim ∫_{η_{x,λ}(N_j)} f dHⁿ = ∫_{T_x N_j} f dHⁿ”.) Claim: for every y ∈ N and φ ∈ C_c(ℝ^Q), ∫_{η_{y,r}(N)} φ dHⁿ → ∫_{T_y} φ dHⁿ as r ↓ 0 (so N has approximate tangent space T_y at y), and for every R > 0, sup_{0<r≤1} r^{−n} Hⁿ(N ∩ B̄_{rR}(y)) < ∞.
 Proof. Let w := w_y, spt φ ⊆ B_R(0), 0 < r ≤ 1. By (d), ∫_{η(N)} φ dHⁿ = r^{−n} ∫_N φ((x − y)/r) dHⁿ(x). If the integrand is nonzero at x then x = Φ(v) with v ∈ Ω and |Φ(v) − Φ(w)| < rR, hence c|v − w| < rR and |v − w| < R/c. Let Ω′ := Ω ∩ B_{R/c+1}(w): a bounded open set on which Φ is injective and Lipschitz (argument of (c)). By the injective area formula (Simon Ch. 2, (3.5); SimonGMT `Chapter02.injective_area_formula_lipschitzOn`, and in weighted form `Chapter02.weighted_area_formula_lipschitz_injOn` applied to a global Lipschitz extension of Φ|Ω′, which agrees with Φ on the open set Ω′ and so has the same derivative there; applied to φ⁺ and φ⁻ separately), with the area Jacobian JΦ(v) := √det(⟨DΦ(v)e_i, DΦ(v)e_j⟩)_{i,j} (this equals SimonGMT's area Jacobian normDet DΦ(v), by Mathlib `LinearMap.normDet_sq_eq_det_gram` for the standard orthonormal basis of ℝⁿ together with `LinearMap.normDet_nonneg`),
 r^{−n} ∫_N φ((x − y)/r) dHⁿ(x) = r^{−n} ∫_{Ω′} φ((Φ(v) − Φ(w))/r) JΦ(v) dv = ∫_{ℝⁿ} 1_{Ω′}(w + rs) φ((Φ(w + rs) − Φ(w))/r) JΦ(w + rs) ds,
 the last step by the substitution v = w + rs (dv = rⁿ ds). The last integrand vanishes for |s| ≥ R/c and is bounded by sup|φ| · max_{|z−w|≤R/c} JΦ(z) < ∞ (JΦ is continuous since DΦ is; accepted DAG lemma `lpf_wtc_cat_gram_jacobian_continuous`). For fixed s, as r ↓ 0: w + rs ∈ Ω′ eventually (Ω′ open), (Φ(w + rs) − Φ(w))/r → DΦ(w)s, and JΦ(w + rs) → JΦ(w). By dominated convergence the integral tends to JΦ(w) ∫_{ℝⁿ} φ(DΦ(w)s) ds (this limit is the accepted DAG lemma `lpf_wtc_cat_rescaled_integral_tendsto`), which equals ∫_{T_y} φ dHⁿ by the area formula for the injective linear (hence Lipschitz) map s ↦ DΦ(w)s, whose Jacobian is the constant JΦ(w). For the density bound, take φ₀ ∈ C_c(ℝ^Q) with 1_{B̄_R(0)} ≤ φ₀ ≤ 1_{B_{2R}(0)}; the same identity (with 2R in place of R) gives r^{−n} Hⁿ(N ∩ B̄_{rR}(y)) = Hⁿ(η(N) ∩ B̄_R(0)) ≤ ∫_{η(N)} φ₀ dHⁿ ≤ max_{|z−w|≤2R/c} JΦ(z) · Lⁿ(B_{2R/c}(0)) for all 0 < r ≤ 1. □
 (f) (Upper Density Theorem, Simon Ch. 1, 3.6 with Remark 3.7(2); SimonGMT `Chapter01.simon_theorem_3_6`.) Let W ⊆ ℝ^Q be open, S ⊆ ℝ^Q Hⁿ-null-measurable and g : ℝ^Q → [0, ∞] with ∫_{S∩K} g dHⁿ < ∞ for every compact K ⊆ W. Then for Hⁿ-a.e. y ∈ W ∖ S, ρ^{−n} ∫_{S ∩ B̄_ρ(y)} g dHⁿ → 0 as ρ ↓ 0. Proof: cover W by countably many open balls B with closure B ⊆ W; μ_B := g·Hⁿ⌞(S ∩ B) is a finite Borel (hence Borel regular) measure, so by 3.6 its upper n-density vanishes at Hⁿ-a.e. point outside S ∩ B; for y ∈ B ∖ S and small ρ, B̄_ρ(y) ⊆ B, so μ_B(B̄_ρ(y)) = ∫_{S ∩ B̄_ρ(y)} g dHⁿ. The constant ω_n and the positive factor between Simon's Hⁿ and μHE[n] change neither null sets nor the vanishing of the limit. (This is the accepted DAG lemma `lpf_wtc_ae_zero_density_off_set`.)

1. (Compact pieces with continuous weight; Remark 1.8(1).) There are compact C_k ⊆ M (k ∈ ℕ) with θ|C_k continuous, Hⁿ(C_k) < ∞ and Hⁿ(M ∖ ⋃_k C_k) = 0. (The accepted DAG lemma `lpf_wtc_lusin_compact_pieces` has exactly this statement.) Proof: let V_i (i ≥ 1) be open sets with compact closures closure V_i ⊆ V and ⋃_i V_i = V (e.g. V_i := {x ∈ V : |x| < i, dist(x, ℝ^Q ∖ V) > 1/i}). Fix i. θ is Hⁿ-integrable on M ∩ closure V_i, so there are a Borel function θ_i and a Borel set M_i′ ⊆ M ∩ V_i with Hⁿ((M ∩ V_i) ∖ M_i′) = 0 and θ = θ_i on M_i′ (M is Hⁿ-null-measurable); θ_i > 0 on M_i′ because θ > 0 on M. ν_i(B) := ∫_{B ∩ M_i′} θ_i dHⁿ is a finite Borel measure on ℝ^Q, hence closed- and compact-inner regular. For j ≥ 1, Lusin's theorem (Simon Ch. 1, 1.17; SimonGMT `Chapter01.exists_isClosed_continuousOn_of_measurable`, applicable because ν_i is finite and closed-inner regular) gives a closed C_{i,j} ⊆ M_i′ with ν_i(M_i′ ∖ C_{i,j}) < 1/j and θ_i|C_{i,j} continuous. C_{i,j} is closed and contained in the compact set closure V_i, hence compact; C_{i,j} ⊆ M, and θ|C_{i,j} = θ_i|C_{i,j} is continuous; so ν_i(M_i′ ∖ ⋃_j C_{i,j}) = 0, and since θ_i > 0 on M_i′, Hⁿ(M_i′ ∖ ⋃_j C_{i,j}) = 0, whence Hⁿ((M ∩ V_i) ∖ ⋃_j C_{i,j}) = 0. θ is continuous and positive on the compact C_{i,j}, so θ ≥ m > 0 there and Hⁿ(C_{i,j}) ≤ m⁻¹ ∫_{C_{i,j}} θ dHⁿ < ∞ (trivial if C_{i,j} = ∅). Since M = ⋃_i (M ∩ V_i), enumerating all C_{i,j} as C_k gives the claim.

2. (Unweighted tangent of a piece on the chart; proof of 1.6 “⟹”.) Fix C := C_k. Apply (f):
 (i) with W := ℝ^Q, S := C ∖ N, g := 1 (Hⁿ(S) ≤ Hⁿ(C) < ∞): for Hⁿ-a.e. y ∈ C ∩ N, ρ^{−n} Hⁿ((C ∖ N) ∩ B̄_ρ(y)) → 0;
 (ii) with W := ℝ^Q, S := N ∖ C, g := 1 (locally finite by 0(c)): for Hⁿ-a.e. y ∈ C ∩ N, ρ^{−n} Hⁿ((N ∖ C) ∩ B̄_ρ(y)) → 0.
 Let y ∈ C ∩ N satisfy (i) and (ii) and let φ ∈ C_c(ℝ^Q), spt φ ⊆ B_R(0), η := η_{y,r}. As η is a bijection, η(C) = η(C ∩ N) ⊔ η(C ∖ N) and η(N) = η(C ∩ N) ⊔ η(N ∖ C), all these sets are Hⁿ-measurable with locally finite measure (by (d), Hⁿ(C) < ∞ and 0(c)), and φ is bounded with compact support, so
 ∫_{η(C)} φ dHⁿ = ∫_{η(N)} φ dHⁿ − ∫_{η(N∖C)} φ dHⁿ + ∫_{η(C∖N)} φ dHⁿ.
 By (d), |∫_{η(N∖C)} φ| ≤ sup|φ| · r^{−n} Hⁿ((N ∖ C) ∩ B̄_{rR}(y)) = sup|φ| · Rⁿ (rR)^{−n} Hⁿ((N ∖ C) ∩ B̄_{rR}(y)) → 0 by (ii), and likewise |∫_{η(C∖N)} φ| → 0 by (i), while ∫_{η(N)} φ → ∫_{T_y} φ by 0(e). Hence C has approximate tangent space T_y at y (dim T_y = n by 0(a)). Moreover r^{−n} Hⁿ(C ∩ B̄_{rR}(y)) ≤ r^{−n} Hⁿ(N ∩ B̄_{rR}(y)) + r^{−n} Hⁿ((C ∖ N) ∩ B̄_{rR}(y)) is bounded for 0 < r ≤ 1 small (0(e) and (i)). (The accepted DAG lemma `lpf_wtc_density_bound_of_tangent` derives such a bound from the tangent property alone.)

3. (Remaining mass of M.) Apply (f) with W := V, S := M ∖ C, g := θ (θ ≥ 0 on M and ∫_{(M∖C)∩K} θ ≤ ∫_{M∩K} θ < ∞ for compact K ⊆ V): for Hⁿ-a.e. y ∈ C (C ⊆ M ⊆ V and y ∉ M ∖ C), ρ^{−n} ∫_{(M∖C) ∩ B̄_ρ(y)} θ dHⁿ → 0.

4. (Weighted blow-up; Remark 1.8(1).) Let y ∈ C ∩ N satisfy the conclusions of steps 2 and 3, let φ ∈ C_c(ℝ^Q) with spt φ ⊆ B_R(0), and choose r₀ ∈ (0, 1] with B̄_{r₀R}(y) ⊆ V (V open). For 0 < r < r₀, by (d),
 ∫_{η(M)} φ(z) θ(y + rz) dHⁿ(z) = r^{−n} ∫_M φ(η(x)) θ(x) dHⁿ(x),
 where x ↦ φ(η(x))θ(x) vanishes off M ∩ B_{rR}(y) and is Hⁿ-integrable (|φ(η(x))θ(x)| ≤ sup|φ| θ(x) and θ is integrable on M ∩ B̄_{r₀R}(y)); also x ↦ φ(η(x)) and x ↦ φ(η(x))(θ(x) − θ(y)) are integrable on C (Hⁿ(C) < ∞, θ integrable on the compact C ⊆ M ∩ V). Splitting M = C ⊔ (M ∖ C) and writing θ = θ(y) + (θ − θ(y)) on C (accepted DAG lemma `lpf_wtc_wtt_blowup_integral_split`):
 r^{−n} ∫_M φ(η(x)) θ(x) dHⁿ(x) = I₁ + I₂ + I₃, where
 I₁ := θ(y) r^{−n} ∫_C φ(η(x)) dHⁿ(x) = θ(y) ∫_{η(C)} φ dHⁿ → θ(y) ∫_{T_y} φ dHⁿ (step 2 and (d));
 I₂ := r^{−n} ∫_{C ∩ B̄_{rR}(y)} φ(η(x))(θ(x) − θ(y)) dHⁿ(x), so |I₂| ≤ sup|φ| · sup_{C ∩ B̄_{rR}(y)} |θ − θ(y)| · r^{−n} Hⁿ(C ∩ B̄_{rR}(y)) → 0, because θ|C is continuous at y and the density ratio is bounded (step 2) — this is the Lebesgue-point estimate of the parent's sketch;
 I₃ := r^{−n} ∫_{(M∖C) ∩ B̄_{rR}(y)} φ(η(x)) θ(x) dHⁿ(x), so |I₃| ≤ sup|φ| · Rⁿ (rR)^{−n} ∫_{(M∖C) ∩ B̄_{rR}(y)} θ dHⁿ → 0 (step 3; accepted DAG lemma `lpf_wtc_wtt_remainder_vanishes`).
 Hence ∫_{η_{y,r}(M)} φ(z) θ(y + rz) dHⁿ(z) → θ(y) ∫_{T_y} φ dHⁿ for every φ ∈ C_c(ℝ^Q); with dim T_y = n (0(a)) this is HasWeightedApproximateTangentSpaceAt n M θ y T_y.

5. (Conclusion.) Let Z be the set of y ∈ M ∩ N at which the claim fails, i.e. HasWeightedApproximateTangentSpaceAt n M θ y (range DΦ(w_y)) does not hold. Then Z ⊆ (M ∖ ⋃_k C_k) ∪ ⋃_k Z_k, where Z_k ⊆ C_k ∩ N is the union of the Hⁿ-null exceptional sets of steps 2(i), 2(ii) and 3 for C = C_k: indeed every y ∈ (C_k ∩ N) ∖ Z_k satisfies the claim by step 4, and w_y is the only w ∈ Ω with Φ(w) = y (0(a)). By step 1 and countable subadditivity Hⁿ(Z) = 0. As M ∩ N is Hⁿ-null-measurable (0(b)), this is exactly ∀ᵐ y ∂(Hⁿ⌞(M ∩ Φ(Ω))), ∀ w ∈ Ω, Φ(w) = y → HasWeightedApproximateTangentSpaceAt n M θ y (LinearMap.range (fderiv ℝ Φ w)). ∎
 (For n = 0 all steps hold verbatim: ℝ⁰ is a point, H⁰ = μHE[0] is counting measure, λ⁰ = 1, N is empty or a single point and T_y = {0}.)

Implementation remarks (not part of the mathematical argument). (i) The frozen type of this lemma is byte-identical to that of `lpf_weighted_tangent_on_c1_chart` (lipschitz-pushforward branch; speculative-ready, not comparator-accepted at the time of this split, hence the fresh name). If that declaration is comparator-accepted when this node is decomposed, it can be reused as a reuse child with its exact name and identical type. (ii) Otherwise, in this node's own decomposition the following comparator-accepted declarations can be included as reuse children (exact names, identical frozen types): `lpf_wtc_cat_fderiv_lower_bound` (0(a)), `lpf_wtc_chart_image_measurable_locally_finite` (0(b), 0(c)), `lpf_wtc_blowup_setIntegral_image` (0(d)), `lpf_wtc_caf_lipschitz_localization` and `lpf_wtc_caf_signed_of_lintegral` (the area formula on Ω′ in 0(e)), `lpf_wtc_cat_gram_jacobian_continuous` and `lpf_wtc_cat_rescaled_integral_tendsto` (the limit in 0(e)), `lpf_wtc_ae_zero_density_off_set` (0(f)), `lpf_wtc_lusin_compact_pieces` (step 1), `lpf_wtc_tangent_transfer` and `lpf_wtc_density_bound_of_tangent` (step 2), `lpf_wtc_wtt_blowup_integral_split`, `lpf_wtc_wtt_continuity_error_vanishes` and `lpf_wtc_wtt_remainder_vanishes` (step 4). (iii) Imports: the SimonGMT modules `Chapter02.AreaDomain`, `Chapter02.AreaLipschitz`, `Chapter01.DensityComparison` and `Chapter01.Lusin` are prebuilt in the shared package and may be added to Submission.lean, as accepted nodes do.

## Key steps

1. Chart facts: |DΦ(w)s| ≥ c|s|, Φ injective on Ω with c⁻¹-Lipschitz inverse, N = Φ(Ω) Borel and locally Hⁿ-finite.
2. Blow-up change of variables; C¹ blow-up via the injective area formula and dominated convergence: N has approximate tangent space DΦ(w_y)(ℝⁿ) at y with bounded density ratios.
3. Remark 1.8(1): Lusin compact pieces C_k ⊆ M with θ|C_k continuous and Hⁿ(C_k) < ∞ cover M up to an Hⁿ-null set.
4. Upper Density Theorem: Hⁿ⌞(C∖N), Hⁿ⌞(N∖C) and θHⁿ⌞(M∖C) have zero n-density at Hⁿ-a.e. point of C ∩ N, so C has approximate tangent T_y there (proof of 1.6 ⟹).
5. Weighted blow-up = θ(y)·(blow-up of C) + continuity error on C + zero-density remainder → θ(y)∫_{T_y}φ; the exceptional set is a countable union of null sets.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean workspace GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (both identical; workspace HEAD d8d46c95)`
- `python3 importlib verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') -> scope prefix: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique|def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n '^theorem|^def' simongmt Chapter02/{Lipschitz,AreaLipschitz,AreaCritical,AreaDomain,WhitneyExtension,WhitneyJet}.lean Chapter01/{Lusin,DensityComparison}.lean Chapter03/{SubmanifoldCover,Differential,DisjointCover}.lean`
- `grep -n '^theorem' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_smul0)`
- `grep -rn 'theorem Measurable.find|theorem measurable_find|theorem ContinuousOn.measurableEmbedding|theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurable_fderiv|theorem measurableSet_of_differentiableAt|theorem DifferentiableWithinAt.differentiableAt|theorem ae_restrict_iff|theorem tendstoUniformlyOn_of_ae_tendsto|IsSigmaCompact.image|theorem normDet_sq_eq_det_gram|theorem normDet_nonneg|theorem hausdorffMeasure_image_le' mathlib/Mathlib`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 and Chapter01 (WhitneyExtension.olean absent; AreaCritical, AreaLipschitz, AreaDomain, WhitneyJet, Lusin, DensityComparison present)`
- `python3 scan of dag.json (360 nodes): uniqueness of slicing_im_tg_* names; byte-identity of child types with lpf_countably_rectifiable_c1_cover / lpf_weighted_tangent_on_c1_chart (speculative-ready); live statuses and statements of lpf_c1r_*, lpf_c1_local_antilipschitz, lpf_lipschitz_c1_immersion_pieces, lpf_wtc_*, lpf_tde_chart_directional_deriv, lpf_ccr_hasDerivAt_line_of_comp, rectifiability_weighted_tangent_ae, br_weightedTangent_congr, iwl_weighted_tangent_locality`
- `read nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json (twin proofs; reuse-child mechanism)`
- `git show <workspace_result_commit>:GMT/Ch06/Submission.lean for 138 accepted nodes (extra SimonGMT imports such as Chapter02.AreaDomain, Chapter01.DensityComparison, Chapter02.AreaBranches are allowed)`
- `lake env lean /tmp/tg_split/Stmts.lean (four child types in exact comparator scope; 0 errors)`
- `lake env lean /tmp/tg_split/Assembly.lean (frozen parent type proved from chart_cover, chart_tangent, chart_gradient stubs; #print axioms: propext, sorryAx [stubs only], Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/CProof.lean (complete proof of the line_deriv frozen type; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/Avail.lean (#check of cited Mathlib and SimonGMT lemmas in the Submission import closure)`
- `python3 verifier/lean_contract.py validate_lean_statement on the four child types (all OK)`
- `rg 'slicing_im_tg' local-references/197bdd4b88278494/project and lake-packages-25730c7c/simongmt (no match)`
- `sed book/chapter-03.txt (1.1-1.9, 2.1-2.2), chapter-02.txt (1.4-1.8, 4.1-4.11), chapter-01.txt (3.6-3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/tmp/tg_split/Stmts.lean`
- `/tmp/tg_split/Assembly.lean`
- `/tmp/tg_split/CProof.lean`
- `/tmp/tg_split/Avail.lean`

Snapshot and imports:
- The snapshot (project d8d46c95, the workspace HEAD; Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract.lean and Submission.lean. Child types may therefore use only contract, SimonGMT and Mathlib names. The comparator scope is namespace GMT.Ch06 with the contract's opens.
- SimonGMT supplies the following:
  - CountablyRectifiable as countably many Lipschitz images plus an Hⁿ-null set, and HasWeightedApproximateTangentSpaceAt with uniqueness at θ(x) ≠ 0.
  - Lipschitz image bounds for μHE[n].
  - Area-formula critical-image and injective results (AreaCritical, AreaLipschitz, AreaDomain), Lusin (Chapter01.Lusin) and the upper density theorem 3.6 (Chapter01.DensityComparison). These modules are not imported by the contract but are prebuilt and may be added to the imports, as accepted nodes do.
  - Its Chapter02.WhitneyExtension module is not prebuilt, so it cannot be imported.
- SimonGMT lacks the chart-cover direction of Simon Lemma 1.2 (SubmanifoldCover proves only the easy direction), a tangential gradient for Lipschitz functions, and tangent identification on C¹ charts.
- Mathlib supplies Rademacher on sets (LipschitzOnWith.ae_differentiableWithinAt_of_mem), μHE[n] = volume on ℝⁿ, measurable_fderiv, measurableSet_of_differentiableAt, Lusin–Souslin images and measurable embeddings, Measurable.find, Egorov, and normDet_sq_eq_det_gram.

DAG and reuse:
- The chart-cover and chart-tangent lemmas exist in the DAG only as the speculative-ready lpf twins. Their types are byte-identical to the children chart_cover and chart_tangent, but they are not yet comparator-accepted, so fresh names are used.
- Many of the twins' leaves are comparator-accepted and are listed in the child proofs for reuse in those children's own decompositions.
- No accepted declaration has a type identical to any child. slicing_im_tg_* matches nowhere: not in the snapshot project, not in SimonGMT, not among the 360 DAG nodes.

Kernel checks:
- All four child types elaborate in the exact scope and pass the verifier's statement validator.
- The frozen parent type is proved from chart_cover, chart_tangent and chart_gradient; sorryAx comes only from the stubs.
- line_deriv is fully proved with standard axioms.

These checks do not certify the analytic proofs of chart_cover, chart_tangent and chart_gradient.
