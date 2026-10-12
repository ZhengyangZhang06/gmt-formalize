# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. n := m+1. ℝ^k = Eucl k, with inner product ⟨·,·⟩ and norm |·|. Lᵏ = volume on ℝᵏ, which equals μHE[k] there. Hᵏ := μHE[k] on ℝ^P. Write DΦ(w) := fderiv ℝ Φ w and Dh(w) := fderiv ℝ h w. ∇h(w) ∈ ℝⁿ is the gradient, so Dh(w)u = ⟨∇h(w), u⟩. For a linear map T : ℝᵏ → ℝ^P put J_k(T) := T.normDet = √det(T*T). This equals √(Gram determinant of T e_1, …, T e_k) (Mathlib `LinearMap.normDet`, `normDet_sq_eq_det_gram`), and J_k(T) > 0 iff T is injective. Set E := Ω ∩ Φ⁻¹(W), which is Borel. By hypothesis, for w ∈ E: f(Φw) = h(w); ĝ(w) := G(Φw) ≠ 0; ĝ(w) ∈ range DΦ(w); and ⟨ĝ(w), DΦ(w)u⟩ = Dh(w)u for all u. K and c > 0 are the Lipschitz and antilipschitz constants of Φ on Ω.

Tools.
- (AF) Area formula for injective Lipschitz maps. Let V ⊆ ℝᵏ be open, σ : ℝᵏ → ℝ^P Lipschitz and injective on V, S ⊆ V Borel and F : ℝ^P → [0, ∞] Borel. Then ∫_{σ(S)} F dHᵏ = ∫_S F(σ(v)) J_k(Dσ(v)) dv, and σ(S) is Borel (Lusin–Souslin, `MeasurableSet.image_of_continuousOn_injOn`).
 Source: Simon Ch. 2, (3.2)/(3.5)–(3.6); Federer 3.2.3, 3.2.5. In Lean, apply SimonGMT `Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitzOn_fiberSum` on the open set V with weight w := 1_S·(F∘σ). Injectivity on V makes the fibre sum at y equal to 1_{σ(S)}(y)F(y). On the open set V the within-derivative is the derivative, so areaJacobianWithin σ V v = J_k(Dσ(v)). The comparator-accepted DAG lemma lpf_raf_chart_change_of_variables is the same statement for antilipschitz charts.
- (CV) Change of variables in ℝⁿ (Mathlib `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`). If S ⊆ ℝⁿ is Borel and χ : ℝⁿ → ℝⁿ is injective on S with derivative Dχ(y) (within S) at every y ∈ S, then ∫_{χ(S)} F dLⁿ = ∫_S |det Dχ(y)| F(χ(y)) dy for every F ≥ 0.
- (TO) Coordinates and Tonelli. For y ∈ ℝⁿ write y = [t, v] with t := y_0 ∈ ℝ and v := (y_1, …, y_m) ∈ ℝ^m. The map y ↦ (t, v) is a linear isometry ℝⁿ → ℝ × ℝ^m for the Euclidean product norm. It is also a volume-preserving measurable equivalence onto L¹ ⊗ L^m: compose `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp` / `PiLp.volume_preserving_ofLp` (ℝⁿ ≅ (Fin n → ℝ)) with `MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => volume) 0` ((Fin (m+1) → ℝ) ≅ ℝ × (Fin m → ℝ)) and `PiLp.volume_preserving_toLp` back to ℝ^m. Alternatively, SimonGMT `Poincare.SimonGMT.Chapter02.coarea_projection_lintegral` / `WithLp.volume_preserving_toLp` performs Fubini through WithLp 2 (ℝ × ℝ^m). For S ⊆ ℝⁿ put S_t := {v : [t, v] ∈ S}. For Borel F ≥ 0 on ℝⁿ: ∫F dLⁿ = ∫_ℝ ∫_{ℝ^m} F([t, v]) dv dt, and t ↦ ∫F([t, v]) dv is Borel (`lintegral_prod`, `Measurable.lintegral_prod_right'`).
- glue: the sibling gluing lemma (slicing_im_coarea_glue).

1. (Chart facts.)
 - Φ is injective on Ω.
 - For w ∈ Ω and u ∈ ℝⁿ, |DΦ(w)u| ≥ c|u|: divide c|t||u| ≤ |Φ(w+tu) − Φ(w)| by |t| and let t → 0. So DΦ(w) is injective and J_n(DΦ(w)) > 0.
 - W = Φ(E), since W ⊆ Φ(Ω).
 - For w ∈ E, Dh(w) ≠ 0: write ĝ(w) = DΦ(w)u₀; then Dh(w)u₀ = ⟨ĝ(w), DΦ(w)u₀⟩ = |ĝ(w)|² > 0.
 - For S ⊆ E and t ∈ ℝ: Φ(S) ∩ f⁻¹{t} = Φ(S ∩ h⁻¹{t}), since f(Φw) = h(w) on E and Φ is injective on Ω.

2. (Straightening at a regular point.) Fix w₀ ∈ E. Let ν₀ := ∇h(w₀)/|∇h(w₀)| and choose an orthonormal basis (ν₀, b_1, …, b_m) of ℝⁿ. Let π(w) := (⟨b_1, w⟩, …, ⟨b_m, w⟩) ∈ ℝ^m; |π(u)| ≤ |u| by Bessel. Define Ψ : ℝⁿ → ℝⁿ by Ψ(w) := [h(w), π(w)].
 - Ψ is C¹ with DΨ(w)u = [Dh(w)u, π(u)].
 - DΨ(w₀) is injective, hence invertible: if Dh(w₀)u = 0 and π(u) = 0, then u = sν₀ and 0 = Dh(w₀)u = s|∇h(w₀)|, so u = 0.
 - Inverse function theorem. Ψ has the strict derivative DΨ(w₀) at w₀, a linear isomorphism, so `HasStrictFDerivAt.toOpenPartialHomeomorph` (or `ContDiffAt.toOpenPartialHomeomorph`) gives an open partial homeomorphism Ψₗ with Ψₗ = Ψ on its source and w₀ ∈ Ψₗ.source.
 - Put O := Ψₗ.source ∩ Ω ∩ {w : DΨ(w) is invertible}. This set is open: invertibility is an open condition, DΨ is continuous, and Ω is open. It contains w₀. Put O′ := Ψ(O) = Ψₗ '' O, which is open and contained in Ψₗ.target.
 - Let χ := Ψₗ.symm (a total function; its values off Ψₗ.target are irrelevant). Then χ : O′ → O is the inverse of Ψ|O. At every y ∈ O′, Ψ is C¹ at χ(y) with invertible derivative, so `OpenPartialHomeomorph.contDiffAt_symm` shows that χ is C¹ at y with Dχ(y) = DΨ(χ(y))⁻¹. Hence χ is C¹ on O′.
 - Write Ψ(w₀) = [t₀, v₀] and choose δ > 0 such that the box B′ := {[t, v] : |t − t₀| < δ, |v − v₀| < δ} has closure(B′) ⊆ O′. Let Λ := max over closure(B′) of ‖Dχ‖ < ∞, and O₁(w₀) := χ(B′), an open neighbourhood of w₀ with O₁(w₀) ⊆ O ⊆ Ω.
 - For y = [t, v] ∈ B′, Ψ(χ(y)) = y gives h(χ(y)) = t and π(χ(y)) = v.
 - Each slice B′_t is an open ball of ℝ^m (if |t − t₀| < δ) or empty; in particular it is open and convex.

3. (Slice maps.) For t ∈ ℝ define σ_t : ℝ^m → ℝ^P, σ_t(v) := Φ(χ([t, v])). For v, v′ ∈ B′_t:
 (a) |σ_t(v) − σ_t(v′)| ≥ c|χ([t,v]) − χ([t,v′])| ≥ c|π(χ([t,v])) − π(χ([t,v′]))| = c|v − v′|, using χ(B′) ⊆ Ω and |π| ≤ 1. In particular σ_t is injective on B′_t.
 (b) |σ_t(v) − σ_t(v′)| ≤ KΛ|v − v′|: χ is Λ-Lipschitz on the convex set B′ by the mean value inequality, and Φ is K-Lipschitz on Ω.
 (c) σ_t is differentiable at v with Dσ_t(v) = DΦ(χ([t,v])) ∘ Dχ([t,v]) ∘ ι, where ι(z) := [0, z] (chain rule).
 (d) For a Borel S ⊆ O₁(w₀), put S′ := Ψ(S) = χ⁻¹(S) ∩ B′ (Borel). Then σ_t(S′_t) = Φ(S ∩ h⁻¹{t}). Indeed, for w ∈ S, Ψ(w) = [h(w), π(w)] ∈ S′ and χ(Ψ(w)) = w; conversely, if [t, v] ∈ S′ then χ([t, v]) ∈ S and h(χ([t, v])) = t.

4. (Jacobian identity.) Let y = [t, v] ∈ B′ with w := χ(y) ∈ E. Put A := DΦ(w), D := Dχ(y) (invertible), a := D[1, 0] ∈ ℝⁿ, B := D∘ι : ℝ^m → ℝⁿ and ĝ := ĝ(w) ≠ 0. Claim: J_m(A∘B) = |ĝ| · J_n(A) · |det D|.
 (i) Differentiating h(χ(y)) = y_0 near y (chain rule) gives Dh(w)∘D = (z ↦ z_0), i.e. Dh(w)a = 1 and Dh(w)∘B = 0. B = D∘ι is injective, because D is invertible and ι is injective, so range B ⊆ ker Dh(w) has dimension m. Since Dh(w) ≠ 0 (step 1), dim ker Dh(w) = m, so range B = ker Dh(w). Thus step 4 is a pure linear-algebra lemma: for A : ℝⁿ → ℝ^P injective, D : ℝⁿ → ℝⁿ invertible and ĝ ∈ range A with ⟨ĝ, A(Dy)⟩ = y_0 for all y (so ĝ ≠ 0 when n ≥ 1), J_m(A∘D∘ι) = |ĝ|·J_n(A)·|det D|. It needs neither π nor the chart, and a decomposition of this node may state it as a separate child.
 (ii) T := range A has dimension n and contains ĝ. Also range(A∘B) = A(ker Dh(w)) = {Au : ⟨ĝ, Au⟩ = 0} = T ∩ ĝ^⊥, and T = (T ∩ ĝ^⊥) ⊕ ℝĝ orthogonally.
 (iii) Let e := ĝ/|ĝ| and choose an orthonormal basis (e, q_1, …, q_m) of T with q_j ∈ T ∩ ĝ^⊥. Use the orthonormal basis ([1,0], [0,e_1], …, [0,e_m]) of ℝⁿ.
 - The matrix of the bijection A∘D : ℝⁿ → T in these bases is block lower-triangular. Its first row is (⟨Aa, e⟩, 0, …, 0), because A D[0,e_j] = A B e_j ∈ T ∩ ĝ^⊥. Its lower-right m×m block is the matrix of A∘B : ℝ^m → T ∩ ĝ^⊥ in orthonormal bases.
 - Hence J_n(A∘D) = |⟨Aa, e⟩| · J_m(A∘B). (normDet is the absolute determinant in orthonormal bases of the domain and of any subspace containing the range: `normDet_codRestrict`, `normDet_eq_abs_det`, `LinearIsometry.normDet_eq_one`, `normDet_comp_of_finrank_eq`.)
 - Moreover ⟨Aa, e⟩ = ⟨ĝ, Aa⟩/|ĝ| = Dh(w)a/|ĝ| = 1/|ĝ|.
 (iv) J_n(A∘D) = J_n(A)·|det D|, because D : ℝⁿ → ℝⁿ (`normDet_comp_of_finrank_eq`, `normDet_eq_abs_det`).
 Combining (iii) and (iv) gives the claim. By 3(c), this reads J_m(Dσ_t(v)) = |G(Φ(χ(y)))| · J_n(DΦ(χ(y))) · |det Dχ(y)|. For m = 0 everything degenerates consistently: J_0 = 1 and |ĝ| J_1(A) |det D| = |Dh(w)a| = 1.

5. (Co-area identity on a box.) Let S ⊆ E ∩ O₁(w₀) be Borel, S′ := Ψ(S) ⊆ B′, and g ≥ 0 Borel. Then:
 ∫_{Φ(S)} |G| g dHⁿ
 = ∫_S |G(Φw)| g(Φw) J_n(DΦ(w)) dw — (AF) for Φ on the open set Ω (Lipschitz and injective there), F := |G|·g Borel;
 = ∫_{S′} |G(Φχ(y))| g(Φχ(y)) J_n(DΦ(χ(y))) |det Dχ(y)| dy — (CV) for χ on S′, with χ(S′) = S, χ injective and differentiable on B′;
 = ∫_{S′} g(σ_{y_0}(y_1..y_m)) J_m(Dσ_{y_0}(y_1..y_m)) dy — step 4, as χ(S′) ⊆ E;
 = ∫_ℝ ∫_{S′_t} g(σ_t(v)) J_m(Dσ_t(v)) dv dt — (TO). The integrand y ↦ 1_{S′}(y) g(Φ(χ(y))) J_m(DΦ(χ(y))∘Dχ(y)∘ι) is Borel, since χ, Dχ and DΦ are continuous on B′;
 = ∫_ℝ ∫_{σ_t(S′_t)} g dH^m dt — (AF) for σ_t on the open set B′_t, where it is Lipschitz and injective by 3(a),(b), with S′_t ⊆ B′_t Borel;
 = ∫_ℝ ∫_{Φ(S) ∩ f⁻¹{t}} g dH^m dt — by 3(d) and step 1.
 For every t, ∫_{Φ(S) ∩ f⁻¹{t}} g dH^m = ∫_{S′_t} g(σ_t(v)) J_m(Dσ_t(v)) dv; both sides vanish when S′_t = ∅. The right side is Borel in t by (TO). So t ↦ ∫_{Φ(S) ∩ f⁻¹{t}} g dH^m is measurable.

6. (Cover and glue.) If E = ∅ then W = ∅ and both sides vanish. Otherwise every w₀ ∈ E has the open neighbourhood O₁(w₀) of step 2. ℝⁿ is second countable, so countably many O₁(w_k), k ∈ ℕ, cover E (Lindelöf, `TopologicalSpace.isOpen_iUnion_countable`).
 - Put D_k := (E ∩ O₁(w_k)) ∖ ⋃_{l<k} O₁(w_l). These are Borel, pairwise disjoint, and ⋃_k D_k = E.
 - Put W_k := Φ(D_k). These are Borel (Lusin–Souslin), pairwise disjoint (Φ injective on Ω), contained in W, and ⋃_k W_k = Φ(E) = W.
 - By step 5 with S := D_k ⊆ E ∩ O₁(w_k), each t ↦ ∫_{W_k ∩ f⁻¹{t}} g dH^m is measurable, and ∫_ℝ ∫_{W_k ∩ f⁻¹{t}} g dH^m dt = ∫_{W_k} |G| g dHⁿ.
 Apply glue with X := ℝ^P, μ := Hⁿ, ν := H^m, the measurable f, J := |G(·)| (as ‖G x‖ₑ), g, M := W and the pieces W_k. Since W ∖ ⋃_k W_k = ∅, both remainder hypotheses hold trivially. Its conclusion is exactly the claim: t ↦ ∫_{W ∩ f⁻¹{t}} g dH^m is a.e.-measurable and ∫_ℝ ∫_{W ∩ f⁻¹{t}} g dH^m dt = ∫_W ‖G x‖ₑ g(x) dHⁿ. ∎

## Key steps

1. On E := Ω ∩ Φ⁻¹(W): Dh ≠ 0, DΦ injective, and Φ(S) ∩ f⁻¹{t} = Φ(S ∩ h⁻¹{t}).
2. Inverse function theorem for Ψ(w) := [h(w), π(w)] at each w₀ ∈ E: a C¹ inverse χ on a box B′ with h∘χ = t, π∘χ = v; the slice maps σ_t := Φ∘χ([t,·]) are Lipschitz and c-antilipschitz on the ball slices B′_t.
3. Jacobian identity, pure linear algebra: for A injective, D invertible and ĝ ∈ range A with ⟨ĝ, A(Dy)⟩ = y₀, J_m(A∘D∘ι) = |ĝ|·J_n(A)·|det D| (range A∘D∘ι = range A ∩ ĝ^⊥; block-triangular determinant).
4. On each box: area formula for Φ, change of variables for χ, the Jacobian identity, Tonelli, and the area formula for σ_t give the co-area identity with a measurable slice function.
5. Lindelöf: countably many boxes cover E; disjointify, push forward by Φ, and apply glue.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean (byte-identical); read Contract.lean (IsRectifiableTriple, Eucl, scope commands)`
- `grep -rn 'slicing_im_coarea_' local-references/197bdd4b88278494/project (no match)`
- `python3 scan of dag.json: statuses and lean_statement of all lipschitz_pushforward nodes; byte comparison of candidate child types with lpf_c1_approximation_real, lpf_countably_rectifiable_c1_cover, lpf_weighted_tangent_on_c1_chart (identical, all speculative-ready) and lpf_ccr_hasDerivAt_line_of_comp (accepted 18:04Z, Eucl Q-valued); collision check of the nine names against all 369 DAG lean_name values (none)`
- `read nodes/root-lipschitz-pushforward-im-a1-{countably-rectifiable-c1-cover-a1,weighted-tangent-on-c1-chart-a1,lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1,chart-chain-rule-a1-line-deriv-comp-a1}/parent-supplied-natural-proof.md and nodes/root-slicing-a1-slice-integer-multiplicity-a1/{parent-supplied-natural-proof.md,decomposition-v1.json}`
- `grep -n '^theorem|^def' SimonGMT Chapter03/{Rectifiable,Differential,DisjointCover,SubmanifoldCover}.lean and Chapter02/{AreaLipschitz,AreaDomain,AreaCritical,Area,Lipschitz,CoareaLinear,CoareaProjection,WhitneyExtension}.lean`
- `grep for SimonGMT names weighted_area_formula_lipschitzOn_fiberSum, weighted_area_formula_lipschitz_injOn, injective_area_formula_lipschitzOn, area_image_criticalSet_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn, exists_contDiff_one_extension_of_whitney, exists_isClosed_continuousOn_of_measurable, simon_theorem_3_6, coarea_projection_lintegral (all present)`
- `grep in pinned Mathlib for hausdorffMeasure_apply, hausdorffMeasure_le_liminf_tsum, euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, normDet_comp_of_finrank_eq, normDet_eq_abs_det, normDet_codRestrict, lintegral_image_eq_lintegral_abs_det_fderiv_mul, OpenPartialHomeomorph.contDiffAt_symm, measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, Measurable.lintegral_prod_right', MeasurableSet.image_of_continuousOn_injOn, NullMeasurableSet.exists_measurable_subset_ae_eq, Measure.restrict_apply₀', restrict_congr_set, lintegral_iUnion, lintegral_tsum, lintegral_inter_add_sdiff, LipschitzOnWith.extend_real, isOpen_iUnion_countable (all present)`
- `sed book/chapter-02.txt §6 (6.1–6.7) and book/chapter-03.txt §1–2 (1.1–1.9, 2.1–2.10)`
- `lake build GMT.Ch06.Submission in scratch /tmp/coarea-decomp-47PgtZ/proj (frozen d8d46c9 contract, shared lake-packages-25730c7c)`
- `lake env lean Scratch/Stmts.lean and Scratch/FinalCheck.lean (nine child types and the parent type in the exact comparator scope; 0 errors)`
- `lake env lean Scratch/Assembly.lean (parent type from eilenberg, glue, pieces, chart_critical, chart_regular; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/Pieces.lean (pieces from c1_approx, chart_cover, chart_tangent, line_deriv; standard axioms) and Scratch/GradId.lean`
- `lake env lean Scratch/Glue.lean (glue proved outright; standard axioms); lake env lean Scratch/Review_C1.lean (c1_approx from the accepted lpf_c1r_lusin_closed, lpf_c1r_uniform_remainder, lpf_c1r_whitney_extension types; standard axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-line-deriv-comp-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Stmts.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/FinalCheck.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Assembly.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Pieces.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Glue.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/GradId.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Review_C1.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract. Submission is byte-identical to it, and no `slicing_im_coarea_*` name exists in the project or in the 369 DAG nodes. SimonGMT supplies the needed area-formula library: weighted_area_formula_lipschitzOn_fiberSum, injective_area_formula_lipschitzOn, area_image_criticalSet_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn, a Whitney extension (source only, no .olean), Lusin, the upper density theorem, the linear co-area formula and HasWeightedApproximateTangentSpaceAt with uniqueness. It has no nonlinear co-area formula and no Eilenberg inequality. Mathlib supplies the Hausdorff measure covering lemmas, the μHE normalization, normDet, the inverse function theorem, change of variables, Fubini/Tonelli and Lusin–Souslin. The lipschitz-pushforward branch has speculative-ready nodes byte-identical to three proposed children (c1_approx, chart_cover, chart_tangent); because they are not accepted, they get new names here, and their accepted sub-lemmas (lpf_c1r_*, lpf_wtc_*, lpf_c1_local_antilipschitz, lpf_raf_chart_change_of_variables) are cited for reuse at the next level. lpf_ccr_hasDerivAt_line_of_comp was accepted during this session and is cited as an alternative route for line_deriv. Lean checks in the exact comparator scope: all nine child types elaborate; the parent type follows from five children; pieces follows from four; glue is proved outright; c1_approx follows from three accepted types. All of these use only propext, Classical.choice and Quot.sound. These checks do not certify the remaining analytic proofs.
