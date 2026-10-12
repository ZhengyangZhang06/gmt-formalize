# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the parent proof (the product triple Π = τ((0,1) × M, θ∘π_2, e₀ ∧ ξ∘π_2), Simon 3.2(2)), with the product formula of Step 1 in the measure form (MP), and with the weighted tangent condition (parent Step 3) supplied by the sibling product_tangent (iwl_cr_ip_product_weighted_tangent).

Notation. E := ℝ^P = Eucl P, E′ := ℝ^{P+1} = Eucl (P+1), Hᵏ := μHE[k], L¹ := Lebesgue measure on ℝ. Φ(s, x) := (s, x_1, …, x_P) (Lean: (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))); π(y) := (y_1, …, y_P) (Lean: (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P+1)) ℝ y))); y₀ := (EuclideanSpace.equiv (Fin (P+1)) ℝ y) 0; Φ′ : ℝ × E → E′, Φ′(p) := Φ(p.1, p.2); e₀ := EuclideanSpace.single 0 1 = Φ(1, 0); ι(v) := Φ(0, v); M̃ := {y ∈ E′ : π(y) ∈ M ∧ y₀ ∈ (0,1)}; θ̃ := θ ∘ π (Lean: fun y => θ (π y)); O := {y ∈ E′ : y₀ ∈ (0,1)} (open), so M̃ = O ∩ {π ∈ M}. (MP) denotes the hypothesis: for every A ⊆ E that is Hᵐ-null-measurable, countably m-rectifiable and has Hᵐ(A ∩ K) < ∞ for every compact K, H^{m+1}⌞{y : π(y) ∈ A} = Φ′_*(L¹ ⊗ Hᵐ⌞A).
Coordinate facts (all by Fin.cons/Fin.tail computations, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons, Fin.cons_zero, Fin.cons_self_tail): (F1) π(Φ(s,u)) = u, (Φ(s,u))₀ = s and Φ(y₀, π(y)) = y; (F2) Φ is linear: Φ(s,u) − Φ(s′,u′) = Φ(s − s′, u − u′), Φ(s,u) + Φ(s′,u′) = Φ(s + s′, u + u′), c·Φ(s,u) = Φ(cs, cu); in particular ι is linear and π is linear; (F3) ⟨Φ(a,u), Φ(b,w)⟩ = ab + ⟨u,w⟩ (sum over Fin (P+1) split by Fin.sum_univ_succ), hence ‖Φ(s,u)‖² = s² + ‖u‖², |s| ≤ ‖Φ(s,u)‖ and ‖u‖ ≤ ‖Φ(s,u)‖; (F4) Φ′ is a homeomorphism ℝ × E → E′ with continuous inverse y ↦ (y₀, π(y)) (Continuous.finCons, continuous_pi), hence a measurable embedding (Homeomorph.measurableEmbedding); in particular Φ′ and π are Borel measurable.
Derived facts from (MP) used below. (D1) (null sets) If N ⊆ E and Hᵐ(N) = 0 then H^{m+1}({y : π(y) ∈ N}) = 0: N is Hᵐ-null-measurable (NullMeasurableSet.of_null), countably m-rectifiable (countablyRectifiable_of_measure_zero) and Hᵐ(N ∩ K) ≤ Hᵐ(N) = 0 < ∞, so by (MP) H^{m+1}⌞{π ∈ N} = Φ′_*(L¹ ⊗ Hᵐ⌞N) = Φ′_*(L¹ ⊗ 0) = 0 (Hᵐ⌞N = 0 as Hᵐ(N) = 0; Measure.prod_zero, Measure.map_zero), and H^{m+1}({π ∈ N}) = (H^{m+1}⌞{π ∈ N})({π ∈ N}) = 0. (D2) (product sets) If A satisfies the hypotheses of (MP), then ν_A := Hᵐ⌞A is finite on compact sets (ν_A(K) = Hᵐ(K ∩ A), Measure.restrict_apply), hence σ-finite (instance SigmaFinite.of_isFiniteMeasureOnCompacts), and H^{m+1}⌞{y : π(y) ∈ A ∧ y₀ ∈ (0,1)} = Φ′_*((L¹⌞(0,1)) ⊗ ν_A). Proof: {π ∈ A ∧ y₀ ∈ (0,1)} = O ∩ {π ∈ A} and O is Borel, so H^{m+1}⌞(O ∩ {π ∈ A}) = (H^{m+1}⌞{π ∈ A})⌞O (Measure.restrict_restrict) = (Φ′_*(L¹ ⊗ ν_A))⌞O (MP) = Φ′_*((L¹ ⊗ ν_A)⌞Φ′⁻¹(O)) (Measure.restrict_map, Φ′ measurable) and Φ′⁻¹(O) = (0,1) × E by (F1), so (L¹ ⊗ ν_A)⌞((0,1) × E) = (L¹⌞(0,1)) ⊗ (ν_A⌞E) = (L¹⌞(0,1)) ⊗ ν_A (Measure.prod_restrict, Measure.restrict_univ).

1. (Local finiteness.) Let K ⊆ ℝ^P be compact. θ is integrable on M ∩ K (field integrableOn, K ⊆ univ) and θ ≥ 1 on M; M ∩ K is null-measurable, so 1 ≤ |θ| holds Hᵐ⌞(M ∩ K)-a.e. (ae_restrict_mem₀) and Hᵐ(M ∩ K) = ∫⁻_{M∩K} 1 dHᵐ ≤ ∫⁻_{M∩K} |θ| dHᵐ < ∞ (lintegral_mono_ae; finiteness of the integral of an integrable function). Hence ν := Hᵐ⌞M is finite on compacts and σ-finite, and M satisfies the hypotheses of (MP) (null-measurable and countably m-rectifiable by the triple). For every Hᵐ-null-measurable A ⊆ M the same holds (CountablyRectifiable.mono; Hᵐ(A ∩ K) ≤ Hᵐ(M ∩ K)), so (D2) applies to A. In particular H^{m+1}⌞M̃ = Φ′_*ρ with ρ := (L¹⌞(0,1)) ⊗ ν.
2. (The contraction ℒ and the orientation ξ′.) ι : E → E′ is linear by (F2), hence a continuous linear map (finite dimension; LinearMap.toContinuousLinearMap). Let ℒ := compContinuousLinearMapCLM ι ∘L (evaluation at e₀) ∘L curryLeftLI : Λ^{m+1}(E′) →L Λ^m(E). By curryLeft_apply_apply, ℒ(α)(v) = α.curryLeft(e₀)(ι ∘ v) = α(Matrix.vecCons e₀ (ι ∘ v)) = α(Fin.cons e₀ (ι ∘ v)) = α(e₀, ιv_1, …, ιv_m) (this holds by rfl). Define ξ′(y) := ξ(π(y)) ∘L ℒ ∈ NVector E′ (m+1), so ξ′(y)(α) = ξ(π(y))(ℒα).
3. (Characterization.) Let s, x, α, β with β(v) = α(e₀, ιv_1, …, ιv_m) for all v. Then ℒα = β (ext, Step 2) and π(Φ(s, x)) = x (F1), so ξ′(Φ(s, x))(α) = ξ(x)(ℒα) = ξ(x)(β). This is the second conjunct. It remains to verify the seven fields of IsRectifiableTriple univ (m+1) M̃ θ̃ ξ′.
4. (subset) M̃ ⊆ univ.
5. (nullMeasurableSet) M is Hᵐ-null-measurable, so there is a Borel M_B with M =ᵐ M_B, i.e. N := M Δ M_B has Hᵐ(N) = 0. The set where y ∈ {π ∈ M} and y ∈ {π ∈ M_B} disagree is {π ∈ N}, which is H^{m+1}-null by (D1); so {π ∈ M} =ᵐ {π ∈ M_B}, and {π ∈ M_B} is Borel (π continuous). Hence {π ∈ M} is H^{m+1}-null-measurable (NullMeasurableSet.congr), and so is M̃ = O ∩ {π ∈ M} (O open).
6. (countablyRectifiable) By the triple, M ⊆ M₀ ∪ ⋃_j range F_j with Hᵐ(M₀) = 0 and F_j : Eucl m → E K_j-Lipschitz. For u ∈ Eucl (m+1) write u₀ := (equiv u) 0 and tail u := equiv⁻¹(Fin.tail (equiv u)) ∈ Eucl m, so ‖u‖² = u₀² + ‖tail u‖² (Fin.sum_univ_succ). Define G_j(u) := Φ(u₀, F_j(tail u)). By (F3), ‖G_j u − G_j u′‖² = |u₀ − u′₀|² + ‖F_j(tail u) − F_j(tail u′)‖² ≤ |u₀ − u′₀|² + K_j²‖tail u − tail u′‖² ≤ max(1, K_j)² ‖u − u′‖², so G_j is max(1, K_j)-Lipschitz. M̃₀ := {π ∈ M₀} has H^{m+1}(M̃₀) = 0 by (D1). If y ∈ M̃ then either π(y) ∈ M₀, i.e. y ∈ M̃₀, or π(y) = F_j(w) for some j, w, and then u := equiv⁻¹(Fin.cons y₀ (equiv w)) has u₀ = y₀, tail u = w, so G_j(u) = Φ(y₀, π(y)) = y by (F1). Hence M̃ ⊆ M̃₀ ∪ ⋃_j range G_j.
7. (pos) If y ∈ M̃ then π(y) ∈ M and θ̃(y) = θ(π(y)) > 0 (field pos).
8. (integrableOn) Let K′ ⊆ E′ be compact and K := π(K′), compact (π continuous). Then M̃ ∩ K′ ⊆ M̃_K := {y : π(y) ∈ M ∩ K ∧ y₀ ∈ (0,1)}. M ∩ K is null-measurable and ⊆ M, so by Step 1 and (D2), H^{m+1}⌞M̃_K = Φ′_*((L¹⌞(0,1)) ⊗ Hᵐ⌞(M ∩ K)). By MeasurableEmbedding.integrable_map_iff (F4), θ̃ is integrable for this measure iff θ̃∘Φ′ is integrable for (L¹⌞(0,1)) ⊗ Hᵐ⌞(M ∩ K); and θ̃(Φ′(s, u)) = θ(u) by (F1), which is integrable there because θ is integrable on M ∩ K and L¹⌞(0,1) is a finite measure (Integrable.comp_snd). So θ̃ is integrable on M̃_K, hence on M̃ ∩ K′ (IntegrableOn.mono_set).
9. (aestronglyMeasurable) By Step 1, H^{m+1}⌞M̃ = Φ′_*ρ. By MeasurableEmbedding.aestronglyMeasurable_map_iff (F4) it suffices that ξ′∘Φ′ is a.e. strongly measurable for ρ. Now ξ′(Φ′(s, u)) = ξ(u) ∘L ℒ = C(ξ(u)) by (F1), where C : NVector E m → NVector E′ (m+1), C(T) := T ∘L ℒ, is a continuous linear map. ξ is a.e. strongly measurable for ν (field aestronglyMeasurable), hence (s, u) ↦ ξ(u) is a.e. strongly measurable for ρ (AEStronglyMeasurable.comp_snd, ν s-finite), and so is its composition with the continuous map C (Continuous.comp_aestronglyMeasurable).
10. (orients) (a) Call x ∈ E good if there is an orthonormal τ : Fin m → E with HasWeightedApproximateTangentSpaceAt m M θ x (span τ) and ξ(x) = ±simpleNVector τ. By the field orients, Hᵐ⌞M-a.e. x is good; as M is null-measurable, N := M ∩ {x : x not good} satisfies Hᵐ(N) = 0 (Measure.restrict_apply₀'), so H^{m+1}({π ∈ N}) = 0 by (D1). (b) Claim: every y ∈ M̃ with π(y) ∉ N satisfies the orientation property at y. Granting this, {y : property fails} ∩ M̃ ⊆ {π ∈ N}, so (H^{m+1}⌞M̃)({property fails}) = H^{m+1}({property fails} ∩ M̃) = 0 (Measure.restrict_apply₀', M̃ null-measurable by Step 5; measure_mono_null), i.e. the property holds H^{m+1}⌞M̃-a.e. (c) Proof of the claim. Let x := π(y) ∈ M ∖ N, so x is good: τ orthonormal, span τ a weighted tangent space of (M, θ) at x, ξ(x) = ±simpleNVector τ. Let s₀ := y₀ ∈ (0, 1); then y = Φ(s₀, x) by (F1). Put τ̃ := (e₀, ιτ_1, …, ιτ_m) (Lean: Fin.cons e₀ (fun i => Φ 0 (τ i))). (i) τ̃ is orthonormal: by (F3), ‖e₀‖ = 1, ‖ιτ_i‖ = ‖τ_i‖ = 1, ⟨e₀, ιτ_i⟩ = 0 and ⟨ιτ_i, ιτ_j⟩ = ⟨τ_i, τ_j⟩ = 0 for i ≠ j. (ii) The sibling product_tangent applies to (MP), M, θ, x, τ, s₀: M is null-measurable and countably m-rectifiable (triple), Hᵐ(M ∩ K) < ∞ (Step 1), θ ≥ 0 on M (field pos), θ is integrable on M ∩ K for every compact K (field integrableOn), τ is orthonormal, span τ is a weighted tangent space at x, and s₀ ∈ (0, 1). It gives HasWeightedApproximateTangentSpaceAt (m+1) M̃ θ̃ (Φ(s₀, x)) (span τ̃), and Φ(s₀, x) = y. (iii) If ξ(x) = simpleNVector τ then for every α, ξ′(y)(α) = ξ(x)(ℒα) = (ℒα)(τ_1, …, τ_m) = α(e₀, ιτ_1, …, ιτ_m) = simpleNVector τ̃ (α), so ξ′(y) = simpleNVector τ̃ (ext); if ξ(x) = −simpleNVector τ, the same computation gives ξ′(y) = −simpleNVector τ̃. Thus (i)–(iii) give the orientation property at y with the frame τ̃. ∎

Formalization aid (kernel-checked in the contract scope after import GMT.Ch06.Submission at the frozen commit; uses no helper declarations): construction of ℒ with its defining property, as a tactic fragment usable inside the proof (here P m : ℕ are in context).

obtain ⟨L, hL⟩ : ∃ L : Covector (Eucl (P + 1)) (m + 1) →L[ℝ] Covector (Eucl P) m,
    ∀ (α : Covector (Eucl (P + 1)) (m + 1)) (v : Fin m → Eucl P),
      L α v = α (Fin.cons (EuclideanSpace.single 0 1) fun i =>
        (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) := by
  let ι : Eucl P →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun v => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ v))
      map_add' := by
        intro v w
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := by
        intro c v
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply]
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  exact ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM ι).comp
    ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single 0 1 : Eucl (P + 1))).comp
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl (P + 1)) (F := ℝ)
        (n := m)).toContinuousLinearMap), fun α v => rfl⟩

## Key steps

1. θ ≥ 1 and local integrability give Hᵐ(M ∩ K) < ∞, so (MP) applies to M and its null-measurable subsets; (D2) gives H^{m+1}⌞M̃ = Φ′_*((L¹⌞(0,1)) ⊗ Hᵐ⌞M) and (D1) transfers null sets.
2. ℒ(α)(v) = α(e₀, ιv) via curryLeft and compContinuousLinearMap; ξ′(y) := ξ(π y) ∘L ℒ satisfies the stated characterization.
3. Null-measurability, countable (m+1)-rectifiability (Lipschitz G_j(u) = Φ(u₀, F_j(tail u)) plus a null set), positivity and local integrability (product measure, Integrable.comp_snd).
4. a.e. strong measurability of ξ′ via the measure identity and MeasurableEmbedding.aestronglyMeasurable_map_iff.
5. Orientation: off the null set {π ∈ N}, τ̃ = (e₀, ιτ) is orthonormal, product_tangent gives the weighted tangent plane span τ̃ at y = Φ(y₀, π y), and ξ′(y) = ±simpleNVector τ̃.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3 -I: dag.json lean_name/status of all root.integrality_weak_limits-a1* nodes and of all accepted nodes; lean_statement of iwl_cr_hausdorff_product_formula, iwl_cr_interval_product_im, iwl_cycle_reduction, br_loc_tauAction_current, ltg_tau_integrable, fiw_tl_blowup_setIntegral, fiw_tl_growth_bound, br_weightedTangent_congr, iwl_weighted_tangent_locality, fiw_im_mass_formula, lpf_pic_current_of_dominated_density, lpf_wtc_blowup_setIntegral_image, polyhedral_approx_rt_tau_integrableOn, isoperimetric_abs_covector_apply_le, lpf_simple_nvector_algebra`
- `grep -rl iwl_cr_ip .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca (no match); grep -rho 'iwl_cr_[a-z_]*' dag.json`
- `python3 -I: nodes/{root-boundary-rectifiability-a1-localization-a1-tau-current-a1, root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1, root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1}/accepted-candidate.json: contract lean_statement == dag.json lean_statement, audit.comparator_passed`
- `rg -n 'def curryLeft|curryLeftLI|theorem curryLeft_apply_apply|def compContinuousLinearMapCLM' mathlib/Mathlib/Analysis/Normed/Module/Alternating/ mathlib/Mathlib/Topology/Algebra/Module/Alternating/`
- `rg -n 'μHE|euclideanHausdorffMeasure_eq_volume|Isometry.euclideanHausdorffMeasure_image|Isometry.map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_homothety_image|euclideanHausdorffMeasure_smul' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n in mathlib/Mathlib (snapshot) for MeasurableEmbedding.integral_map, MeasurableEmbedding.integrable_map_iff, MeasurableEmbedding.aestronglyMeasurable_map_iff, restrict_map, prod_restrict, restrict_restrict, prod_apply, integral_prod, Integrable.comp_snd, Integrable.mul_prod, AEStronglyMeasurable.comp_snd, integral_comp_mul_add, integral_Ioc_eq_integral_Ioo, integral_of_le, tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, norm_integral_le_of_norm_le, finrank_span_eq_card, restrict_apply₀', ae_restrict_mem₀, lintegral_indicator_one, setIntegral_congr_fun, SigmaFinite.of_isFiniteMeasureOnCompacts, Continuous.finCons, Homeomorph.measurableEmbedding, aestronglyMeasurable_iUnion_iff, NullMeasurableSet.congr, IntegrableOn.mono_set, IntegrableOn.of_ae_sdiff_eq_zero, Integrable.bdd_mul, norm_iteratedFDeriv_zero`
- `grep -n '^theorem|^def|^structure|^abbrev' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean and simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,FormsDuality,Product}.lean`
- `python3 -I /tmp/ipdec/scripts/gen.py and /tmp/ipdec/scripts/build.py (lean_contract.validate_lean_statement on the 7 child types, the parent type and the sibling type; comparator challenge layout of gmt-compare.py child_modules)`
- `lake env lean /tmp/ipdec/Check.lean (7 comparator-layout challenge targets; parent assembly from child and sibling stubs; #print axioms)`
- `lake env lean /tmp/ipdec/Appendix2.lean (complete proofs of iwl_cr_ip_restrict_preimage_eq_map and iwl_cr_ip_slice_formula; contraction snippet; #print axioms)`
- `lake env lean /tmp/ipdec/Sanity3.lean (construction of the contraction map; product_tangent conclusion feeds product_triple orients)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1-tau-current-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1-tau-current-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ipdec/scripts/gen.py`
- `/tmp/ipdec/scripts/build.py`
- `/tmp/ipdec/Check.lean`
- `/tmp/ipdec/Appendix2.lean`
- `/tmp/ipdec/Sanity3.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The snapshot's GMT/Ch06/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

DAG and naming:
- The DAG contains no product current and no Hausdorff product formula except the sibling iwl_cr_hausdorff_product_formula (decomposing). It is used only by the parent, through hMP.
- Reusable accepted declarations, each with identical frozen types and comparator_passed: br_loc_tauAction_current (τ is a current), ltg_tau_integrable, and fiw_tl_blowup_setIntegral. lpf_wtc_blowup_setIntegral_image is an alpha-equivalent duplicate; fiw_tl_growth_bound and br_weightedTangent_congr are not needed.
- The names iwl_cr_ip_* are unreserved: no match in dag.json, in any decomposition file, or in the run directory.

SimonGMT:
- Chapter06/Product.lean has only point products (pointProduct, pointSliceTest), no interval product. No match for a Hausdorff product formula there or in Mathlib, where only hausdorffMeasure_pi_real exists.
- Chapter03/Rectifiable.lean supplies blowUpMap, HasWeightedApproximateTangentSpaceAt, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, countablyRectifiable_range and regular_euclideanHausdorffMeasure_restrict_submodule.

Mathlib supplies every tool cited in the child proofs:
- ContinuousAlternatingMap.curryLeft, curryLeftLI and curryLeft_apply_apply (Analysis/Normed/Module/Alternating/Curry.lean), and compContinuousLinearMapCLM;
- μHE lemmas: Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume;
- MeasurableEmbedding.integral_map, MeasurableEmbedding.integrable_map_iff and MeasurableEmbedding.aestronglyMeasurable_map_iff, Homeomorph.measurableEmbedding;
- Measure.restrict_map, Measure.prod_restrict, Measure.restrict_restrict, Measure.prod_apply, Measure.restrict_apply₀', ae_restrict_mem₀, SigmaFinite.of_isFiniteMeasureOnCompacts;
- integral_prod, Integrable.comp_snd, Integrable.mul_prod, AEStronglyMeasurable.comp_snd, aestronglyMeasurable_iUnion_iff;
- intervalIntegral.integral_comp_mul_add, intervalIntegral.integral_of_le, integral_Ioc_eq_integral_Ioo;
- tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, norm_integral_le_of_norm_le;
- finrank_span_eq_card, NullMeasurableSet.congr, IntegrableOn.mono_set, Continuous.finCons.

Lean checks:
- Comparator-layout elaboration of all 7 child types.
- The parent assembly.
- Complete proofs of measure_identity and slice_formula (axioms: propext, Classical.choice, Quot.sound).
- The ℒ construction and the product_tangent→product_triple interface.

Public citation for the product formula: Federer, Geometric Measure Theory (1969) 3.2.23. The product current and its integer multiplicity: Simon, Introduction to GMT, Ch. 6, 3.2(2).
