# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.product_exists-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5 and 6 of the parent-supplied proof (definition of [[0,1]]×X(η) := ∫_0^1 X(φ^η_s) ds, its linearity, the bound M(Z) ≤ M(X), the characterization ProdChar and uniqueness; the support inclusion spt Z ⊆ cyl(spt X)). Siblings used: slice_forms (iwl_cr_ci_slice_testForm), vanish_off_support (isoperimetric_apply_eq_zero_of_disjoint_support), current_criterion (dph_iprod_current_of_bound) and slice_continuity (dph_iprod_slice_continuity, conjunct (D1)).

Notation. ℝ^p = Eucl p; cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1} for s ∈ ℝ, x ∈ ℝ^m; ι(v) := cons(0, v) = (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; ι∘v := (fun i => ι (v i)) and (e₀, ι∘v) := Fin.cons e₀ (fun i => ι (v i)) for tuples v; for a q-covector γ on ℝ^p (γ : Covector (Eucl p) q), |γ| := covectorEuclideanNorm γ = (Σ_{I : Fin q → Fin p strictly increasing} γ(b_{I 0}, …, b_{I (q−1)})²)^{1/2} with b_i := EuclideanSpace.basisFun (Fin p) ℝ i, and ‖γ‖ is its operator norm; D^q(ℝ^p) := TestFormOn univ q, D_q(ℝ^p) := GeometricCurrentOn univ q, M := mass; for a test form ω, ω(x) denotes (ω : DifferentialForm (Eucl p) q) x; t(y) := EuclideanSpace.equiv (Fin (m+1)) ℝ y 0, tl(y) := (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m+1)) ℝ y)) and cyl(A) := {y : t(y) ∈ [0,1], tl(y) ∈ A}; spt := support; a family φ : ℝ → D^k(ℝ^m) is a dt-slice family of η ∈ D^{k+1}(ℝ^{m+1}) on [0,1] if φ(s)(x)(v) = η(cons(s,x))(e₀, ι∘v) for all s ∈ [0,1], x, v; ProdChar(X, Z) (X ∈ D_k(ℝ^m), Z ∈ D_{k+1}(ℝ^{m+1})) means Z(η) = ∫_0^1 X(φ(s)) ds for every η ∈ D^{k+1}(ℝ^{m+1}) and every dt-slice family φ of η on [0,1].

Let m, k and X ∈ D_k(ℝ^m) with M(X) < ∞; B := M(X).toReal ≥ 0.
1. (Chosen slice families.) For every η ∈ D^{k+1}(ℝ^{m+1}), slice_forms (with P := m, m := k) provides φ^η : ℝ → D^k(ℝ^m) with φ^η(s)(x)(v) = η(cons(s,x))(e₀, ι∘v) for all s, x, v. Fix such a choice for every η (the `choose` tactic). In particular φ^η is a dt-slice family of η on [0,1].
2. (Independence of the slice family.) If φ is any dt-slice family of η on [0,1], then φ(s) = φ^η(s) for every s ∈ [0,1] (Subtype.ext, funext x, ContinuousAlternatingMap.ext v: both sides equal η(cons(s,x))(e₀, ι∘v)). Hence ∫_0^1 X(φ(s)) ds = ∫_0^1 X(φ^η(s)) ds by intervalIntegral.integral_congr (uIcc 0 1 = Icc 0 1, Set.uIcc_of_le).
3. (Integrability.) By (D1) of slice_continuity, s ↦ X(φ^η(s)) is continuous on [0,1], hence interval integrable on [0,1] (ContinuousOn.intervalIntegrable_of_Icc).
4. (Linearity.) Put Z₀(η) := ∫_0^1 X(φ^η(s)) ds. For η, η′ ∈ D^{k+1}(ℝ^{m+1}) the family s ↦ φ^η(s) + φ^{η′}(s) is a dt-slice family of η + η′ (evaluation of forms and covectors is pointwise additive: Pi.add_apply, ContinuousAlternatingMap.add_apply). By step 2, linearity of X (map_add) and intervalIntegral.integral_add (with step 3), Z₀(η + η′) = ∫_0^1 (X(φ^η(s)) + X(φ^{η′}(s))) ds = Z₀(η) + Z₀(η′). For a ∈ ℝ, s ↦ a·φ^η(s) is a dt-slice family of a·η (Pi.smul_apply, ContinuousAlternatingMap.smul_apply), so Z₀(a·η) = ∫_0^1 a·X(φ^η(s)) ds = a·Z₀(η) (map_smul, intervalIntegral.integral_const_mul). Thus Z₀ : D^{k+1}(ℝ^{m+1}) →ₗ[ℝ] ℝ.
5. (Bound.) If C ∈ ℝ and |η(y)| ≤ C for all y, then (D1) gives |X(φ^η(s))| ≤ B·C for s ∈ [0,1], in particular for s ∈ uIoc 0 1 = Ioc 0 1; intervalIntegral.norm_integral_le_of_norm_le_const gives |Z₀(η)| ≤ B·C·|1 − 0| = B·C.
6. (The current; conjunct (c).) By current_criterion (with P := m+1, q := k+1, U := univ, T₀ := Z₀ and B), there is Z ∈ D_{k+1}(ℝ^{m+1}) with Z(η) = Z₀(η) for all η and M(Z) ≤ ENNReal.ofReal B = M(X) (ENNReal.ofReal_toReal, M(X) ≠ ∞).
7. (Conjunct (a), ProdChar(X, Z).) If φ is a dt-slice family of η on [0,1], then Z(η) = Z₀(η) = ∫_0^1 X(φ(s)) ds by step 2.
8. (Conjunct (b), uniqueness.) Let Z′ satisfy ProdChar(X, Z′). For every η, applying it to the dt-slice family φ^η gives Z′(η) = ∫_0^1 X(φ^η(s)) ds = Z₀(η) = Z(η); hence Z′ = Z (GeometricCurrentOn.ext).
9. (Conjunct (d), support.) spt X = univ ∖ zeroRegion(X) = zeroRegion(X)ᶜ is closed (GeometricCurrentOn.isOpen_zeroRegion), so cyl(spt X) = t⁻¹([0,1]) ∩ tl⁻¹(spt X) is closed (t and tl are continuous). Let y₀ ∈ spt Z and suppose y₀ ∉ cyl(spt X). Choose ρ > 0 with ball(y₀, ρ) ∩ cyl(spt X) = ∅ (Metric.isOpen_iff for the open complement) and put W := ball(y₀, ρ).
   (i) Z vanishes on W. Let η ∈ D^{k+1}(ℝ^{m+1}) with tsupport η ⊆ W, and let s ∈ [0,1], j_s(x) := cons(s,x). If j_s(x) ∉ tsupport η then η(j_s(x)) = 0 (image_eq_zero_of_notMem_tsupport), so φ^η(s)(x) = 0; thus support φ^η(s) ⊆ j_s⁻¹(tsupport η), which is closed (j_s continuous), and tsupport φ^η(s) ⊆ j_s⁻¹(tsupport η) (closure_minimal). If x ∈ tsupport φ^η(s) ∩ spt X, then j_s(x) ∈ tsupport η ⊆ W, while t(j_s(x)) = s ∈ [0,1] and tl(j_s(x)) = x ∈ spt X (ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons, ContinuousLinearEquiv.symm_apply_apply), so j_s(x) ∈ W ∩ cyl(spt X) = ∅, a contradiction. Hence tsupport φ^η(s) and spt X are disjoint and X(φ^η(s)) = 0 by vanish_off_support. By intervalIntegral.integral_congr, Z(η) = ∫_0^1 X(φ^η(s)) ds = ∫_0^1 0 ds = 0.
   (ii) W is open, closure W ⊆ closedBall(y₀, ρ) (closure_ball_subset_closedBall) is compact (isCompact_closedBall, IsCompact.of_isClosed_subset) and closure W ⊆ univ; with (i), W belongs to the family whose union is zeroRegion(Z), so y₀ ∈ W ⊆ zeroRegion(Z) (Set.mem_sUnion, Metric.mem_ball_self), contradicting y₀ ∈ spt Z = univ ∖ zeroRegion(Z). Hence spt Z ⊆ cyl(spt X).
Steps 6–9 give the four conjuncts for this Z. ∎

Lean aid (verified, optional). The following tactic block was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) in the exact comparator scope (import GMT.Ch06.Submission; the contract's opens; namespace GMT.Ch06) as the proof of `theorem Submission.dph_iprod_exists : (<the frozen lean_statement>) := by`, with the sibling declarations present under their Submission names (zero errors; `#print axioms` lists only propext, Classical.choice and Quot.sound apart from sorryAx inherited from stubs that stood in for the already-accepted reused declarations). It can be used as is or as a guide:

```lean
  have hSF := Submission.iwl_cr_ci_slice_testForm
  have hVS := Submission.isoperimetric_apply_eq_zero_of_disjoint_support
  have hCC := Submission.dph_iprod_current_of_bound
  have hC := Submission.dph_iprod_slice_continuity
  intro m k X hX
  choose φ hφc hφ using fun η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1) => hSF m k η
  have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
  have hcongr : ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
      (ψ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
        (ψ s : DifferentialForm (Eucl m) k) x v =
          (η : DifferentialForm (Eucl (m + 1)) (k + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      ∫ s in (0 : ℝ)..1, X (ψ s) = ∫ s in (0 : ℝ)..1, X (φ η s) := by
    intro η ψ hψ
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have : ψ s = φ η s := by
      apply Subtype.ext; funext x; ext v; rw [hψ s hs x v, hφ η s x v]
    simp only [this]
  have hint : ∀ η, IntervalIntegrable (fun s => X (φ η s)) MeasureTheory.volume 0 1 := by
    intro η
    exact ((hC.1 m k X hX η (φ η) (fun s _ x v => hφ η s x v)).1).intervalIntegrable_of_Icc zero_le_one
  let T₀ : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun η => ∫ s in (0 : ℝ)..1, X (φ η s)
      map_add' := by
        intro η η'
        have h := hcongr (η + η') (fun s => φ η s + φ η' s) (by
          intro s _ x v
          show ((φ η s : DifferentialForm (Eucl m) k) + (φ η' s : DifferentialForm (Eucl m) k)) x v = _
          rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, hφ η s x v, hφ η' s x v]
          rfl)
        rw [← h]
        have : (fun s => X (φ η s + φ η' s)) = fun s => X (φ η s) + X (φ η' s) := by
          funext s; exact map_add X.toCurrent _ _
        rw [this, intervalIntegral.integral_add (hint η) (hint η')]
      map_smul' := by
        intro c η
        have h := hcongr (c • η) (fun s => c • φ η s) (by
          intro s _ x v
          show (c • (φ η s : DifferentialForm (Eucl m) k)) x v = _
          rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, hφ η s x v]
          rfl)
        rw [← h]
        have : (fun s => X (c • φ η s)) = fun s => c * X (φ η s) := by
          funext s; exact map_smul X.toCurrent c _
        rw [this, intervalIntegral.integral_const_mul]
        rfl }
  have hT₀ : ∀ η, T₀ η = ∫ s in (0 : ℝ)..1, X (φ η s) := fun η => rfl
  have hbound : ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (C : ℝ),
      (∀ y, covectorEuclideanNorm ((η : DifferentialForm (Eucl (m + 1)) (k + 1)) y) ≤ C) →
      |T₀ η| ≤ X.mass.toReal * C := by
    intro η C hηC
    have hb := (hC.1 m k X hX η (φ η) (fun s _ x v => hφ η s x v)).2 C hηC
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := X.mass.toReal * C) (f := fun s => X (φ η s)) (by
        intro s hs
        rw [Set.uIoc_of_le zero_le_one] at hs
        rw [Real.norm_eq_abs]
        exact hb s ⟨hs.1.le, hs.2⟩)
    rw [hT₀]
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using this
  obtain ⟨Z, hZ, hZm⟩ := hCC (m + 1) (k + 1) univ T₀ X.mass.toReal hB0 hbound
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro η ψ hψ
    rw [hZ η, hT₀, hcongr η ψ hψ]
  · intro Z' hZ'
    ext η
    rw [hZ' η (φ η) (fun s _ x v => hφ η s x v), hZ η, hT₀]
  · calc Z.mass ≤ ENNReal.ofReal X.mass.toReal := hZm
      _ = X.mass := ENNReal.ofReal_toReal hX.ne
  · intro y₀ hy₀
    by_contra hcyl
    have hsuppX : IsClosed X.support := by
      have : X.support = (X.zeroRegion)ᶜ := by
        ext y; simp [GeometricCurrentOn.support]
      rw [this]; exact X.isOpen_zeroRegion.isClosed_compl
    have hclosed : IsClosed {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
        (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} := by
      apply IsClosed.inter
      · exact isClosed_Icc.preimage (by fun_prop)
      · exact hsuppX.preimage (by fun_prop)
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl y₀ hcyl
    have hvan : Z.VanishesOn (ball y₀ ρ) := by
      intro η hη
      rw [hZ η, hT₀]
      have h0 : ∀ s ∈ Set.uIcc (0 : ℝ) 1, X (φ η s) = 0 := by
        intro s hs
        rw [Set.uIcc_of_le zero_le_one] at hs
        apply hVS
        rw [Set.disjoint_left]
        intro x hx hxX
        have hsub : tsupport (φ η s : DifferentialForm (Eucl m) k) ⊆
            (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ⁻¹'
              tsupport (η : DifferentialForm (Eucl (m + 1)) (k + 1)) := by
          apply closure_minimal _ ((isClosed_tsupport _).preimage (by fun_prop))
          intro x' hx'
          by_contra hn
          apply hx'
          ext v
          rw [hφ η s x' v, image_eq_zero_of_notMem_tsupport hn]
          rfl
        have h2 := hη (hsub hx)
        apply hball h2
        refine ⟨?_, ?_⟩
        · simp only [Set.mem_setOf_eq, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero]
          exact hs
        · simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
            ContinuousLinearEquiv.symm_apply_apply]
          exact hxX
      rw [intervalIntegral.integral_congr h0]
      simp
    have hW : ball y₀ ρ ⊆ Z.zeroRegion := by
      intro y hy
      refine Set.mem_sUnion.mpr ⟨ball y₀ ρ, ⟨isOpen_ball, ?_, subset_univ _, hvan⟩, hy⟩
      exact (isCompact_closedBall y₀ ρ).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
    exact hy₀.2 (hW (mem_ball_self hρ))
```

## Key steps

1. Choose slice families φ^η by slice_forms; any dt-slice family of η on [0,1] has the same integral.
2. Z₀(η) := ∫_0^1 X(φ^η(s)) ds is linear (integrability from (D1)) and |Z₀(η)| ≤ M(X).toReal·C when |η| ≤ C (bound of (D1)).
3. current_criterion turns Z₀ into Z with M(Z) ≤ M(X); ProdChar and uniqueness follow from the independence of the slice family.
4. Support: for η supported in a ball disjoint from the closed cylinder, every slice φ^η(s), s ∈ [0,1], is supported off spt X, so X(φ^η(s)) = 0 (vanish_off_support) and Z vanishes on the ball.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical); python3 -I verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem) → namespace GMT.Ch06 with its opens (exact child-comparator scope)`
- `grep -n '^def|^abbrev|^theorem|^structure' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality,FormSupNorm,Product,GeometricPointProduct,ParametricCurrentContinuity,AffineCurrentPushforward,FormsDuality,FixedSupportCurrentTopology}.lean: GeometricCurrentOn (continuous' = sequential continuity at 0), TestFormOnConverges, exteriorDerivativeTestOn and GeometricCurrentOn.boundary_apply, exteriorDerivative = extDeriv, covectorEuclideanNorm, massAdmissibleOn, massOn/mass, zeroRegion/support; no product with [[0,1]], no slice-continuity, FTC or current-from-sup-bound lemma`
- `python3 -I over dag.json (662 nodes): statuses, lean_names and lean_statements of the four handoff prerequisites and of every accepted declaration mentioning covectorEuclideanNorm with ‖·‖, Fin.cons, HasDerivAt, ContinuousOn (fun s …) or →ₗ[ℝ] (found fiw_ims_sc_covectorNorm_le_opNorm = (C3), fiw_ims_sc_continuous_of_bound, iwl_sp_covectorEuclideanNorm_pullback_le; none covers (C1), slice continuity, (∗) or the FTC); isolated-comparator-result.json of the four reused nodes (passed = True)`
- `git show c8cb71851ed3018dcc8a0a89a946b8610884f81a:GMT/Ch06/Submission.lean (accepted Lean proof of fiw_ims_sc_covectorNorm_le_opNorm, reproduced as (C3) of slice_norm)`
- `grep in the snapshot mathlib for the library inputs of the child proofs: extDeriv_apply, Fin.cons_comp_succ_succAbove, Fin.removeNth_zero, fderiv_continuousAlternatingMap_apply_const_apply, HasCompactMulSupport.uniformContinuous_of_continuous (to_additive), Convex.norm_image_sub_le_of_norm_hasDerivWithin_le, hasDerivAt_iff_isLittleO_nhds_zero, intervalIntegral.integral_eq_sub_of_hasDerivAt, tsupport_fderiv_subset, norm_iteratedFDeriv_zero, EuclideanSpace.equiv, ContinuousAlternatingMap.le_opNorm: all found`
- `read /runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py (_existing_lean_name_problem; _solve_children maps a child to an accepted node with identical lean_name and lean_statement) and store.py (ensure returns existing nodes unchanged)`
- `uniqueness of the new names: python3 over dag.json lean_names; grep -rn 'dph_ip' GMT/ .lake/packages/simongmt/ and the reference project; git log --all -S 'dph_ip_' (no match)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on all 12 child statements; lake env lean on /tmp/dphip/lean/{Parent,Children}.lean (parent and 8 new statements elaborate) and on the interface/proof checks IfaceParent, IfaceBoundary, IfaceExists, ChkSliceNorm, ChkHSlices, ChkCriterion, ChkContinuity, ChkExtDeriv, ChkFTC and the assembled Recheck.lean built from the final JSON (0 errors; #print axioms: propext, Classical.choice, Quot.sound, plus sorryAx only via stubs of the four accepted reused declarations)`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `GMT/Ch06/Contract.lean`
- `GMT/Ch06/Submission.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/ParametricCurrentContinuity.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/parent-supplied-natural-proof.md`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/isolated-comparator-result.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/isolated-comparator-result.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/isolated-comparator-result.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-slice-forms-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/store.py`
- `/tmp/dphip/lean/Recheck.lean`

The pinned project and SimonGMT contain no product of a current with [[0,1]] in Eucl (m+1), no continuity of currents along slices, no slice identity for exterior derivatives, no FTC along slices and no current-from-sup-bound criterion, so steps 1–10 of the supplied proof are new obligations. Its black boxes (R1)–(R4) are comparator-accepted declarations with no sibling prerequisites (cmb_abs_apply_le_of_massOn_le, isoperimetric_apply_eq_zero_of_disjoint_support, iwl_sp_exists_compatible_testForm, iwl_cr_ci_slice_testForm; isolated comparators passed). They are reused by name with byte-identical frozen types, titles and statements. (C3) equals the accepted fiw_ims_sc_covectorNorm_le_opNorm of another branch; its accepted proof is reproduced inside the new child slice_norm. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot. All 12 child statements are valid one-line types and elaborate in the exact comparator scope. The eight new dph_iprod_* names are globally unique. A Lean file assembled from the final JSON proves every new child from exactly its declared dependencies, and the selected parent from the children, with 0 errors and only standard axioms besides the four reused stubs.
