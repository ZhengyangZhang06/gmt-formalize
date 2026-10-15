# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_ftc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent-supplied proof (fundamental theorem of calculus for s ↦ X(ψ_s)), with the uniform estimate of the difference quotient obtained from the mean value inequality (equivalently, the supplied integral representation ∫_0^1 [Dψ(cons(s+τh,x)) − Dψ(cons(s,x))](e₀) dτ). Siblings used: mass_bound (cmb_abs_apply_le_of_massOn_le), slice_norm (dph_iprod_slice_covector_norm_le, conjuncts (C2), (C3)) and slice_continuity (dph_iprod_slice_continuity, conjunct (D2)).

Notation. ℝ^p = Eucl p; cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1} for s ∈ ℝ, x ∈ ℝ^m; ι(v) := cons(0, v) = (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; ι∘v := (fun i => ι (v i)) and (e₀, ι∘v) := Fin.cons e₀ (fun i => ι (v i)) for tuples v; for a q-covector γ on ℝ^p (γ : Covector (Eucl p) q), |γ| := covectorEuclideanNorm γ = (Σ_{I : Fin q → Fin p strictly increasing} γ(b_{I 0}, …, b_{I (q−1)})²)^{1/2} with b_i := EuclideanSpace.basisFun (Fin p) ℝ i, and ‖γ‖ is its operator norm; D^q(ℝ^p) := TestFormOn univ q, D_q(ℝ^p) := GeometricCurrentOn univ q, M := mass; for a test form ω, ω(x) denotes (ω : DifferentialForm (Eucl p) q) x; Dψ(y) := fderiv ℝ ψ y.

Let X, ψ, Ψ, Ψ′ be as in the statement; g(t) := X(Ψ(t)).
0. (Mass estimate.) Let B := M(X).toReal ≥ 0 and c := √((m+1)^q) ≥ 0. As M(X) < ∞, X.massOn univ = M(X) = ENNReal.ofReal B (ENNReal.ofReal_toReal), so mass_bound with U = W = univ gives (MB): |X(ω)| ≤ B·C for every ω ∈ D^q(ℝ^m) and C with |ω(x)| ≤ C for all x.
1. (The form ψ′.) Let ψ′(y) := Dψ(y)(e₀). ψ is C^∞, so y ↦ Dψ(y) is continuous (ContDiff.continuous_fderiv) and ψ′ is continuous (evaluation at the constant e₀, Continuous.clm_apply). ψ′ has compact support: fderiv ℝ ψ has compact support (HasCompactSupport.fderiv) and ψ′ = (L ↦ L e₀) ∘ fderiv ℝ ψ maps 0 to 0 (HasCompactSupport.comp_left). By hypothesis Ψ′(s)(x)(v) = ψ′(cons(s,x))(ι∘v) for all s, x, v.
2. (Continuity, first conjunct.) By (D2) of slice_continuity with ω := ψ′ and the family Ψ′, s ↦ X(Ψ′(s)) is continuous on ℝ.
3. (Lines in the time direction.) cons(s + τ, x) = cons(s, x) + τ·e₀ for all s, τ, x: apply EuclideanSpace.equiv and compare coordinates by Fin.cases (coordinate 0: s + τ = s + τ·1; coordinate i.succ: x_i = x_i + τ·0).
4. (Derivative, second conjunct.) Fix s. By hasDerivAt_iff_isLittleO_nhds_zero and Asymptotics.isLittleO_iff it suffices, for every ε > 0, to show |g(s+h) − g(s) − h·X(Ψ′(s))| ≤ ε|h| for all h near 0. ψ′ is uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). Choose ε′ > 0 with B·c·ε′ ≤ ε (e.g. ε′ := ε/(B·c + 1)) and δ > 0 with ‖ψ′(y) − ψ′(y′)‖ < ε′ whenever dist(y, y′) < δ; let |h| < δ. Put Θ_h := Ψ(s+h) − Ψ(s) − h·Ψ′(s) ∈ D^q(ℝ^m), so Θ_h(x)(v) = Ψ(s+h)(x)(v) − Ψ(s)(x)(v) − h·Ψ′(s)(x)(v).
   Fix x, put y := cons(s, x) and define the curve f(τ) := ψ(y + τe₀) − τ·ψ′(y) of q-covectors on ℝ^{m+1}. By the chain rule (τ ↦ y + τe₀ has derivative e₀, and ψ is differentiable), f has derivative f′(τ) = Dψ(y + τe₀)(e₀) − ψ′(y) = ψ′(y + τe₀) − ψ′(y) at every τ. For τ in the segment uIcc 0 h we have |τ| ≤ |h| < δ and dist(y + τe₀, y) = ‖τe₀‖ = |τ| (EuclideanSpace.norm_single), so ‖f′(τ)‖ < ε′. The mean value inequality on the convex set uIcc 0 h (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le) gives ‖f(h) − f(0)‖ ≤ ε′|h|. By step 3, f(h) − f(0) = ψ(cons(s+h,x)) − ψ(cons(s,x)) − h·ψ′(cons(s,x)), and hence, by the hypotheses on Ψ and Ψ′, Θ_h(x)(v) = (f(h) − f(0))(ι∘v) for every v. So (C2) and (C3) give |Θ_h(x)| ≤ |f(h) − f(0)| ≤ c·‖f(h) − f(0)‖ ≤ c·ε′·|h|.
   By (MB) for Θ_h, |X(Θ_h)| ≤ B·c·ε′·|h| ≤ ε|h|, and by linearity of X (map_sub, map_smul) X(Θ_h) = g(s+h) − g(s) − h·X(Ψ′(s)). Hence g has derivative X(Ψ′(s)) at s.
5. (Integral identity, third conjunct.) By step 4 for every s ∈ uIcc 0 1 and step 2 (a continuous function is interval integrable, Continuous.intervalIntegrable), intervalIntegral.integral_eq_sub_of_hasDerivAt gives ∫_0^1 X(Ψ′(s)) ds = X(Ψ(1)) − X(Ψ(0)). ∎

Lean aid (verified, optional). The following tactic block was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) in the exact comparator scope (import GMT.Ch06.Submission; the contract's opens; namespace GMT.Ch06) as the proof of `theorem Submission.dph_iprod_horizontal_ftc : (<the frozen lean_statement>) := by`, with the sibling declarations present under their Submission names (zero errors; `#print axioms` lists only propext, Classical.choice and Quot.sound apart from sorryAx inherited from stubs that stood in for the already-accepted reused declarations). It can be used as is or as a guide:

```lean
  have hMB := Submission.cmb_abs_apply_le_of_massOn_le
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  have hC := Submission.dph_iprod_slice_continuity
  intro m q X ψ Ψ Ψ' hX hΨ hΨ'
  have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
  have hmb : X.massOn univ ≤ ENNReal.ofReal X.mass.toReal := by
    rw [ENNReal.ofReal_toReal hX.ne]
    exact le_rfl
  have hC2 := hSN.2.1 m q
  have hC3 := hSN.2.2 (m + 1) q
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt ((((m + 1 : ℕ)) : ℝ) ^ q) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ Real.sqrt_nonneg _
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Eucl (m + 1), e₀ = EuclideanSpace.single 0 1 := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'def⟩ : ∃ ψ' : Eucl (m + 1) → Covector (Eucl (m + 1)) q,
      ψ' = fun y => fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y e₀ := ⟨_, rfl⟩
  have hψd : Differentiable ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) :=
    ψ.property.1.1.differentiable (by simp)
  have hψ'c : Continuous ψ' := by
    rw [hψ'def]
    exact (ψ.property.1.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ's : HasCompactSupport ψ' := by
    rw [hψ'def]
    exact (ψ.property.1.2.fderiv ℝ).comp_left
      (g := fun L : Eucl (m + 1) →L[ℝ] Covector (Eucl (m + 1)) q => L e₀) rfl
  have hΨ'2 : ∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ' s : DifferentialForm (Eucl m) q) x v =
      ψ' ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
    intro s x v
    rw [hΨ' s x v, hψ'def, he₀]
  have hcont := (hC.2 m q X hX ψ' Ψ' hψ'c hψ's hΨ'2).1
  have hpath : ∀ (s τ : ℝ) (x : Eucl m),
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons (s + τ) (EuclideanSpace.equiv (Fin m) ℝ x)) =
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) +
        τ • e₀ := by
    intro s τ x
    rw [he₀]
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t => X (Ψ t)) (X (Ψ' s)) s := by
    intro s
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    have huc := hψ's.uniformContinuous_of_continuous hψ'c
    obtain ⟨ε', hε', hε'ε⟩ : ∃ ε' > 0, X.mass.toReal * c * ε' ≤ ε := by
      refine ⟨ε / (X.mass.toReal * c + 1), by positivity, ?_⟩
      have hpos : 0 < X.mass.toReal * c + 1 := by positivity
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      nlinarith [mul_nonneg hB0 hc0]
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp huc ε' hε'
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    obtain ⟨Θ, hΘdef⟩ : ∃ Θ : TestFormOn (univ : Set (Eucl m)) q, Θ = Ψ (s + h) - Ψ s - h • Ψ' s :=
      ⟨_, rfl⟩
    have hΘx : ∀ (x : Eucl m) (v : Fin q → Eucl m), (Θ : DifferentialForm (Eucl m) q) x v =
        (Ψ (s + h) : DifferentialForm (Eucl m) q) x v - (Ψ s : DifferentialForm (Eucl m) q) x v -
          h * (Ψ' s : DifferentialForm (Eucl m) q) x v := by
      intro x v
      rw [hΘdef]
      rfl
    have hΘ : ∀ x, covectorEuclideanNorm ((Θ : DifferentialForm (Eucl m) q) x) ≤ c * (ε' * |h|) := by
      intro x
      obtain ⟨y, hy⟩ : ∃ y : Eucl (m + 1),
          y = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) :=
        ⟨_, rfl⟩
      obtain ⟨f, hfdef⟩ : ∃ f : ℝ → Covector (Eucl (m + 1)) q,
          f = fun τ => (ψ : DifferentialForm (Eucl (m + 1)) q) (y + τ • e₀) - τ • ψ' y := ⟨_, rfl⟩
      have hf : ∀ τ ∈ Set.uIcc (0 : ℝ) h,
          HasDerivWithinAt f (ψ' (y + τ • e₀) - ψ' y) (Set.uIcc (0 : ℝ) h) τ := by
        intro τ _
        have h1 : HasDerivAt (fun τ : ℝ => y + τ • e₀) e₀ τ := by
          simpa using ((hasDerivAt_id τ).smul_const e₀).const_add y
        have h2 : HasDerivAt (fun τ : ℝ => (ψ : DifferentialForm (Eucl (m + 1)) q) (y + τ • e₀))
            (ψ' (y + τ • e₀)) τ := by
          rw [hψ'def]
          exact (hψd _).hasFDerivAt.comp_hasDerivAt τ h1
        have h3 : HasDerivAt (fun τ : ℝ => τ • ψ' y) (ψ' y) τ := by
          simpa using (hasDerivAt_id τ).smul_const (ψ' y)
        rw [hfdef]
        exact (h2.sub h3).hasDerivWithinAt
      have hbound : ∀ τ ∈ Set.uIcc (0 : ℝ) h, ‖ψ' (y + τ • e₀) - ψ' y‖ ≤ ε' := by
        intro τ hτ
        rw [← dist_eq_norm]
        apply le_of_lt
        apply hδ'
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he₀, EuclideanSpace.norm_single, norm_one,
          mul_one, Real.norm_eq_abs]
        have : |τ| ≤ |h| := by
          rcases le_total 0 h with h0 | h0
          · rw [Set.uIcc_of_le h0] at hτ
            rw [abs_of_nonneg hτ.1, abs_of_nonneg h0]; exact hτ.2
          · rw [Set.uIcc_of_ge h0] at hτ
            rw [abs_of_nonpos hτ.2, abs_of_nonpos h0]; linarith [hτ.1]
        exact lt_of_le_of_lt this hh
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound (convex_uIcc 0 h)
        Set.left_mem_uIcc Set.right_mem_uIcc
      rw [sub_zero, Real.norm_eq_abs] at hmv
      have hγ : ∀ v : Fin q → Eucl m, (f h - f 0) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) = (Θ : DifferentialForm (Eucl m) q) x v := by
        intro v
        rw [hΘx, hΨ, hΨ, hΨ'2, hfdef, hpath, ← hy]
        simp only [zero_smul, add_zero, ContinuousAlternatingMap.sub_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
        ring
      have h4 := hC2 (f h - f 0) ((Θ : DifferentialForm (Eucl m) q) x) (fun v => (hγ v).symm)
      refine h4.trans ((hC3 _).trans ?_)
      rw [← hc]
      exact mul_le_mul_of_nonneg_left hmv hc0
    have h5 := hMB m q univ univ X Θ X.mass.toReal (c * (ε' * |h|)) hB0 hmb (subset_univ _) hΘ
    have hlin : X Θ = X (Ψ (s + h)) - X (Ψ s) - h • X (Ψ' s) := by
      rw [hΘdef]
      have e1 := map_sub X.toCurrent (Ψ (s + h) - Ψ s) (h • Ψ' s)
      have e2 := map_sub X.toCurrent (Ψ (s + h)) (Ψ s)
      have e3 := map_smul X.toCurrent h (Ψ' s)
      exact e1.trans (by rw [e2, e3])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← hlin]
    calc |X Θ| ≤ X.mass.toReal * (c * (ε' * |h|)) := h5
      _ = (X.mass.toReal * c * ε') * |h| := by ring
      _ ≤ ε * |h| := mul_le_mul_of_nonneg_right hε'ε (abs_nonneg h)
  refine ⟨hcont, hderiv, ?_⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hcont.intervalIntegrable 0 1)
```

## Key steps

1. ψ′ := Dψ(·)(e₀) is continuous with compact support, so (D2) gives continuity of s ↦ X(Ψ′(s)).
2. cons(s+τ, x) = cons(s,x) + τ·e₀.
3. Mean value inequality and uniform continuity of ψ′: ‖ψ(cons(s+h,x)) − ψ(cons(s,x)) − h·ψ′(cons(s,x))‖ ≤ ε′|h| uniformly in x.
4. (C2), (C3), mass_bound and linearity of X give |X(Ψ(s+h)) − X(Ψ(s)) − h·X(Ψ′(s))| ≤ ε|h|, i.e. HasDerivAt.
5. intervalIntegral.integral_eq_sub_of_hasDerivAt gives the integral identity.

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
