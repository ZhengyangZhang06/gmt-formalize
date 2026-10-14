# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent-supplied proof (continuity in s of X(φ_s) for dt-slices, and the same for horizontal slices, with the bound |X(φ_s)| ≤ M(X).toReal·sup|η|). Siblings used: mass_bound (cmb_abs_apply_le_of_massOn_le) and slice_norm (dph_iprod_slice_covector_norm_le), conjuncts (C1), (C2), (C3).

Notation. ℝ^p = Eucl p; cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1} for s ∈ ℝ, x ∈ ℝ^m; ι(v) := cons(0, v) = (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; ι∘v := (fun i => ι (v i)) and (e₀, ι∘v) := Fin.cons e₀ (fun i => ι (v i)) for tuples v; for a q-covector γ on ℝ^p (γ : Covector (Eucl p) q), |γ| := covectorEuclideanNorm γ = (Σ_{I : Fin q → Fin p strictly increasing} γ(b_{I 0}, …, b_{I (q−1)})²)^{1/2} with b_i := EuclideanSpace.basisFun (Fin p) ℝ i, and ‖γ‖ is its operator norm; D^q(ℝ^p) := TestFormOn univ q, D_q(ℝ^p) := GeometricCurrentOn univ q, M := mass; for a test form ω, ω(x) denotes (ω : DifferentialForm (Eucl p) q) x; a family φ : ℝ → D^k(ℝ^m) is a dt-slice family of η ∈ D^{k+1}(ℝ^{m+1}) on [0,1] if φ(s)(x)(v) = η(cons(s,x))(e₀, ι∘v) for all s ∈ [0,1], x, v.

0. (Preliminaries.) Let X ∈ D_q(ℝ^m) (q = k in (D1)) with M(X) < ∞ and B := M(X).toReal ≥ 0 (ENNReal.toReal_nonneg). Since X.mass is by definition X.massOn univ and M(X) ≠ ∞, X.massOn univ = ENNReal.ofReal B (ENNReal.ofReal_toReal). Hence mass_bound (with U = W = univ, this B, tsupport ⊆ univ trivially) gives: (MB) for every ω ∈ D^q(ℝ^m) and C ∈ ℝ with |ω(x)| ≤ C for all x, |X(ω)| ≤ B·C. Moreover, for all s, s′, x: dist(cons(s,x), cons(s′,x)) = |s − s′| (EuclideanSpace.dist_eq and Fin.sum_univ_succ: the 0-th coordinates are s, s′, all other coordinates coincide; √((s − s′)²) = |s − s′|). Finally X is linear: X(ω − ω′) = X(ω) − X(ω′) (in Lean `map_sub X.toCurrent ω ω′`, used with `exact`, since `rw [map_sub]` does not match the submodule subtraction syntactically).
1. ((D1), continuity on [0,1].) Let η ∈ D^{k+1}(ℝ^{m+1}) and φ a dt-slice family of η on [0,1]. η is continuous with compact support, hence uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). Let c := √((m+1)^{k+1}) ≥ 0. Fix s₀ ∈ [0,1] and ε > 0. Choose ε′ > 0 with B·c·ε′ < ε (e.g. ε′ := ε/(B·c + 1)) and, by uniform continuity (Metric.uniformContinuous_iff), δ > 0 such that ‖η(y) − η(y′)‖ < ε′ whenever dist(y, y′) < δ. Let s ∈ [0,1] with |s − s₀| < δ. For each x, the k-covector γ′ := (φ(s) − φ(s₀))(x) satisfies γ′(v) = φ(s)(x)(v) − φ(s₀)(x)(v) = [η(cons(s,x)) − η(cons(s₀,x))](e₀, ι∘v) for every v (pointwise subtraction, and the slice identity at s and at s₀, both in [0,1]). So (C1) applies to γ := η(cons(s,x)) − η(cons(s₀,x)), and with (C3): |(φ(s) − φ(s₀))(x)| ≤ |γ| ≤ c·‖γ‖ ≤ c·ε′, because dist(cons(s,x), cons(s₀,x)) = |s − s₀| < δ. By (MB) for the test form φ(s) − φ(s₀) and linearity, |X(φ(s)) − X(φ(s₀))| = |X(φ(s) − φ(s₀))| ≤ B·c·ε′ < ε. Hence s ↦ X(φ(s)) is continuous within [0,1] at s₀ (Metric.continuousWithinAt_iff), i.e. ContinuousOn on Icc 0 1.
2. ((D1), bound.) Let C ∈ ℝ with |η(y)| ≤ C for all y, and s ∈ [0,1]. For every x, (C1) with γ := η(cons(s,x)) and γ′ := φ(s)(x) (the slice identity at s) gives |φ(s)(x)| ≤ |η(cons(s,x))| ≤ C; by (MB), |X(φ(s))| ≤ B·C.
3. ((D2).) Let ω : ℝ^{m+1} → q-covectors be continuous with compact support and Ψ : ℝ → D^q(ℝ^m) with Ψ(s)(x)(v) = ω(cons(s,x))(ι∘v) for all s, x, v. The argument of steps 1–2 applies verbatim with (C2) in place of (C1), c := √((m+1)^q), ω in place of η (continuous with compact support, hence uniformly continuous) and Ψ in place of φ; since the slice identity holds for every s ∈ ℝ, one obtains continuity of s ↦ X(Ψ(s)) on all of ℝ (Metric.continuous_iff) and |X(Ψ(s))| ≤ B·C for every s whenever |ω(y)| ≤ C for all y. ∎

Lean aid (verified, optional). The following tactic block was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) in the exact comparator scope (import GMT.Ch06.Submission; the contract's opens; namespace GMT.Ch06) as the proof of `theorem Submission.dph_iprod_slice_continuity : (<the frozen lean_statement>) := by`, with the sibling declarations present under their Submission names (zero errors; `#print axioms` lists only propext, Classical.choice and Quot.sound apart from sorryAx inherited from stubs that stood in for the already-accepted reused declarations). It can be used as is or as a guide:

```lean
  have hMB := Submission.cmb_abs_apply_le_of_massOn_le
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  have hdist : ∀ (m : ℕ) (s s₀ : ℝ) (x : Eucl m),
      dist ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))) =
        |s - s₀| := by
    intro m s s₀ x
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_succ]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hmb : ∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ →
      X.massOn univ ≤ ENNReal.ofReal X.mass.toReal := by
    intro m k X hX
    rw [ENNReal.ofReal_toReal hX.ne]
    exact le_rfl
  refine ⟨?_, ?_⟩
  · intro m k X hX η φ hφ
    have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
    have hC1 := hSN.1 m k
    have hC3 := hSN.2.2 (m + 1) (k + 1)
    refine ⟨?_, ?_⟩
    · have huc : UniformContinuous (η : DifferentialForm (Eucl (m + 1)) (k + 1)) :=
        η.property.1.2.uniformContinuous_of_continuous η.property.1.1.continuous
      intro s₀ hs₀
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      set c := Real.sqrt ((((m + 1 : ℕ)) : ℝ) ^ (k + 1)) with hc
      have hc0 : 0 ≤ c := Real.sqrt_nonneg _
      obtain ⟨ε', hε', hε'ε⟩ : ∃ ε' > 0, X.mass.toReal * c * ε' < ε := by
        refine ⟨ε / (X.mass.toReal * c + 1), by positivity, ?_⟩
        have hpos : 0 < X.mass.toReal * c + 1 := by positivity
        rw [← mul_div_assoc, div_lt_iff₀ hpos]
        nlinarith [mul_nonneg hB0 hc0]
      obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp huc ε' hε'
      refine ⟨δ, hδ, fun {s} hs hss₀ => ?_⟩
      have hdiff : ∀ x, covectorEuclideanNorm
          (((φ s - φ s₀ : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x) ≤ c * ε' := by
        intro x
        have h1 := hC1 ((η : DifferentialForm (Eucl (m + 1)) (k + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) -
          (η : DifferentialForm (Eucl (m + 1)) (k + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))
          (((φ s - φ s₀ : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x) (by
            intro v
            show ((φ s : DifferentialForm (Eucl m) k) - (φ s₀ : DifferentialForm (Eucl m) k)) x v = _
            rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hφ s hs x v, hφ s₀ hs₀ x v]
            rfl)
        refine h1.trans ((hC3 _).trans (mul_le_mul_of_nonneg_left ?_ hc0))
        rw [← dist_eq_norm]
        apply le_of_lt
        apply hδ'
        rw [hdist]
        rw [Real.dist_eq] at hss₀
        exact hss₀
      have h2 := hMB m k univ univ X (φ s - φ s₀) X.mass.toReal (c * ε') hB0 (hmb m k X hX)
        (subset_univ _) hdiff
      have hsub : X (φ s - φ s₀) = X (φ s) - X (φ s₀) := map_sub X.toCurrent _ _
      rw [Real.dist_eq, ← hsub]
      calc |X (φ s - φ s₀)| ≤ X.mass.toReal * (c * ε') := h2
        _ = X.mass.toReal * c * ε' := by ring
        _ < ε := hε'ε
    · intro C hC s hs
      apply hMB m k univ univ X (φ s) X.mass.toReal C hB0 (hmb m k X hX) (subset_univ _)
      intro x
      exact (hC1 _ _ (fun v => hφ s hs x v)).trans (hC _)
  · intro m q X hX ω Ψ hωc hωs hΨ
    have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
    have hC2 := hSN.2.1 m q
    have hC3 := hSN.2.2 (m + 1) q
    refine ⟨?_, ?_⟩
    · have huc : UniformContinuous ω := hωs.uniformContinuous_of_continuous hωc
      rw [Metric.continuous_iff]
      intro s₀ ε hε
      set c := Real.sqrt ((((m + 1 : ℕ)) : ℝ) ^ q) with hc
      have hc0 : 0 ≤ c := Real.sqrt_nonneg _
      obtain ⟨ε', hε', hε'ε⟩ : ∃ ε' > 0, X.mass.toReal * c * ε' < ε := by
        refine ⟨ε / (X.mass.toReal * c + 1), by positivity, ?_⟩
        have hpos : 0 < X.mass.toReal * c + 1 := by positivity
        rw [← mul_div_assoc, div_lt_iff₀ hpos]
        nlinarith [mul_nonneg hB0 hc0]
      obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp huc ε' hε'
      refine ⟨δ, hδ, fun s hss₀ => ?_⟩
      have hdiff : ∀ x, covectorEuclideanNorm
          (((Ψ s - Ψ s₀ : TestFormOn (univ : Set (Eucl m)) q) : DifferentialForm (Eucl m) q) x) ≤ c * ε' := by
        intro x
        have h1 := hC2 (ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) -
          ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))
          (((Ψ s - Ψ s₀ : TestFormOn (univ : Set (Eucl m)) q) : DifferentialForm (Eucl m) q) x) (by
            intro v
            show ((Ψ s : DifferentialForm (Eucl m) q) - (Ψ s₀ : DifferentialForm (Eucl m) q)) x v = _
            rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hΨ s x v, hΨ s₀ x v]
            rfl)
        refine h1.trans ((hC3 _).trans (mul_le_mul_of_nonneg_left ?_ hc0))
        rw [← dist_eq_norm]
        apply le_of_lt
        apply hδ'
        rw [hdist]
        rw [Real.dist_eq] at hss₀
        exact hss₀
      have h2 := hMB m q univ univ X (Ψ s - Ψ s₀) X.mass.toReal (c * ε') hB0 (hmb m q X hX)
        (subset_univ _) hdiff
      have hsub : X (Ψ s - Ψ s₀) = X (Ψ s) - X (Ψ s₀) := map_sub X.toCurrent _ _
      rw [Real.dist_eq, ← hsub]
      calc |X (Ψ s - Ψ s₀)| ≤ X.mass.toReal * (c * ε') := h2
        _ = X.mass.toReal * c * ε' := by ring
        _ < ε := hε'ε
    · intro C hC s
      apply hMB m q univ univ X (Ψ s) X.mass.toReal C hB0 (hmb m q X hX) (subset_univ _)
      intro x
      exact (hC2 _ _ (fun v => hΨ s x v)).trans (hC _)
```

## Key steps

1. mass_bound with B = M(X).toReal gives |X(ω)| ≤ B·C whenever |ω| ≤ C pointwise.
2. η (resp. ω) is uniformly continuous and dist(cons(s,x), cons(s′,x)) = |s − s′|.
3. (C1) (resp. (C2)) and (C3) bound |φ(s)(x) − φ(s₀)(x)| uniformly in x; linearity of X gives continuity.
4. (C1) (resp. (C2)) and mass_bound give |X(φ(s))| ≤ M(X).toReal·C.

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
