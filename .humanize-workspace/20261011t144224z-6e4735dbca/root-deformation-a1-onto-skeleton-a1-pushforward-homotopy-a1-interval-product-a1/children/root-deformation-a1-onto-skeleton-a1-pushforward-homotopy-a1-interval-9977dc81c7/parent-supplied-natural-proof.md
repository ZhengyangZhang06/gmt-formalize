# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_norm-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent-supplied proof (coefficient bounds (C1), (C2), (C3)), written out for the exact SimonGMT definition of covectorEuclideanNorm. Conjunct (C3) is also the frozen type of the comparator-accepted declaration fiw_ims_sc_covectorNorm_le_opNorm of another DAG branch (candidate commit c8cb71851ed3018dcc8a0a89a946b8610884f81a); its proof is reproduced in step 5.

Notation. ℝ^p = Eucl p; ι(v) := cons(0, v) = (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; ι∘v := (fun i => ι (v i)) and (e₀, ι∘v) := Fin.cons e₀ (fun i => ι (v i)) for tuples v; b^{(p)}_i := EuclideanSpace.basisFun (Fin p) ℝ i (= EuclideanSpace.single i 1); for a q-covector γ on ℝ^p (γ : Covector (Eucl p) q), |γ| := covectorEuclideanNorm γ = (Σ_{I : Fin q → Fin p strictly increasing} γ(b_{I 0}, …, b_{I (q−1)})²)^{1/2} with b_i := EuclideanSpace.basisFun (Fin p) ℝ i, and ‖γ‖ is its operator norm.

1. (Basis vectors.) e₀ = b^{(m+1)}_0, because EuclideanSpace.basisFun_apply gives b^{(m+1)}_0 = EuclideanSpace.single 0 1. For j : Fin m, ι(b^{(m)}_j) = b^{(m+1)}_{j.succ}: apply the injective map EuclideanSpace.equiv (Fin (m+1)) ℝ to both sides (ContinuousLinearEquiv.apply_symm_apply) and compare coordinates by Fin.cases: at coordinate 0 the left side is Fin.cons 0 _ 0 = 0 and the right side is (single j.succ 1) 0 = 0 since j.succ ≠ 0; at coordinate i.succ the left side is (single j 1) i and the right side is (single j.succ 1) i.succ, which agree because Fin.succ is injective.
2. (Sums along an injection.) Let A, B be finite types, g : A → B injective, F : B → ℝ with F ≥ 0 and G : A → ℝ with G(a) ≤ F(g(a)) for all a. Then Σ_a G(a) ≤ Σ_a F(g(a)) (Finset.sum_le_sum) = Σ_{b ∈ g(A)} F(b) (Finset.sum_image, using injectivity) ≤ Σ_b F(b) (Finset.sum_le_sum_of_subset_of_nonneg, F ≥ 0).
3. ((C1).) Let γ, γ′ be as in (C1). Unfolding covectorEuclideanNorm, |γ′| = √S′ and |γ| = √S with S′ := Σ_{I : Fin k → Fin m} G(I), G(I) := (if I strictly increasing then γ′(b^{(m)} ∘ I)² else 0), and S := Σ_{J : Fin (k+1) → Fin (m+1)} F(J), F(J) := (if J strictly increasing then γ(b^{(m+1)} ∘ J)² else 0) ≥ 0. As √ is monotone (Real.sqrt_le_sqrt) it suffices to show S′ ≤ S, which follows from step 2 with g(I) := Fin.cons 0 (fun i => (I i).succ) once we check:
   (a) g is injective: if g(I) = g(I′), evaluating at i.succ gives (I i).succ = (I′ i).succ, hence I i = I′ i for all i.
   (b) If I is strictly increasing, so is g(I): let a < b in Fin (k+1) and use Fin.cases on a and b. If a = 0 = b this contradicts a < b. If a = 0 and b = j.succ, then g(I)(a) = 0 < (I j).succ = g(I)(b) (Fin.succ_pos). If a = i.succ and b = 0, a < b is impossible (Fin.not_lt_zero). If a = i.succ and b = j.succ, then i < j (Fin.succ_lt_succ_iff), so I i < I j and (I i).succ < (I j).succ.
   (c) G(I) ≤ F(g(I)) for every I: if I is not strictly increasing, G(I) = 0 ≤ F(g(I)). Otherwise both `if`s take their first branch by (b), and by the hypothesis on γ′, γ′(b^{(m)} ∘ I) = γ(Fin.cons e₀ (fun i => ι(b^{(m)}_{I i}))); by Fin.cases and step 1 (index 0: e₀ = b^{(m+1)}_0; index i.succ: ι(b^{(m)}_{I i}) = b^{(m+1)}_{(I i).succ}) this tuple equals b^{(m+1)} ∘ g(I). Hence G(I) = F(g(I)).
   So S′ ≤ S and |γ′| ≤ |γ|.
4. ((C2).) Identical, with A := (Fin q → Fin m), B := (Fin q → Fin (m+1)), g(I) := fun i => (I i).succ (injective because Fin.succ is injective; strictly increasing whenever I is, by Fin.succ_lt_succ_iff), and γ′(b^{(m)} ∘ I) = γ(fun i => ι(b^{(m)}_{I i})) = γ(b^{(m+1)} ∘ g(I)) by the hypothesis and step 1.
5. ((C3).) For every I : Fin n → Fin P, ContinuousAlternatingMap.le_opNorm gives |α(b ∘ I)| ≤ ‖α‖·Π_i ‖b_{I i}‖ = ‖α‖, the basis vectors having norm 1 (OrthonormalBasis.norm_eq_one). Hence every summand of the sum defining |α|² is at most ‖α‖² (strictly increasing I: square the bound, pow_le_pow_left₀ with sq_abs; other I: 0 ≤ ‖α‖²), and the sum has #(Fin n → Fin P) = P^n summands, so it is at most P^n·‖α‖² (Finset.sum_le_sum, Finset.card_univ). Therefore |α| ≤ √(P^n·‖α‖²) = √(P^n)·‖α‖ (Real.sqrt_le_sqrt, Real.sqrt_mul, Real.sqrt_sq with ‖α‖ ≥ 0). ∎

Lean aid (verified, optional). The following tactic block was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) in the exact comparator scope (import GMT.Ch06.Submission; the contract's opens; namespace GMT.Ch06) as the proof of `theorem Submission.dph_iprod_slice_covector_norm_le : (<the frozen lean_statement>) := by`, with the sibling declarations present under their Submission names (zero errors; `#print axioms` lists only propext, Classical.choice and Quot.sound). It can be used as is or as a guide:

```lean
  have hb0 : ∀ m : ℕ, (EuclideanSpace.single 0 1 : Eucl (m + 1)) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0 := by
    intro m; simp [EuclideanSpace.basisFun_apply]
  have hbι : ∀ (m : ℕ) (j : Fin m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (EuclideanSpace.basisFun (Fin m) ℝ j))) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ j.succ := by
    intro m j
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [EuclideanSpace.basisFun_apply]
    · simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
  have key : ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (g : A → B), Function.Injective g →
      ∀ (F : B → ℝ) (G : A → ℝ), (∀ b, 0 ≤ F b) → (∀ a, G a ≤ F (g a)) → ∑ a, G a ≤ ∑ b, F b := by
    intro A B _ _ _ g hg F G hF hG
    calc ∑ a, G a ≤ ∑ a, F (g a) := Finset.sum_le_sum (fun a _ => hG a)
      _ = ∑ b ∈ Finset.univ.image g, F b := (Finset.sum_image (fun a _ b _ h => hg h)).symm
      _ ≤ ∑ b, F b := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hF b)
  refine ⟨?_, ?_, ?_⟩
  · intro m k γ γ' hγ'
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply key (fun I : Fin k → Fin m => (Fin.cons 0 (fun i => (I i).succ) : Fin (k + 1) → Fin (m + 1)))
    · intro I I' h
      funext i
      have := congrFun h i.succ
      simpa using this
    · intro J; split_ifs <;> positivity
    · intro I
      by_cases h1 : StrictMono I
      · have h2 : StrictMono (Fin.cons 0 (fun i => (I i).succ) : Fin (k + 1) → Fin (m + 1)) := by
          intro a b hab
          induction a using Fin.cases with
          | zero =>
            induction b using Fin.cases with
            | zero => exact absurd hab (lt_irrefl _)
            | succ j => simp [Fin.succ_pos]
          | succ i =>
            induction b using Fin.cases with
            | zero => exact absurd hab (Fin.not_lt_zero _)
            | succ j =>
              simp only [Fin.cons_succ, Fin.succ_lt_succ_iff] at hab ⊢
              exact h1 hab
        rw [if_pos h1, if_pos h2, hγ']
        apply le_of_eq
        congr 2
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Fin.cons_zero]
          exact hb0 m
        · simp only [Fin.cons_succ]
          exact hbι m (I i)
      · rw [if_neg h1]
        split_ifs <;> positivity
  · intro m q γ γ' hγ'
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply key (fun I : Fin q → Fin m => (fun i => (I i).succ : Fin q → Fin (m + 1)))
    · intro I I' h
      funext i
      have := congrFun h i
      simpa using this
    · intro J; split_ifs <;> positivity
    · intro I
      by_cases h1 : StrictMono I
      · have h2 : StrictMono (fun i => (I i).succ : Fin q → Fin (m + 1)) :=
          fun a b hab => Fin.succ_lt_succ_iff.mpr (h1 hab)
        rw [if_pos h1, if_pos h2, hγ']
        apply le_of_eq
        congr 2
        funext i
        exact hbι m (I i)
      · rw [if_neg h1]
        split_ifs <;> positivity
  · intro P n α
    have hcoef : ∀ I : Fin n → Fin P,
        |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ ‖α‖ := by
      intro I
      have h := ContinuousAlternatingMap.le_opNorm α
        (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))
      simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one,
        Real.norm_eq_abs] at h
      exact h
    rw [covectorEuclideanNorm]
    calc Real.sqrt _ ≤ Real.sqrt ((P : ℝ) ^ n * ‖α‖ ^ 2) := by
          apply Real.sqrt_le_sqrt
          calc _ ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := by
                apply Finset.sum_le_sum
                intro I _
                split_ifs
                · rw [← sq_abs]
                  exact pow_le_pow_left₀ (abs_nonneg _) (hcoef I) 2
                · positivity
            _ = (P : ℝ) ^ n * ‖α‖ ^ 2 := by simp [Finset.card_univ]
      _ = Real.sqrt ((P : ℝ) ^ n) * ‖α‖ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
```

## Key steps

1. e₀ = b_0 and ι(b_j) = b_{j.succ} in the standard orthonormal bases.
2. A sum whose terms are dominated, along an injection, by nonnegative terms is bounded by the full sum.
3. (C1): I ↦ Fin.cons 0 (succ ∘ I) is injective, preserves strict monotonicity and carries the coefficient γ′(b ∘ I) to γ(b ∘ g(I)).
4. (C2): I ↦ succ ∘ I has the same three properties for horizontal slices.
5. (C3): each coefficient is at most ‖α‖ by le_opNorm and there are P^n coefficients.

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
