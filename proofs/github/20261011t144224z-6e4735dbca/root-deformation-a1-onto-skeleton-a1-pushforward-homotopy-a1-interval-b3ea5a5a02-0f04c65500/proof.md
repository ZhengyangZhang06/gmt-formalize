# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_slices-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent-supplied proof (horizontal slices are test forms, via (R3) = compatible_form with f = j_s), together with the test form ψ′ = Dψ(·)(e₀) introduced in its step 7. Sibling used: compatible_form (iwl_sp_exists_compatible_testForm).

Notation. ℝ^p = Eucl p; cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1} for s ∈ ℝ, x ∈ ℝ^m; ι(v) := cons(0, v) = (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; ι∘v := (fun i => ι (v i)) and (e₀, ι∘v) := Fin.cons e₀ (fun i => ι (v i)) for tuples v; D^q(ℝ^p) := TestFormOn univ q, D_q(ℝ^p) := GeometricCurrentOn univ q, M := mass; for a test form ω, ω(x) denotes (ω : DifferentialForm (Eucl p) q) x; Dψ(y) := fderiv ℝ ψ y.

1. (ι is continuous linear.) The map w ↦ Fin.cons 0 w from (Fin m → ℝ) to (Fin (m+1) → ℝ) is ℝ-linear (check additivity and homogeneity coordinatewise with Fin.cases: coordinate 0 gives 0 = 0 + 0 and 0 = c·0). Composing it with the continuous linear equivalences EuclideanSpace.equiv (Fin m) ℝ and (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (a linear map between finite-dimensional spaces is continuous, LinearMap.toContinuousLinearMap) gives a continuous linear map ι : ℝ^m →L[ℝ] ℝ^{m+1} with ι(v) = (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)) definitionally.
2. (j_s is affine.) Fix s ∈ ℝ and let j_s(x) := cons(s, x). Then j_s(x) = cons(s, 0) + ι(x) for all x: apply the injective map EuclideanSpace.equiv (Fin (m+1)) ℝ and compare coordinates by Fin.cases (coordinate 0: s = s + 0; coordinate i.succ: x_i = 0 + x_i). Hence j_s is C^∞ (contDiff_const.add ι.contDiff) and fderiv ℝ j_s x = ι for every x (((ι.hasFDerivAt).const_add _).fderiv).
3. (j_s is proper.) ‖x‖ ≤ ‖j_s(x)‖ for every x, since by EuclideanSpace.norm_eq and Fin.sum_univ_succ, ‖j_s(x)‖² = s² + ‖x‖². Let K ⊆ ℝ^{m+1} be compact. Then j_s⁻¹(K) is closed (K is closed and j_s continuous) and bounded (if K ⊆ closedBall(0, R) then j_s⁻¹(K) ⊆ closedBall(0, R)), hence compact (Metric.isCompact_of_isClosed_isBounded; ℝ^m is proper). So j_s⁻¹(K) ∩ univ is compact.
4. (Slices of an arbitrary test form.) Let ω ∈ D^q(ℝ^{m+1}) and s ∈ ℝ. Apply compatible_form with P := m, Q := m+1, j := q, U := univ (open), V := univ, A := univ ⊆ U, f := j_s (C^∞ by step 2; the properness hypothesis holds by step 3) and this ω. It yields η ∈ D^q(ℝ^m), ζ and an open N with univ ⊆ N and η(x) = (ω(j_s x)).compContinuousLinearMap (fderiv ℝ j_s x) for all x ∈ N, i.e. for all x. By step 2 the right side is (ω(cons(s,x))).compContinuousLinearMap ι, whose value at v is ω(cons(s,x))(fun i => ι(v i)) (definitional unfolding of compContinuousLinearMap). Hence: for every ω ∈ D^q(ℝ^{m+1}) and s ∈ ℝ there is η_{ω,s} ∈ D^q(ℝ^m) with η_{ω,s}(x)(v) = ω(cons(s,x))(ι∘v) for all x, v.
5. (The test form ψ′.) Let ψ′(y) := Dψ(y)(e₀) = fderiv ℝ ψ y e₀. ψ is C^∞, so fderiv ℝ ψ is C^∞ (ContDiff.fderiv_right, using ∞ + 1 ≤ ∞) and so is ψ′ (ContDiff.clm_apply with the constant e₀). fderiv ℝ ψ has compact support (HasCompactSupport.fderiv) and ψ′ = (L ↦ L e₀) ∘ fderiv ℝ ψ with 0 ↦ 0, so ψ′ has compact support (HasCompactSupport.comp_left); trivially tsupport ψ′ ⊆ univ. Hence ψ′ ∈ D^q(ℝ^{m+1}).
6. (Conclusion.) For each s choose Ψ(s) := η_{ψ,s} and Ψ′(s) := η_{ψ′,s} from step 4 (Classical.choice, e.g. the `choose` tactic). Then Ψ(s)(x)(v) = ψ(cons(s,x))(ι∘v) and Ψ′(s)(x)(v) = ψ′(cons(s,x))(ι∘v) = Dψ(cons(s,x))(e₀)(ι∘v) for all s, x, v, which are the two required identities. ∎

Lean aid (verified, optional). The following tactic block was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) in the exact comparator scope (import GMT.Ch06.Submission; the contract's opens; namespace GMT.Ch06) as the proof of `theorem Submission.dph_iprod_horizontal_slices : (<the frozen lean_statement>) := by`, with the sibling declarations present under their Submission names (zero errors; `#print axioms` lists only propext, Classical.choice and Quot.sound apart from sorryAx inherited from stubs that stood in for the already-accepted reused declarations). It can be used as is or as a guide:

```lean
  have hCF := Submission.iwl_sp_exists_compatible_testForm
  intro m q ψ
  let L : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    { toFun := fun w => Fin.cons 0 w
      map_add' := by
        intro a b; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro c a; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let ι : Eucl m →L[ℝ] Eucl (m + 1) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap ∘L
      LinearMap.toContinuousLinearMap L ∘L (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap
  have hιv : ∀ v : Eucl m,
      ι v = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)) :=
    fun v => rfl
  have hj : ∀ s : ℝ, (fun x : Eucl m =>
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) =
      fun x => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s 0) + ι x := by
    intro s
    funext x
    rw [hιv]
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have hnorm : ∀ (s : ℝ) (x : Eucl m), ‖x‖ ≤ ‖(EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))‖ := by
    intro s x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    apply Real.sqrt_le_sqrt
    simp only [ContinuousLinearEquiv.apply_symm_apply] at *
    simp
    positivity
  have hslice : ∀ (ω : TestFormOn (univ : Set (Eucl (m + 1))) q) (s : ℝ),
      ∃ η : TestFormOn (univ : Set (Eucl m)) q, ∀ (x : Eucl m) (v : Fin q → Eucl m),
        (η : DifferentialForm (Eucl m) q) x v = (ω : DifferentialForm (Eucl (m + 1)) q)
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (fun i => ι (v i)) := by
    intro ω s
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl m =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) := by
      rw [hj s]
      exact contDiff_const.add ι.contDiff
    have hfd : ∀ x, fderiv ℝ (fun x : Eucl m =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) x = ι := by
      intro x
      rw [hj s]
      exact ((ι.hasFDerivAt).const_add _).fderiv
    have hpr : ∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ univ →
        IsCompact ((fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ⁻¹' K ∩ univ) := by
      intro K hK _
      rw [inter_univ]
      apply Metric.isCompact_of_isClosed_isBounded
      · exact hK.isClosed.preimage hsm.continuous
      · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
        refine (Metric.isBounded_closedBall (x := (0 : Eucl m)) (r := R)).subset ?_
        intro x hx
        have := hR hx
        rw [mem_closedBall, dist_zero_right] at this ⊢
        exact (hnorm s x).trans this
    obtain ⟨η, ζ, N, -, hAN, -, -, hη2, -⟩ := hCF m (m + 1) q univ univ univ _ isOpen_univ
      (subset_univ _) hsm hpr ω
    refine ⟨η, fun x v => ?_⟩
    rw [hη2 x (hAN (mem_univ x)), hfd x]
    rfl
  have hψ' : ∃ ψ' : TestFormOn (univ : Set (Eucl (m + 1))) q, ∀ y,
      (ψ' : DifferentialForm (Eucl (m + 1)) q) y =
        fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y (EuclideanSpace.single 0 1) := by
    refine ⟨⟨fun y => fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y (EuclideanSpace.single 0 1),
      ⟨⟨?_, ?_⟩, subset_univ _⟩⟩, fun y => rfl⟩
    · exact (ψ.property.1.1.fderiv_right (by simp)).clm_apply contDiff_const
    · exact (ψ.property.1.2.fderiv ℝ).comp_left (g := fun L => L (EuclideanSpace.single 0 1)) rfl
  obtain ⟨ψ', hψ'⟩ := hψ'
  choose Ψ hΨ using fun s => hslice ψ s
  choose Ψ' hΨ' using fun s => hslice ψ' s
  refine ⟨Ψ, Ψ', fun s x v => ?_, fun s x v => ?_⟩
  · rw [hΨ s x v]
    rfl
  · rw [hΨ' s x v, hψ']
    rfl
```

## Key steps

1. ι is continuous linear and j_s(x) := cons(s,x) = cons(s,0) + ι(x), so j_s is C^∞ with fderiv ℝ j_s x = ι.
2. ‖x‖ ≤ ‖j_s(x)‖, so preimages of compact sets under j_s are compact.
3. compatible_form with f = j_s and U = V = A = univ yields, for every test form ω and s, a test form equal to ω(cons(s,·))∘ι everywhere.
4. ψ′ := Dψ(·)(e₀) is a test form; apply the previous step to ψ and ψ′ for every s and choose.

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
