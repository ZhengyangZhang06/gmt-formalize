# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1.pullback_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (N4)–(N6) and the cut-off forms ω' := χ·p^#ω (step 5) and γ' := χ·p^#γ (step 6) of the parent proof, including the claim dγ' = p^#(dγ) on S, stated once for a general smooth form γ, degree l, target dimension m and open set O. Notation: β(x) := (p^#γ)(x) = (γ(pL x)).compContinuousLinearMap pL; |·| = covectorEuclideanNorm; d = exteriorDerivative = extDeriv, so dω(x) = alternatizeUncurryFin(fderiv ℝ ω x).
1. (Cutoff.) K := S ∩ pL⁻¹(tsupport γ) is compact and K ⊆ O, with O open. By the sibling smooth_cutoff (Submission.cbr_ci_pw_proj_smooth_cutoff applied to K ⊆ O) there are χ : ℝ^P → ℝ and an open set O' such that χ is C^∞, χ has compact support, tsupport χ ⊆ O, 0 ≤ χ ≤ 1, K ⊆ O', and χ = 1 on O'.
2. (β is C^∞.) β = Λ ∘ γ ∘ pL, where Λ := ContinuousAlternatingMap.compContinuousLinearMapCLM pL : Λ^l(ℝ^m) → Λ^l(ℝ^P) is the continuous linear map α ↦ α.compContinuousLinearMap pL (compContinuousLinearMapCLM_apply). pL and Λ are continuous linear, hence C^∞, and γ is C^∞, so β is C^∞ (ContDiff.comp).
3. (Vanishing of β.) If pL x ∉ tsupport γ, then γ(pL x) = 0 (image_eq_zero_of_notMem_tsupport), so β(x)(v) = γ(pL x)(pL ∘ v) = 0 for every v, i.e. β(x) = 0.
4. (Definition of γ'; property (a).) Let g(x) := χ(x)·β(x). g is C^∞ as the product of the C^∞ function χ and the C^∞ form β (ContDiff.smul); g has compact support because χ does (HasCompactSupport.smul_right); and tsupport g ⊆ tsupport χ ⊆ O (tsupport_smul_subset_left). Hence g is a C^∞ compactly supported l-form with tsupport g ⊆ univ, i.e. γ' := g ∈ TestFormOn univ l, and (a) holds.
5. (Absolute homogeneity of the coefficient norm.) For c ∈ ℝ and an l-covector α on ℝ^P, each coefficient satisfies (cα)(e_{I(1)}, …, e_{I(l)}) = c·α(e_{I(1)}, …, e_{I(l)}), so the sum of squares defining |cα|² is c² times the one defining |α|²; as √(c²X) = √(c²)·√X = |c|·√X for X ≥ 0 (Real.sqrt_mul, Real.sqrt_sq_eq_abs), |cα| = |c|·|α|.
6. (Property (b).) For every x: |γ'(x)| = |χ(x)β(x)| = |χ(x)|·|β(x)| = χ(x)·|β(x)| ≤ |β(x)|, by step 5, 0 ≤ χ(x) ≤ 1 and |β(x)| ≥ 0 (covectorEuclideanNorm_nonneg).
7. (Property (c).) Let x ∈ S. If x ∈ O', then χ(x) = 1 and γ'(x) = β(x). If x ∉ O', then x ∉ K (because K ⊆ O'); since x ∈ S, this means pL x ∉ tsupport γ, so β(x) = 0 by step 3 and γ'(x) = χ(x)·0 = 0 = β(x).
8. (Property (d) at x ∈ S ∩ O'.) O' is an open neighbourhood of x on which χ = 1, so g = β on O', i.e. g =ᶠ[𝓝 x] β. The exterior derivative at a point depends only on the germ of the form there (it is alternatizeUncurryFin of fderiv, and fderiv depends only on the germ: Filter.EventuallyEq.extDeriv_eq), so dγ'(x) = dβ(x). By naturality of d under pull-back (extDeriv_pullback with f := pL and smoothness order r := ∞ ≥ minSmoothness ℝ 2 = 2; γ is differentiable at pL x, pL is C^∞, and fderiv ℝ pL x = pL by ContinuousLinearMap.fderiv), dβ(x) = ((dγ)(pL x)).compContinuousLinearMap pL = (p^#(dγ))(x). Hence (d) holds at x.
9. (Property (d) at x ∈ S ∖ O'.) As in step 7, pL x ∉ tsupport γ. The set V := (tsupport γ)ᶜ is open (tsupport γ is closed), contains pL x, and γ = 0 on V. Hence pL⁻¹(V) is an open neighbourhood of x (pL is continuous) on which β = 0 (step 3) and therefore g = χ·0 = 0. Thus g =ᶠ[𝓝 x] 0 and γ =ᶠ[𝓝 (pL x)] 0, and by locality (as in step 8) dγ'(x) = d(0)(x) and (dγ)(pL x) = d(0)(pL x). The exterior derivative of the zero form vanishes (the derivative of a constant is 0 and alternatizeUncurryFin is linear), so dγ'(x) = 0 and (p^#(dγ))(x) = 0.compContinuousLinearMap pL = 0. Hence (d) holds at x.
10. Steps 4, 6, 7, 8 and 9 prove (a), (b), (c) and (d) for γ'. ∎

Formalization aid (not part of the mathematical argument). During decomposition, the following proof of exactly this frozen type was compiled in the contract scope (after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s; Lean v4.35.0-rc3, Mathlib 25730c7c), using only the sibling declarations named in it and the standard axioms [propext, Classical.choice, Quot.sound]. It passes the leaf rule (one appended theorem, no helper declarations) and may be used directly or adapted:
```lean
theorem Submission.cbr_ci_pw_proj_pullback_extension : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (S O : Set (Euclid P)) (γ : DifferentialForm (Euclid m) l), ContDiff ℝ (⊤ : ℕ∞) γ → IsOpen O → IsCompact (S ∩ pL ⁻¹' tsupport γ) → S ∩ pL ⁻¹' tsupport γ ⊆ O → ∃ γ' : TestFormOn (univ : Set (Euclid P)) l, tsupport (γ' : DifferentialForm (Euclid P) l) ⊆ O ∧ (∀ x, covectorEuclideanNorm ((γ' : DifferentialForm (Euclid P) l) x) ≤ covectorEuclideanNorm ((γ (pL x)).compContinuousLinearMap pL)) ∧ (∀ x ∈ S, (γ' : DifferentialForm (Euclid P) l) x = (γ (pL x)).compContinuousLinearMap pL) ∧ ∀ x ∈ S, exteriorDerivative (γ' : DifferentialForm (Euclid P) l) x = (exteriorDerivative γ (pL x)).compContinuousLinearMap pL := by
  intro P m l pL S O γ hγ hO hK hKO
  obtain ⟨χ, O', hχ, hχc, hχO, hχ01, hO', hKO', hχ1⟩ :=
    Submission.cbr_ci_pw_proj_smooth_cutoff P _ O hK hO hKO
  set β : DifferentialForm (Euclid P) l := fun x => (γ (pL x)).compContinuousLinearMap pL with hβdef
  have hβ : ContDiff ℝ (⊤ : ℕ∞) β := by
    have := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin l) (F := ℝ) pL).contDiff
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) |>.comp (hγ.comp pL.contDiff)
    simpa [Function.comp_def] using this
  set g : DifferentialForm (Euclid P) l := fun x => χ x • β x with hgdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hχ.smul hβ
  have hgc : HasCompactSupport g := hχc.smul_right
  have hgs : tsupport g ⊆ tsupport χ := tsupport_smul_subset_left _ _
  let γ' : TestFormOn (univ : Set (Euclid P)) l := ⟨g, ⟨⟨hg, hgc⟩, subset_univ _⟩⟩
  -- vanishing of β off pL⁻¹(tsupport γ)
  have hβ0 : ∀ x, pL x ∉ tsupport γ → β x = 0 := by
    intro x hx
    ext v
    simp [hβdef, image_eq_zero_of_notMem_tsupport hx]
  -- scaling of the coefficient norm
  have hscale : ∀ (c : ℝ) (α : Covector (Euclid P) l),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    have : (∑ I : Fin l → Fin P, if StrictMono I then
          ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) =
        c ^ 2 * ∑ I : Fin l → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs <;> simp [mul_pow]
    rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  refine ⟨γ', hgs.trans hχO, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · change covectorEuclideanNorm (χ x • β x) ≤ covectorEuclideanNorm (β x)
    rw [hscale, abs_of_nonneg (hχ01 x).1]
    exact mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2
  · change χ x • β x = β x
    by_cases hxO' : x ∈ O'
    · rw [hχ1 x hxO', one_smul]
    · have : pL x ∉ tsupport γ := fun h => hxO' (hKO' ⟨hx, h⟩)
      rw [hβ0 x this, smul_zero]
  · change extDeriv g x = (extDeriv γ (pL x)).compContinuousLinearMap pL
    by_cases hxO' : x ∈ O'
    · have hev : g =ᶠ[𝓝 x] β := by
        filter_upwards [hO'.mem_nhds hxO'] with y hy
        simp [hgdef, hχ1 y hy]
      rw [hev.extDeriv_eq]
      have hpb := extDeriv_pullback (x := x) (ω := γ) (f := ⇑pL) (r := ((⊤ : ℕ∞) : WithTop ℕ∞))
        ((hγ.differentiable (by simp)).differentiableAt) pL.contDiff.contDiffAt (by simp)
      simpa [ContinuousLinearMap.fderiv] using hpb
    · have hxK : pL x ∉ tsupport γ := fun h => hxO' (hKO' ⟨hx, h⟩)
      have hopen : IsOpen ((tsupport γ)ᶜ) := (isClosed_tsupport γ).isOpen_compl
      have hev : g =ᶠ[𝓝 x] 0 := by
        filter_upwards [(hopen.preimage pL.continuous).mem_nhds hxK] with y hy
        simp [hgdef, hβ0 y hy]
      have hev' : γ =ᶠ[𝓝 (pL x)] 0 := by
        filter_upwards [hopen.mem_nhds hxK] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      rw [hev.extDeriv_eq, hev'.extDeriv_eq]
      ext v
      simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
```

## Key steps

1. smooth_cutoff applied to the compact K = S ∩ pL⁻¹(tsupport γ) ⊆ O gives χ ∈ C_c^∞ with tsupport χ ⊆ O, 0 ≤ χ ≤ 1 and χ ≡ 1 on an open O' ⊇ K.
2. β = p^#γ = compContinuousLinearMapCLM pL ∘ γ ∘ pL is C^∞ and vanishes wherever pL x ∉ tsupport γ; γ' := χ·β is a test form on ℝ^P with tsupport γ' ⊆ O.
3. |χβ| = χ|β| ≤ |β| because the coefficient norm is absolutely homogeneous.
4. On S: γ' = β (χ = 1 on O', and β = 0 at points of S outside O').
5. On S ∩ O', γ' = β near x, so dγ'(x) = dβ(x) = p^#(dγ)(x) by locality and extDeriv_pullback; on S ∖ O', γ' and γ vanish near x and pL x, so both sides are 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `sed of SimonGMT Chapter06 Forms.lean, Currents.lean, Mass.lean, FormSupNorm.lean in lake-packages-25730c7c/simongmt (DifferentialForm, exteriorDerivative = extDeriv, TestFormOn, TestFormOnConverges, GeometricCurrentOn, boundary_apply, exteriorDerivativeTestOn, covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn)`
- `rg -n in local-references/123e8435b4a2469b/mathlib/Mathlib: extDeriv_pullback (Analysis/Calculus/DifferentialForm/Basic.lean:259), Filter.EventuallyEq.extDeriv_eq (:188), exists_contDiff_support_eq_eq_one_iff (Geometry/Manifold/PartitionOfUnity.lean:789), IsCompact.exists_cthickening_subset_open (Topology/MetricSpace/Thickening.lean:426), IsCompact.cthickening (:283), closure_thickening_subset_cthickening (:293), compContinuousLinearMapCLM (Topology/Algebra/Module/Alternating/Topology.lean:281), ContinuousAlternatingMap.le_opNorm (Analysis/Normed/Module/Alternating/Basic.lean:212), isBoundedBilinearMap_apply (Analysis/Normed/Operator/BoundedLinearMaps.lean:391), Continuous.comp_aestronglyMeasurable (MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:233), norm_iteratedFDeriv_zero (Analysis/Calculus/ContDiff/FTaylorSeries.lean:823), iteratedFDeriv_zero (Analysis/Calculus/ContDiff/Basic.lean:75), enorm_integral_le_lintegral_enorm and norm_integral_le_of_norm_le (MeasureTheory/Integral/Bochner/Basic.lean:333, 985), setIntegral_congr_fun and integral_indicator (MeasureTheory/Integral/Bochner/Set.lean:73, 185), lintegral_indicator_one (MeasureTheory/Integral/Lebesgue/Basic.lean:572), tsupport_smul_subset_left and HasCompactSupport.smul_right (Topology/Algebra/Support.lean:168, 466)`
- `rg -n 'add_compContinuousLinearMap|zero_compContinuousLinearMap|theorem extDeriv_zero' in the Mathlib snapshot: no match (the proofs use ext/congr instead)`
- `rg -n 'compContinuousLinearMap|extDeriv_pullback|exists_contDiff_support_eq_eq_one_iff|massAdmissibleOn' in local-references/123e8435b4a2469b/project/GMT: no match (no project lemma to reuse)`
- `python3 -I scans of dag.json: no lean_name with prefix cbr_ci_pw_proj_ except the selected parent cbr_ci_pw_projected_current; existing cutoff/pull-back declarations (dgcr_bwd_normal_cutoff, rsd_mw_tfa_smooth_cutoff, cbr_rlim_smooth_cutoff, dor_lmb_fc_dtop_cutoff_pullback, ...) have different frozen types, so none is reusable; selected node depth 5, depends_on covector_bounds-a1 (cbr_ci_pw_orthonormal_covector_bounds)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _solve_children, _existing_lean_name_problem, _overlay_accepted_children), leaf_verification.py check_source_delta, prompts.py DECOMPOSITION_AUDIT; verifier/gmt-compare.py contract_scope and child_modules; verifier/lean_contract.py validate_lean_statement; swarm-project.json (max_depth 6, max_children 12, max_nodes 5000)`
- `lake env lean /tmp/proj-decomp-b5/Children.lean, A.lean, B.lean, C1.lean, C2.lean, D.lean, E.lean, All.lean (#print axioms) and /tmp/proj-decomp-b5/cmp/NodeChallenges.lean (comparator-replayed scope); extracted check_source_delta run on each child proof`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-35232fb38e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-35232fb38e/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/tmp/proj-decomp-b5/All.lean`
- `/tmp/proj-decomp-b5/cmp/NodeChallenges.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). Every Mathlib lemma the child proofs use exists in the snapshot at the paths and lines listed. Mathlib has no lemma for add or zero of compContinuousLinearMap or for extDeriv of the zero form; the proofs handle these with ext/congr. The project snapshot has no lemma to reuse. Apart from the parent, no DAG declaration has the prefix cbr_ci_pw_proj_, so the six names are fresh. No accepted cutoff or pull-back declaration has an identical frozen type, so none is reused. The runtime caps depth at 6, so these depth-6 children are leaves (one appended theorem each). All six child types elaborate in the comparator's replayed contract scope and pass validate_lean_statement. Complete Lean proofs of all six compile with only [propext, Classical.choice, Quot.sound] and pass check_source_delta. The parent assembly compiles against them and the covector_bounds type; its only sorryAx comes from that placeholder.
