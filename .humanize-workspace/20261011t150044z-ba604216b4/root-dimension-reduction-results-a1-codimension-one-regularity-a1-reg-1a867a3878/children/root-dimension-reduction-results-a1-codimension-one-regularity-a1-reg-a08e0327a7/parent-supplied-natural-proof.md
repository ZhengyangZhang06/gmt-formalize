# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.chart_geometry-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 1 of the supplied proof of chart_perimeter ("Aι = id, ‖A‖ ≤ 1 (A is the adjoint of an isometry), and for v ∈ D, π(G(v)) = v, p^⊥(G(v)) = u(v) and A∘DG(v) = id (u and Du take values in (range ι)^⊥)"), with the omitted details filled in. Only differentiability of u on D is needed (the parent has u ∈ C²(D), which implies it).

Proof.
1. ((i) ‖A‖ ≤ 1.) Taking adjoints is a linear isometric equivalence between operator spaces (ContinuousLinearMap.adjoint is a LinearIsometryEquiv; LinearIsometryEquiv.norm_map), so ‖A‖ = ‖ι‖; and ‖ι‖ ≤ 1 because ι is a linear isometry (LinearIsometry.norm_toContinuousLinearMap_le).
2. ((ii) Aι = id.) For z, w ∈ ℝ^{n+1}: ⟨A(ιz), w⟩ = ⟨ιz, ιw⟩ = ⟨z, w⟩ (ContinuousLinearMap.adjoint_inner_left; LinearIsometry.inner_map_map). Since this holds for every w, A(ιz) = z (ext_inner_right).
3. (A kills u on D.) For v ∈ D and every w: ⟨A(u(v)), w⟩ = ⟨u(v), ιw⟩ = ⟨ιw, u(v)⟩ = 0 (adjoint_inner_left, real_inner_comm, hypothesis). Hence A(u(v)) = 0.
4. ((iii) and (iv).) Let v ∈ D. Then G(v) − x = ιv + u(v), so A(G(v) − x) = A(ιv) + A(u(v)) = v + 0 = v by steps 2–3, and therefore G(v) − x − ιA(G(v) − x) = ιv + u(v) − ιv = u(v).
5. (The derivative of G.) D is open and v ∈ D, so D is a neighbourhood of v and u is differentiable at v (DifferentiableOn.differentiableAt). By the sum rule (the constant x has derivative 0 and the continuous linear map ι is its own derivative), G has derivative ι + Du(v) at v, so DG(v) = ι + Du(v).
6. (A∘Du(v) = 0.) The map g := A∘u vanishes on the neighbourhood D of v (step 3), so g has derivative 0 at v (hasFDerivAt_const and HasFDerivAt.congr_of_eventuallyEq). By the chain rule g also has derivative A∘Du(v) at v (A is continuous linear). By uniqueness of the Fréchet derivative (HasFDerivAt.unique), A∘Du(v) = 0.
7. ((v).) For y ∈ ℝ^{n+1}: A(DG(v)y) = A(ιy + Du(v)y) = A(ιy) + A(Du(v)y) = y + 0 = y by steps 2, 5 and 6. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the contract). The declaration below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b366308 when placed after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the frozen contract's `open` commands (both inside and outside a `noncomputable section`), and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.codim1_lur_graph_chart_adjoint_identities : ∀ (P n : ℕ) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ : ℝ), DifferentiableOn ℝ u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap‖ ≤ 1 ∧ (∀ z : Euclid (n + 1), ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι z) = z) ∧ ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ContinuousLinearMap.adjoint ι.toContinuousLinearMap (x + ι v + u v - x) = v ∧ x + ι v + u v - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (x + ι v + u v - x)) = u v ∧ ∀ y : Euclid (n + 1), ContinuousLinearMap.adjoint ι.toContinuousLinearMap (fderiv ℝ (fun y => x + ι y + u y) v y) = y := by
  intro P n x ι u δ₁ hu horth
  set A := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hAdef
  -- (1) ‖ι*‖ = ‖ι‖ ≤ 1
  have hA : ‖A‖ ≤ 1 := by
    rw [hAdef, LinearIsometryEquiv.norm_map]
    exact ι.norm_toContinuousLinearMap_le
  -- (2) ι*ι = id
  have hAι : ∀ z, A (ι z) = z := by
    intro z
    apply ext_inner_right ℝ
    intro w
    rw [hAdef, ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map z w
  -- (3) ι* kills the normal values u(v)
  have hAu : ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, A (u v) = 0 := by
    intro v hv
    apply ext_inner_right ℝ
    intro w
    rw [hAdef, ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact horth v hv w
  refine ⟨hA, hAι, fun v hv => ?_⟩
  have hsub : x + ι v + u v - x = ι v + u v := by abel
  have hπ : A (x + ι v + u v - x) = v := by
    rw [hsub, map_add, hAι, hAu v hv, add_zero]
  refine ⟨hπ, ?_, fun y => ?_⟩
  · rw [hπ, hsub]; abel
  · -- (4) ι* ∘ DG(v) = id, since ι* ∘ u ≡ 0 on the open ball
    have hvn : ball (0 : Euclid (n + 1)) δ₁ ∈ 𝓝 v := isOpen_ball.mem_nhds hv
    have hud : DifferentiableAt ℝ u v := hu.differentiableAt hvn
    have hG : fderiv ℝ (fun y => x + ι y + u y) v = ι.toContinuousLinearMap + fderiv ℝ u v := by
      have h1 : HasFDerivAt (fun y => x + ι y + u y) (ι.toContinuousLinearMap + fderiv ℝ u v) v :=
        ((ι.toContinuousLinearMap.hasFDerivAt).const_add x).add hud.hasFDerivAt
      exact h1.fderiv
    have hAdu : A ∘L fderiv ℝ u v = 0 := by
      have h0 : (fun y => A (u y)) =ᶠ[𝓝 v] fun _ => (0 : Euclid (n + 1)) :=
        Filter.eventually_of_mem hvn fun z hz => hAu z hz
      have h2 : HasFDerivAt (fun y => A (u y)) (A ∘L fderiv ℝ u v) v :=
        A.hasFDerivAt.comp v hud.hasFDerivAt
      have h3 : HasFDerivAt (fun y => A (u y)) (0 : Euclid (n + 1) →L[ℝ] Euclid (n + 1)) v :=
        (hasFDerivAt_const (0 : Euclid (n + 1)) v).congr_of_eventuallyEq h0
      exact h2.unique h3
    have hAdu' : A (fderiv ℝ u v y) = 0 := by
      simpa using congrArg (fun L : Euclid (n + 1) →L[ℝ] Euclid (n + 1) => L y) hAdu
    rw [hG]
    show A (ι y + fderiv ℝ u v y) = y
    rw [map_add, hAdu', add_zero]
    exact hAι y
```

## Key steps

1. ‖ι*‖ = ‖ι‖ ≤ 1 and ⟨ι*ιz, w⟩ = ⟨ιz, ιw⟩ = ⟨z, w⟩, so ι*ι = id.
2. u(v) ⊥ range ι gives ι*u(v) = 0 on D; hence ι*(G(v) − x) = v and G(v) − x − ιι*(G(v) − x) = u(v).
3. DG(v) = ι + Du(v), and ι*∘u ≡ 0 on the open set D forces ι*∘Du(v) = 0.
4. Hence ι*(DG(v)y) = y.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C lake-packages-25730c7c/{mathlib,simongmt} rev-parse HEAD; python3 read of snapshot project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem det_succ_column_zero|theorem det_le |smoothTransition' <snapshot>/mathlib/Mathlib`
- `rg -n 'def curryLeft|def mkContinuous|compContinuousLinearMapCLM|continuous_of_finiteDimensional|toContinuousAlternatingMap' <snapshot>/mathlib/Mathlib/{Topology/Algebra/Module/Alternating,Analysis/Normed/Module/Alternating,LinearAlgebra/Alternating}`
- `rg -n 'volumeForm_robust|abs_volumeForm_apply_le' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean; rg -n 'adjoint_inner_left|norm_adjoint' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean; rg -n 'ContinuousOn.measurable_piecewise' <snapshot>/mathlib/Mathlib`
- `#check in the GMT.Ch07.Submission import closure: Matrix.det_le (unknown constant), Module.Basis.det, Matrix.det_apply, Fintype.card_perm, ContinuousAlternatingMap.curryLeft_apply_apply, Orientation.abs_volumeForm_apply_le, Orientation.volumeForm_robust', ContinuousOn.measurable_piecewise, Real.smoothTransition.contDiff, PiLp.norm_apply_le, MultilinearMap.continuous_of_finiteDimensional (unknown constant)`
- `grep -n '^theorem|^def|^abbrev|^structure' simongmt Chapter06/{Forms,Currents,Mass}.lean`
- `python3 scans of dag.json (902 then 983 nodes): frozen types of codim1_lur_chart_divergence_formula, dor_ims_massOn_le_measure and the selected node; accepted statements containing covectorEuclideanNorm, massOn with IsIntegerMultiplicity, R.measure … ≠ ∞, succAbove, Matrix.det; lean_name lookup of the five new names (no hits)`
- `grep -rl -E '<five new names>' runs/.../nodes runs/.../dag.json (no match); git for-each-ref | xargs -n 100 sh -c 'git grep -l -E "<five new names>" "$@" -- GMT/*.lean' (0 of 1695 ref tips; control cmr_abs_apply_le_massOn: 3 tips)`
- `git show {7a706164,702e7082,fae4fd1e}:GMT/Ch07/Submission.lean > Cand_*.lean; diff against GMT/Ch07/Contract.lean (additions only); '#print axioms' for cmr_abs_apply_le_massOn, rsd_imrep_compact_measure_ne_top, dor_ims_massOn_le_measure`
- `lean -DautoImplicit=false (LEAN_PATH from 'lake env printenv LEAN_PATH') /tmp/cpsplit/final/{Types,Inst,Assembly,FullChain,FullChainNoSection}.lean, /tmp/cpsplit/proto/{Laplace,DetCov,Coeff,Chart,TestForm}.lean, /tmp/cpsplit/out/Appendices.lean`
- `sed -n 560,640p book/chapter-06.txt (Simon 6.2.34–2.35); grep -n '( 1)j aj dx|!j  D ( 1)j 1' book/chapter-06.txt`
- `read nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-{1a867a3878,5d8d9c70c5}/ (handoff, supplied proof, decomposition-v1.json) and the handoffs/accepted-candidate.json of the two reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1a867a3878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1a867a3878/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cpsplit/final/Types.lean`
- `/tmp/cpsplit/final/Inst.lean`
- `/tmp/cpsplit/final/Assembly.lean`
- `/tmp/cpsplit/final/FullChain.lean`
- `/tmp/cpsplit/final/FullChainNoSection.lean`
- `/tmp/cpsplit/out/Appendices.lean`
- `/tmp/cpsplit/reuse/Cand_cmr_abs_apply_le_massOn.lean`
- `/tmp/cpsplit/reuse/Cand_rsd_imrep_compact_measure_ne_top.lean`
- `/tmp/cpsplit/reuse/Cand_dor_ims_massOn_le_measure.lean`

Pins match.
- Snapshot manifest: project b4d606db, Mathlib 25730c7c; both equal workspace HEAD and the lake package checkout (lake-packages-25730c7c/mathlib).
- simongmt is 2b366308 in both the snapshot lake-manifest and the package checkout.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library (what exists).
- In the import closure: Matrix.det_succ_column_zero; Matrix.det_apply with Fintype.card_perm (Leibniz); Module.Basis.det.
- Also present: Orientation.volumeForm_robust' and Orientation.abs_volumeForm_apply_le (Hadamard).
- Alternating-map API: AlternatingMap.mkContinuous, ContinuousAlternatingMap.curryLeft and compContinuousLinearMapCLM.
- Analysis: Real.smoothTransition (ContDiff of every order, values in [0, 1]); ContinuousLinearMap.adjoint_inner_left; ContinuousOn.measurable_piecewise.
- SimonGMT Chapter06 supplies Covector, DifferentialForm, TestFormOn, covectorEuclideanNorm, massAdmissibleOn and GeometricCurrentOn.le_massOn.

Library (what is missing).
- Matrix.det_le (Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean) and MultilinearMap.continuous_of_finiteDimensional are not in the import closure; Lean reports unknown constant.
- coeff_bound therefore proves the entrywise bound from the Leibniz formula, and det_covector obtains continuity from Hadamard's inequality.

DAG.
- Accepted declarations reused with byte-identical types:
  - rsd_imrep_compact_measure_ne_top (candidate 702e7082);
  - cmr_abs_apply_le_massOn (candidate 7a706164).
- Each candidate file only adds to Contract.lean. A fresh compile of each prints only propext, Classical.choice and Quot.sound, as it does for dor_ims_massOn_le_measure (fae4fd1e).
- The five new names occur in no dag.json node (983 nodes), no nodes/ file, and no GMT/*.lean at any of the 1695 ref tips.

Lean.
- Types.lean elaborates all 7 child types after import GMT.Ch07.Submission with the contract opens.
- Inst.lean confirms the matrix-column, coordinate, indicator, adjoint and smoothness-order conventions by rfl.
- Assembly.lean proves the frozen selected type from test_form and the two reused declarations, with chart_divergence and mass_upper_bound as axioms; no sorryAx occurs.
- FullChain.lean proves all five new children and then the selected theorem. Each new child depends only on the standard axioms; the selected theorem adds exactly its two resolved dependencies and the two reused declarations. The same holds with no enclosing noncomputable section.
- An independent review subagent re-ran these files and accepted the split.
