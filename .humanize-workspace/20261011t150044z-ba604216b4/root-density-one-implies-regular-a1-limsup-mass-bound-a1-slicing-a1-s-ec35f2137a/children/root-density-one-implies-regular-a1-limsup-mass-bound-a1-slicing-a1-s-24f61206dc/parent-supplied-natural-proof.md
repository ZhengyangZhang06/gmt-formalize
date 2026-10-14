# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1.gram_cofactor-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 6 (the Jacobian identity |G(Φ(w))|·JΦ(w) = JΦ_s(z)), in the straightened coordinates of parent step 2 with the distinguished coordinate placed first (i = 0): a_l = DΦ(w)e_l and u = G(Φ(w)). The supplied proof obtains it from the Gram determinant formula (Gram determinant of n+1 vectors = Gram determinant of n of them times the squared distance of the remaining one to their span) and dist(a_0, span{a_1, …, a_n}) = 1/|u|. Departure: the same squared identity det Gram(a_1, …, a_n) = |u|²·det Gram(a_0, …, a_n) is proved here directly by the cofactor (Cramer) formula; this needs no orthogonal projection and no linear independence.

Notation. A := [⟨a_i, a_j⟩]_{i,j=0}^{n} (Matrix.of fun i j => inner ℝ (a i) (a j)), A' := [⟨a_{i+1}, a_{j+1}⟩]_{i,j=0}^{n−1} (for n = 0 the empty matrix, determinant 1), δ := (1, 0, …, 0) ∈ ℝ^{n+1} (Pi.single 0 1). The real inner product is symmetric and bilinear.

1. (Coefficients.) Since u ∈ span{a_0, …, a_n}, there is c ∈ ℝ^{n+1} with u = Σ_{l=0}^{n} c_l a_l (Submodule.mem_span_range_iff_exists_fun).
2. (Dual relations.) ⟨u, a_i⟩ = δ_i for every i ∈ {0, …, n}: for i = 0 this is the hypothesis ⟨u, a_0⟩ = 1, and for i = k+1 it is the hypothesis ⟨u, a_{k+1}⟩ = 0 (case split Fin.cases).
3. (A·c = δ.) For every i: (A c)_i = Σ_j ⟨a_i, a_j⟩ c_j = ⟨a_i, Σ_j c_j a_j⟩ = ⟨a_i, u⟩ = ⟨u, a_i⟩ = δ_i, by step 1, symmetry and step 2.
4. (|u|² = c_0.) |u|² = ⟨u, u⟩ = ⟨Σ_l c_l a_l, u⟩ = Σ_l c_l ⟨a_l, u⟩ = Σ_l c_l δ_l = c_0 (steps 1 and 2).
5. (Adjugate.) For every square matrix, adj(A)·A = det(A)·I (Matrix.adjugate_mul). Applying this to c and using step 3: adj(A)·δ = adj(A)·(A·c) = (adj(A)·A)·c = det(A)·c. The 0-th entry of adj(A)·δ is Σ_j adj(A)_{0j} δ_j = adj(A)_{00}; hence adj(A)_{00} = det(A)·c_0.
6. (Cofactor.) By the cofactor description of the adjugate (Matrix.adjugate_fin_succ_eq_det_submatrix), adj(A)_{00} = (−1)^{0+0}·det(A.submatrix (Fin.succAbove 0) (Fin.succAbove 0)). Since Fin.succAbove 0 = Fin.succ, the submatrix has entries A_{i+1, j+1} = ⟨a_{i+1}, a_{j+1}⟩, i.e. it is A'. So adj(A)_{00} = det A'.
7. (Conclusion.) By steps 6, 5 and 4: det A' = det(A)·c_0 = c_0·det A = |u|²·det A, which is the claim Matrix.det (Matrix.of fun i j : Fin n => ⟨a i.succ, a j.succ⟩) = ‖u‖² · Matrix.det (Matrix.of fun i j => ⟨a i, a j⟩). ∎

Formal check (scratch validation by the decomposition author; not part of the frozen contract). The tactic proof below, for `theorem Submission.dor_lmbsf_pc_gram_det_succ_eq : <exactly the frozen lean_statement> := by`, compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c as a single theorem inserted into GMT/Ch07/Submission.lean (namespace GMT.Ch07, frozen imports only), with no helper declaration and no set_option; it also compiles under maxHeartbeats 70000, and the controller's leaf gate (leaf_verification.check_source_delta) accepts the insertion. #print axioms of the assembled selected theorem reports propext, Classical.choice and Quot.sound.
```lean
  intro P n a u hu h0 hk
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j => inner ℝ (a i) (a j) with hA
  have hua : ∀ i, inner ℝ u (a i) = (Pi.single 0 1 : Fin (n + 1) → ℝ) i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [h0]
    · simp [hk k, Fin.succ_ne_zero]
  have hAc : A.mulVec c = Pi.single 0 1 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    have : ∑ j, inner ℝ (a i) (a j) * c j = inner ℝ (a i) u := by
      rw [← hc, inner_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_smul_right]; ring
    rw [this, real_inner_comm, hua]
  have hnorm : ‖u‖ ^ 2 = c 0 := by
    rw [← real_inner_self_eq_norm_sq]
    calc inner ℝ u u = inner ℝ (∑ l, c l • a l) u := by rw [hc]
      _ = ∑ l, c l * inner ℝ (a l) u := by
          rw [sum_inner]; refine Finset.sum_congr rfl (fun l _ => ?_); rw [real_inner_smul_left]
      _ = c 0 := by
          have hl : ∀ l, inner ℝ (a l) u = (Pi.single 0 1 : Fin (n + 1) → ℝ) l := fun l => by
            rw [real_inner_comm, hua]
          simp_rw [hl]
          simp [Pi.single_apply]
  have hadj : A.adjugate.mulVec (A.mulVec c) = A.det • c := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hAc] at hadj
  have h00 := congrFun hadj 0
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.smul_apply, smul_eq_mul] at h00
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at h00
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul, Fin.succAbove_zero] at h00
  rw [hnorm, mul_comm, ← h00]
  rfl
```

## Key steps

1. Write u = Σ c_l a_l; then ⟨u, a_i⟩ = δ_{i0}, so the Gram matrix A satisfies A·c = δ and ‖u‖² = c_0.
2. adj(A)·A = det(A)·I applied to c gives adj(A)_{00} = det(A)·c_0.
3. The (0,0) cofactor of A is the determinant of the Gram matrix of a_1, …, a_n (Fin.succAbove 0 = Fin.succ).
4. Hence det Gram(a_1, …, a_n) = ‖u‖²·det Gram(a_0, …, a_n).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; python3 read of <snapshot>/project/lake-manifest.json; git rev-parse HEAD and git -C .lake/packages/{mathlib,simongmt} rev-parse HEAD`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `grep -n '^theorem' simongmt Chapter02/{WeightedArea,CoareaLinear,CoareaProjection,CoareaLinearAlgebra}.lean; cat Chapter02/{Area,AreaParametrization,WeightedArea,CoareaProjection,CoareaLinear}.lean; sed AreaApproximation.lean, AreaCritical.lean`
- `grep -rln 'coarea|Coarea|co-area' simongmt/Poincare/SimonGMT (only the Chapter02 linear and projection co-area files plus mentions in Chapter03; no nonlinear co-area formula)`
- `Lean probe after import GMT.Ch07.Submission in the contract scope: #check weighted_area_formula_of_injective_derivative, areaJacobianAt, LinearMap.normDet, Matrix.gram, ContDiffAt.toOpenPartialHomeomorph (unknown); lintegral_image_eq_lintegral_abs_det_fderiv_mul, HasStrictFDerivAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, Measurable.lintegral_prod_right', lintegral_iUnion, lintegral_tsum, MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurable_piecewise, measurable_fderiv, Matrix.det_succ_row_zero, TopologicalSpace.isOpen_iUnion_countable, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (available)`
- `grep -rnE 'theorem (adjugate_fin_succ_eq_det_submatrix|adjugate_mul |isOpen_iUnion_countable|Countable.exists_eq_range|eq_self_or_eq_succAbove|surjective_of_injective|Filter.EventuallyEq.fderiv_eq|measurable_fderiv |MeasurableSet.image_of_continuousOn_injOn|lintegral_iUnion |lintegral_tsum|Measurable.lintegral_prod_right'|ContinuousOn.measurable_piecewise|normDet_sq_eq_det_gram|lintegral_prod |lintegral_indicator )' <snapshot>/mathlib/Mathlib; grep 'volume_preserving_piFinSuccAbove|PiLp.volume_preserving_ofLp|PiLp.volume_preserving_toLp' <snapshot>/mathlib/Mathlib`
- `python3 -I scans of dag.json (1527 nodes): regex 'co-?area|Gram|straighten|implicit function|inverse function|Tonelli|areaJacobianAt|normDet|level set' over statements; accepted nodes matching 'Fin.cons|insertNth|piFinSuccAbove|∫⁻ t, ∫⁻|HasStrictFDerivAt|Pairwise|disjoint'; status and candidate_commit of codim1_lura_gram_area_formula, codim1_zsl_gc_local_inverse, codim1_lura_lintegral_image_eq_tsum_pieces, dtc_bc_lr_local_inverse; lean_name collision check for dor_lmbsf_pc_* (none); cross-parent reuse edges (562)`
- `git grep dor_lmbsf_pc_ over all refs (no match); git show 58ab3bbd:GMT/Ch07/Submission.lean (the proof base is the bare frozen contract)`
- `git show d5ba41d6:GMT/Ch07/Submission.lean and git show 013681e4:GMT/Ch07/Submission.lean, then lake env lean with #print axioms (propext, Classical.choice, Quot.sound); git log -1 d5ba41d6 (frozen-import leaf gate)`
- `read _recursive_lean/leaf_verification.py (check_source_delta), parent_verification.py, runtime.py (_existing_lean_name_problem, reuse of accepted children by lean_name), verifier/gmt-compare.py (contract_scope, child_modules), verifier/lean_contract.py`
- `lake env lean /tmp/pc-decomp/v1/{Types,Assembly,Leaves1,Leaves2,Leaves3}.lean, /tmp/pc-decomp/v2/Combined.lean, /tmp/pc-decomp/v2/cmp/*_Challenge.lean, /tmp/pc-decomp/v3/{Submission,SubmissionHB}.lean; python3 check_source_delta on each new leaf insertion`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-ec35f2137a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-db95546c3f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2511ff6312/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/runtime.py`
- `/tmp/pc-decomp/v1/Types.lean`
- `/tmp/pc-decomp/v1/Assembly.lean`
- `/tmp/pc-decomp/v2/Combined.lean`
- `/tmp/pc-decomp/v3/Submission.lean`

Pins match. The snapshot manifest gives project b4d606d and Mathlib 25730c7c; its lake-manifest gives simongmt 2b366308. Workspace HEAD and .lake/packages agree. Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical.

What exists. Snapshot Mathlib has every library fact the children use:
- adjugate_mul and adjugate_fin_succ_eq_det_submatrix (LinearAlgebra/Matrix/Adjugate.lean:268, 366);
- volume_preserving_piFinSuccAbove (Constructions/Pi.lean:818);
- PiLp.volume_preserving_ofLp and PiLp.volume_preserving_toLp (Haar/InnerProductSpace.lean:134, 139);
- Measurable.lintegral_prod_right' and lintegral_prod (Measure/Prod.lean:123, 1009);
- lintegral_indicator and lintegral_iUnion (Lebesgue/Basic.lean:510, 597), and lintegral_tsum (Lebesgue/Add.lean:362);
- ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean:523) and MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821);
- measurable_fderiv (FDeriv/Measurable.lean:378) and Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:260);
- Fin.eq_self_or_eq_succAbove (Fin/Tuple/Basic.lean:841) and LinearMap.surjective_of_injective (FiniteDimensional/Basic.lean:291);
- TopologicalSpace.isOpen_iUnion_countable (Topology/Bases.lean:932) and Set.Countable.exists_eq_range (Set/Countable.lean:149).

What is missing. SimonGMT has no nonlinear co-area formula; Chapter02 has only the linear and projection co-area formulas. Its weighted area formula (WeightedArea.lean:76, 120), normDet and areaJacobianAt are not available under the frozen imports, and leaf proofs may not add imports (leaf_verification.check_source_delta). The child types therefore use Gram determinants.

DAG. Two accepted declarations are reused with byte-identical types: codim1_lura_gram_area_formula (candidate d5ba41d6) and codim1_zsl_gc_local_inverse (candidate 013681e4). Fresh compiles of both print only propext, Classical.choice and Quot.sound, and runtime._existing_lean_name_problem permits sharing accepted nodes. The six new dor_lmbsf_pc_* names occur in no dag.json node and in no ref. The related nodes dtc_bc_lc_sl_chart_coarea, dimred_cs_sos_spine_coarea and dtc_bc_lc_sl_coarea are unaccepted and have different types.

Lean. All 8 child types pass validate_lean_statement, and their gmt-compare challenge modules elaborate. The integrated /tmp/pc-decomp/v3/Submission.lean proves the exact frozen selected type from the reused proofs and from prototype proofs of all six new children, with axioms propext, Classical.choice and Quot.sound. Each new prototype passes check_source_delta and fits in 70000 heartbeats.
