# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.coeff_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 8 of the supplied proof of chart_perimeter ("every entry of M_w has absolute value ≤ 1 (|φ| ≤ 1 and |Ae_i| ≤ ‖A‖ ≤ 1), so |det M_w| ≤ (n+1)! (Matrix.det_le) … covectorEuclideanNorm(ω_φ(w)) ≤ (P^n((n+1)!)²)^{1/2} = c₀"). Departure (library gap only): Matrix.det_le lives in Mathlib.LinearAlgebra.Matrix.AbsoluteValue, which is not in the import closure of GMT.Ch07.Submission (#check Matrix.det_le: unknown constant), so step 1 below proves the same entrywise determinant bound from the Leibniz formula. The factor ζ(w) ∈ [0, 1] of the supplied proof is absorbed into p (test_form applies this lemma with p = ζ(w)φ(π(w)), |p| ≤ 1).

Proof.
1. (Leibniz bound.) Let m ∈ ℕ and let M be a real m×m matrix with |M_{r,c}| ≤ 1 for all r, c. By the Leibniz formula (Matrix.det_apply), det M = Σ_{σ ∈ Perm(Fin m)} sign(σ)·Π_i M_{σ(i), i}. By the triangle inequality (Finset.abs_sum_le_sum_abs), |det M| ≤ Σ_σ |sign(σ)|·|Π_i M_{σ(i),i}|. Here sign(σ) = ±1 (Int.units_eq_one_or), so |sign(σ)| = 1, and |Π_i M_{σ(i),i}| = Π_i |M_{σ(i),i}| ≤ 1 (Finset.abs_prod, Finset.prod_le_one₀). Hence |det M| ≤ Σ_σ 1 = |Perm(Fin m)| = m! (Fintype.card_perm).
2. (Coefficients as determinants.) Fix I : Fin n → Fin P and write e_i := EuclideanSpace.basisFun (Fin P) ℝ i (the unit vectors of ℝ^P). By hypothesis α(e_{I(0)}, …, e_{I(n−1)}) = det M^I, where M^I_{r,0} = p_r and M^I_{r,k+1} = (A e_{I(k)})_r.
3. (Entry bounds.) For a vector y ∈ ℝ^m and every coordinate r, |y_r| ≤ |y| (PiLp.norm_apply_le). Distinguish the column index (Fin.cases): for column 0, |M^I_{r,0}| = |p_r| ≤ |p| ≤ 1; for column k+1, |M^I_{r,k+1}| ≤ |A e_{I(k)}| ≤ ‖A‖·|e_{I(k)}| = ‖A‖ ≤ 1 (ContinuousLinearMap.le_opNorm and |e_i| = 1).
4. (Each coefficient.) By steps 1–3 with m = n + 1, |α(e_{I(0)}, …, e_{I(n−1)})| ≤ (n+1)! for every I : Fin n → Fin P; hence α(e_{I(0)}, …, e_{I(n−1)})² ≤ ((n+1)!)² (sq_le_sq').
5. (Summation.) By definition covectorEuclideanNorm(α) = √(Σ_{I : Fin n → Fin P} s_I) with s_I = α(e_{I(0)}, …, e_{I(n−1)})² if I is strictly increasing and s_I = 0 otherwise. By step 4 (and 0 ≤ ((n+1)!)²) every s_I ≤ ((n+1)!)², and there are |Fin n → Fin P| = P^n indices I (Fintype.card_fun, Fintype.card_fin). By monotonicity of the square root (Real.sqrt_le_sqrt), covectorEuclideanNorm(α) ≤ √(P^n·((n+1)!)²) = (n+1)!·√(P^n) (Real.sqrt_mul with P^n ≥ 0, Real.sqrt_sq with (n+1)! ≥ 0). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the contract). The declaration below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b366308 when placed after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the frozen contract's `open` commands (both inside and outside a `noncomputable section`), and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.codim1_lur_det_covector_norm_le : ∀ (P n : ℕ) (A : Euclid P →L[ℝ] Euclid (n + 1)) (p : Euclid (n + 1)) (α : Covector (Euclid P) n), ‖A‖ ≤ 1 → ‖p‖ ≤ 1 → (∀ a : Fin n → Euclid P, α a = Matrix.det (Matrix.of fun r c : Fin (n + 1) => (Fin.cons p (fun k : Fin n => A (a k)) : Fin (n + 1) → Euclid (n + 1)) c r)) → covectorEuclideanNorm α ≤ ((n + 1).factorial : ℝ) * Real.sqrt ((P : ℝ) ^ n) := by
  intro P n A p α hA hp hα
  -- (1) Leibniz: a square matrix with entries of absolute value ≤ 1 has |det| ≤ m!
  have hleib : ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) ℝ), (∀ r c, |M r c| ≤ 1) → |M.det| ≤ (m.factorial : ℝ) := by
    intro m M hM
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i, M (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin m), |Equiv.Perm.sign σ • ∏ i, M (σ i) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin m), (1 : ℝ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [Units.smul_def, zsmul_eq_mul, abs_mul]
          have hs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [hs, one_mul, Finset.abs_prod]
          exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => hM _ _)
      _ = (m.factorial : ℝ) := by
          simp [Finset.card_univ, Fintype.card_perm]
  -- (2) every coefficient is bounded by (n+1)!
  have hcoef : ∀ I : Fin n → Fin P,
      |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ ((n + 1).factorial : ℝ) := by
    intro I
    rw [hα]
    apply hleib
    intro r c
    refine Fin.cases ?_ (fun k => ?_) c
    · simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le p r).trans hp
    · simp only [Matrix.of_apply, Fin.cons_succ]
      have h1 := PiLp.norm_apply_le (A (EuclideanSpace.basisFun (Fin P) ℝ (I k))) r
      have h2 : ‖A (EuclideanSpace.basisFun (Fin P) ℝ (I k))‖ ≤ 1 := by
        calc ‖A (EuclideanSpace.basisFun (Fin P) ℝ (I k))‖
            ≤ ‖A‖ * ‖EuclideanSpace.basisFun (Fin P) ℝ (I k)‖ := A.le_opNorm _
          _ = ‖A‖ := by simp
          _ ≤ 1 := hA
      rw [← Real.norm_eq_abs]
      exact h1.trans h2
  -- (3) sum over the P^n coordinate tuples
  unfold covectorEuclideanNorm
  have hF : (0 : ℝ) ≤ ((n + 1).factorial : ℝ) := by positivity
  calc Real.sqrt (∑ I : Fin n → Fin P, if StrictMono I then
        (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
      ≤ Real.sqrt (∑ _I : Fin n → Fin P, ((n + 1).factorial : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        refine Finset.sum_le_sum fun I _ => ?_
        split_ifs
        · exact sq_le_sq' (abs_le.1 (hcoef I)).1 (abs_le.1 (hcoef I)).2
        · positivity
    _ = ((n + 1).factorial : ℝ) * Real.sqrt ((P : ℝ) ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq hF, mul_comm]
        push_cast
        ring
```

## Key steps

1. Leibniz formula: a real m×m matrix with entries of absolute value ≤ 1 has |det| ≤ m!.
2. α(e_I) = det[p, Ae_{I(0)}, …, Ae_{I(n−1)}], whose entries are bounded by |p| ≤ 1 and |Ae_i| ≤ ‖A‖ ≤ 1.
3. Hence every coefficient satisfies |α(e_I)| ≤ (n+1)!.
4. Summing at most P^n squares gives covectorEuclideanNorm(α) ≤ (n+1)!·√(P^n).

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
