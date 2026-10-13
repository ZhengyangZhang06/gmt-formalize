# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.det_laplace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 6 of the supplied proof of chart_perimeter: the expansion of det[φ(v), e_{j.succAbove 0}, …, e_{j.succAbove(n−1)}] along its first column (Matrix.det_succ_column_zero), "only the row-j term survives (every other minor contains the zero row j) and its minor is the identity". It is the coordinate form of the identity ω = Σ_j (−1)^{j−1} a_j dx^1 ∧ … ∧ \hat{dx^j} ∧ … ∧ dx^n of Simon Ch. 6, 2.34–2.35 (book/chapter-06.txt lines 594–595 and 625–626; 2.35 prints the sign as (−1)^j, a misprint, since dω = div a dx^1 ∧ … ∧ dx^n requires (−1)^{j−1} as in the proof of 2.34), written with indices counted from 0, where the sign becomes (−1)^j.

Proof.
1. (Entries.) By the definition of the standard basis vectors (EuclideanSpace.single; PiLp.single_apply), M_{r,0} = p_r, and M_{r,k+1} = 1 if r = j.succAbove k and M_{r,k+1} = 0 otherwise.
2. (Expansion along column 0.) By the Laplace expansion along the first column (Matrix.det_succ_column_zero), det M = Σ_{i=0}^{n} (−1)^i M_{i,0} det N_i = Σ_{i=0}^{n} (−1)^i p_i det N_i, where N_i is the n×n matrix obtained from M by deleting row i and column 0: (N_i)_{r,k} = M_{i.succAbove r, k+1}, which by step 1 equals 1 if i.succAbove r = j.succAbove k and 0 otherwise.
3. (The term i = j.) (N_j)_{r,k} = 1 if j.succAbove r = j.succAbove k and 0 otherwise. Since j.succAbove is injective, this is 1 if r = k and 0 otherwise. So N_j is the identity matrix and det N_j = 1 (Matrix.det_one).
4. (The terms i ≠ j.) Let i ≠ j. Since j ≠ i, j lies in the range of i.succAbove (Fin.exists_succAbove_eq): j = i.succAbove r₀ for some r₀ ∈ {0, …, n−1}. Row r₀ of N_i is (N_i)_{r₀,k} = [j = j.succAbove k], and j.succAbove k ≠ j for every k (Fin.succAbove_ne); so row r₀ of N_i is zero. A square matrix with a zero row has determinant 0 (Matrix.det_eq_zero_of_row_eq_zero), hence det N_i = 0.
5. (Conclusion.) By steps 3–4, in the sum of step 2 only the term i = j is nonzero (Finset.sum_eq_single), so det M = (−1)^j p_j · 1 = (−1)^j p_j. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the contract). The declaration below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b366308 when placed after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the frozen contract's `open` commands (both inside and outside a `noncomputable section`), and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.codim1_lur_det_laplace_first_column : ∀ (n : ℕ) (p : Euclid (n + 1)) (j : Fin (n + 1)), Matrix.det (Matrix.of fun r c : Fin (n + 1) => (Fin.cons p (fun k : Fin n => EuclideanSpace.single (j.succAbove k) (1 : ℝ)) : Fin (n + 1) → Euclid (n + 1)) c r) = (-1 : ℝ) ^ (j : ℕ) * p j := by
  intro n p j
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single j]
  · -- the surviving term: the minor is the identity
    have hminor : ((Matrix.of fun r c : Fin (n + 1) => (Fin.cons p (fun k : Fin n => EuclideanSpace.single (j.succAbove k) (1 : ℝ)) : Fin (n + 1) → Euclid (n + 1)) c r).submatrix j.succAbove Fin.succ) = 1 := by
      ext r k
      simp [Matrix.submatrix_apply, Matrix.one_apply, PiLp.single_apply]
    rw [hminor, Matrix.det_one]
    simp
  · intro i _ hij
    -- row `r₀` with `i.succAbove r₀ = j` of the minor vanishes
    obtain ⟨r₀, hr₀⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    have hzero : ((Matrix.of fun r c : Fin (n + 1) => (Fin.cons p (fun k : Fin n => EuclideanSpace.single (j.succAbove k) (1 : ℝ)) : Fin (n + 1) → Euclid (n + 1)) c r).submatrix i.succAbove Fin.succ).det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero r₀
      intro k
      simp [Matrix.submatrix_apply, hr₀]
    rw [hzero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h
```

## Key steps

1. Laplace expansion along column 0: det M = Σ_i (−1)^i p_i det N_i, where (N_i)_{r,k} = [i.succAbove r = j.succAbove k].
2. N_j is the identity matrix because j.succAbove is injective.
3. For i ≠ j, writing j = i.succAbove r₀, row r₀ of N_i is zero, so det N_i = 0.
4. Hence det M = (−1)^j p_j.

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
