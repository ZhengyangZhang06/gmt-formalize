# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_triangle-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof's repeated use of “M_G(A ± B) ≤ M_G(A) + M_G(B) for open G (definition of M_G)” — sibling-fact paragraph (F4) and steps 4(b), 6, 8 and 9 — with the identity required only for forms supported in G, as step 9 needs (there Z(ω) = S(ω) − S̃(ω) holds only for tsupport ω ⊆ W).

1. Let ω be admissible for M_G: ω ∈ 𝒟^k(U), tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x. Then −ω is admissible as well: tsupport(−ω) = tsupport ω, and |−ω(x)| = |ω(x)| because the Euclidean coefficient norm is invariant under α ↦ −α (SimonGMT covectorEuclideanNorm_neg).
2. By the definition of M_G as a supremum, ofReal(X(ω)) ≤ M_G(X), ofReal(Y(ω)) ≤ M_G(Y) and ofReal(Y(−ω)) ≤ M_G(Y); by linearity Y(−ω) = −Y(ω). Hence ofReal(|Y(ω)|) ≤ M_G(Y) (|Y(ω)| is Y(ω) or −Y(ω)).
3. c·Y(ω) ≤ |c·Y(ω)| = |c|·|Y(ω)| ≤ |Y(ω)|, so by hypothesis Z(ω) = X(ω) + c·Y(ω) ≤ X(ω) + |Y(ω)|. Since ofReal is monotone and ofReal(p + q) ≤ ofReal(p) + ofReal(q) for all real p, q (ENNReal.ofReal_add_le): ofReal(Z(ω)) ≤ ofReal(X(ω)) + ofReal(|Y(ω)|) ≤ M_G(X) + M_G(Y).
4. Taking the supremum over all admissible ω gives M_G(Z) ≤ M_G(X) + M_G(Y). ∎

Remark (not part of the proof). c = 1 gives the sum and c = −1 the difference; e.g. M_G(A − B) ≤ M_G(A) + M_G(B) for the contract Sub, since (A − B)(ω) = A(ω) − B(ω). The parent uses it for M_G(∂A_t) ≤ M_G(B_t) + M_G(P) (step 4(b)), M(S̃) ≤ M(S″⌞W) + M(P) (step 6), M_G(Z) ≤ M_G(T′) + M_G(X) + M_G((∂R)⌞W) + M_G(P) (step 8) and M_W(Z) ≤ M_W(S) + M_W(S̃) (step 9).

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308, placed after `import GMT.Ch07.Submission` in the child comparator scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`). `exact Submission.lcmp_massOn_le_add_of_eval_eq` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.lcmp_massOn_le_add_of_eval_eq : ∀ (P k : ℕ) (U G : Set (Euclid P)) (X Y Z : GeometricCurrentOn U k) (c : ℝ), |c| ≤ 1 → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ G → Z ω = X ω + c * Y ω) → Z.massOn G ≤ X.massOn G + Y.massOn G := by
  intro P k U G X Y Z c hc hZ
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  have hneg : -ω ∈ massAdmissibleOn U k G := by
    refine ⟨?_, fun x => ?_⟩
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) =
          -(ω : DifferentialForm (Euclid P) k) := rfl
      rw [hco, tsupport_neg]
      exact hω.1
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) x =
          -((ω : DifferentialForm (Euclid P) k) x) := rfl
      rw [hco, covectorEuclideanNorm_neg]
      exact hω.2 x
  have hXle : ENNReal.ofReal (X ω) ≤ X.massOn G := X.le_massOn hω
  have hYle : ENNReal.ofReal (Y ω) ≤ Y.massOn G := Y.le_massOn hω
  have hYle' : ENNReal.ofReal (Y (-ω)) ≤ Y.massOn G := Y.le_massOn hneg
  have hYneg : Y (-ω) = -Y ω := map_neg Y.toCurrent ω
  rw [hYneg] at hYle'
  have habs : ENNReal.ofReal |Y ω| ≤ Y.massOn G := by
    rcases abs_cases (Y ω) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hYle
    · rw [h]; exact hYle'
  have hcy : c * Y ω ≤ |Y ω| :=
    calc c * Y ω ≤ |c * Y ω| := le_abs_self _
      _ = |c| * |Y ω| := abs_mul _ _
      _ ≤ 1 * |Y ω| := by gcongr
      _ = |Y ω| := one_mul _
  show ENNReal.ofReal (Z ω) ≤ X.massOn G + Y.massOn G
  calc ENNReal.ofReal (Z ω) = ENNReal.ofReal (X ω + c * Y ω) := by rw [hZ ω hω.1]
    _ ≤ ENNReal.ofReal (X ω + |Y ω|) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (X ω) + ENNReal.ofReal |Y ω| := ENNReal.ofReal_add_le
    _ ≤ X.massOn G + Y.massOn G := add_le_add hXle habs
```

## Key steps

1. For ω admissible in G, −ω is admissible too, so ofReal(|Y(ω)|) ≤ M_G(Y).
2. c·Y(ω) ≤ |Y(ω)| since |c| ≤ 1, so ofReal(Z(ω)) ≤ ofReal(X(ω)) + ofReal(|Y(ω)|) ≤ M_G(X) + M_G(Y).
3. Take the supremum over admissible ω.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); cat local-references/123e8435b4a2469b/manifest.json`
- `rg -n 'lcmp_|good_slice|lipschitz_cutoff' local-references/123e8435b4a2469b/project (no match)`
- `rg -n 'theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem countable_meas_level_set_pos|theorem IsOpen.exists_contDiff_support_eq|theorem prod_apply_symm|theorem measurable_measure_prodMk_left|theorem lintegral_liminf_le|theorem extraction_forall_of_frequently|theorem integral_withDensity_eq_integral_smul|theorem tendsto_measure_iInter_atTop|theorem closure_eq_iInter_thickening' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'; rg -n 'theorem (one_of_one_le|zero_of_nonpos|le_one|nonneg)|protected theorem contDiff' .../Analysis/SpecialFunctions/SmoothTransition.lean`
- `lake env lean /tmp/lcmp/Names.lean, Names2.lean, Names3.lean, N4.lean (#check of every cited Mathlib/SimonGMT declaration after import GMT.Ch07.Submission; MonotoneOn.intervalIntegral_deriv_mem_uIcc and MonotoneOn.intervalIntegrable_deriv are not in the import closure)`
- `sed SimonGMT Chapter06/{Mass,Currents,CurrentLocalEquality,Forms}.lean (massOn, massAdmissibleOn, covectorEuclideanNorm_neg, le_massOn, massOn_mono, boundary_apply, boundary_boundary, zeroRegion/support, TestFormOn); rg -n -i 'slice by|lipschitz slic|flat norm|deformation theorem' Chapter06 (no match)`
- `python3 -I scans of dag.json: lean_statement/status/children/depends_on of all 514 nodes; sibling frozen types of the selected node; accepted nodes mentioning support/massOn/IMRep/withDensity (155); smooth cut-off and mass-triangle candidates; collision check of the 8 proposed names`
- `grep -c of the six lcmp_ names in dag.json, issue-workers.json, DAG.md, GMT/, .lake/packages/simongmt; git grep -l lcmp_ over all 1117 distinct ref commits -- GMT (no match)`
- `git show 02c6122c94d0280a6288d299659b2dab7b59e109:GMT/Ch07/Submission.lean and 702e7082a5a7012f7a8f6efd9d272697e426f50b:GMT/Ch07/Submission.lean (accepted proofs of the two reused declarations)`
- `sed -n 3160,3230p and 6557,6600p runtime.py (_overlay_accepted_children: prerequisites = children + depends_on; _existing_lean_name_problem: reuse only for accepted identical types); sed -n 480,620p verifier/gmt-compare.py (contract_scope, child_modules)`
- `lake env lean /tmp/lcmp/Types1.lean; /tmp/lcmp/AsmFinal.lean; /tmp/lcmp/Validate.lean; /tmp/lcmp/FinalCheck.lean (#print axioms)`
- `sed -n 150,262p book/chapter-07.txt (Simon 7.2.4 proof, (1)–(12))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/lcmp/Types1.lean`
- `/tmp/lcmp/AsmFinal.lean`
- `/tmp/lcmp/Validate.lean`
- `/tmp/lcmp/FinalCheck.lean`
- `/tmp/lcmp/out/subproblems.json`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (manifest: project b4d606db, mathlib 25730c7c), and the snapshot project contains no lcmp_ declaration. Neither the snapshot Mathlib nor the pinned SimonGMT states any of the six new child facts: Lipschitz cut-off, good slicing level, mass localization, mass triangle inequality, IMRep restriction calculus, compact outer bound. SimonGMT Chapter06 has only massOn/le_massOn/massOn_mono and covectorEuclideanNorm_neg. Every Mathlib declaration cited in the child proofs is located in the snapshot and checked importable after import GMT.Ch07.Submission. The exception is MonotoneOn.intervalIntegral_deriv_mem_uIcc (DerivIntegrable.lean): it is cited by the parent's step 5 but is not imported, so child good_slice_level uses a Tonelli-based majorant instead. Two accepted DAG declarations with byte-identical frozen types are reused: rsd_cmr_support_subset_of_vanish and rsd_imrep_compact_measure_ne_top. In Lean: all eight child types elaborate in the comparator scope, and all eight child proofs compile with only propext, Classical.choice and Quot.sound. A conditional assembly from the six exact sibling types plus the eight child types proves the exact frozen parent type, with the same axioms. Simon's text (chapter-07.txt lines 176–258) confirms the parent's corrections S̃_j = S_j⌞W_α − P_j and γ ↑ α.
