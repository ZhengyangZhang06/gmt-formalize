# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1.imrep_restriction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, sibling-fact paragraph (F5) (“A⌞B, represented by (M_A ∩ B, θ_A, ξ_A), ... (A⌞B)(ω) = A(ω) if ω vanishes outside B ... μ_{A⌞B} = μ_A⌞B ... M(A⌞B) = μ_A(B)”) and its closing sentence (“(R.measure, orient) is a representation in the sense of (F7), and for Borel B the current of (F7) built from it coincides with the IM restriction of (F5)”). This child isolates the measure-theoretic identities behind these sentences; they hold for every IMRep (openness of U is not needed).

Notation: ν := Hⁿ⌞M, so μ_R = ν.withDensity θ, where θ : ℝ^P → ℕ is Borel (IMRep field measurable_mult) and is used as a density through the cast ℕ → [0, ∞).

1. (a) A measure with a density with respect to ν is absolutely continuous with respect to ν (Mathlib withDensity_absolutelyContinuous): if ν(N) = 0 then μ_R(N) = ∫_N θ dν = 0.
2. (b) The IMRep field aestronglyMeasurable_orient says that ξ is a.e. strongly measurable for ν. By (a), every ν-null set is μ_R-null, so ξ is a.e. strongly measurable for μ_R (AEStronglyMeasurable.mono_ac).
3. (c), weights. Let E be Borel and R′ as in the statement. Restriction to a measurable set commutes with taking a density, and restrictions compose: (ν.withDensity θ)⌞E = (ν⌞E).withDensity θ (restrict_withDensity) and ν⌞E = (Hⁿ⌞M)⌞E = Hⁿ⌞(E ∩ M) (Measure.restrict_restrict). Hence μ_R⌞E = (Hⁿ⌞(M ∩ E)).withDensity θ = μ_{R′}, because R′ has carrier M ∩ E and multiplicity θ.
4. (c), actions. The map x ↦ θ(x) ∈ [0, ∞) is Borel (a Borel map into ℕ followed by a map out of the discrete space ℕ). For any measure λ, any Borel density g : ℝ^P → [0, ∞) and any function h : ℝ^P → ℝ, ∫ h d(λ.withDensity g) = ∫ g·h dλ as Bochner integrals, without any integrability assumption (Mathlib integral_withDensity_eq_integral_smul; if one side is not integrable, neither is the other and both integrals are 0). Apply this with λ = Hⁿ⌞(M ∩ E), g = θ and h(x) = ⟨ω(x), ξ(x)⟩: by step 3, ∫_E ⟨ω, ξ⟩ dμ_R = ∫ ⟨ω, ξ⟩ dμ_{R′} = ∫_{M∩E} θ ⟨ω, ξ⟩ dHⁿ, and the last integral is R′(ω) by the definition of IMRep.action for R′ (carrier M ∩ E, multiplicity θ, orientation ξ). ∎

Remark (how the parent uses the child; not part of the proof). With E = ℝ^P and R′ = R, (c) gives R(ω) = ∫ ⟨ω, ξ⟩ dμ_R; with (a), (b), sibling im_calculus (d) and child imrep_local_finiteness this verifies the representation hypotheses of the slicing sibling for (μ_{R_j}, ξ_{R_j}) and (μ_{∂R_j}, ξ_{∂R_j}). With E = W_s = {f < t}, the IM restriction R′ produced by im_calculus (b) represents a current whose values are ∫_{W_s} ⟨ω, ξ⟩ dμ_R, i.e. the slice currents A_t = R_j⌞W_s and B_t = (∂R_j)⌞W_s of the slicing sibling are integer multiplicity with weights μ_{R_j}⌞W_s and μ_{∂R_j}⌞W_s; the same identity gives (R⌞W)(ω) = R(ω) and (S″⌞W)(ω) = S″(ω) for forms supported in W (steps 6 and 7).

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308, placed after `import GMT.Ch07.Submission` in the child comparator scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`). `exact Submission.lcmp_imRep_measure_restrict` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.lcmp_imRep_measure_restrict : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), R.measure ≪ μHE[n].restrict R.carrier ∧ AEStronglyMeasurable R.orient R.measure ∧ ∀ (E : Set (Euclid P)) (R' : IMRep U n), MeasurableSet E → R'.carrier = R.carrier ∩ E → R'.mult = R.mult → R'.orient = R.orient → R'.measure = R.measure.restrict E ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = ∫ x in E, R.orient x (ω x) ∂R.measure := by
  intro P n U R
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  refine ⟨hac, R.aestronglyMeasurable_orient.mono_ac hac, ?_⟩
  intro E R' hE hc hm ho
  have hmeasEq : R'.measure = R.measure.restrict E := by
    unfold IMRep.measure
    rw [restrict_withDensity hE, Measure.restrict_restrict hE, hc, hm, inter_comm]
  refine ⟨hmeasEq, fun ω => ?_⟩
  have hmult : (fun x => (R'.mult x : ℝ≥0∞)) = fun x => (((R'.mult x : NNReal)) : ℝ≥0∞) := by
    funext x
    simp
  have hmeas : Measurable fun x => ((R'.mult x : ℕ) : NNReal) :=
    (measurable_from_nat (f := fun k : ℕ => (k : NNReal))).comp R'.measurable_mult
  rw [← hmeasEq]
  unfold IMRep.action IMRep.measure
  rw [hmult, integral_withDensity_eq_integral_smul hmeas]
  congr 1
  funext x
  rw [ho, NNReal.smul_def, smul_eq_mul]
  norm_cast
```

## Key steps

1. μ_R = (Hⁿ⌞M).withDensity θ ≪ Hⁿ⌞M, hence ξ is μ_R-a.e. strongly measurable.
2. (ν.withDensity θ)⌞E = (ν⌞E).withDensity θ and (Hⁿ⌞M)⌞E = Hⁿ⌞(M ∩ E), so μ_R⌞E = μ_{R′}.
3. ∫ h d(λ.withDensity θ) = ∫ θ h dλ (no integrability needed) turns ∫_E ⟨ω, ξ⟩ dμ_R into ∫_{M∩E} θ ⟨ω, ξ⟩ dHⁿ = R′(ω).

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
