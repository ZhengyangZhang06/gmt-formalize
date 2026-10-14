# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.count_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1 (H⁰ = μHE[0] = μH[0] is the counting measure, μH[0]{x} = 1) and the finite-set integrals used in parent steps 1 and 6. Simon's printed proof of Ch. 6, 8.2 (book/chapter-06.txt lines 2322–2323) only says that "the theorem is trivial in case n = 0", so this argument is extracted and specialized from the parent-supplied proof (Part III, CL(0)).

1. Normalisation. Mathlib MeasureTheory.Measure.euclideanHausdorffMeasure_zero gives μHE[0] = μH[0] on ℝ^P; rewrite both goals with it. Mathlib MeasureTheory.Measure.hausdorffMeasure_zero_singleton gives μH[0]{x} = 1 for every x ∈ ℝ^P. Singletons of ℝ^P are Borel, hence measurable (MeasurableSingletonClass). So it suffices to prove both identities for μ := μH[0].
2. Integrability of f on F. As sets, F = ⋃_{x∈F} {x} (Set.biUnion_of_singleton). For each x ∈ F, f is integrable on {x} with respect to μ by Mathlib integrableOn_singleton, because ‖f(x)‖ₑ < ∞ (f(x) is a real number) and μ{x} = 1 < ∞. No measurability of f is needed: on {x} the restricted measure is μ{x}·δ_x, and f agrees a.e. with the constant f(x). Integrability on each piece of a finite union gives integrability on the union (Mathlib integrableOn_finite_biUnion, the index set F being finite). Hence f is integrable on F.
3. Bochner integral. With the integrability of step 2, Mathlib MeasureTheory.setIntegral_finset gives ∫_F f dμ = Σ_{x∈F} μ.real{x} • f(x). Here μ.real{x} = (μ{x}).toReal = 1 (measureReal_def), so ∫_F f dμ = Σ_{x∈F} f(x). This is the first identity.
4. Lower integral. For a measure with measurable singletons and a finset F, Mathlib MeasureTheory.lintegral_finset gives ∫⁻_F g dμ = Σ_{x∈F} g(x)·μ{x} for every g : ℝ^P → [0, ∞]; no measurability of g is needed. Since μ{x} = 1, this equals Σ_{x∈F} g(x). This is the second identity.
5. Steps 1–4 prove both identities for μHE[0]. ∎

Appendix (not part of the mathematical argument). The following Lean tactic proof of exactly this frozen type compiled in this decomposition session as the body of `theorem Submission.cbrz_finset_integral_hausdorff_zero : <frozen type> := by`, placed in `namespace GMT.Ch07` after `import GMT.Ch07.Submission` with the contract's opens (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630); `#print axioms` reports only propext, Classical.choice, Quot.sound.
```lean
  intro P F f g
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_zero]
  constructor
  · have hint : IntegrableOn f (F : Set (Euclid P)) μH[0] := by
      have hF : (F : Set (Euclid P)) = ⋃ x ∈ (F : Set (Euclid P)), ({x} : Set (Euclid P)) :=
        (Set.biUnion_of_singleton _).symm
      rw [hF, integrableOn_finite_biUnion F.finite_toSet]
      intro x _
      exact integrableOn_singleton (by simp) (by simp [Measure.hausdorffMeasure_zero_singleton])
    rw [setIntegral_finset F hint]
    simp [measureReal_def, Measure.hausdorffMeasure_zero_singleton]
  · rw [lintegral_finset]
    simp [Measure.hausdorffMeasure_zero_singleton]
```

## Key steps

1. μHE[0] = μH[0] (euclideanHausdorffMeasure_zero) and μH[0]{x} = 1 (hausdorffMeasure_zero_singleton); singletons are measurable
2. f is integrable on each singleton (integrableOn_singleton), hence on the finite union F (integrableOn_finite_biUnion)
3. Bochner integral over a finset = Σ μ.real{x}·f(x) = Σ f(x) (setIntegral_finset)
4. lower integral over a finset = Σ g(x)·μ{x} = Σ g(x) (lintegral_finset)

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cmp GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Contract.lean (identical); git -C .lake/packages/mathlib log -1 (25730c7c); git -C .lake/packages/simongmt log -1 and git -C lake-packages-25730c7c/simongmt log -1 (both 2b36630); cmp of SimonGMT Chapter03/Rectifiable.lean and Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean between the two package copies (identical)`
- `python3 -I scan of dag.json (902 nodes): lean_name in {cbrz_finset_integral_hausdorff_zero, cbrz_approxTangent_finite_zero, cbrz_isIntegerMultiplicity_point_sum, cbrz_imrep_zero_local_point_sum, cbrz_point_sum_limit} (none), lean_name prefix 'cbrz' (none), lean_statement identical to a proposed one (none); selected node record (status decomposing, message 'subproblem decomposition attempt 2', children []); frozen lean_statement of cbr_isIntegerMultiplicity_of_local; accepted statements containing 'IMRep U 0', 'IMRep V 0', 'μHE[0]', 'HasApproximateTangentSpaceAt 0', 'GeometricCurrentOn U 0' (dtc_dim_zero_carrier_finite, dor_zdm_imrep_zero_structure, regcomp_cop_zdr_unitOrientation_zero, regcomp_cop_zdr_setIntegral_eq_indicator, dtc_dim_zero_erase_point, dtc_point_current, ...)`
- `python3 -I substring scan of the five proposed names in all 807 nodes/*/decomposition-v*.json (only this node's decomposition-v1.json)`
- `read nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/{parent-child-handoff.json, parent-supplied-plan.md, parent-supplied-natural-proof.md, decomposition-v1.json, decomposition-review-receipt-v1.json, decomposition-review-receipt-v2.json, decomposition-audit-v1.json, decomposition-scope-v1.json}`
- `grep -rn --include=*.lean in <snapshot>/mathlib/Mathlib: 'euclideanHausdorffMeasure_zero', 'theorem hausdorffMeasure_zero_singleton', 'theorem lintegral_finset', 'theorem setIntegral_finset', 'theorem integrableOn_singleton', 'integrableOn_finite_biUnion', 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero', 'theorem IsCompact.tendsto_subseq', 'theorem Finite.exists_infinite_fiber', 'theorem extraction_of_frequently_atTop', 'theorem isCompact_univ_pi', 'theorem tendsto_nhds_of_eventually_eq', 'Ioo_mem_nhdsGT', 'image_eq_zero_of_notMem_tsupport', 'theorem Countable.exists_eq_range', 'def apply' (ContinuousAlternatingMap.apply), 'theorem Continuous.eval_const', 'protected theorem exists_nat_gt' (ENNReal), 'theorem limsup_le_iSup', 'theorem liminf_le_limsup', 'DiscreteMeasurableSpace.toMeasurableAdd₂', 'theorem measurable_to_countable'', 'singleton_inter'`
- `grep -n / sed -n of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT: Chapter03/Rectifiable.lean ('def CountablyRectifiable', 'theorem countablyRectifiable_of_measure_zero', 'theorem countablyRectifiable_range', 'theorem countablyRectifiable_iUnion', 'def blowUpMap', 'def HasApproximateTangentSpaceAt'); Chapter06/Currents.lean (testFormOnSubmodule, TestFormOn, GeometricCurrentOn, WeaklyConvergesOn); Chapter06/Mass.lean (massOn, massOn_mono, WeaklyConvergesOn.massOn_le_liminf); Chapter06/CurrentLocalEquality.lean (testFormOnInclusion, GeometricCurrentOn.restrictDomain, restrictDomain_apply); Chapter06/Forms.lean (Covector, DifferentialForm, IsSmoothForm, IsTestForm)`
- `grep -n '8.2\|trivial in case' book/chapter-06.txt; sed -n 2296,2330p book/chapter-06.txt (Simon Ch. 6, 8.2 statement and the remark 'the theorem is trivial in case n = 0')`
- `sed -n of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py: _decompose (1389-1560), _solve_children (1802-2000), _install_parent_supplied_child_handoff (1660-1730), _accepted_checkpoint (2365), _dependency_problem and _existing_lean_name_problem (6537-6600); swarm-project.json (max_children 12, max_depth 6, max_nodes 1000)`
- `git show 897839f250d247f64d81132474211f0ab45b65b3:GMT/Ch07/Submission.lean (accepted child theorems are declared as 'theorem Submission.X : <type> := by' in namespace GMT.Ch07 after the section 'end')`
- `python3 -I /tmp/cz0v2-8d3f/scripts/scope.py: verifier/lean_contract.py validate_lean_statement on the five statements (all OK, unchanged) and verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) (replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `lake env lean /tmp/cz0v2-8d3f/lean/{Types,Assembly,C1,C2,C3,C4,Combined,SubStyle,Coe}.lean with toolchain lean-4.35.0-rc3 (#print axioms: the five children and the hypothesis-only assembly use [propext, Classical.choice, Quot.sound]; the parent declared from the children plus an im_local stub adds only sorryAx)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/Pigeonhole.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Hom/ContinuousEvalConst.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Insert.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-68d9893f8c/decomposition-review-receipt-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cz0v2-8d3f/lean/Types.lean`
- `/tmp/cz0v2-8d3f/lean/Assembly.lean`
- `/tmp/cz0v2-8d3f/lean/Combined.lean`
- `/tmp/cz0v2-8d3f/lean/SubStyle.lean`
- `/tmp/cz0v2-8d3f/lean/Coe.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c, SimonGMT 2b36630), and the two SimonGMT package copies agree on every file used. Neither the snapshot Mathlib nor SimonGMT contains a degree-0 closure theorem, a finite-set approximate-tangent lemma, or a point-sum-is-IM lemma. SimonGMT Chapter03 supplies only the definitions and basic closure properties of CountablyRectifiable and HasApproximateTangentSpaceAt, and Chapter06 supplies currents, mass, lower semicontinuity of mass and domain restriction. In the DAG, the accepted degree-0 lemmas of other branches are only partial tools, and no node has a lean_statement identical to a proposed child, so the split is new and no cross-branch node is reused. Every Mathlib and SimonGMT lemma cited in the child proofs exists in the pinned versions and was used in proofs that compiled. The five cbrz_* names collide with no DAG node, no other decomposition file and no declaration. All five exact lean_statements pass the verifier lexical check unchanged and elaborate in the replayed contract scope. A hypothesis-only assembly proves the frozen parent type from imrep_point_sum, point_sum_limit, point_sum_im and the frozen im_local type. Complete Lean proofs of all five children compile in Submission form using only propext, Classical.choice and Quot.sound.
