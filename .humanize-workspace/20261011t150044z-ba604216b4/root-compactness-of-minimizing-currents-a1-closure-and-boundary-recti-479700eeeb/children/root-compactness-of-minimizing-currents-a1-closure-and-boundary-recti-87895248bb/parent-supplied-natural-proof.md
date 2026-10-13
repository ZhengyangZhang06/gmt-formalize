# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.upper_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 4 (Simon Ch. 1, Theorem 3.26(1); book/chapter-01.txt lines 1197–1215). Simon 3.3 is supplied by the sibling density_comparison (Lean: Submission.cbr_ci_gp_density_comparison). Notation: Hⁿ = μHE[n], ω = unitBallVolume n, Θ*(x) := limsup_{r→0+} Hⁿ(M ∩ B̄_r(x))/(ω·ofReal(rⁿ)) ∈ [0, ∞], and ν₀ := μHE[n].restrict M.
1. Preliminaries. ν₀(ℝ^P) = Hⁿ(M) < ∞, so ν₀ is a finite Borel measure on the metric space ℝ^P (isFiniteMeasure_restrict). Finite Borel measures on metric spaces are weakly regular, in particular outer regular, so Set.exists_isOpen_lt_of_lt applies to ν₀ and to arbitrary, not necessarily measurable, sets. Since M is measurable, ν₀(S) = Hⁿ(S ∩ M) for every S ⊆ ℝ^P (Measure.restrict_apply').
2. Superlevel sets are null. Let t ∈ [0, ∞] with 1 < t < ∞. Put A_t := {x ∈ M : t < Θ*(x)} and a := Hⁿ(A_t) ≤ Hⁿ(M) < ∞.
(a) We show t·a ≤ a + ε for every ε > 0. Since ν₀(A_t) = Hⁿ(A_t ∩ M) = a < a + ε, outer regularity gives an open U ⊇ A_t with ν₀(U) = Hⁿ(U ∩ M) < a + ε (Measure.restrict_apply, as the open set U is measurable).
(b) Put μ' := μHE[n].restrict (M ∩ U) and let x ∈ A_t. Then x ∈ U, so B_η(x) ⊆ U for some η > 0 (Metric.isOpen_iff). For 0 < r < η, B̄_r(x) ⊆ B_η(x) ⊆ U, hence μ'(B̄_r(x)) = Hⁿ(B̄_r(x) ∩ (M ∩ U)) = Hⁿ(M ∩ B̄_r(x)) (Measure.restrict_apply; closed balls are measurable). So the functions r ↦ μ'(B̄_r(x))/(ω·ofReal(rⁿ)) and r ↦ Hⁿ(M ∩ B̄_r(x))/(ω·ofReal(rⁿ)) agree eventually in 𝓝[>]0, and their limsups coincide (Filter.limsup_congr). Therefore t < Θ*(x) = limsup_{r→0+} μ'(B̄_r(x))/(ω·ofReal(rⁿ)).
(c) By (b), density_comparison applies to the measure μ', the set A_t and the constant t (0 < 1 < t), together with (IB). It gives t·a = t·Hⁿ(A_t) ≤ μ'(ℝ^P) = Hⁿ(M ∩ U) = Hⁿ(U ∩ M) < a + ε (Measure.restrict_apply_univ).
(d) By (a)–(c) and ENNReal.le_of_forall_pos_le_add, t·a ≤ a. If a ≠ 0 then, since a ≠ ∞ and 1 < t, a = a·1 < a·t = t·a (ENNReal.mul_lt_mul_right), a contradiction. Hence Hⁿ(A_t) = a = 0.
3. The exceptional set. Let x ∈ M with 1 < Θ*(x). Then Θ*(x) − 1 ≠ 0, so k⁻¹ < Θ*(x) − 1 for some k ∈ ℕ (ENNReal.exists_inv_nat_lt). Since (k+1)⁻¹ ≤ k⁻¹, the number t_k := 1 + (k+1)⁻¹ satisfies t_k < Θ*(x) (lt_tsub_iff_right), and every t_k satisfies 1 < t_k < ∞. Therefore {x ∈ M : 1 < Θ*(x)} ⊆ ⋃_{k∈ℕ} A_{t_k}, which by step 2 is a countable union of Hⁿ-null sets. Hence Hⁿ({x ∈ M : 1 < Θ*(x)}) = 0 (measure_iUnion_null, measure_mono_null).
4. Conclusion. ν₀({a : ¬(Θ*(a) ≤ 1)}) = Hⁿ({a : 1 < Θ*(a)} ∩ M) = 0 (Measure.restrict_apply', not_le). That is, Θ*(a) ≤ 1 for ν₀-almost every a (ae_iff). ∎

Validated Lean tactic script. It was kernel-checked during this decomposition inside a copy of GMT/Ch07/Submission.lean, at the insertion point used for child declarations, with default heartbeats; the only axioms are propext, Classical.choice and Quot.sound. It is the body after `theorem Submission.cbr_ci_gp_upper_density_le_one : <frozen type> := by` and it calls the sibling Submission.cbr_ci_gp_density_comparison:
```lean
  intro P n M hIB hM hMfin
  set Θ : Euclid P → ℝ≥0∞ := fun x => limsup (fun r : ℝ => μHE[n] (M ∩ closedBall x r) /
    (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) with hΘ
  have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict M) :=
    isFiniteMeasure_restrict.2 hMfin.ne
  -- Step 2: each superlevel set `A_t`, `1 < t < ∞`, is null
  have key : ∀ t : ℝ≥0∞, 1 < t → t ≠ ∞ → μHE[n] {x | x ∈ M ∧ t < Θ x} = 0 := by
    intro t ht1 httop
    set A := {x | x ∈ M ∧ t < Θ x} with hAdef
    have hAM : A ⊆ M := fun x hx => hx.1
    have hAfin : μHE[n] A ≠ ∞ := (lt_of_le_of_lt (measure_mono hAM) hMfin).ne
    have hle : t * μHE[n] A ≤ μHE[n] A := by
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have hlt : ((μHE[n] : Measure (Euclid P)).restrict M) A < μHE[n] A + ε := by
        rw [Measure.restrict_apply' hM, inter_eq_left.2 hAM]
        exact ENNReal.lt_add_right hAfin (by simpa using hε.ne')
      obtain ⟨U, hUA, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt A _ hlt
      rw [Measure.restrict_apply hUo.measurableSet] at hU
      have h := Submission.cbr_ci_gp_density_comparison P n ((μHE[n] : Measure (Euclid P)).restrict (M ∩ U)) A t hIB
        (zero_lt_one.trans ht1) (fun x hx => ?_)
      · rw [Measure.restrict_apply_univ, inter_comm] at h
        exact h.trans hU.le
      · obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hUo x (hUA hx)
        have heq : (fun r : ℝ => ((μHE[n] : Measure (Euclid P)).restrict (M ∩ U)) (closedBall x r) /
              (unitBallVolume n * ENNReal.ofReal (r ^ n))) =ᶠ[𝓝[>] 0]
            (fun r : ℝ => μHE[n] (M ∩ closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) := by
          have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < η :=
            nhdsWithin_le_nhds (gt_mem_nhds hη)
          filter_upwards [hsmall] with r hr
          rw [Measure.restrict_apply measurableSet_closedBall]
          have hsub : closedBall x r ⊆ U := (closedBall_subset_ball hr).trans hball
          congr 2
          ext y
          constructor
          · rintro ⟨hy, hyM, -⟩
            exact ⟨hyM, hy⟩
          · rintro ⟨hyM, hy⟩
            exact ⟨hy, hyM, hsub hy⟩
        rw [limsup_congr heq]
        exact hx.2
    by_contra hA0
    have : μHE[n] A * 1 < μHE[n] A * t := ENNReal.mul_lt_mul_right hA0 hAfin ht1
    rw [mul_one, mul_comm] at this
    exact absurd hle (not_le.2 this)
  -- Step 3: the exceptional set is a countable union of null sets
  have hcover : {x | x ∈ M ∧ 1 < Θ x} ⊆
      ⋃ k : ℕ, {x | x ∈ M ∧ 1 + ((k : ℝ≥0∞) + 1)⁻¹ < Θ x} := by
    intro x hx
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt hx.2).ne'
    refine mem_iUnion.2 ⟨k, hx.1, ?_⟩
    have h1 : ((k : ℝ≥0∞) + 1)⁻¹ < Θ x - 1 :=
      lt_of_le_of_lt (ENNReal.inv_le_inv.2 le_self_add) hk
    rw [add_comm]
    exact lt_tsub_iff_right.1 h1
  have hnull : μHE[n] {x | x ∈ M ∧ 1 < Θ x} = 0 := by
    refine measure_mono_null hcover (measure_iUnion_null fun k => key _ ?_ ?_)
    · exact ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.2
        (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, ENNReal.one_ne_top⟩))
    · exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (by simp)⟩
  -- Step 4: conclusion
  rw [ae_iff, Measure.restrict_apply' hM]
  refine measure_mono_null ?_ hnull
  intro x hx
  exact ⟨hx.2, not_le.1 hx.1⟩
```

## Key steps

1. ν₀ = Hⁿ⌞M is finite, hence outer regular, and ν₀(S) = Hⁿ(S ∩ M) for every set S.
2. For 1 < t < ∞ and ε > 0, choose an open U ⊇ A_t with Hⁿ(M ∩ U) < Hⁿ(A_t) + ε; on small balls around points of A_t, Hⁿ⌞(M ∩ U) agrees with Hⁿ⌞M, so the upper densities coincide.
3. density_comparison gives t·Hⁿ(A_t) ≤ Hⁿ(M ∩ U) < Hⁿ(A_t) + ε, hence Hⁿ(A_t) = 0.
4. {x ∈ M : Θ*(x) > 1} ⊆ ⋃_k A_{1+1/(k+1)} is Hⁿ-null, so Θ* ≤ 1 at Hⁿ⌞M-almost every point.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical); grep -n 'def unitBallVolume' and 'abbrev MultiVector' in the snapshot Contract.lean (lines 143, 48)`
- `grep -n 'theorem exists_disjoint_subfamily_covering_enlargement' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean (line 59)`
- `grep -n 'theorem hausdorffMeasure_le_liminf_tsum' and 'theorem hausdorffMeasure_apply' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (lines 555, 546)`
- `grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean (line 818)`
- `grep -n 'def vitaliFamily' and 'theorem tendsto_filterAt' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean (lines 1021, 1060)`
- `grep -rn 'theorem tendsto_tsum_compl_atTop_zero' <snapshot>/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ (ENNReal.lean line 235)`
- `grep -n 'countable_of_nonempty_interior' <snapshot>/mathlib/Mathlib/Topology/Bases.lean (line 493)`
- `grep -n 'exists_isOpen_lt_of_lt' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean (line 359)`
- `grep -rn 'theorem le_iff' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/ (CompleteLattice.lean line 46: Measure.le_iff' is setwise for all sets)`
- `grep -n 'frequently_lt_of_lt_limsup' and 'eventually_lt_of_limsup_lt' <snapshot>/mathlib/Mathlib/Order/LiminfLimsup.lean (lines 646, 605)`
- `grep -n 'euclideanHausdorffMeasure' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (def at line 68: μHE[d] = volume.addHaarScalarFactor μH[d] • μH[d])`
- `lean with LEAN_PATH from lake env on /tmp/gp-decomp/Check1.lean, Inst.lean, Inst2.lean, Api1.lean, Api2.lean (import GMT.Ch07.Submission): all cited lemmas reachable; HasBesicovitchCovering (Euclid P) and OuterRegular of finite measures found; Integrable τ μ for τ : Euclid P → MultiVector P n fails (ContinuousENorm not synthesized; the TopologicalSpace instance is ContinuousLinearMap.topologicalSpace, equal by rfl to the norm topology)`
- `lean on /tmp/gp-decomp/Final.lean and /tmp/gp-decomp/SubmissionInplace.lean: four child theorems proved from their exact frozen types, plus the parent assembly with the IB type as hypothesis; #print axioms gives propext, Classical.choice, Quot.sound`
- `python3 -I scan of dag.json: 1322 lean_names, none with prefix cbr_ci_gp_; the selected type and the cbr_ci_euclideanHausdorff_le_isodiametric type are equal to the strings used; inspected limsup/upper-density/covector nodes (regcomp_atl_upper_density_zero, idtp_dema_upper_density_zero, doraggt_ae_rescaled_lebesgue_point, regcomp_covector_*, cbr_lower_density_of_slice_property): no identical type to reuse`
- `git show 031b51256 (accepted Submission.regcomp_atl_upper_density_zero: Vitali + Measure.hausdorffMeasure_le_liminf_tsum pattern with crude constant 6^n)`
- `sed -n 1,100p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean (outerMeasure_le_tsum_of_fiveTimesCovering, simon_theorem_3_3: sharp-constant finite-tail argument, outside the contract import closure); Chapter06/Mass.lean covectorEuclideanNorm; Chapter06/Forms.lean Covector`
- `sed -n 560,735p and 1190,1240p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt (Simon 3.1-3.8, 3.26)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the four child types (all pass); leaf_verification.check_source_delta forbidden-token regex on the four proof bodies (no hits)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _render_parent_supplied_plan: children receive only their own sibling prerequisites)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-479700eeeb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/tmp/gp-decomp/Final.lean`
- `/tmp/gp-decomp/SubmissionInplace.lean`

Contract and reuse: the snapshot contract (project b4d606db, Mathlib 25730c7c) is byte-identical to the workspace Submission.lean. Every Mathlib lemma used by the child proofs exists in the snapshot and is reachable from import GMT.Ch07.Submission. The SimonGMT formalization of Simon 3.3 is not importable from the contract, so density_comparison re-proves it and takes IB as an explicit hypothesis. No existing DAG declaration has an identical type, and the cbr_ci_gp_ names are fresh.

Instance finding: Integrable cannot be stated for MultiVector-valued maps with default instances, so the L1 data is passed as StronglyMeasurable plus a finite ∫⁻‖·‖ₑ.

Validation: all four child types elaborate in contract scope and pass the verifier's lexical check. Each child was proved sorry-free from its exact frozen type, compiled inside a copy of Submission.lean. The frozen parent type follows from upper_density, weighted_field and lebesgue_error together with the IB sibling. Only propext, Classical.choice and Quot.sound are used.
