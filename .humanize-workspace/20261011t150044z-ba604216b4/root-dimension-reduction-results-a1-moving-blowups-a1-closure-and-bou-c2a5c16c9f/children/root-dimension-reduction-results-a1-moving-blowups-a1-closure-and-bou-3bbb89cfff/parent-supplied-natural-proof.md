# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.upper_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 4 (Simon Ch. 1, Theorem 3.26(1); book/chapter-01.txt lines 1197–1215). Simon 3.3 is supplied by the sibling density_comparison (Lean: Submission.dmcbr_ci_gp_density_comparison). Notation: Hⁿ = μHE[n], ω = unitBallVolume n, Θ*(x) := limsup_{r→0+} Hⁿ(M ∩ B̄_r(x))/(ω·ofReal(rⁿ)) ∈ [0, ∞], and ν₀ := μHE[n].restrict M.
1. Preliminaries. ν₀(ℝ^P) = Hⁿ(M) < ∞, so ν₀ is a finite Borel measure on the metric space ℝ^P (isFiniteMeasure_restrict). Finite Borel measures on metric spaces are weakly regular, in particular outer regular, so Set.exists_isOpen_lt_of_lt applies to ν₀ and to arbitrary, not necessarily measurable, sets. Since M is measurable, ν₀(S) = Hⁿ(S ∩ M) for every S ⊆ ℝ^P (Measure.restrict_apply').
2. Superlevel sets are null. Let t ∈ [0, ∞] with 1 < t < ∞. Put A_t := {x ∈ M : t < Θ*(x)} and a := Hⁿ(A_t) ≤ Hⁿ(M) < ∞.
(a) We show t·a ≤ a + ε for every ε > 0. Since ν₀(A_t) = Hⁿ(A_t ∩ M) = a < a + ε, outer regularity gives an open U ⊇ A_t with ν₀(U) = Hⁿ(U ∩ M) < a + ε (Measure.restrict_apply, as the open set U is measurable).
(b) Put μ' := μHE[n].restrict (M ∩ U) and let x ∈ A_t. Then x ∈ U, so B_η(x) ⊆ U for some η > 0 (Metric.isOpen_iff). For 0 < r < η, B̄_r(x) ⊆ B_η(x) ⊆ U, hence μ'(B̄_r(x)) = Hⁿ(B̄_r(x) ∩ (M ∩ U)) = Hⁿ(M ∩ B̄_r(x)) (Measure.restrict_apply; closed balls are measurable). So the functions r ↦ μ'(B̄_r(x))/(ω·ofReal(rⁿ)) and r ↦ Hⁿ(M ∩ B̄_r(x))/(ω·ofReal(rⁿ)) agree eventually in 𝓝[>]0, and their limsups coincide (Filter.limsup_congr). Therefore t < Θ*(x) = limsup_{r→0+} μ'(B̄_r(x))/(ω·ofReal(rⁿ)).
(c) By (b), density_comparison applies to the measure μ', the set A_t and the constant t (0 < 1 < t), together with (IB). It gives t·a = t·Hⁿ(A_t) ≤ μ'(ℝ^P) = Hⁿ(M ∩ U) = Hⁿ(U ∩ M) < a + ε (Measure.restrict_apply_univ).
(d) By (a)–(c) and ENNReal.le_of_forall_pos_le_add, t·a ≤ a. If a ≠ 0 then, since a ≠ ∞ and 1 < t, a = a·1 < a·t = t·a (ENNReal.mul_lt_mul_right), a contradiction. Hence Hⁿ(A_t) = a = 0.
3. The exceptional set. Let x ∈ M with 1 < Θ*(x). Then Θ*(x) − 1 ≠ 0, so k⁻¹ < Θ*(x) − 1 for some k ∈ ℕ (ENNReal.exists_inv_nat_lt). Since (k+1)⁻¹ ≤ k⁻¹, the number t_k := 1 + (k+1)⁻¹ satisfies t_k < Θ*(x) (lt_tsub_iff_right), and every t_k satisfies 1 < t_k < ∞. Therefore {x ∈ M : 1 < Θ*(x)} ⊆ ⋃_{k∈ℕ} A_{t_k}, which by step 2 is a countable union of Hⁿ-null sets. Hence Hⁿ({x ∈ M : 1 < Θ*(x)}) = 0 (measure_iUnion_null, measure_mono_null).
4. Conclusion. ν₀({a : ¬(Θ*(a) ≤ 1)}) = Hⁿ({a : 1 < Θ*(a)} ∩ M) = 0 (Measure.restrict_apply', not_le). That is, Θ*(a) ≤ 1 for ν₀-almost every a (ae_iff). ∎

Validated Lean tactic script. It was kernel-checked during this decomposition (Lean v4.35.0-rc3, Mathlib 25730c7c, default heartbeats) both after `import GMT.Ch07.Submission` in the contract's namespace and opens and inside a copy of GMT/Ch07/Submission.lean at the insertion point used for child declarations; `#print axioms` reports only propext, Classical.choice and Quot.sound. It is the body after `theorem Submission.dmcbr_ci_gp_upper_density_le_one : <frozen type> := by` and it calls the sibling Submission.dmcbr_ci_gp_density_comparison:
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
      have h := Submission.dmcbr_ci_gp_density_comparison P n ((μHE[n] : Measure (Euclid P)).restrict (M ∩ U)) A t hIB
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
- `cat SNAPSHOT/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git rev-parse HEAD (b4d606db1), .lake/packages/mathlib (25730c7c), .lake/packages/simongmt (2b366308); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> IDENTICAL`
- `python3 -I scan of RUN/dag.json (2102 nodes, 2102 distinct lean names): selected node depth 5, depends_on isodiametric_bound-a1 (dmcbr_ci_euclideanHausdorff_le_isodiametric, type ∀ (P n : ℕ), (μHE[n] : Measure (Euclid P)) ≤ (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid P))); byte-identical lean_statement only at root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1 (cbr_ci_ae_good_points, speculative-ready); its children cbr_ci_gp_density_comparison, cbr_ci_gp_upper_density_le_one, cbr_ci_gp_lebesgue_error_tendsto, cbr_ci_gp_weighted_field_l1 (decomposing or speculative-ready, none accepted, each the only node with its type); substring 'dmcbr_ci_gp' over all lean names -> none`
- `python3 -I field comparison of the subproblem records in both parent-child-handoff.json files (key, title, statement, lean_statement, depends_on, natural_proof, proof_key_steps equal; only lean_name differs); read mirror decomposition-v1.json, decomposition-audit-v1.json (acceptable=true, all four natural_proof_acceptable=true) and decomposition-scope-v1.json`
- `recomputed decomposition_scope digest from the dag.json node and parent-supplied-natural-proof.json proof -> 8e96bd0840ef4e76c27104c6aa207c788d835f10de1226826936c97b41c0327a`
- `rg -n over SNAPSHOT/mathlib/Mathlib: 'theorem exists_disjoint_subfamily_covering_enlargement ' (MeasureTheory/Covering/Vitali.lean:59); 'countable_of_nonempty_interior' (Topology/Bases.lean:493); 'theorem tendsto_tsum_compl_atTop_zero' (Topology/Algebra/InfiniteSum/ENNReal.lean:235); 'theorem hausdorffMeasure_apply|theorem hausdorffMeasure_le_liminf_tsum' (MeasureTheory/Measure/Hausdorff.lean:546,555); "theorem le_iff'" (MeasureTheory/Measure/CompleteLattice.lean:46); 'exists_isOpen_lt_of_lt' (MeasureTheory/Measure/Regular.lean:359); 'def vitaliFamily|theorem tendsto_filterAt' (MeasureTheory/Covering/Besicovitch.lean:1021,1060); 'theorem ae_tendsto_lintegral_enorm_sub_div' (MeasureTheory/Covering/Differentiation.lean:818); 'frequently_lt_of_lt_limsup' (Order/LiminfLimsup.lean:646); 'eventually_lt_of_limsup_lt' (Order/LiminfLimsup.lean:605, to_dual attribute); 'theorem le_opNorm|theorem opNorm_le_bound' (Analysis/Normed/Module/Alternating/Basic.lean:212,241)`
- `rg -n 'def unitBallVolume|abbrev MultiVector' SNAPSHOT/project/GMT/Ch07/Contract.lean (lines 143, 48); rg -n 'def covectorEuclideanNorm' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (line 30)`
- `rg -c dmcbr_ci_gp SNAPSHOT/project (no match, exit 1); rg -c dmcbr_ci_gp SNAPSHOT/mathlib/Mathlib (no match, exit 1); rg -l --glob '*.lean' dmcbr_ci_gp GMT .lake/packages/simongmt/Poincare (no match, exit 1)`
- `sed -n 596,700p and 1185,1222p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt (Simon 3.3 at line 602, 3.4(*), 3.5, proof of 3.3 ending near 696; 3.26 at 1197, proof of 3.26(1) from 1209)`
- `lake env lean /tmp/dmcbr-gp-split-7f3c/Types.lean (four child types after import GMT.Ch07.Submission with the contract namespace/opens: only 'declaration uses sorry' warnings)`
- `lake env lean /tmp/dmcbr-gp-split-7f3c/Final.lean (four children proved by the scripts in their natural proofs, plus dmcbr_ci_gp_assembly_check proving the exact frozen parent type from them and the isodiametric sibling type as hypothesis; no warnings; #print axioms: propext, Classical.choice, Quot.sound for all five)`
- `lake env lean /tmp/dmcbr-gp-split-7f3c/SubmissionInplace.lean (copy of GMT/Ch07/Submission.lean with an IB stand-in, the four children and Submission.dmcbr_ci_ae_good_points inserted before main_theorem; children axiom-clean; parent sorryAx only from the IB stand-in)`
- `python3 -I: lean_contract.validate_lean_statement on the four types (valid, unchanged); leaf_verification.check_source_delta (extracted via ast, pydantic absent) on Submission.lean plus each single-child insertion (accepted)`
- `grep runtime.py: _decompose (node.depth >= max_depth), _existing_lean_name_problem, _dependency_problem, _reference_use_problem; read decomposition_scope.py`
- `WebSearch 'upper density Hausdorff measure at most 1 almost everywhere Mattila Theorem 6.2 Federer 2.10.19 proof Vitali covering' -> only indirect references, e.g. De Lellis lecture notes https://sites.math.washington.edu//~toro/Courses/07-08/582/delellis-06.pdf; Simon's text remains the cited source`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-c2a5c16c9f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-479700eeeb/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-479700eeeb/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/tmp/dmcbr-gp-split-7f3c/Types.lean`
- `/tmp/dmcbr-gp-split-7f3c/Final.lean`
- `/tmp/dmcbr-gp-split-7f3c/SubmissionInplace.lean`

Pins match, and the snapshot contract is byte-identical to Submission.lean. The selected node is byte-identical (type, statement, dependency, supplied proof) to cbr_ci_ae_good_points, whose four-child split was independently audited as acceptable. Those children are unaccepted and reserved by another parent, so the split is mirrored with fresh dmcbr_ci_gp_ names, which match nothing in the DAG, the snapshot, the workspace GMT sources or SimonGMT. Every library lemma used by the child proofs exists at the pinned Mathlib revision (locations above). The four child types elaborate after import GMT.Ch07.Submission. The four child scripts compile sorry-free both in the import-based file and in an in-place copy of Submission.lean. The conditional assembly proves the exact frozen parent type from the children plus the frozen type of the isodiametric sibling. The axioms are only propext, Classical.choice and Quot.sound. The Simon citations are accurate: 1.3.3–3.5 at chapter-01.txt lines 602–696 and 3.26(1) at lines 1197–1215.
