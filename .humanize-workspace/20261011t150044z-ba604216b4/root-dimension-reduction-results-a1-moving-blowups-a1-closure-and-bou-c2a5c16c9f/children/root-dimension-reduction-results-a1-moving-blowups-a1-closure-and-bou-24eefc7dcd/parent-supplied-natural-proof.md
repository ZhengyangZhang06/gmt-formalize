# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.lebesgue_error-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 5–6 (Besicovitch differentiation with closed balls, then normalisation by ω_nrⁿ). This proof uses the lintegral form of the differentiation theorem that step 5 names (VitaliFamily.ae_tendsto_lintegral_enorm_sub_div). In place of the bound Hⁿ(M ∩ B̄_r(a)) ≤ 2ω_nrⁿ it uses any finite eventual bound C on the density quotient. Notation: Hⁿ = μHE[n], ω = unitBallVolume n, ν₀ := μHE[n].restrict M. For a point a and r > 0 put I(r) := ∫⁻_{M∩B̄_r(a)} ‖τ(x) − τ(a)‖ₑ dHⁿ(x), m(r) := Hⁿ(M ∩ B̄_r(a)) and w(r) := ω·ofReal(rⁿ).
1. Integrability. ν₀(ℝ^P) = Hⁿ(M) < ∞, so ν₀ is a finite (hence s-finite and locally finite) Borel measure (isFiniteMeasure_restrict). τ is strongly measurable and ∫⁻ ‖τ‖ₑ dν₀ = ∫⁻_M ‖τ‖ₑ dHⁿ < ∞, so τ has finite integral. Hence τ is ν₀-integrable, in particular locally integrable, as a map into the normed space MultiVector P n. (Formalisation note: with the default instances the proposition `Integrable τ ν₀` does not elaborate for MultiVector P n, because no ContinuousENorm instance is found for the strong topology of Covector (Euclid P) n →L[ℝ] ℝ. Pass the integrability directly as the argument of the differentiation lemma with `(E := MultiVector P n)`, namely `Integrable.locallyIntegrable ⟨hτ.aestronglyMeasurable, hfin⟩`. This typechecks because the strong topology and the norm topology are definitionally equal.)
2. Differentiation. Euclid P is a finite-dimensional normed space, so it has the Besicovitch covering property and v := Besicovitch.vitaliFamily ν₀ is a Vitali family for ν₀. By VitaliFamily.ae_tendsto_lintegral_enorm_sub_div, for ν₀-almost every a, (∫⁻_E ‖τ(y) − τ(a)‖ₑ dν₀(y))/ν₀(E) → 0 as E → v.filterAt a. By Besicovitch.tendsto_filterAt ν₀ a, B̄_r(a) → v.filterAt a as r → 0+. Composing the two limits, (∫⁻_{B̄_r(a)} ‖τ − τ(a)‖ₑ dν₀)/ν₀(B̄_r(a)) → 0 as r → 0+. Fix such an a; we prove the implication at a.
3. Rewriting. Closed balls are measurable, so (ν₀)⌞B̄_r(a) = Hⁿ⌞(B̄_r(a) ∩ M) (Measure.restrict_restrict) and ν₀(B̄_r(a)) = Hⁿ(B̄_r(a) ∩ M) (Measure.restrict_apply). Using B̄_r(a) ∩ M = M ∩ B̄_r(a), step 2 says q(r) := I(r)/m(r) → 0 as r → 0+.
4. Bounded density. Assume limsup_{r→0+} m(r)/w(r) < ∞ and choose C with limsup m/w < C < ∞ (exists_between). Then m(r)/w(r) < C for all r in some set belonging to 𝓝[>]0 (Filter.eventually_lt_of_limsup_lt).
5. Comparison. Let r > 0 with m(r)/w(r) < C. If m(r) = 0, the integral over the null set M ∩ B̄_r(a) vanishes (setLIntegral_measure_zero), so I(r)/w(r) = 0 ≤ C·q(r). If m(r) ≠ 0, then also m(r) ≤ Hⁿ(M) < ∞, so m(r)⁻¹·m(r) = 1 (ENNReal.inv_mul_cancel). Then I(r)/w(r) = I(r)·m(r)⁻¹·m(r)·w(r)⁻¹ = q(r)·(m(r)/w(r)) ≤ q(r)·C. Hence 0 ≤ I(r)/w(r) ≤ C·q(r) eventually in 𝓝[>]0.
6. Limit. Since C ≠ ∞, C·q(r) → C·0 = 0 (ENNReal.Tendsto.const_mul). The squeeze theorem (tendsto_of_tendsto_of_tendsto_of_le_of_le', with the constant lower bound 0) then gives I(r)/w(r) → 0 as r → 0+, which is the assertion. ∎

Validated Lean tactic script. It was kernel-checked during this decomposition (Lean v4.35.0-rc3, Mathlib 25730c7c, default heartbeats) both after `import GMT.Ch07.Submission` in the contract's namespace and opens and inside a copy of GMT/Ch07/Submission.lean at the insertion point used for child declarations; `#print axioms` reports only propext, Classical.choice and Quot.sound. It is the body after `theorem Submission.dmcbr_ci_gp_lebesgue_error_tendsto : <frozen type> := by`:
```lean
  intro P n M τ hM hMfin hτ hfin
  have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict M) := isFiniteMeasure_restrict.2 hMfin.ne
  have hL := (Besicovitch.vitaliFamily ((μHE[n] : Measure (Euclid P)).restrict M)).ae_tendsto_lintegral_enorm_sub_div
    (E := MultiVector P n) (f := τ) (Integrable.locallyIntegrable ⟨hτ.aestronglyMeasurable, hfin⟩)
  filter_upwards [hL] with a ha hlim
  have hball := ha.comp (Besicovitch.tendsto_filterAt ((μHE[n] : Measure (Euclid P)).restrict M) a)
  -- rewrite the Besicovitch quotient in terms of `M ∩ closedBall a r`
  have hq : Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) /
      μHE[n] (M ∩ closedBall a r)) (𝓝[>] 0) (𝓝 0) := by
    refine hball.congr fun r => ?_
    simp only [Function.comp_apply]
    rw [Measure.restrict_restrict measurableSet_closedBall,
      Measure.restrict_apply measurableSet_closedBall, inter_comm]
  -- the density quotient is eventually bounded by a finite constant
  obtain ⟨C, hC1, hC2⟩ := exists_between hlim
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n)) < C :=
    eventually_lt_of_limsup_lt hC1
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hupper : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal (r ^ n))
        ≤ C * ((∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) / μHE[n] (M ∩ closedBall a r)) := by
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    set I := ∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]
    set m := μHE[n] (M ∩ closedBall a r)
    set w := unitBallVolume n * ENNReal.ofReal (r ^ n)
    by_cases hm0 : m = 0
    · have hI : I = 0 := setLIntegral_measure_zero _ _ hm0
      simp [hI]
    · have hmtop : m ≠ ∞ := (lt_of_le_of_lt (measure_mono inter_subset_left) hMfin).ne
      have hIw : I / w = I / m * (m / w) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_assoc m⁻¹,
          ENNReal.inv_mul_cancel hm0 hmtop, one_mul]
      rw [hIw, mul_comm C]
      gcongr
  have hCq : Tendsto (fun r : ℝ => C * ((∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) /
      μHE[n] (M ∩ closedBall a r))) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hq (Or.inr hC2.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCq
    (Eventually.of_forall fun _ => zero_le) hupper
```

## Key steps

1. τ is Hⁿ⌞M-integrable (strongly measurable with finite ∫⁻‖τ‖ₑ); pass this with E := MultiVector P n.
2. Besicovitch Vitali family, ae_tendsto_lintegral_enorm_sub_div and tendsto_filterAt give I(r)/Hⁿ(M ∩ B̄_r(a)) → 0 for almost every a.
3. limsup of the density quotient < C < ∞ gives, eventually, I(r)/(ω_n rⁿ) ≤ C·I(r)/Hⁿ(M ∩ B̄_r(a)); a null ball gives I(r) = 0.
4. Squeeze: I(r)/(ω_n rⁿ) → 0.

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
