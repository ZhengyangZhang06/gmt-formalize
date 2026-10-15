# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1`
- Child DAG node: `root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1.quotient_rescale-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the rescaling part of step 7 of the selected node's supplied proof, isolated for an arbitrary function F. That step uses two facts: the map r ↦ Rr sends 𝓝[>] 0 to 𝓝[>] 0, and ofReal((Rr)ᵏ) = Rᵏ · ofReal(rᵏ) with 0 < Rᵏ < ∞.

Let k ∈ ℕ and F : ℝ → [0, ∞] with F(ρ)/ofReal(ρᵏ) → 0 as ρ → 0+, and let R > 0. Put c := ofReal(Rᵏ) ∈ [0, ∞].

1. (The constant.) Rᵏ > 0 since R > 0 (`pow_pos`), so c ≠ 0 (`ENNReal.ofReal_pos`) and c ≠ ∞ (`ENNReal.ofReal_ne_top`).

2. (The substitution ρ = R·r.) Let φ(r) := R·r.
   - φ(r) → R·0 = 0 as r → 0 (`tendsto_id.const_mul R`), hence also along 𝓝[>] 0 (`nhdsWithin_le_nhds`).
   - r > 0 implies φ(r) > 0 (`mul_pos`), and r > 0 holds eventually along 𝓝[>] 0 (`self_mem_nhdsWithin`).
   - Therefore φ tends to 0 within (0, ∞), i.e. Tendsto φ (𝓝[>] 0) (𝓝[>] 0) (`tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`).

3. (Composition.) By the hypothesis and step 2 (`Tendsto.comp`), G(r) := F(R·r) / ofReal((R·r)ᵏ) → 0 as r → 0+.

4. (Constant factor.) Since c ≠ ∞, c · G(r) → c · 0 = 0 as r → 0+ (`ENNReal.Tendsto.const_mul` with side condition c ≠ ∞, then `mul_zero`).

5. (Identity for r > 0.) Let r > 0. Then rᵏ > 0, so b := ofReal(rᵏ) satisfies b⁻¹ = ofReal((rᵏ)⁻¹) (`ENNReal.ofReal_inv_of_pos`). Also (R·r)ᵏ = Rᵏ·rᵏ (`mul_pow`), and ofReal(Rᵏ·rᵏ) = c·b (`ENNReal.ofReal_mul`, Rᵏ ≥ 0). Hence
   c · G(r) = c · ((c·b)⁻¹ · F(R·r))   (`ENNReal.div_eq_inv_mul`)
            = c · (c⁻¹ · b⁻¹ · F(R·r))   (`ENNReal.mul_inv`, valid since c ≠ 0 and c ≠ ∞)
            = (c · c⁻¹) · b⁻¹ · F(R·r)   (associativity)
            = b⁻¹ · F(R·r)               (`ENNReal.mul_inv_cancel`, c ≠ 0, c ≠ ∞)
            = ofReal((rᵏ)⁻¹) · F(R·r).

6. (Conclusion.) The set (0, ∞) belongs to 𝓝[>] 0, so the identity of step 5 holds eventually along 𝓝[>] 0. By step 4 and `Tendsto.congr'`, ofReal((rᵏ)⁻¹) · F(R·r) → 0 as r → 0+. Since R > 0 was arbitrary, this proves the claim. ∎

Formalization notes. This exact argument compiled as the body of `theorem Submission.iwl_imc_quotient_rescale_tendsto_zero` (frozen type above) in a scratch build of frozen commit d8d46c9. Its axioms are propext, Classical.choice and Quot.sound.
  intro k F hF R hR
  have hmap : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hR hr
  have hlim := ENNReal.Tendsto.const_mul (hF.comp hmap)
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (R ^ k) ≠ ∞))
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  have hRk : 0 < R ^ k := pow_pos hR k
  have hrk : 0 < r ^ k := pow_pos hr' k
  have hRk0 : ENNReal.ofReal (R ^ k) ≠ 0 := by simpa using hRk
  simp only [Function.comp_apply]
  rw [mul_pow, ENNReal.ofReal_mul hRk.le, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hRk0) (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc, ← mul_assoc,
    ENNReal.mul_inv_cancel hRk0 ENNReal.ofReal_ne_top, one_mul, ENNReal.ofReal_inv_of_pos hrk]

## Key steps

1. c := ofReal(Rᵏ) satisfies 0 < c < ∞ because R > 0.
2. r ↦ R·r maps 𝓝[>] 0 into 𝓝[>] 0, so F(Rr)/ofReal((Rr)ᵏ) → 0 as r → 0+.
3. Multiplying by the finite constant c keeps the limit 0.
4. For r > 0, c·F(Rr)/ofReal((Rr)ᵏ) = ofReal((rᵏ)⁻¹)·F(Rr) since ofReal((Rr)ᵏ) = c·ofReal(rᵏ); conclude with Tendsto.congr' along 𝓝[>] 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (identical)`
- `rg -n 'lpf_wtc_ae_zero_density_off_set|iwl_imc_quotient_rescale_tendsto_zero|iwl_imc_density_zero_off_set' local-references/197bdd4b88278494 (no match; the snapshot is the frozen contract)`
- `rg -n 'dimensionalUpperDensity' project/GMT/Ch06/Contract.lean (lines 38, 346)`
- `rg -n 'theorem ofReal_inv_of_pos|theorem exists_inv_nat_lt|protected theorem mul_inv |protected theorem mul_inv_cancel |protected theorem div_eq_inv_mul' mathlib/Mathlib/Basic/ENNReal/Inv.lean (945, 650, 245, 103, 48)`
- `rg -n 'theorem ofReal_mul |theorem ofReal_pow ' mathlib/Mathlib/Basic/ENNReal/Real.lean (297, 306); grep ofReal_ne_top Basic/ENNReal/Basic.lean:346; rg 'theorem rpow_natCast' Analysis/SpecialFunctions/Pow/NNReal.lean:686`
- `rg -n 'tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within|self_mem_nhdsWithin' mathlib/Mathlib/Topology/NhdsWithin.lean (470, 150; nhdsWithin_le_nhds 188); 'protected theorem Tendsto.const_mul' Topology/Instances/ENNReal/Lemmas.lean:354; Filter.Tendsto.const_mul Topology/Algebra/Monoid/Defs.lean:132; Tendsto.congr' and Tendsto.comp Order/Filter/Tendsto.lean:104,122`
- `grep -rn 'withDensity_apply|restrict_restrict|exists_measurable_subset_ae_eq|setLIntegral_measure_zero|measure_eq_iInf_isOpen|of_pseudoMetrizableSpace_of_isFiniteMeasure|isOpen_biUnion_countable|ae_ball_iff|tendsto_of_le_liminf_of_limsup_le' mathlib/Mathlib (WithDensity.lean:44, Restrict.lean:205, NullMeasurable.lean:214, Integral/Lebesgue/Basic.lean:478, Regular.lean:368 and 1072, Topology/Bases.lean:942, OuterMeasure/AE.lean:163, Topology/Order/LiminfLimsup.lean:305)`
- `python3 dag.json scans: lean_name/lean_statement/status/candidate_commit of lpf_wtc_ae_zero_density_off_set, rectifiability_density_comparison, imc_ae_zero_density_off_set, fiw_tl_tr_scaling_limit, all nodes mentioning dimensionalUpperDensity or rescal*; name-collision check for iwl_imc_quotient_rescale_tendsto_zero (none)`
- `git show 12d217bb:GMT/Ch06/Submission.lean (accepted proof of Submission.lpf_wtc_ae_zero_density_off_set, lines 362-527); cat nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/isolated-comparator-result.json (passed: true)`
- `sed runtime.py (flows dce97d36d07f and d253855dab51): _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _publish_decomposition_workspace; store.py refresh/ensure; parallel.enabled; prompts.py DECOMPOSITION_AUDIT and SPECULATIVE_PARENT_TASK; issue-workers.json worker start times`
- `grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity' simongmt Chapter01/Densities.lean (39, 44); grep realUnitBallVolume_pos/_ne_top Chapter01/Hausdorff.lean (499, 506)`
- `sed -n 600,712p book/chapter-01.txt (Simon Ch. 1, 3.3 density comparison, 3.6 Upper Density Theorem, 3.7(2) localization)`
- `lean v4.35.0-rc3 scratch /tmp/dzos-split-r4lR6b with LEAN_PATH over lake-packages-25730c7c: lean -o build/GMT/Ch06/Submission.olean (frozen); lean -o build2/GMT/Ch06/Submission.olean src/Submission2.lean; gmt-compare.child_modules contract mode -> checks/{lpf,resc,parent}_NodeChallenge.lean (frozen build) and _NodeSolution.lean (build2) with #print axioms; lean_contract.validate_lean_statement`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Monoid/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1-density-zero-off-set-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/issue-workers.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dzos-split-r4lR6b/src/Submission2.lean`
- `/tmp/dzos-split-r4lR6b/logs/sub2b.out`
- `/tmp/dzos-split-r4lR6b/checks/resc_NodeSolution.lean`
- `/tmp/dzos-split-r4lR6b/checks/parent_NodeChallenge.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract, and Submission is byte-identical to it. No snapshot file mentions lpf_wtc_ae_zero_density_off_set or the new name (rg: no match), as expected for a frozen contract.

Every Mathlib lemma used by both child proofs exists at the cited snapshot lines:
- ENNReal arithmetic: Basic/ENNReal/Inv.lean and Real.lean;
- filters: NhdsWithin.lean and Instances/ENNReal/Lemmas.lean;
- measure theory: WithDensity.lean, Restrict.lean, NullMeasurable.lean and Regular.lean.

The DAG holds the accepted theorem lpf_wtc_ae_zero_density_off_set (status accepted, candidate 12d217bb, isolated comparator passed). Its hypotheses are identical to the selected node's, and its conclusion is the case R = 1. The controller's code permits reusing it by name with the identical type.

Scratch Lean confirms the split:
- both child types and the parent type elaborate in the comparator child scope;
- the new child's proof and the parent assembly compile together with lpf's accepted proof;
- axioms: propext, Classical.choice, Quot.sound.
