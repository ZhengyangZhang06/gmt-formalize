# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_density-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_density-a1.rescaled_ball_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof, i.e. Simon 7.3.1 proof, display (1) with "for each R > 0" (chapter-07.txt lines 329–335), restated for measures. Hypotheses in the order of the Lean statement: (H1) λ_j > 0 for every j; (H2) λ_j → 0; (H3) q(r) := μ(B_r(x))/(ω_n·ofReal(rⁿ)) → ofReal θ as r → 0 in the filter 𝓝[>] 0, where ω_n := unitBallVolume n and / is division in [0, ∞]; (H4) μ_j(s) = ofReal((λ_j⁻¹)ⁿ)·μ((dilation x λ_j)⁻¹(s)) for every j and every measurable s. Fix ρ > 0 and put K := ω_n·ofReal(ρⁿ).
1. 0 < ω_n < ∞. ω_n is the volume of the open unit ball B_1(0) of Euclid n = EuclideanSpace ℝ (Fin n), whose volume is an additive Haar measure. It is positive on the nonempty open set B_1(0) (Metric.measure_ball_pos) and finite on the bounded set B_1(0) (measure_ball_lt_top; Euclid n is proper). This holds for every n, including n = 0 (a one-point space, ω_0 = 1). Hence K ≠ ∞. For every r > 0, L_r := ω_n·ofReal(rⁿ) satisfies L_r ≠ 0 (as ofReal(rⁿ) > 0) and L_r ≠ ∞.
2. Preimages of balls. Let λ > 0 and y ∈ ℝ^P. By the definitions of dilation and dilationCLM, dilation x λ y = −(λ⁻¹•x) + dilationCLM P λ y = −(λ⁻¹•x) + λ⁻¹•y = λ⁻¹•(y − x). Hence |dilation x λ y| = λ⁻¹·|y − x|, and |dilation x λ y| < ρ ⟺ |y − x| < λρ (multiply by λ > 0) ⟺ dist(y, x) < λρ. Thus (dilation x λ)⁻¹(B_ρ(0)) = B_{λρ}(x).
3. Fix j. B_ρ(0) is open, hence measurable. So (H4) and step 2 (with λ = λ_j > 0 by (H1)) give μ_j(B_ρ(0)) = ofReal((λ_j⁻¹)ⁿ)·μ(B_{λ_jρ}(x)).
4. Algebra in [0, ∞]. Let λ := λ_j, r := λρ > 0 and A := μ(B_r(x)) ∈ [0, ∞]. Since a/b = a·b⁻¹ in [0, ∞], K·(A/L_r) = (K/L_r)·A for every A, including A = ∞ (ENNReal.mul_comm_div). Moreover:
- K/L_r = (ω_n·ofReal(ρⁿ))/(ω_n·ofReal(rⁿ)) = ofReal(ρⁿ)/ofReal(rⁿ), cancelling the common factor ω_n ∉ {0, ∞} (ENNReal.mul_div_mul_left);
- ofReal(ρⁿ)/ofReal(rⁿ) = ofReal(ρⁿ/rⁿ), since rⁿ > 0 (ENNReal.ofReal_div_of_pos);
- ofReal(ρⁿ/rⁿ) = ofReal((λ⁻¹)ⁿ), because rⁿ = λⁿρⁿ and ρⁿ/(λⁿρⁿ) = (λ⁻¹)ⁿ for λ, ρ ≠ 0.
Combining with step 3: μ_j(B_ρ(0)) = K·q(λ_jρ) for every j.
5. By (H2), λ_jρ → 0·ρ = 0, and λ_jρ > 0 for every j by (H1). Hence λ_jρ → 0 in the filter 𝓝[>] 0 (tendsto_nhdsWithin_iff). Composing with (H3), q(λ_jρ) → ofReal θ.
6. Multiplication by the constant K ≠ ∞ is continuous on [0, ∞] (ENNReal.Tendsto.const_mul with side condition K ≠ ∞). So K·q(λ_jρ) → K·ofReal θ = ω_n·ofReal(ρⁿ)·ofReal θ. By step 4 the sequence μ_j(B_ρ(0)) coincides term by term with K·q(λ_jρ), so μ_j(B_ρ(0)) → ω_n·ofReal(ρⁿ)·ofReal θ.

## Key steps

1. 0 < ω_n < ∞ for every n (volume on Euclid n is an additive Haar measure), so K = ω_n·ofReal(ρⁿ) ≠ ∞.
2. (dilation x λ)⁻¹(B_ρ(0)) = B_{λρ}(x) for λ > 0, since dilation x λ y = λ⁻¹(y − x).
3. μ_j(B_ρ(0)) = ofReal((λ_j⁻¹)ⁿ)·μ(B_{λ_jρ}(x)) = K·q(λ_jρ), where q(r) = μ(B_r(x))/(ω_n·ofReal(rⁿ)), by cancelling ω_n in [0, ∞].
4. λ_jρ → 0 in 𝓝[>] 0, so q(λ_jρ) → ofReal θ.
5. Multiplying by the finite constant K gives μ_j(B_ρ(0)) → ω_n·ofReal(ρⁿ)·ofReal θ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp … GMT/Ch07/Submission.lean (identical; snapshot project b4d606d, mathlib 25730c7c)`
- `rg -n 'theorem countable_meas_level_set_pos|theorem countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top|theorem countable_meas_pos_of_disjoint_iUnion' mathlib/Mathlib`
- `rg -n 'tendsto_measure_of_null_frontier|le_liminf_measure_open_of_tendsto|limsup_measure_closed_le_of_tendsto' mathlib/Mathlib; sed -n 180,280p mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean (tendsto_measure_of_le_liminf_measure_of_limsup_measure_le)`
- `grep -n 'cancel|div_self|mul_div_mul' mathlib/Mathlib/Basic/ENNReal/Inv.lean (mathlib/Mathlib/Data/ENNReal/Inv.lean is a deprecated stub re-exporting Mathlib.Basic.ENNReal.Inv)`
- `rg -n 'liminf|limsup|sphere|frontier' project/GMT`
- `rg -n 'null_frontier|sphere.*= 0|measure_sphere|frontier.*= 0|vague|VaguelyConverges|RadonConverges|WeaklyConvergesMeasure' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `rg -l 'dtc_rescaled_ball_measure_tendsto|dtc_tendsto_measure_ball_of_vague|dtc_measure_ball_eq_of_null_sphere' .humanize/ and git grep over all local branches (no match)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the three child types`
- `lake env lean /tmp/bd-decomp-7a1/{Assembly,Print,A/ChildA,B/ChildB,C/ChildC,Combined}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/bd-decomp-7a1/Assembly.lean`
- `/tmp/bd-decomp-7a1/Print.lean`
- `/tmp/bd-decomp-7a1/A/ChildA.lean`
- `/tmp/bd-decomp-7a1/B/ChildB.lean`
- `/tmp/bd-decomp-7a1/C/ChildC.lean`
- `/tmp/bd-decomp-7a1/Combined.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

No existing lemma fits. Neither the snapshot project (project/GMT) nor SimonGMT has a lemma linking vague convergence of plain Measure (Euclid P) to ball measures, or extending an identity across null-sphere radii. SimonGMT's RadonConverges (Chapter08/VarifoldConvergence.lean) concerns varifolds and does not apply. The three children are therefore new.

Mathlib supplies the ingredients:
- countably many charged spheres: Measure.countable_meas_level_set_pos and countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top (SFinite.lean);
- density of good radii: Set.Countable.measure_zero with Real.volume_Ioo;
- the cut-off sandwich: integral_eq_lintegral_of_nonneg_ae, Monotone.measure_iUnion, Antitone.measure_iInter, tendsto_measure_iUnion_atTop, tendsto_of_le_liminf_of_limsup_le;
- the scaling step: ENNReal.mul_div_mul_left, ENNReal.mul_comm_div, ENNReal.ofReal_div_of_pos, ENNReal.Tendsto.const_mul, ENNReal.mul_div_cancel_right (Mathlib/Basic/ENNReal/Inv.lean), Metric.measure_ball_pos, measure_ball_lt_top.

The portmanteau lemma tendsto_measure_of_le_liminf_measure_of_limsup_measure_le (Portmanteau.lean) and Set.Countable.dense_compl are not in the import closure of GMT.Ch07.Submission, so the children's proofs avoid them.

Lean checks:
- All three child types elaborate in the replayed comparator scope and pass the validator.
- Scratch proofs of all three children compile with only propext, Classical.choice and Quot.sound.
- Combined.lean proves the exact frozen parent type from the three child types plus the frozen sibling types dtc_mass_eq_measure and dtc_blowUp_scaling. sorryAx comes only from the two sibling stubs.
- No name collision.
