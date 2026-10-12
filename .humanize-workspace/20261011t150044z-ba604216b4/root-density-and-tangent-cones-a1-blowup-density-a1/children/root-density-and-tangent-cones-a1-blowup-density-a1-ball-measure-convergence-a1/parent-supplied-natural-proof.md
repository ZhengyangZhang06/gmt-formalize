# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_density-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_density-a1.ball_measure_convergence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, i.e. Simon 7.3.1 proof, display (4) (chapter-07.txt lines 348–351). The compact sets F of the parent's step 3(i) are taken to be closed balls, so inner regularity is replaced by continuity from below. Hypotheses in the order of the Lean statement: (H1) ρ > 0; (H2) μ(B_r(0)) ≠ ∞ for every r > 0; (H3) for every r > 0, μ_j(B_r(0)) ≠ ∞ for all sufficiently large j; (H4) ∫f dμ_j → ∫f dμ for every continuous compactly supported f : ℝ^P → ℝ; (H5) μ(sphere(0, ρ)) = 0. All measures live on the Borel sets of ℝ^P. ofReal : ℝ → [0, ∞] is continuous and monotone. ∫ denotes the Bochner integral, which is 0 for non-integrable functions.
1. Cut-off functions. For real a < b let φ_{a,b}(y) := min(1, max(0, (b − |y|)/(b − a))). It is continuous and 0 ≤ φ_{a,b} ≤ 1. Also φ_{a,b}(y) = 1 if |y| ≤ a (then (b − |y|)/(b − a) ≥ 1), and φ_{a,b}(y) = 0 if |y| ≥ b. Hence support φ_{a,b} ⊆ B_b(0) and tsupport φ_{a,b} ⊆ closedBall(0, b), which is compact because ℝ^P is proper. So φ_{a,b} is continuous with compact support.
2. Integral comparisons. Let ν be any measure on ℝ^P, let a < b with b > 0, and put φ := φ_{a,b}.
 (i) ofReal(∫φ dν) ≤ ν(B_b(0)). Since φ ≥ 0 is measurable, ∫φ dν = (∫⁻ ofReal(φ) dν).toReal, whether or not φ is ν-integrable (integral_eq_lintegral_of_nonneg_ae; if the lintegral is ∞ both sides are 0). Therefore ofReal(∫φ dν) ≤ ∫⁻ ofReal(φ) dν, using ofReal(t.toReal) ≤ t. Since ofReal(φ) ≤ 1_{B_b(0)} pointwise, ∫⁻ ofReal(φ) dν ≤ ν(B_b(0)).
 (ii) If ν(B_b(0)) < ∞, then ν(E) ≤ ofReal(∫φ dν) for every measurable E on which φ = 1. Indeed, 1_E ≤ ofReal(φ) pointwise gives ν(E) ≤ ∫⁻ ofReal(φ) dν ≤ ν(B_b(0)) < ∞. As this lintegral is finite, ofReal((∫⁻ ofReal(φ) dν).toReal) = ∫⁻ ofReal(φ) dν, and the formula in (i) gives the claim.
3. Lower bound: μ(B_ρ(0)) ≤ liminf_j μ_j(B_ρ(0)). Fix k ∈ ℕ, put a_k := ρ − 1/(k+1) < ρ and φ := φ_{a_k, ρ}.
- By (H4), ∫φ dμ_j → ∫φ dμ, hence ofReal(∫φ dμ_j) → ofReal(∫φ dμ).
- By 2(i) (ν = μ_j, b = ρ), ofReal(∫φ dμ_j) ≤ μ_j(B_ρ(0)) for every j. So ofReal(∫φ dμ) = lim_j ofReal(∫φ dμ_j) ≤ liminf_j μ_j(B_ρ(0)).
- By 2(ii) (ν = μ, with μ(B_ρ(0)) < ∞ by (H1)–(H2), and E = closedBall(0, a_k)), μ(closedBall(0, a_k)) ≤ ofReal(∫φ dμ) ≤ liminf_j μ_j(B_ρ(0)).
The closed balls closedBall(0, a_k) increase in k and their union is B_ρ(0): a_k < ρ, and |y| < ρ implies |y| ≤ a_k for large k. By continuity of measure from below, μ(B_ρ(0)) = sup_k μ(closedBall(0, a_k)) ≤ liminf_j μ_j(B_ρ(0)).
4. Upper bound: limsup_j μ_j(closedBall(0, ρ)) ≤ μ(closedBall(0, ρ)). Fix k ∈ ℕ, put b_k := ρ + 1/(k+1) and g := φ_{ρ, b_k}, so g = 1 on closedBall(0, ρ) and g = 0 outside B_{b_k}(0).
- By (H3) there is j_0 with μ_j(B_{b_k}(0)) < ∞ for all j ≥ j_0. For such j, 2(ii) (ν = μ_j, E = closedBall(0, ρ)) gives μ_j(closedBall(0, ρ)) ≤ ofReal(∫g dμ_j).
- By (H4), ofReal(∫g dμ_j) → ofReal(∫g dμ). Hence limsup_j μ_j(closedBall(0, ρ)) ≤ ofReal(∫g dμ), and ofReal(∫g dμ) ≤ μ(B_{b_k}(0)) by 2(i) (ν = μ).
The open balls B_{b_k}(0) decrease in k and their intersection is closedBall(0, ρ). Also μ(B_{b_0}(0)) = μ(B_{ρ+1}(0)) < ∞ by (H2). By continuity of measure from above, inf_k μ(B_{b_k}(0)) = μ(closedBall(0, ρ)). Hence limsup_j μ_j(closedBall(0, ρ)) ≤ μ(closedBall(0, ρ)).
5. Null boundary. closedBall(0, ρ) = B_ρ(0) ∪ sphere(0, ρ). By subadditivity and (H5), μ(closedBall(0, ρ)) ≤ μ(B_ρ(0)) + μ(sphere(0, ρ)) = μ(B_ρ(0)).
6. Conclusion. Since μ_j(B_ρ(0)) ≤ μ_j(closedBall(0, ρ)), steps 4, 5 and 3 give limsup_j μ_j(B_ρ(0)) ≤ limsup_j μ_j(closedBall(0, ρ)) ≤ μ(closedBall(0, ρ)) ≤ μ(B_ρ(0)) ≤ liminf_j μ_j(B_ρ(0)). In the complete linear order [0, ∞] with its order topology, liminf ≥ L ≥ limsup implies convergence to L (tendsto_of_le_liminf_of_limsup_le; the boundedness side conditions are automatic in [0, ∞]). Hence μ_j(B_ρ(0)) → μ(B_ρ(0)). This is the portmanteau sandwich; Mathlib's Portmanteau file is not imported by GMT.Ch07.Submission, so the sandwich is carried out directly as above.

## Key steps

1. Radial piecewise-linear cut-offs φ_{a,b} are continuous with compact support, 0 ≤ φ ≤ 1, equal to 1 on closedBall(0,a) and 0 off B_b(0).
2. ofReal(∫φ dν) ≤ ν(B_b(0)) for every ν, and ν(E) ≤ ofReal(∫φ dν) when ν(B_b(0)) < ∞ and φ = 1 on E (via ∫φ = (∫⁻ ofReal φ).toReal).
3. Lower bound μ(B_ρ(0)) ≤ liminf μ_j(B_ρ(0)), via φ_{ρ−1/(k+1), ρ} and continuity from below over closed balls.
4. Upper bound limsup μ_j(closedBall(0,ρ)) ≤ μ(closedBall(0,ρ)), via φ_{ρ, ρ+1/(k+1)}, eventual finiteness of μ_j on balls, and continuity from above.
5. The null sphere gives μ(closedBall(0,ρ)) ≤ μ(B_ρ(0)); the liminf/limsup sandwich in [0, ∞] gives convergence.

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
