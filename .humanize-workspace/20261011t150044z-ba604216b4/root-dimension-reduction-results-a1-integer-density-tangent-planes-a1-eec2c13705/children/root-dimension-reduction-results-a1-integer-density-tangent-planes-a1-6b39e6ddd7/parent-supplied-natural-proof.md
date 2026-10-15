# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.planes_union_vertex_density-a1.density_of_ball_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof.
1. (0 < ω_n < ∞.) ω_n = unitBallVolume n = volume(B_1(0)), the volume of the open unit ball of Euclid n.
   - B_1(0) is open and nonempty (it contains 0), and volume on Euclid n is an additive Haar measure, hence positive on nonempty open sets (IsOpen.measure_pos). So ω_n ≠ 0.
   - Euclid n is a proper space and volume is finite on compact sets, so volume(B_1(0)) < ∞ (measure_ball_lt_top). So ω_n ≠ ∞.
   (This also covers n = 0, where Euclid 0 is a point.)
2. (Nondegenerate normalization.) Let 0 < ρ < r and a_ρ := ω_n·ofReal(ρⁿ). Since ρⁿ > 0 (pow_pos), ofReal(ρⁿ) ∈ (0, ∞) (ENNReal.ofReal_pos, ENNReal.ofReal_ne_top). With step 1, a_ρ ≠ 0 (mul_ne_zero) and a_ρ ≠ ∞ (ENNReal.mul_ne_top).
3. (The ratio is constant.) For 0 < ρ < r, the hypothesis and step 2 give M_{B_ρ(x)}(T)/a_ρ = (ofReal(θ)·a_ρ)/a_ρ = ofReal(θ) (ENNReal.mul_div_cancel_right).
4. (Limit.) Since r > 0, the interval (0, r) belongs to the filter 𝓝[>] 0 (Ioo_mem_nhdsGT). By step 3, the function ρ ↦ M_{B_ρ(x)}(T)/(ω_n·ofReal(ρⁿ)) is eventually equal along 𝓝[>] 0 to the constant ofReal(θ). Hence it tends to ofReal(θ) (tendsto_const_nhds.congr').
5. Together with the hypothesis 0 ≤ θ, this is exactly the definition of HasMassDensity T x θ. ∎

## Key steps

1. ω_n is the volume of a nonempty bounded open set, so 0 < ω_n < ∞; hence 0 < ω_n·ofReal(ρⁿ) < ∞ for ρ > 0.
2. For 0 < ρ < r the density ratio equals ofReal(θ)·a/a = ofReal(θ).
3. (0, r) ∈ 𝓝[>] 0, so the ratio is eventually constant and tends to ofReal(θ); with θ ≥ 0 this is HasMassDensity T x θ.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-eec2c13705/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git show 739de92ed9c1c966a024107e882db5b7c5000276:GMT/Ch07/Submission.lean (this node's proof base) compared with Contract.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json and lakefile.toml)`
- `grep -rn restrictDomain .lake/packages/simongmt/Poincare/SimonGMT/; cat Chapter06/CurrentLocalEquality.lean Chapter06/Mass.lean; sed -n 1,560p Chapter06/Currents.lean`
- `python3 scans of dag.json lean_statement/lean_name/status for: 'restrictDomain'; 'testFormOnInclusion'; 'HasMassDensity' with 'unitBallVolume' or 'massOn (ball ...) ='; 'Measure (Euclid P)' with 'IsOpen'; 'IsConnected' with 'Submodule'; lean_name 'support_eq_inter'; exact frozen types and statuses of idtp_planar_cycle_eq_const_mul, idtp_tdc_subspace_ball_measure, dimred_im_mass_measure, dtc_restrictDomain_isIntegerMultiplicity, rsd_cmr_support_eq_inter, dtc_massOn_eq_of_agreeOn, cmc_ml_measure_eq_of_eq_on_open_subsets, imrep_represents_support_eq_inter_measure_support, dor_ims_support_of_massOn_eq, dtc_vanish_off_support, dtc_localize, idtp_ccd_planar_support_mass`
- `python3 scan of accepted nodes whose natural proofs cite Submission.* lemmas outside their lineage, plus git show <candidate_commit>:GMT/Ch07/Submission.lean. It shows ancestor-prerequisite use (e.g. dorag_dbs_sharp_mass_ratio uses dorag_monotonicity_density, a prerequisite of its parent) and added import headers (e.g. dtc_blowUp_density adds Mathlib.MeasureTheory.Function.ContinuousMapDense)`
- `grep -rl 'idtp_tdc_puvd' .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/ workspaces/.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean workspaces/gmt-ch07/GMT (no match); lean_name collision scan over all 974 dag.json nodes (no match)`
- `grep -rn 'euclideanHausdorffMeasure_zero_or_top|euclideanHausdorffMeasure_zero|nullSingletonClass_hausdorff|hausdorffMeasure_zero_singleton|measure_compl_support|closed_of_finiteDimensional|isConnected_compl_singleton_of_one_lt_rank|ext_of_generateFrom_of_iUnion|Ioo_mem_nhdsGT|isOpen_iUnion_countable' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `sed -n 478,520p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `sed -n 1,120p, 305,388p verifier/gmt-compare.py; sed -n 1,80p verifier/lean_contract.py (child scope replay; only the frozen files other than Submission.lean are byte-checked)`
- `lake env lean /tmp/puvd-split/gen/Probe.lean /tmp/puvd-split/gen/Probe2.lean (#check of every cited Mathlib/SimonGMT name under the contract imports)`
- `lake env lean /tmp/puvd-split/final/Statements.lean (four `theorem Submission.X : (type) := by sorry` in the contract scope)`
- `lake env lean /tmp/puvd-split/final/Assembly.lean (#print axioms puvd_assembly_check)`
- `lake env lean /tmp/puvd-split/val/C1.lean /tmp/puvd-split/val/C2.lean /tmp/puvd-split/val/C3.lean /tmp/puvd-split/val/C4.lean (#print axioms c1_check … c4_check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/github-workflow.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-eec2c13705/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-eec2c13705/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-eec2c13705/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-15cbdbde67/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Connected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/puvd-split/gen/Probe.lean`
- `/tmp/puvd-split/gen/Probe2.lean`
- `/tmp/puvd-split/final/Statements.lean`
- `/tmp/puvd-split/final/Assembly.lean`
- `/tmp/puvd-split/val/C1.lean`
- `/tmp/puvd-split/val/C2.lean`
- `/tmp/puvd-split/val/C3.lean`
- `/tmp/puvd-split/val/C4.lean`
- `/tmp/puvd-split/external_types.json`

Pins and contract:
- Project HEAD b4d606db, mathlib 25730c7c and simongmt 2b366308 match manifest.json and lakefile.toml.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and to Submission.lean at this node's proof base 739de92e. No accepted lemma is pre-merged there, so accepted and prerequisite lemmas are cited by their frozen DAG types, as the supplied proof already does.

SimonGMT definitions used: restrictDomain(_apply), testFormOnInclusion(_coe), GeometricCurrentOn.boundary(_apply), exteriorDerivativeTestOn, zeroRegion/support, massOn.

Reuse:
- Accepted lemmas the children use: dtc_restrictDomain_isIntegerMultiplicity, rsd_cmr_support_eq_inter, dtc_massOn_eq_of_agreeOn, dimred_im_mass_measure, cmc_ml_measure_eq_of_eq_on_open_subsets, imrep_represents_support_eq_inter_measure_support.
- Still decomposing: idtp_planar_cycle_eq_const_mul (prerequisite of the ancestor two_dim_cone_density) and idtp_tdc_subspace_ball_measure (this node's sibling prerequisite).
- No existing node states any proposed child:
  - the only restriction-preserves-∂ = 0 result is dtc_localize, and only for U ∖ spt ∂T;
  - 'exact homogeneous ball mass implies density' appears only inside dtc_blowUp_density, bundled with blow-up convergence;
  - idtp_ccd_planar_support_mass is a different ball-plus-density statement.
- The four idtp_tdc_puvd_* names occur in no dag.json node, run node file or worktree source.

Mathlib:
- Every cited name exists and #checks under the contract imports, except isConnected_compl_singleton_of_one_lt_rank.
- That lemma needs `import Mathlib.Analysis.Normed.Module.Connected`. Its olean is present; the comparator byte-checks only the frozen files other than Submission.lean; and accepted candidates have added Mathlib imports before.
- plane_domain also gives an import-free route via Complex.cos_arg/sin_arg, which are available.

Lean:
- All four lean_statements elaborate as Submission.X stubs in the contract scope.
- Assembly.lean proves the exact frozen parent type from the four child types plus the frozen types of dimred_im_mass_measure and idtp_tdc_subspace_ball_measure. Its axioms are propext, Classical.choice and Quot.sound.
- Sorry-free validation proofs of all four children use only those three axioms.

Book: chapter-07.txt lines 505–510 (constancy of Θ on P_i ∖ {0}) is the source of the argument.
