# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.carrier_null_measurable-a1`
- Child DAG node: `root.first_rectifiability-a1.carrier_null_measurable-a1.uniform_lower_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 ("Uniform pieces") of the supplied proof of frt_carrier_nullMeasurable, isolated for one point x and a general density value t ∈ (0, ∞]. In the parent it is applied with μ := V.weight, x ∈ M and t := ENNReal.ofReal θ(x), which is > 0 because θ(x) > 0 (ENNReal.ofReal_pos). The supplied indices m ≥ 1 and k ≥ 1 are written here as m + 1 and k + 1 with m, k ∈ ℕ. The supplied clause θ(x) ≥ 1/m only serves to choose m and does not appear in the conclusion.

Conventions. Inequalities between extended reals are in ℝ≥0∞ = [0, ∞], where 0⁻¹ = ∞ and ∞⁻¹ = 0. B_ρ(x) := closedBall x ρ, ω_n := unitBallVolume n, and densityRatio n μ x ρ = μ(B_ρ(x)) / (ω_n · ENNReal.ofReal(ρ)^n). The hypothesis HasDensity n μ x t means Tendsto (densityRatio n μ x) (𝓝[>] 0) (𝓝 t), i.e. the ratio tends to t as ρ ↓ 0. The proof uses no property of μ or of ω_n.

1. Choice of m (the source's "choose m with θ(x) ≥ 1/m"). Since t > 0, t ≠ 0. By the Archimedean property of ℝ≥0∞ (ENNReal.exists_inv_nat_lt, Mathlib/Basic/ENNReal/Inv.lean:650) there is m ∈ ℕ with (m : ℝ≥0∞)⁻¹ < t. Since m ≤ m + 1 and inversion on ℝ≥0∞ is antitone (ENNReal.inv_le_inv, Inv.lean:302), (m + 1)⁻¹ ≤ m⁻¹ < t. In particular (m + 1)⁻¹ ≤ t.

2. Strict gap (the source's "ENNReal.ofReal θ(x) > (2m)⁻¹"). Let a := (m : ℝ≥0∞) + 1 and c := (2a)⁻¹.
- a ≠ 0, because a ≥ 1, and a ≠ ∞, because a is a sum of two finite numbers.
- Since 1 < 2 and a ∉ {0, ∞}, multiplication by a preserves the strict inequality (ENNReal.mul_lt_mul_left, Mathlib/Basic/ENNReal/Operations.lean:62). So a = 1·a < 2·a.
- Inversion on ℝ≥0∞ is strictly antitone (ENNReal.inv_lt_inv, Inv.lean:292). Hence, using Step 1, c = (2a)⁻¹ < a⁻¹ ≤ t, i.e. c < t.

3. Eventual strict bound. The interval Ioi c = (c, ∞] is open in the order topology of ℝ≥0∞ and contains t by Step 2. So it is a neighbourhood of t (Ioi_mem_nhds, Mathlib/Topology/Order/OrderClosed.lean:227). By the hypothesis HasDensity n μ x t, its preimage S := {ρ ∈ ℝ : c < densityRatio n μ x ρ} belongs to 𝓝[>] 0.

4. A uniform interval. ℝ has no greatest element, so by mem_nhdsGT_iff_exists_Ioo_subset (Mathlib/Topology/Order/LeftRightNhds.lean:104) there is a real u > 0 with (0, u) ⊆ S. By the Archimedean property of ℝ (exists_nat_one_div_lt, Mathlib/Algebra/Order/Archimedean/Basic.lean:211) there is k ∈ ℕ with 1/(k + 1) < u.

5. Conclusion. Let ρ ∈ ℝ with 0 < ρ ≤ 1/(k + 1). Then ρ < u, so ρ ∈ (0, u) ⊆ S, i.e. c < densityRatio n μ x ρ. Hence (2((m : ℝ≥0∞) + 1))⁻¹ = c ≤ densityRatio n μ x ρ, and the pair (m, k) is as required. The case t = ∞ is included: Step 1 then holds for every m, and Ioi c is a neighbourhood of ∞ because c < ∞. ∎

## Key steps

1. t ≠ 0 gives m ∈ ℕ with m⁻¹ < t (ENNReal.exists_inv_nat_lt), hence (m+1)⁻¹ ≤ t by antitonicity of inversion.
2. a := m+1 ∈ (0,∞) satisfies a < 2a, so c := (2a)⁻¹ < a⁻¹ ≤ t (ENNReal.mul_lt_mul_left, ENNReal.inv_lt_inv).
3. Ioi c is a neighbourhood of t (Ioi_mem_nhds), so by HasDensity the set {ρ : c < densityRatio n μ x ρ} lies in 𝓝[>] 0.
4. mem_nhdsGT_iff_exists_Ioo_subset gives u > 0 with the strict bound on (0,u); exists_nat_one_div_lt gives k with 1/(k+1) < u.
5. For 0 < ρ ≤ 1/(k+1), ρ ∈ (0,u), so c < densityRatio n μ x ρ and hence (2(m+1))⁻¹ ≤ densityRatio n μ x ρ.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (both 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'exists_iUnion_isClosed' mathlib/Mathlib (Topology/MetricSpace/HausdorffDistance.lean:207 IsOpen.exists_iUnion_isClosed)`
- `rg -n 'theorem exists_inv_nat_lt|theorem le_div_iff_mul_le|theorem Tendsto.const_mul' mathlib/Mathlib (Basic/ENNReal/Inv.lean:650, :369; Topology/Instances/ENNReal/Lemmas.lean:354)`
- `rg -n 'theorem inv_le_inv|theorem inv_lt_inv|theorem mul_lt_mul_left' mathlib/Mathlib/Basic/ENNReal (Inv.lean:302, :292; Operations.lean:62)`
- `rg -n 'theorem mem_nhdsGT_iff_exists_Ioo_subset|theorem Ioo_mem_nhdsLT|theorem Ioi_mem_nhds|lemma exists_nat_one_div_lt|lemma le_limsup_of_frequently_le' mathlib/Mathlib (Topology/Order/LeftRightNhds.lean:104; Topology/Order/OrderClosed.lean:282 with @[to_dual] Ioo_mem_nhdsGT, :227; Algebra/Order/Archimedean/Basic.lean:211; Order/LiminfLimsup.lean:241)`
- `rg -n 'theorem measure_ball_pos|theorem measure_ball_lt_top|theorem mem_closure_iff |theorem le_of_tendsto |theorem of_null|protected theorem iUnion|protected theorem diff|theorem continuous_ofReal|theorem continuous_pow|lemma volume_euclideanSpace_eq_dirac' (OpenPos.lean:212; Typeclasses/Finite.lean:373; MetricSpace/Pseudo/Defs.lean:1220; OrderClosed.lean:133; NullMeasurable.lean:111/133/174; ENNReal/Lemmas.lean:69/406; Haar/InnerProductSpace.lean:142)`
- `grep -n 'isOpen_domain|weight_finite_on_compact|def weight|abbrev Euclidean' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean (336, 576, 557, 54)`
- `python3 -I: contract_scope/child_modules from verifier/gmt-compare.py and validate_lean_statement from verifier/lean_contract.py on both child statements (pass; namespace GMT.Ch08, replay: opens, namespace GMT.Ch08, section/end Definitions)`
- `lake env lean /tmp/cnm-scratch-k7q2/Full.lean (both children proved sorry-free; #print axioms = propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/cnm-scratch-k7q2/Assembly.lean (sibling + both children as sorry'd frozen interfaces; parent proof sorry-free; target `exact Submission.frt_carrier_nullMeasurable` at the frozen parent type)`
- `lake env lean /tmp/cnm-scratch-k7q2/Ch_{uniform_lower_density,closure_lower_density}_{Challenge,Solution}.lean (comparator form; solutions use only standard axioms)`
- `python3 collision check of frt_cnm_* against dag.json lean_name values (184 nodes) and nodes/*/*.json; git grep over all refs; grep -r over workspaces/ (no hits)`
- `python3 survey of nodes/*/decomposition-v1.json should_split/rationale (DAG split precedent)`
- `grep -n 'measurable' book/chapter-08.txt (printed proof of 1.2 delegates 'M is H^n-measurable' to Ch. 3, 1.9, lines 150-155)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/LeftRightNhds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-carrier-null-measurable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-hausdorff-null-of-weight-null-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/tmp/cnm-scratch-k7q2/Full.lean`
- `/tmp/cnm-scratch-k7q2/Assembly.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Contract.lean and Submission.lean are byte-identical (2e5cd5b3…).

No varifold or GMT lemma in Mathlib or SimonGMT states either child, so both children are new. Each is proved only from facts that do exist in the pinned Mathlib (file:line in the snapshot):
- ENNReal.exists_inv_nat_lt: Inv.lean:650
- ENNReal.inv_le_inv / inv_lt_inv: Inv.lean:302 / :292
- ENNReal.mul_lt_mul_left: Operations.lean:62
- ENNReal.le_div_iff_mul_le: Inv.lean:369
- ENNReal.Tendsto.const_mul: ENNReal/Lemmas.lean:354
- ENNReal.continuous_ofReal / continuous_pow: ENNReal/Lemmas.lean:69 / :406
- Ioi_mem_nhds: OrderClosed.lean:227
- Ioo_mem_nhdsLT/GT: OrderClosed.lean:282, the GT form via @[to_dual]
- mem_nhdsGT_iff_exists_Ioo_subset: LeftRightNhds.lean:104
- exists_nat_one_div_lt: Archimedean/Basic.lean:211
- Metric.measure_ball_pos: OpenPos.lean:212
- measure_ball_lt_top: Typeclasses/Finite.lean:373
- Metric.mem_closure_iff: Pseudo/Defs.lean:1220
- le_of_tendsto: OrderClosed.lean:133

The parent assembly additionally uses:
- IsOpen.exists_iUnion_isClosed: HausdorffDistance.lean:207. It makes the supplied Step 2 a one-liner, so Step 2 gets no child.
- le_limsup_of_frequently_le: LiminfLimsup.lean:241
- NullMeasurableSet.of_null / iUnion / diff: NullMeasurable.lean:111/133/174
- SimonGMT Varifold.isOpen_domain and weight_finite_on_compact: Varifold.lean:336/576

In scratch files importing GMT.Ch08.Submission with the comparator's replayed scope, both child statements elaborate and pass validate_lean_statement. The comparator-generated NodeChallenge/NodeSolution files compile. Both children are fully proved using only propext, Classical.choice and Quot.sound. The parent assembly checks against the sorry'd frozen interfaces of the sibling and both children, with no sorry of its own.

The pinned Mathlib deprecates Set.diff_subset/mem_diff in favour of sdiff_subset/mem_sdiff. The names frt_cnm_exists_uniform_densityRatio_lower and frt_cnm_densityRatio_lower_closure collide with nothing in the DAG, the node JSONs, git refs or the workspaces.
