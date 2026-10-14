# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1`
- Child DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.smooth_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (compact core) and the first two bullets of step 6 (smooth cut-off). The exceptional set {χ ≠ 1} will play the role of ℝ^P ∖ K in the parent's final estimate.

1. Compact core. We find a compact K ⊆ V with ν(V ∖ K) < ofReal δ. Note that ofReal δ > 0 because δ > 0, and ν(V) ≤ ν(ℝ^P) < ∞ because ν is finite.
   (a) Elementary argument (parent step 2). For j ≥ 1 let K_j := {y ∈ ℝ^P : ‖y‖ ≤ j and B(y, 1/j) ⊆ V}, where B(y, r) is the open ball.
   - For r > 0 the set A_r := {y : B(y, r) ⊆ V} is closed. Let y_k → y with y_k ∈ A_r, and let ‖z − y‖ < r. Since ‖z − y_k‖ ≤ ‖z − y‖ + ‖y − y_k‖ and ‖y − y_k‖ → 0, we have ‖z − y_k‖ < r for large k. So z ∈ B(y_k, r) ⊆ V, and hence B(y, r) ⊆ V.
   - So K_j = A_{1/j} ∩ closedBall(0, j) is closed and bounded in ℝ^P, hence compact (Heine–Borel).
   - K_j ⊆ V, because y ∈ B(y, 1/j) ⊆ V. Also K_j ⊆ K_{j+1}, because B(y, 1/(j+1)) ⊆ B(y, 1/j) and ‖y‖ ≤ j ≤ j + 1.
   - ⋃_j K_j = V. If y ∈ V, openness gives r > 0 with B(y, r) ⊆ V; for every integer j ≥ max(‖y‖, 1/r, 1) we have 1/j ≤ r, so y ∈ K_j.
   - The sets V ∖ K_j are Borel (V open, K_j closed), decrease, and have empty intersection. Since ν(V ∖ K_1) < ∞, continuity from above gives ν(V ∖ K_j) → 0.
   Choose j with ν(V ∖ K_j) < ofReal δ and put K := K_j.
   (b) Equivalent Mathlib route (the one used in the compiled check). From IsFiniteMeasure ν, Lean infers that ν is inner regular for compact sets on sets of finite measure (InnerRegularCompactLTTop ν). V is measurable because it is open. MeasurableSet.exists_isCompact_sdiff_lt, applied to V with ν V ≠ ∞ and ofReal δ ≠ 0, gives a compact K ⊆ V with ν(V ∖ K) < ofReal δ.

2. Open set in between. ℝ^P is locally compact and regular, K is compact, V is open, and K ⊆ V. So exists_open_between_and_isCompact_closure gives an open V₀ with K ⊆ V₀, closure V₀ ⊆ V, and closure V₀ compact.

3. Smooth Urysohn function. K is compact in the Hausdorff space ℝ^P, hence closed, and K ⊆ V₀ with V₀ open. Apply the smooth Urysohn lemma on the finite-dimensional space ℝ^P (exists_contDiff_support_eq_eq_one_iff, with smoothness order n := (⊤ : ℕ∞)). It gives χ : ℝ^P → ℝ with
   - ContDiff ℝ (⊤ : ℕ∞) χ, i.e. χ is C^∞ (an untyped ⊤ : WithTop ℕ∞ would mean analytic), and range χ ⊆ [0, 1];
   - support χ = V₀;
   - for every x, x ∈ K ⟺ χ(x) = 1.

4. Support and range. tsupport χ = closure(support χ) = closure V₀. Hence tsupport χ is compact, i.e. χ has compact support, and tsupport χ ⊆ V. For every x, χ(x) ∈ range χ ⊆ [0, 1], so 0 ≤ χ(x) ≤ 1.

5. Measure of the exceptional set. By step 3, {x : χ(x) ≠ 1} = ℝ^P ∖ K. Every point outside K lies in ℝ^P ∖ V or in V ∖ K. By monotonicity and subadditivity of ν and the hypothesis ν(ℝ^P ∖ V) = 0,
   ν({x : χ(x) ≠ 1}) = ν(ℝ^P ∖ K) ≤ ν(ℝ^P ∖ V) + ν(V ∖ K) = ν(V ∖ K) < ofReal δ.

Steps 3–5 give all the required properties of χ.

Lean note. A compiled route (no extra imports):
- `have := hν` makes the regularity instances available.
- Get K from `hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V) (ENNReal.ofReal_pos.mpr hδ).ne'`, and V₀ from `exists_open_between_and_isCompact_closure hKc hV hKV`.
- Get χ from `exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀`.
- Prove `tsupport χ = closure V₀` by `rw [tsupport, hχsupp]`; `HasCompactSupport χ` unfolds to `IsCompact (tsupport χ)`.
- Prove {x | χ x ≠ 1} = Kᶜ by `ext x; simp only [mem_ofPred_eq, mem_compl_iff, hχ1 x]`, then use `measure_mono` and `measure_union_le`.

## Key steps

1. Inner regularity gives a compact K ⊆ V with ν(V ∖ K) < δ, either from the exhaustion K_j = {‖y‖ ≤ j, B(y,1/j) ⊆ V} or from MeasurableSet.exists_isCompact_sdiff_lt.
2. There is an open V₀ with K ⊆ V₀ such that closure V₀ is compact and contained in V.
3. Smooth Urysohn lemma: a C^∞ χ with values in [0,1], support χ = V₀, and χ = 1 exactly on K.
4. tsupport χ = closure V₀ is compact and contained in V.
5. {χ ≠ 1} = ℝ^P ∖ K, so ν{χ ≠ 1} ≤ ν(ℝ^P ∖ V) + ν(V ∖ K) < δ.

## Reference use

### local-project

Queries:
- `cat nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1/parent-child-handoff.json parent-supplied-plan.md parent-supplied-natural-proof.json`
- `python3 -I scan of dag.json: lean_name and status of all nodes; nodes whose lean_statement mentions covectorEuclideanNorm; membership test for the five rsd_mw_tfa_ names (run at 222 and again at 261 nodes)`
- `grep -rl rsd_mw_tfa --include=*.lean --include=*.json workspaces/ (all 1399 swarm worktrees)`
- `grep -rn -e 'def covectorEuclideanNorm' -e 'def IsTestForm' -e 'abbrev DifferentialForm' -e 'abbrev Covector' simongmt/Poincare; grep -rn covectorEuclideanNorm simongmt (only _zero, _nonneg, _neg exist)`
- `grep -n -A 12 'theorem Integrable.exists_hasCompactSupport_integral_sub_le' -e 'theorem Integrable.exists_hasCompactSupport_lintegral_sub_le' Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `cat Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `grep -rn -A 8 -e 'theorem exists_contDiff_support_eq_eq_one_iff' -e 'theorem exists_open_between_and_isCompact_closure' -e 'theorem exists_compact_between' -e 'theorem exists_contDiff_tsupport_subset' Mathlib`
- `sed -n 830,860p Mathlib/MeasureTheory/Measure/Regular.lean (MeasurableSet.exists_isCompact_sdiff_lt)`
- `grep -rn -e uniformContinuous_of_continuous -e 'theorem HasCompactSupport.comp_left' -e 'theorem ContDiff.const_smul' -e 'theorem lintegral_const_mul' -e 'lemma inv_le_one_of_one_le₀' -e 'lemma ofReal_norm' -e 'mul_lt_mul_left' Mathlib`
- `sed -n 140,155p Mathlib/Analysis/InnerProductSpace/PiL2.lean; grep -n le_opNorm Mathlib/Analysis/Normed/Module/Alternating/Basic.lean; grep -n -e toLp_add -e toLp_smul -e toLp_apply Mathlib/Analysis/Normed/Lp/WithLp.lean Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `sed -n 255,388p verifier/gmt-compare.py (frozen_inputs removes Submission.lean; candidate_inputs)`
- `git show CANDIDATE_COMMIT:GMT/Ch07/Submission.lean | grep ^import, for every accepted node in dag.json`
- `cmp snapshot project/GMT/Ch07/Contract.lean and lake-manifest.json against the workspace; cmp snapshot mathlib ContinuousMapDense.lean SmoothApprox.lean PartitionOfUnity.lean Regular.lean against lake-packages-25730c7c/mathlib`
- `lake env lean /tmp/rsd-mw-tfa-split/Probe.lean (instances and lemma availability after import GMT.Ch07.Submission)`
- `lake env lean /tmp/rsd-mw-tfa-split/Probe2.lean (sub_smul behaviour on Covector)`
- `lake env lean /tmp/rsd-mw-tfa-split/Assembly.lean`
- `lake env lean /tmp/rsd-mw-tfa-split/Children.lean`
- `lake env lean /tmp/rsd-mw-tfa-split/Full.lean`
- `lake env lean /tmp/rsd-mw-tfa-split/NameCheck.lean`
- `reviewer: lake env lean /tmp/rsd-mw-tfa-review/Full.lean NoImport.lean OnlyCMD.lean OnlySA.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/rsd-mw-tfa-split/Probe.lean`
- `/tmp/rsd-mw-tfa-split/Probe2.lean`
- `/tmp/rsd-mw-tfa-split/Assembly.lean`
- `/tmp/rsd-mw-tfa-split/Children.lean`
- `/tmp/rsd-mw-tfa-split/Full.lean`
- `/tmp/rsd-mw-tfa-split/NameCheck.lean`
- `/tmp/rsd-mw-tfa-review/Full.lean`
- `/tmp/rsd-mw-tfa-review/NoImport.lean`
- `/tmp/rsd-mw-tfa-review/OnlyCMD.lean`
- `/tmp/rsd-mw-tfa-review/OnlySA.lean`

Snapshot integrity (project b4d606d, Mathlib 25730c7c): the snapshot Contract.lean and lake-manifest.json are byte-identical to the workspace copies, and the workspace Submission.lean equals Contract.lean. The snapshot Mathlib files ContinuousMapDense, SmoothApprox, PartitionOfUnity and Regular are byte-identical to the build tree lake-packages-25730c7c.

No local declaration provides the facts the children need:
- SimonGMT Chapter06 has only covectorEuclideanNorm_zero, _nonneg and _neg: no triangle inequality, homogeneity, operator-norm bound, continuity, retraction, smoothing or cut-off.
- No accepted DAG node has these types. The related nodes in other branches have different types and are not accepted: dor_ims_smooth_unit_approx, dor_ims_sua_coeff_norm_rep, dor_ims_sua_mollify_unit_field and regcomp_exists_smooth_unit_form_approx (waiting-children or decomposing).
- None of the five rsd_mw_tfa_ names occurs in the 261 DAG lean_names or in the 1399 worktrees.

Mathlib tools located in the pinned snapshot:
- Integrable.exists_hasCompactSupport_lintegral_sub_le (ContinuousMapDense.lean:211);
- UniformContinuous.exists_contDiff_dist_le (SmoothApprox.lean);
- exists_contDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:789);
- exists_open_between_and_isCompact_closure (Separation/Regular.lean:364);
- MeasurableSet.exists_isCompact_sdiff_lt (Measure/Regular.lean);
- HasCompactSupport.uniformContinuous_of_continuous (to_additive, HeineCantor.lean:91);
- ContinuousAlternatingMap.le_opNorm (Alternating/Basic.lean:212);
- EuclideanSpace.norm_eq (PiL2.lean:145);
- ofReal_norm (Normed/Group/Basic.lean:386);
- ENNReal.mul_lt_mul_right (Basic/ENNReal/Operations.lean:58).
ContinuousMapDense and SmoothApprox are outside the import closure of GMT.Ch07.Submission but are prebuilt. gmt-compare.py byte-checks only the frozen files other than Submission.lean, and an accepted node already added an import there.

Instances and Lean behaviour:
- CompleteSpace (Covector (Euclid P) n) and ν.Regular for finite ν are inferred.
- MeasurableSpace, SecondCountableTopology and FiniteDimensional on Covector are not inferred and are not needed.
- rw [sub_smul] fails on Covector; module works.

Lean checks:
- All five child types elaborate as Submission declarations after import GMT.Ch07.Submission alone, in the contract scope.
- The verbatim frozen parent type follows from the children: assembly with only that import.
- Full proofs of all five children compile with the two extra imports.
- Axioms are only propext, Classical.choice and Quot.sound.
- An independent reviewer reproduced all of this.
