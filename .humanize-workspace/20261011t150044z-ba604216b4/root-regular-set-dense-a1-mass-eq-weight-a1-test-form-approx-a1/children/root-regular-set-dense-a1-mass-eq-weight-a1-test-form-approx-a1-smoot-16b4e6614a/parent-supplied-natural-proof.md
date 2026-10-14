# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1`
- Child DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.smooth_uniform-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5 (smoothing and rescaling), with the tolerance chosen for an arbitrary δ.

Notation. F := Covector (Euclid P) n with its operator norm ‖·‖, and N := covectorEuclideanNorm.
Uses sibling norm_props (Submission.rsd_mw_tfa_norm_props):
- (i) N(α + α') ≤ N(α) + N(α');
- (ii) N(t·α) = |t|·N(α);
- (iii) a real C ≥ 0 with N(α) ≤ C‖α‖ for all α ∈ F.

1. Tolerance. Put η := δ/(2C + 1) > 0; note that Cη ≥ 0.

2. Uniform continuity. g is continuous with compact support, hence uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous).

3. Smooth uniform approximation. ℝ^P is a finite-dimensional real normed space, and F is a complete real normed space (Lean infers CompleteSpace (Covector (Euclid P) n)). UniformContinuous.exists_contDiff_dist_le (Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox) convolves g with a normalized smooth bump of small radius. It gives h' : ℝ^P → F with ContDiff ℝ ∞ h' and dist(h'(x), g(x)) = ‖h'(x) − g(x)‖ < η for every x.

4. Bounds for h'. For every x:
   - by (iii), N(h'(x) − g(x)) ≤ C‖h'(x) − g(x)‖ ≤ Cη;
   - by (i), N(h'(x)) = N((h'(x) − g(x)) + g(x)) ≤ Cη + N(g(x)) ≤ 1 + Cη.

5. Rescaling. Let s := (1 + Cη)⁻¹, so 0 < s ≤ 1, and define h(x) := s·h'(x). Then h is C^∞, as a constant multiple of a C^∞ map. For every x, by (ii) and step 4,
   N(h(x)) = s·N(h'(x)) ≤ (1 + Cη)⁻¹·(1 + Cη) = 1.

6. Distance to h'. h(x) − h'(x) = (s − 1)·h'(x), and |s − 1| = 1 − s = Cη/(1 + Cη) = Cη·s. By (ii) and step 4,
   N(h(x) − h'(x)) = Cη·s·N(h'(x)) ≤ Cη·s·(1 + Cη) = Cη.

7. Conclusion. By (i), step 4 and step 6,
   N(h(x) − g(x)) ≤ N(h(x) − h'(x)) + N(h'(x) − g(x)) ≤ 2Cη = 2Cδ/(2C + 1) ≤ δ,
   since 2C ≤ 2C + 1 and δ > 0.

So h is C^∞, and N(h(x)) ≤ 1 and N(h(x) − g(x)) ≤ δ for every x.

Lean note. A compiled route:
- This child needs `import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox` added to GMT/Ch07/Submission.lean.
- Use `hgs.uniformContinuous_of_continuous hgc`, then `hgu.exists_contDiff_dist_le hη0`. The result `ContDiff ℝ ∞ h'` is literally `ContDiff ℝ (⊤ : ℕ∞) h'` as in this child's statement; both elaborate to `ContDiff ℝ (WithTop.some ⊤) h'`.
- The rescaled map is `fun x => s • h' x`, with smoothness `hh's.const_smul s`.
- Prove the covector identity s • y − y = (s − 1) • y with `module`; a bare `rw [sub_smul]` fails on Covector because of the SMul instance path.
- `inv_mul_le_iff₀`, `abs_of_nonpos`, `field_simp`, `div_le_iff₀` and `nlinarith` close the scalar arithmetic.

## Key steps

1. Put η := δ/(2C+1), with C from norm_props.
2. g is uniformly continuous, because it is continuous with compact support.
3. Mathlib's smooth uniform approximation gives a C^∞ h' with ‖h' − g‖ < η everywhere.
4. N(h' − g) ≤ Cη and N(h') ≤ 1 + Cη.
5. h := (1 + Cη)⁻¹·h' satisfies N(h) ≤ 1 and N(h − h') ≤ Cη, so N(h − g) ≤ 2Cη ≤ δ.

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
