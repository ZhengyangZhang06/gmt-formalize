# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.null_set-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.null_set-a1.ball_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the first half of fact 1(e) of the parent proof (M(A) ≤ μ(B_ρ(x))). The parent uses finiteness of μ(B_ρ(x)); here a trivial case distinction replaces it, so no local finiteness or measurability hypothesis is needed.

Notation: M(A) = A.mass = A.massOn univ = sSup{ENNReal.ofReal(A(ω)) : ω ∈ 𝒟^n(ℝ^P), |ω(y)| ≤ 1 for all y}. The support condition tsupport ω ⊆ ℝ^P in massAdmissibleOn univ n univ is automatic.

1. If μ(B_ρ(x)) = ∞, then M(A) ≤ ∞ = μ(B_ρ(x)) (le_top). Assume from now on that μ(B_ρ(x)) ≠ ∞, so μ(B_ρ(x)) < ∞.
2. Since M(A) is defined as a supremum (sSup_le), it suffices to show ENNReal.ofReal(A(ω)) ≤ μ(B_ρ(x)) for every ℝ^P-admissible ω, i.e. every ω ∈ 𝒟^n(ℝ^P) with |ω(y)| ≤ 1 for all y. Fix such an ω and write f(y) := ξ(y)(ω(y)) ∈ ℝ. By hypothesis, A(ω) = ∫_{B_ρ(x)} f dμ.
3. For μ-a.e. y, the hypothesis on ξ with α := ω(y) gives |f(y)| = |ξ(y)(ω(y))| ≤ |ω(y)| ≤ 1. A statement holding μ-a.e. also holds a.e. for the restriction μ⌞B_ρ(x) (ae_restrict_of_ae). So ‖f(y)‖ = |f(y)| ≤ 1 for μ⌞B_ρ(x)-a.e. y (Real.norm_eq_abs).
4. By norm_setIntegral_le_of_norm_le_const_ae (with s := B_ρ(x), μ(s) < ∞ and constant C := 1), |∫_{B_ρ(x)} f dμ| ≤ 1 · μ.real(B_ρ(x)) = μ(B_ρ(x)).toReal. This lemma needs no measurability of f: if f is not a.e. strongly measurable, its Bochner integral is 0.
5. Hence A(ω) ≤ |A(ω)| ≤ μ(B_ρ(x)).toReal (le_abs_self). Therefore ENNReal.ofReal(A(ω)) ≤ ENNReal.ofReal(μ(B_ρ(x)).toReal) = μ(B_ρ(x)), by ENNReal.ofReal_le_ofReal and ENNReal.ofReal_toReal (using μ(B_ρ(x)) ≠ ∞).
6. Taking the supremum over ω gives M(A) ≤ μ(B_ρ(x)). ∎

## Key steps

1. The bound is trivial if μ(B_ρ(x)) = ∞.
2. For admissible ω, |ξ(y)(ω(y))| ≤ |ω(y)| ≤ 1 for μ⌞B_ρ(x)-a.e. y.
3. norm_setIntegral_le_of_norm_le_const_ae gives A(ω) ≤ μ(B_ρ(x)).toReal.
4. Apply ENNReal.ofReal and take the supremum: M(A) ≤ μ(B_ρ(x)).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 -I scan of dag.json: selected node record (depth 4, depends_on cone-a1 and covering-a1); frozen lean_statement of siblings cone-a1 (cbrld_cycle_eval_le_radius_mul_mass) and covering-a1 (cbrld_vitali_setIntegral_le); statements containing '(S - T).support ⊆', 'support ∪', '.mass ≤ S.mass +', 'massOn W ≤ S.massOn W + T.massOn W', '(S - T).mass', '|T ω| ≤', '.mass.toReal' (found cmr_abs_apply_le_massOn, cmc_ml_massOn_eq_of_disjoint_sub_support, cmc_massOn_le_of_le_near_support, cmc_fc_sc_abs_le_mul_mass; none states spt(S − T) ⊆ spt S ∪ spt T or M_W(S − T) ≤ M_W(S) + M_W(T))`
- `grep -rn 'massOn_add|massOn_sub|mass_sub|mass_add_le|support_sub|support_add|sub_apply|zeroRegion_inter|VanishesOn.sub' over lake-packages-25730c7c/simongmt/Poincare/SimonGMT and workspaces/gmt-ch07/GMT; rg -nE 'massOn_sub|mass_sub|support_sub|sub_support|zeroRegion_inter' project/GMT in the snapshot (no current-difference lemma); grep 'instance' in SimonGMT Chapter06 and GMT/Ch07/Submission.lean (only Zero and the contract's Sub instance on GeometricCurrentOn)`
- `sed of SimonGMT Chapter06 Mass.lean (covectorEuclideanNorm_neg, massAdmissibleOn, GeometricCurrentOn.massOn, mass, le_massOn), Currents.lean (GeometricCurrentOn, TestFormOn, exteriorDerivativeTestOn, boundary, boundary_apply, GeometricCurrentOn.ext), CurrentLocalEquality.lean (VanishesOn, zeroRegion, support), Forms.lean (Covector, DifferentialForm, IsSmoothForm, IsTestForm)`
- `grep/rg in snapshot mathlib/Mathlib for: norm_setIntegral_le_of_norm_le_const_ae, setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_integral_of_forall_compl_eq_zero, ContinuousLinearMap.aestronglyMeasurable_comp₂, isBoundedBilinearMap_apply, closedBall_sdiff_ball (closedBall_diff_ball is a deprecated alias), ae_eq_set, setIntegral_congr_set, measure_congr, ofReal_add_le, ofReal_lt_ofReal_iff, ofReal_le_iff_le_toReal, toReal_mono, toReal_ofReal, toReal_add, toReal_pos, mul_lt_top, add_lt_top, image_eq_one_of_notMem_mulTSupport, closure_ball_subset_closedBall, isCompact_closedBall, IsCompact.of_isClosed_subset, measure_mono_null, measure_iUnion_null, le_of_forall_pos_lt_add`
- `sed -n 6530,6640p and 4390,4440p of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_dependency_problem, _existing_lean_name_problem, accepted-theorem reuse rule)`
- `lake env lean /tmp/cbrld-ns-decomp-q7m2/Types.lean, Meas.lean, Children.lean (#print axioms NsCheck.c1 … NsCheck.c5) and Assembly.lean (#print axioms NsCheck.assembly)`
- `python3 -I /tmp/cbrld-ns-decomp-q7m2/scripts/check.py (verifier/lean_contract.py validate_lean_statement, lean_name collision scan of dag.json, verbatim containment in the Lean check files); python3 -I /tmp/cbrld-ns-decomp-q7m2/scripts/gen_challenges.py (verifier/gmt-compare.py child_modules, contract mode) followed by lake env lean on the five generated Challenge_*.lean files`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Gauge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3d838668ea/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3d838668ea/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3d838668ea/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/cbrld-ns-decomp-q7m2/Types.lean`
- `/tmp/cbrld-ns-decomp-q7m2/Meas.lean`
- `/tmp/cbrld-ns-decomp-q7m2/Children.lean`
- `/tmp/cbrld-ns-decomp-q7m2/Assembly.lean`
- `/tmp/cbrld-ns-decomp-q7m2/children.json`
- `/tmp/cbrld-ns-decomp-q7m2/scripts/check.py`
- `/tmp/cbrld-ns-decomp-q7m2/scripts/gen_challenges.py`
- `/tmp/cbrld-ns-decomp-q7m2/challenges/Challenge_support_sub.lean`
- `/tmp/cbrld-ns-decomp-q7m2/challenges/Challenge_mass_sub.lean`
- `/tmp/cbrld-ns-decomp-q7m2/challenges/Challenge_ball_mass.lean`
- `/tmp/cbrld-ns-decomp-q7m2/challenges/Challenge_ball_support.lean`
- `/tmp/cbrld-ns-decomp-q7m2/challenges/Challenge_comparison.lean`

No reusable lemma on the support or mass of a difference of currents exists in the snapshot's project/GMT, in SimonGMT Chapter06 or among DAG nodes. SimonGMT gives only the definitions plus le_massOn, massOn_mono, boundary_apply and GeometricCurrentOn.ext. The contract adds only the Sub instance. The closest accepted node, cmr_abs_apply_le_massOn, is not needed because `comparison` uses only the one-sided le_massOn. Every generic Mathlib tool cited in the child proofs was found in the pinned snapshot. closedBall_diff_ball and Set.diff_eq_empty are deprecated in favour of closedBall_sdiff_ball and sdiff_eq_empty. Measurability of y ↦ ξ y (ω y) needs explicit type arguments for ContinuousLinearMap.aestronglyMeasurable_comp₂; isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ also works. The five child types elaborate in the frozen scope and inside the comparator's NodeChallenge wrapper, pass validate_lean_statement and collide with no DAG lean_name. All five children were proved in Lean. The verbatim frozen parent type was derived from ball_mass, ball_support, comparison and the frozen cone and covering types. All proofs use only propext, Classical.choice and Quot.sound.
