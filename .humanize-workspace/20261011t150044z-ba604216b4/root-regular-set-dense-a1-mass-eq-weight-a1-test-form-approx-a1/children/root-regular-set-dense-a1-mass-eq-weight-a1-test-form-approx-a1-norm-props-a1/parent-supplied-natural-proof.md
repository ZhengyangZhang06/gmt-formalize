# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1`
- Child DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.norm_props-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 1 (Properties of N), with all details filled in.

Notation. e_j := EuclideanSpace.basisFun (Fin P) ℝ j (j ∈ Fin P) is the standard orthonormal basis of ℝ^P, so ‖e_j‖ = 1. 𝓙 is the finite type of all maps I : Fin n → Fin P, and #𝓙 = Fintype.card (Fin n → Fin P). For I ∈ 𝓙, e_I := (e_{I(0)}, …, e_{I(n−1)}), in Lean (fun i => e (I i)). F := Covector (Euclid P) n carries the operator norm ‖·‖ of continuous alternating maps. By definition
N(α) := covectorEuclideanNorm α = √(Σ_{I∈𝓙} q_I(α)), where q_I(α) := α(e_I)² if I is strictly increasing and q_I(α) := 0 otherwise.

1. Coefficient vector. For α ∈ F and I ∈ 𝓙 put c_I(α) := α(e_I) if I is strictly increasing, and c_I(α) := 0 otherwise. Since (if p then a else 0)² = (if p then a² else 0), q_I(α) = c_I(α)² for every I. Let v(α) ∈ EuclideanSpace ℝ 𝓙 be the vector with coordinates c_I(α); in Lean, v α := WithLp.toLp 2 (fun I => c_I α). The Euclidean norm formula ‖w‖ = √(Σ_I ‖w_I‖²) (EuclideanSpace.norm_eq), together with ‖w_I‖² = w_I², gives
   N(α) = ‖v(α)‖ for every α ∈ F.   (∗)

2. Linearity of v. Evaluation at a fixed tuple is linear in the form: (α + α')(e_I) = α(e_I) + α'(e_I) and (t·α)(e_I) = t·α(e_I). So, coordinatewise, c_I(α + α') = c_I(α) + c_I(α') and c_I(t·α) = t·c_I(α); both sides are 0 when I is not strictly increasing. Hence v(α + α') = v(α) + v(α') and v(t·α) = t·v(α) (WithLp.toLp_add, WithLp.toLp_smul).

3. Proof of (i). By (∗), step 2 and the triangle inequality in EuclideanSpace ℝ 𝓙:
   N(α + α') = ‖v(α) + v(α')‖ ≤ ‖v(α)‖ + ‖v(α')‖ = N(α) + N(α').

4. Proof of (ii). By (∗), step 2 and homogeneity of the norm:
   N(t·α) = ‖t·v(α)‖ = |t|·‖v(α)‖ = |t|·N(α).

5. Coordinate bound. For every I ∈ 𝓙, |c_I(α)| ≤ ‖α‖.
   - If I is strictly increasing, the operator-norm bound for continuous alternating maps (ContinuousAlternatingMap.le_opNorm) gives |α(e_I)| ≤ ‖α‖·∏_k ‖e_{I(k)}‖ = ‖α‖·1 = ‖α‖.
   - Otherwise |c_I(α)| = 0 ≤ ‖α‖.

6. Proof of (iii). Put C := √(#𝓙) ≥ 0. By step 5, c_I(α)² = |c_I(α)|² ≤ ‖α‖² for every I, so Σ_I c_I(α)² ≤ #𝓙·‖α‖². Since √ is monotone and ‖α‖ ≥ 0,
   N(α) = √(Σ_I c_I(α)²) ≤ √(#𝓙·‖α‖²) = √(#𝓙)·√(‖α‖²) = C·‖α‖.

7. Proof of (iv). Let α, α' ∈ F.
   - By (i), N(α) = N((α − α') + α') ≤ N(α − α') + N(α').
   - α' − α = −(α − α') and N(−β) = N(β) (covectorEuclideanNorm_neg, or (ii) with t = −1). So by (i), N(α') = N((α' − α) + α) ≤ N(α' − α) + N(α) = N(α − α') + N(α).
   Together with (iii), |N(α) − N(α')| ≤ N(α − α') ≤ C·‖α − α'‖. Thus dist(N(α), N(α')) ≤ C·dist(α, α') for all α, α', so N is Lipschitz with the nonnegative constant C (LipschitzWith.of_dist_le_mul with K := ⟨C, C ≥ 0⟩), hence continuous.

Steps 3, 4, 6 and 7 prove (i)–(iv), with the constant C of (iii) equal to √(Fintype.card (Fin n → Fin P)).

Lean note. A compiled route (about 70 lines, no extra imports):
- Use `classical`, and define c and v with `let`.
- Prove (∗) by `rw [EuclideanSpace.norm_eq]; unfold covectorEuclideanNorm; congr 1`, then `Finset.sum_congr rfl` with `by_cases hI : StrictMono I` and `simp`.
- Prove linearity by `simp only [v, ← WithLp.toLp_add]` (resp. `← WithLp.toLp_smul`), then `congr 1; funext I; by_cases hI : StrictMono I <;> simp [c, hI]`.
- For step 5, use `α.le_opNorm (fun i => e (I i))` followed by `simpa [Real.norm_eq_abs]`; simp knows that basis vectors have norm 1.
- For step 6, use `Real.sqrt_sq`, `Real.sqrt_mul`, `Real.sqrt_le_sqrt`, `Finset.sum_le_sum` and `pow_le_pow_left₀`.
- For step 7, first rewrite N(α' − α) = N(α − α') by `rw [← neg_sub, covectorEuclideanNorm_neg]`, then apply (i) together with `sub_add_cancel`, `abs_le` and `linarith`. Finish with `(LipschitzWith.of_dist_le_mul (K := ⟨_, Real.sqrt_nonneg _⟩) hlip).continuous`.

## Key steps

1. Write N(α) = ‖v(α)‖ for the coefficient vector v(α) = (α(e_I) if I is strictly increasing, else 0)_I in EuclideanSpace ℝ (Fin n → Fin P).
2. v is additive and ℝ-homogeneous, because evaluation at a fixed tuple is linear in α.
3. (i) and (ii) follow from the triangle inequality and homogeneity of the Euclidean norm.
4. |α(e_I)| ≤ ‖α‖·∏‖e_{I(k)}‖ = ‖α‖, so N(α) ≤ √(card(Fin n → Fin P))·‖α‖, which is (iii).
5. |N(α) − N(α')| ≤ N(α − α') ≤ C‖α − α'‖, so N is Lipschitz and hence continuous, which is (iv).

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
