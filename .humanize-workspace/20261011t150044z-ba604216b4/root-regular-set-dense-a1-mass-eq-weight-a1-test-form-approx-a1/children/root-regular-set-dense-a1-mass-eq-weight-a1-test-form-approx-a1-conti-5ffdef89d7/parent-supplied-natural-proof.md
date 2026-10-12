# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1`
- Child DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.continuous_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (L¹-density of continuous compactly supported maps) and step 4 (g₁ := π ∘ g and its a.e. estimate). The integral estimate of step 7 is carried out here for this part alone.

Notation. F := Covector (Euclid P) n with its operator norm ‖·‖ (a real normed space), N := covectorEuclideanNorm, and ‖y‖ₑ = ofReal ‖y‖ is the extended norm.
Uses siblings:
- norm_props (Submission.rsd_mw_tfa_norm_props), part (iii): a real C ≥ 0 with N(α) ≤ C‖α‖ for all α ∈ F;
- retraction (Submission.rsd_mw_tfa_retraction): a continuous ρ : F → F with ρ(0) = 0, N(ρ(a)) ≤ 1 for all a, and N(ρ(a) − b) ≤ 2N(a − b) whenever N(b) ≤ 1.

1. Tolerance. Put η := δ/(2(2C + 1)) > 0.

2. Continuous approximation. ℝ^P is a σ-compact, locally compact metric space with its Borel σ-algebra, hence normal and R1. A finite measure on it is regular (Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure; Lean infers ν.Regular from IsFiniteMeasure ν). Continuous compactly supported maps are dense in L¹(ν; F): apply Integrable.exists_hasCompactSupport_lintegral_sub_le (Mathlib.MeasureTheory.Function.ContinuousMapDense) to β with tolerance ofReal η ≠ 0. This gives a continuous g₀ : ℝ^P → F with compact support and
   ∫⁻ ‖β(x) − g₀(x)‖ₑ dν(x) ≤ ofReal η.

3. Retraction. Put g := ρ ∘ g₀.
   - g is continuous, as a composition of continuous maps.
   - g has compact support: ρ(0) = 0 gives g(x) = 0 whenever g₀(x) = 0, so tsupport g ⊆ tsupport g₀ (HasCompactSupport.comp_left).
   - N(g(x)) = N(ρ(g₀(x))) ≤ 1 for every x.

4. Pointwise estimate. Let x satisfy N(β(x)) ≤ 1; by hypothesis this holds for ν-a.e. x. The retraction estimate with a = g₀(x) and b = β(x), followed by norm_props (iii), gives
   N(g(x) − β(x)) ≤ 2N(g₀(x) − β(x)) ≤ 2C‖g₀(x) − β(x)‖ = 2C‖β(x) − g₀(x)‖.
   Since 2C ≥ 0, ofReal is monotone and ofReal(2C·t) = ofReal(2C)·ofReal(t) for t ≥ 0. So, for ν-a.e. x,
   ofReal(N(g(x) − β(x))) ≤ ofReal(2C)·‖β(x) − g₀(x)‖ₑ.

5. Integration. The lower Lebesgue integral is monotone under a.e. inequalities, and the constant ofReal(2C) is finite (lintegral_const_mul' needs no measurability). Hence
   ∫⁻ ofReal(N(g − β)) dν ≤ ofReal(2C)·∫⁻ ‖β − g₀‖ₑ dν ≤ ofReal(2C)·ofReal(η) = ofReal(2Cη).

6. Arithmetic. 2Cη = 2C·δ/(2(2C + 1)) = δ·C/(2C + 1) < δ, because 0 ≤ C < 2C + 1 and δ > 0. As δ > 0, ofReal(2Cη) < ofReal δ (ENNReal.ofReal_lt_ofReal_iff).

Therefore g is continuous with compact support, N(g(x)) ≤ 1 for every x, and ∫⁻ ofReal(N(g(x) − β(x))) dν(x) < ofReal δ.

Lean note. A compiled route:
- This child needs `import Mathlib.MeasureTheory.Function.ContinuousMapDense` added to GMT/Ch07/Submission.lean. The comparator byte-checks only the frozen Contract and the build inputs, and an accepted node of this run already added an import to Submission.lean.
- After `have := hν`, the instance `ν.Regular` is inferred.
- `hβ.exists_hasCompactSupport_lintegral_sub_le (ENNReal.ofReal_pos.mpr hη0).ne'` returns ⟨g₀, compact support, ∫⁻ ‖β x − g₀ x‖ₑ ≤ _, continuity, integrability⟩.
- Use `hρc.comp hgc` and `hgs.comp_left hρ0`.
- Pointwise: `rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]`, then `ENNReal.ofReal_le_ofReal` and `norm_sub_rev`.
- Integration: `lintegral_mono_ae` and `lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`.
- Final arithmetic: `ENNReal.ofReal_lt_ofReal_iff`, `mul_div_assoc'`, `div_lt_iff₀` and `nlinarith`.

## Key steps

1. Fix C from norm_props and put η := δ/(2(2C+1)).
2. L¹ density (Integrable.exists_hasCompactSupport_lintegral_sub_le): a continuous compactly supported g₀ with ∫⁻ ‖β − g₀‖ₑ dν ≤ η.
3. g := ρ ∘ g₀ is continuous, compactly supported (since ρ(0) = 0), and satisfies N(g) ≤ 1.
4. For ν-a.e. x, N(g − β) ≤ 2N(g₀ − β) ≤ 2C‖β − g₀‖.
5. ∫⁻ ofReal N(g − β) dν ≤ ofReal(2C)·ofReal(η) = ofReal(δC/(2C+1)) < ofReal δ.

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
