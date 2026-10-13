# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1.variation_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the selected proof (variation bound), with its η → 0 argument supplied by the sibling eval_mass_bound and the homogeneity |a·α| = |a|·|α| by the sibling norm_props. The covector ε of the selected proof (from the parent's prerequisite interior_form) enters only through the hypotheses |ε| ≤ ‖z‖ and d(f·ε)(y)(e) = Df(y)(z).
Notation: n = d + 1; e := (fun i => EuclideanSpace.single i (1 : ℝ)) : Fin (d + 1) → ℝⁿ; |α| := covectorEuclideanNorm α; ∂Y := Y.boundary ∈ GeometricCurrentOn U d; M_U(∂Y) := Y.boundary.massOn U.
1. (The test d-form γ.) Put γ(x) := f(x)•ε. It is C^∞ (ContDiff.smul hf contDiff_const), it has compact support (HasCompactSupport.smul_right applied to the compact support of f), and tsupport γ ⊆ tsupport f ⊆ U (tsupport_smul_subset_left). Hence γ belongs to testFormOnSubmodule U d, i.e. γ ∈ TestFormOn U d, and tsupport γ ⊆ U.
2. (M ≥ 0.) 0 ≤ |f(0)| ≤ M.
3. (Coefficient bound.) By the sibling norm_props (Submission.rsd_mw_tfa_norm_props (d + 1) d, part (ii): |t•α| = |t|·|α|), for every x: |γ(x)| = |f(x)•ε| = |f(x)|·|ε| ≤ M·‖z‖, because |f(x)| ≤ M, 0 ≤ |ε| ≤ ‖z‖ (covectorEuclideanNorm_nonneg and the hypothesis) and M ≥ 0 (step 2) (mul_le_mul).
4. (Mass bound.) Apply the sibling eval_mass_bound (Submission.cmr_abs_apply_le_massOn) with P := d + 1, degree d, the domain U, W := U, T := ∂Y, ω := γ and r := M‖z‖. Its hypotheses hold: M_U(∂Y) ≠ ∞ (assumption), tsupport γ ⊆ U (step 1) and |γ(x)| ≤ M‖z‖ for every x (step 3). Hence |∂Y(γ)| ≤ M‖z‖·(M_U(∂Y)).toReal.
5. (Identification of ∂Y(γ).) By the definition of the boundary (GeometricCurrentOn.boundary_apply), ∂Y(γ) = Y(dγ), where dγ := exteriorDerivativeTestOn U d γ ∈ TestFormOn U (d + 1) has underlying form exteriorDerivative γ = exteriorDerivative (fun x => f x • ε) (definitionally). By the representation hypothesis, Y(dγ) = ∫_U u(y)·(exteriorDerivative (fun x => f x • ε))(y)(e) dy, and by the hypothesis on ε the integrand equals u(y)·Df(y)(z) at every point y. Since the integrands agree everywhere, ∂Y(γ) = ∫_U u(y)·Df(y)(z) dy (no measurability of U is used).
6. (Conclusion.) By steps 4 and 5, |∫_U u(y)·Df(y)(z) dy| ≤ M‖z‖·(M_U(∂Y)).toReal = (M_U(∂Y)).toReal·‖z‖·M. ∎
Formalization note: this is a machine leaf (depth 6): exactly one theorem `Submission.cbr_ci_pw_l1_boundary_variation_bound` appended inside `namespace GMT.Ch07` before `main_theorem`, no new import, option or helper declaration; the only non-library dependencies are the siblings `Submission.rsd_mw_tfa_norm_props` and `Submission.cmr_abs_apply_le_massOn` (overlaid as accepted dependencies). The following Lean proof was compiled by this decomposition session after `import GMT.Ch07.Submission` with the real accepted proofs of both siblings present (lean 4.35.0-rc3, Mathlib 25730c7c; `#print axioms` = propext, Classical.choice, Quot.sound; no warnings) and passes the runtime leaf-delta check `check_source_delta`; it may be used verbatim:
theorem Submission.cbr_ci_pw_l1_boundary_variation_bound : ∀ (d : ℕ) (U : Set (Euclid (d + 1))) (Y : GeometricCurrentOn U (d + 1)) (u : Euclid (d + 1) → ℝ) (ε : Covector (Euclid (d + 1)) d) (f : Euclid (d + 1) → ℝ) (z : Euclid (d + 1)) (M : ℝ), (∀ ω : TestFormOn U (d + 1), Y ω = ∫ y in U, u y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))) → Y.boundary.massOn U ≠ ∞ → covectorEuclideanNorm ε ≤ ‖z‖ → (∀ y, exteriorDerivative (fun x => f x • ε) y (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ f y z) → ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ U → (∀ y, |f y| ≤ M) → |∫ y in U, u y * fderiv ℝ f y z| ≤ (Y.boundary.massOn U).toReal * ‖z‖ * M := by
  intro d U Y u ε f z M hrep hfin hεn hεd hf hfc hfU hM
  have hsmul := (Submission.rsd_mw_tfa_norm_props (d + 1) d).2.1
  have hsupp : tsupport (fun x => f x • ε : DifferentialForm (Euclid (d + 1)) d) ⊆ U :=
    (tsupport_smul_subset_left f (fun _ => ε)).trans hfU
  have hmem : (fun x => f x • ε : DifferentialForm (Euclid (d + 1)) d) ∈
      testFormOnSubmodule (E := Euclid (d + 1)) U d :=
    ⟨⟨hf.smul contDiff_const, hfc.smul_right⟩, hsupp⟩
  let γ : TestFormOn U d := ⟨fun x => f x • ε, hmem⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hbound : ∀ x, covectorEuclideanNorm ((γ : DifferentialForm (Euclid (d + 1)) d) x) ≤ M * ‖z‖ := by
    intro x
    change covectorEuclideanNorm (f x • ε) ≤ M * ‖z‖
    rw [hsmul]
    exact mul_le_mul (hM x) hεn (covectorEuclideanNorm_nonneg ε) hM0
  have key := Submission.cmr_abs_apply_le_massOn (d + 1) d U U Y.boundary γ (M * ‖z‖) hfin hsupp hbound
  have heq : Y.boundary γ = ∫ y in U, u y * fderiv ℝ f y z := by
    rw [GeometricCurrentOn.boundary_apply, hrep]
    congr 1
    funext y
    change u y * exteriorDerivative (fun x => f x • ε) y (fun i => EuclideanSpace.single i (1 : ℝ)) = _
    rw [hεd y]
  rw [heq] at key
  calc |∫ y in U, u y * fderiv ℝ f y z| ≤ M * ‖z‖ * (Y.boundary.massOn U).toReal := key
    _ = (Y.boundary.massOn U).toReal * ‖z‖ * M := by ring

## Key steps

1. γ := f·ε is a test d-form on U with tsupport γ ⊆ tsupport f ⊆ U.
2. norm_props (ii): |γ(x)| = |f(x)|·|ε| ≤ M‖z‖, using M ≥ |f(0)| ≥ 0.
3. eval_mass_bound with W := U, T := ∂Y, r := M‖z‖: |∂Y(γ)| ≤ M‖z‖·M_U(∂Y).toReal.
4. ∂Y(γ) = Y(dγ) = ∫_U u·d(f·ε)(e) = ∫_U u·Df(z) by the representation and the hypothesis on ε; rearrange the product.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp .../local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I regex scans of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json lean_statement/title/lean_name for: '∫ y, φ y = 1', 'bump|Bump|mollif|normaliz', 'massOn .*\.toReal', '\| ≤ .*massOn', 'covectorEuclideanNorm \(\w+ • ', 'Continuous \(fun x => ∫', 'cbr_ci_pw_l1' -> accepted dgoj_exists_det_covector, dgcr_stc_exists_normalized_mollifier, cmr_abs_apply_le_massOn, rsd_mw_tfa_norm_props (frozen types byte-identical to the reuse children; status accepted with candidate commits); no DAG lean_name with prefix cbr_ci_pw_l1; reuse-edge census (588 edges; the 4 reused nodes already used by 1/3/8/10 parents)`
- `git grep -n 'theorem Submission.<name> ' in candidate commits 017b0c1fe8fd4d32e469194d32b12ff196e92e1c, 376e5f482d73f6f48d00a4945533b15f784859d5, 7a706164baaf42fc7f55751247396a8836928310, f492ba4a003c8f1324077e050d48667ae23c7100 -- GMT/Ch07/Submission.lean (each adds exactly one theorem over b4d606db); git log --all -S for the three new names (no hits)`
- `rg -n in .../local-references/123e8435b4a2469b/mathlib/Mathlib: 'theorem continuous_of_dominated' (MeasureTheory/Integral/Bochner/Basic.lean:476), 'bounded_above_of_compact_support' (Analysis/Normed/Group/Bounded.lean:153), 'theorem norm_setIntegral_le_of_norm_le_const ' (MeasureTheory/Integral/Bochner/Set.lean:613), 'tendstoUniformlyOn_iff ' (Topology/MetricSpace/Pseudo/Basic.lean:142), 'theorem ContinuousOn.integrableOn_compact ' (MeasureTheory/Function/LocallyIntegrable.lean:592), 'integral_mono_of_nonneg' (MeasureTheory/Integral/Bochner/Basic.lean:676), 'theorem tsupport_smul_subset_left' and 'theorem HasCompactSupport.smul_right' (Topology/Algebra/Support.lean:168, 466), 'theorem integrableOn_const' (MeasureTheory/Integral/IntegrableOn.lean:119), 'theorem measure_ball_lt_top' (MeasureTheory/Measure/Typeclasses/Finite.lean:373), 'closure_ball_subset_closedBall' (Topology/MetricSpace/Pseudo/Lemmas.lean:73), 'theorem tendsto_toReal ' (Topology/Instances/ENNReal/Lemmas.lean:102)`
- `sed of simongmt Poincare/SimonGMT/Chapter06/Forms.lean, Currents.lean, Mass.lean, FormSupNorm.lean (testFormOnSubmodule carrier IsTestForm ∧ tsupport ⊆ U, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply, massAdmissibleOn, massOn, le_massOn, covectorEuclideanNorm)`
- `lake env lean /tmp/l1c-decomp/Types.lean (3 frozen sibling types + 7 child types elaborate after import GMT.Ch07.Submission in the contract namespace and opens) and /tmp/l1c-decomp/Asm.lean (frozen parent type proved from children + siblings)`
- `lake env lean /tmp/l1c-decomp/N1.lean, N2.lean, N3.lean and Full.lean (real accepted proofs of the 4 reused declarations extracted from their candidate commits + the 3 new proofs + the parent assembly: the new children print axioms propext, Classical.choice, Quot.sound; the parent uses sorryAx only through the 3 stubbed frozen sibling prerequisites)`
- `python3 -I: validate_lean_statement (verifier/lean_contract.py) on all 7 child types (pass); check_source_delta copied from leaf_verification.py on the 3 new leaf proofs (pass)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose depth gate, _existing_lean_name_problem identical-type reuse of accepted nodes, _solve_children id reuse, _install_parent_supplied_child_handoff early return for accepted children, _overlay_accepted_children), prompts.py DECOMPOSE/DECOMPOSITION_AUDIT, decomposition_scope.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ae89d381c3/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-ee844cd15b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-786dd02ecc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/l1c-decomp/Types.lean`
- `/tmp/l1c-decomp/Asm.lean`
- `/tmp/l1c-decomp/N1.lean`
- `/tmp/l1c-decomp/N2.lean`
- `/tmp/l1c-decomp/N3.lean`
- `/tmp/l1c-decomp/Full.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). Four facts the selected proof needs already exist as comparator-accepted declarations with byte-identical frozen types: dgoj_exists_det_covector, dgcr_stc_exists_normalized_mollifier, cmr_abs_apply_le_massOn and rsd_mw_tfa_norm_props. Each is a single theorem over the base and is already reused by other parents, so they are reused as children. The three new names cbr_ci_pw_l1_scalar_test_tendsto, cbr_ci_pw_l1_boundary_variation_bound and cbr_ci_pw_l1_squeeze_of_mollified are unused in the DAG and in git. Every Mathlib lemma cited in the new child proofs is present in the pinned snapshot and reachable from import GMT.Ch07.Submission. All 7 child types elaborate in the contract scope and pass validate_lean_statement. The three new children were proved in Lean (standard axioms, leaf-delta check passes) using the real reused proofs. The frozen parent type compiles from the 7 children plus the three frozen sibling prerequisites, so the split implies the selected statement by the supplied proof.
