# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1.osc_l1_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof ("D(δ) ≤ D_k + vol(Q_δ)ε_k + vol(Q_δ)ε_k; letting k → ∞ gives D(δ) ≤ K₀V"), with the outputs of the sibling results smooth_approx and smooth_poincare replaced by the hypotheses on the continuous functions v_k (the parent supplies them), and with the integrability facts of step 1 of the parent proof written out for the set Q_δ.

Notation. n := m + 1; Euclid n = EuclideanSpace ℝ (Fin n) with Lebesgue measure vol; z_i is the i-th coordinate of z; S := Q_δ = {z : δ < z_i < 1 − δ for all i}; Q₁ := {y : 0 < y_i < 1 for all i}. μ := vol restricted to S, so ∫_S f = ∫ f dμ. All integrals are Bochner integrals, and every function to which linearity or monotonicity of the integral is applied below is first shown to be integrable.

1. S ⊆ Q₁. If z ∈ S then for every i, 0 ≤ δ < z_i and z_i < 1 − δ ≤ 1, because δ ≥ 0.
2. S lies in a compact ball. For z ∈ Q₁ every |z_i| < 1, so z_i² ≤ 1. Since ‖z‖ = √(Σ_{i ∈ Fin n} ‖z_i‖²) (EuclideanSpace.norm_eq) and ‖z_i‖² = z_i² (Real.norm_eq_abs, sq_abs), we get Σ_{i ∈ Fin n} z_i² ≤ Σ_{i ∈ Fin n} 1 = n (Finset.sum_le_sum) and hence ‖z‖ ≤ √n (Real.sqrt_le_sqrt). Hence S ⊆ Q₁ ⊆ B̄ := closedBall(0, √n). The ball B̄ is compact (Euclid n is finite dimensional, hence proper; isCompact_closedBall) and vol(B̄) < ∞ (measure_closedBall_lt_top), so vol(S) ≤ vol(B̄) < ∞.
3. Integrability. By step 2, μ is a finite measure (isFiniteMeasure_restrict). Put a := μ(univ) = vol(S), a real number ≥ 0. Since u is integrable on Q₁ ⊇ S, u ∈ L¹(μ) (IntegrableOn.mono_set). Each v_k is continuous, hence integrable on the compact set B̄ (ContinuousOn.integrableOn_compact) and therefore on S ⊆ B̄, so v_k ∈ L¹(μ). Consequently v_k − u, u − v_k and their absolute values lie in L¹(μ). Write ε_k := ∫_S |v_k − u| = ∫ |v_k − u| dμ; by hypothesis ε_k → 0.
4. Fubini integrability. Fix k. On the finite product measure μ ⊗ μ the functions (x, y) ↦ v_k(x) and (x, y) ↦ v_k(y) are integrable (Integrable.comp_fst and Integrable.comp_snd, which only need v_k ∈ L¹(μ) and μ finite). Hence G_k(x, y) := |v_k(x) − v_k(y)| is μ⊗μ-integrable, and by Fubini (Integrable.integral_prod_left) the function d_k(x) := ∫ |v_k(x) − v_k(y)| dμ(y) is μ-integrable. By definition ∫ d_k dμ = ∫_{x∈S}∫_{y∈S}|v_k(x) − v_k(y)| dy dx, which is ≤ K by hypothesis.
5. Pointwise triangle inequality. For all x, y: u(x) − u(y) = (v_k(x) − v_k(y)) + (u(x) − v_k(x)) + (v_k(y) − u(y)), hence |u(x) − u(y)| ≤ |v_k(x) − v_k(y)| + |u(x) − v_k(x)| + |v_k(y) − u(y)| (abs_add_three).
6. Inner integral. Fix x. The three functions of y on the right side of step 5 are μ-integrable: y ↦ |v_k(x) − v_k(y)| (absolute value of a constant minus an L¹(μ) function; constants are μ-integrable because μ is finite), the constant y ↦ |u(x) − v_k(x)|, and y ↦ |v_k(y) − u(y)| (step 3). The left side y ↦ |u(x) − u(y)| is nonnegative. By monotonicity of the integral for a nonnegative function dominated by an integrable one (integral_mono_of_nonneg), linearity (integral_add) and ∫ b dμ = a·b for constants b (integral_const):
   h(x) := ∫ |u(x) − u(y)| dμ(y) ≤ d_k(x) + a·|u(x) − v_k(x)| + ε_k.
7. Outer integral. The right side of step 6, as a function of x, is μ-integrable (d_k by step 4, a·|u − v_k| by step 3, and a constant); the left side h(x) is nonnegative (integral_nonneg). Integrating step 6 over x with the same monotonicity and linearity (integral_const_mul for the middle term), and using ∫ |u − v_k| dμ = ∫ |v_k − u| dμ = ε_k (abs_sub_comm), we get
   D(u) := ∫_{x∈S}∫_{y∈S}|u(x) − u(y)| dy dx = ∫ h dμ ≤ ∫ d_k dμ + a·ε_k + a·ε_k ≤ K + 2a·ε_k,
   the last step by step 4.
8. Limit. Since ε_k → 0, K + 2a·ε_k → K + 2a·0 = K (Tendsto.const_mul and Tendsto.add with tendsto_const_nhds). As D(u) ≤ K + 2a·ε_k for every k, passing to the limit (ge_of_tendsto') gives D(u) ≤ K. ∎

## Key steps

1. δ ≥ 0 gives Q_δ ⊆ Q₁ ⊆ closedBall(0, √(m + 1)); hence vol(Q_δ) < ∞, u ∈ L¹(Q_δ), and every continuous v_k ∈ L¹(Q_δ).
2. Fubini: (x, y) ↦ |v_k(x) − v_k(y)| is integrable on Q_δ × Q_δ, so d_k(x) = ∫_{Q_δ}|v_k(x) − v_k(y)| dy is integrable on Q_δ with ∫_{Q_δ} d_k ≤ K.
3. Integrating |u(x) − u(y)| ≤ |v_k(x) − v_k(y)| + |u(x) − v_k(x)| + |v_k(y) − u(y)| in y and then in x gives D(u) ≤ K + 2 vol(Q_δ) ε_k with ε_k = ∫_{Q_δ}|v_k − u|.
4. ε_k → 0, so D(u) ≤ K.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c759d…, matches); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n 'dimred_mbl_dt_cbm_bvp|cmcdtfrfg_cube_volume' SNAPSHOT/project SNAPSHOT/mathlib/Mathlib lake-packages-25730c7c/simongmt GMT -g '*.lean' (no match)`
- `rg -n 'BVPoincare|poincare_ineq|Poincaré inequality|Poincare inequality' SNAPSHOT/project/GMT -g '*.lean' (Ch02 def BVPoincare : Prop is an unproved specification under main_theorem := by sorry; Ch04 5.6 is the varifold Poincaré spec; Ch07 imports neither); rg -n -i 'poincar[eé] ineq|mean_dev|oscillation' lake-packages-25730c7c/simongmt/Poincare -g '*.lean' (only Chapter04/Poincare.lean, Simon 5.6 local Poincaré for generalized mean curvature: different setting)`
- `rg -n 'lemma Integrable.comp_fst|lemma Integrable.comp_snd|theorem Integrable.integral_prod_left|theorem setIntegral_prod|theorem tendsto_setIntegral_of_monotone|theorem prod_restrict|lemma integral_mono_of_nonneg|lemma abs_integral_le_integral_abs|theorem iUnion_prod_of_monotone|theorem volume_pi_Ioo|lemma isFiniteMeasure_restrict|theorem measure_closedBall_lt_top|theorem ContinuousOn.integrableOn_compact|theorem tendsto_natCast_atTop_atTop|theorem restrict_apply_univ|PiLp.volume_preserving_ofLp|EuclideanSpace.proj|EuclideanSpace.norm_eq|inv_tendsto_atTop' SNAPSHOT/mathlib/Mathlib (all found)`
- `python3 scans of RUN/dag.json (2092 nodes): exact lean_statement matches for each proposed type; cmcdtfrfg_cube_volume is the lean_name of exactly one node (status accepted, candidate_commit a104b3873f3c979b07a45e8d97d3d4d1d84c106a) with byte-identical type; twin children cmcdt_cbm_bvp_* (identical types) unaccepted under another parent; proposed fresh names occur 0 times; git show a104b3873f3c…:GMT/Ch07/Submission.lean (13-line accepted proof)`
- `python3/cat of twin nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c82ada6bf8/{decomposition-v1,decomposition-audit-v1,decomposition-scope-v1,parent-supplied-natural-proof.md}; diff against this node's parent-supplied-natural-proof.md (same argument, steps 0–4)`
- `grep -n in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py for _decompose (node.depth >= max_depth), _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff, _overlay_accepted_children, _reference_use_problem; swarm-project.json (max_depth 6, max_children 12)`
- `python3 -I importing verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) to build the challenge prefix; lake env lean /tmp/dimred-bvp-k4q9/lean/{ChildTypes,Challenge_cube_volume,Challenge_osc_l1_limit,Challenge_osc_exhaustion,Challenge_mean_dev,Assembly,MeanDev,OscL1,OscExh,EndToEnd,ExactE2E}.lean (types elaborate; children fully proved; parent assembled; #print axioms propext, Classical.choice, Quot.sound)`
- `validate_lean_statement from /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py and verifier/lean_contract.py on all four types (accepted unchanged)`
- `sed -n 627,662p book/chapter-02.txt (Simon Ch. 2, 2.7 BV Poincaré); sed -n 1880,1893p book/chapter-06.txt (Ch. 6, proof of 5.1, display (32))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Archimedean.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-f5c7fb83bb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c82ada6bf8/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c82ada6bf8/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dimred-bvp-k4q9/lean/ExactE2E.lean`
- `/tmp/dimred-bvp-k4q9/lean/Assembly.lean`

The pins match (project b4d606db, Mathlib 25730c7c), and the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical. Neither the snapshot project, Mathlib nor SimonGMT contains this BV Poincaré inequality or any of the three new oscillation lemmas. Ch02 BVPoincare is an unproved specification that Ch07 does not import, and SimonGMT's Ch04 Poincaré is the varifold version. The unit-cube volume is already a comparator-accepted DAG declaration, cmcdtfrfg_cube_volume, with the byte-identical type ∀ k : ℕ, volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1, so it is reused. The three new obligations get fresh, collision-free names dimred_mbl_dt_cbm_bvp_*. Their types equal the reviewed but unaccepted twin cmcdt_cbm_bvp_* lemmas owned by another parent. All cited Mathlib lemmas exist at the pinned revision and inside the bare GMT.Ch07.Submission import closure. All four children were compiled with complete proofs, and the exact frozen parent was derived from them plus the two sibling contracts using only propext, Classical.choice and Quot.sound.
