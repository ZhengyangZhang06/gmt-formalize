# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.isoperimetric-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Name: this child is the fresh declaration dmcbr_isoperimetric_filling. Its frozen Lean type is byte-identical to that of cbr_isoperimetric_filling (DAG node root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.isoperimetric-a1, another branch, accepted at candidate commit 054ff0a9), but that name is reserved by the other branch, so it is not reused; that Lean proof may be transplanted with only the declaration name changed. The following argument proves the statement on its own.
Source: parent proof, V3 “(Iso)” (Simon Ch. 6, 6.1 via the deformation theorem 6.2, with the support of the filling controlled by (DT)), re-indexed with m := d − 1 so that Z has degree m + 1. (DT) is the exact frozen statement of the parent node's dependency theorem dimred_mbl_deformation_theorem (not available to this child, hence assumed). M(X) := X.mass = M_{ℝ^P}(X); ‖ω‖_∞ := sup_x |ω(x)|.

1. Let c ≥ 1 (a real number; (DT) provides c ∈ ℝ≥0 with 1 ≤ c) be the constant of (DT) for (P, m). Let Z be IM in 𝒟_{m+1}(ℝ^P) with spt Z compact, ∂Z = 0 and z := M(Z) < ∞ (so z ∈ [0, ∞) and z = M(Z).toReal).
2. Mass zero means zero. If X ∈ 𝒟_k(ℝ^P) has M(X) = 0 then X = 0: for ω with ‖ω‖_∞ ≤ 1 both ω and −ω are admissible (the Euclidean coefficient norm is even), so X(ω) ≤ 0 and −X(ω) ≤ 0; for a general ω, ±sω is admissible for every s > 0 with s‖ω‖_∞ ≤ 1 (‖ω‖_∞ < ∞ since ω is continuous with compact support), so ±X(ω) ≤ 0.
3. The zero current is IM (IMRep with empty carrier, mult 0, orient 0; ∅ is Borel and countably rectifiable by SimonGMT countablyRectifiable_of_measure_zero, the remaining fields are vacuous as Hᵏ⌞∅ = 0) and has empty support (every bounded open set lies in its zero region), and 0 has boundary 0.
4. Case z = 0. By step 2, Z = 0. Take Y := 0: Y is IM, ∂Y = 0 = Z, M(Y) = 0 = c·(2c·0)^{1/(m+1)}·0, and spt Y = ∅ ⊆ thickening(3√P·(2c·0)^{1/(m+1)}, spt Z).
5. Case z > 0. Put ρ := (2cz)^{1/(m+1)} > 0, so ρ^{m+1} = 2cz. Apply (DT) with this ρ, K := spt Z (compact) and Λ := z ∈ ℝ≥0 to T := Z: Z is IM, spt Z ⊆ K, M(Z) ≤ Λ and M(∂Z) = M(0) = 0 < ∞. This gives Q, S ∈ 𝒟_{m+1}(ℝ^P) and R ∈ 𝒟_{m+2}(ℝ^P) with Q, ∂Q, R IM, Z − Q − S = ∂R, (Q = 0 or M(Q) ≥ ρ^{m+1}), M(Q) ≤ c·M(Z) = cz, M(R) ≤ c·ρ·M(Z), M(S) ≤ c·ρ·M(∂Z) = 0, and spt Q ∪ spt R ⊆ thickening(3√P ρ, spt Z).
6. M(S) = 0, so S = 0 (step 2). M(Q) ≤ cz < 2cz = ρ^{m+1} (as z > 0 and c ≥ 1 > 0), so the alternative M(Q) ≥ ρ^{m+1} is impossible and Q = 0. Therefore Z = Z − 0 − 0 = ∂R (equality of currents, checked on every test form).
7. Y := R is IM, ∂Y = Z, M(Y) ≤ cρz = c(2cz)^{1/(m+1)}z, i.e. M(Y) ≤ ENNReal.ofReal(c·(2c·M(Z).toReal)^{1/(m+1)}·M(Z).toReal), and spt Y ⊆ thickening(3√P(2c·M(Z).toReal)^{1/(m+1)}, spt Z). The same constant c works for all Z, which proves the statement. ∎

Remark (form used by siblings): with c_I := c(2c)^{1/(m+1)}, M(Y) ≤ c_I M(Z)^{(m+2)/(m+1)}.

## Key steps

1. Take c from (DT) for (P, m); a current of zero mass is zero.
2. If M(Z) = 0 then Z = 0 and Y := 0 works.
3. Otherwise apply (DT) with ρ := (2cM(Z))^{1/(m+1)}, K := spt Z, Λ := M(Z).
4. M(S) ≤ cρM(∂Z) = 0 gives S = 0; M(Q) ≤ cM(Z) < ρ^{m+1} and the dichotomy give Q = 0.
5. Hence Z = ∂R with the mass and support bounds of (DT); take Y := R.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node, frozen types and status of its five dependencies, lean_name matches for cbr_isoperimetric_filling (accepted, other parent) and for the prefix dmcbr_ (none among 937 nodes), byte comparison of the child types with the children of root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `rg -c dmcbr SNAPSHOT (no match, exit 1); rg -n -i 'isoperimetric|closure theorem|FedererFleming|DeformationTheorem' SNAPSHOT/project/GMT -g '*.lean'`
- `rg -n -F over SNAPSHOT/mathlib/Mathlib, found: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀, euclideanHausdorffMeasure_zero, euclideanHausdorffMeasure_zero_or_top, exists_disjoint_closedBall_covering_ae, ae_tendsto_average_norm_sub, tendsto_filterAt, tendstoUniformlyOn_of_ae_tendsto, lintegral_liminf_le, countable_meas_level_set_pos, measure_inter_add_sdiff, ext_of_generate_finite, isPiSystem_isOpen, MonotoneOn.intervalIntegral_deriv_mem_uIcc, MonotoneOn.intervalIntegrable_deriv, Monotone.ae_differentiableAt, measurable_deriv, rieszMeasure, LipschitzOnWith.extend_real, LipschitzOnWith.extend_pi, finite_approx_of_totallyBounded, hausdorffMeasure_zero_singleton, one_le_hausdorffMeasure_zero_of_nonempty, IsOpen.locallyCompactSpace, ext_of_forall_integral_eq_of_IsFiniteMeasure; not found as literal 'theorem X' headers but located as to_additive/namespace/alias/instance declarations: isAddLeftInvariant_eq_smul, AlternatingMap.map_linearDependent, MeasurableSet.exists_isClosed_diff_lt, Module.Finite.multilinearMap; no match: measure_inter_add_diff (the cited name is measure_inter_add_sdiff)`
- `rg -n over .lake/packages/simongmt/Poincare, all found: simon_theorem_4_16_compact_metrizable, simon_theorem_3_3, simon_theorem_3_26_i, exists_isClosed_continuousOn_of_measurable, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, realUnitBallVolume_nat_eq, measure_toOuterMeasure_isBorelRegular, exteriorDerivative_affinePullbackForm, GeometricCurrentOn.boundary_affinePushforward, WeaklyConvergesOn.massOn_le_liminf, WeaklyConvergesOn.boundary, GeometricCurrentOn.boundary_boundary, countablyRectifiable_of_measure_zero, countablyRectifiable_range, countablyRectifiable_iUnion, CountablyRectifiable.mono; sed on the massOn, support, restrictDomain, HasApproximateTangentSpaceAt and blowUpMap definitions`
- `lake env lean (v4.35.0-rc3) on /tmp/dimred_cbr2/lean/AllTypes.lean (12 types, sorry warnings only), /tmp/dimred_cbr2/lean/Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound) and /tmp/dimred_cbr2/lean/InstCheck.lean; lean_contract.validate_lean_statement on all 12 types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-4c4627e694/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-4c4627e694/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ba6febc1b9/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dimred_cbr2/lean/AllTypes.lean`
- `/tmp/dimred_cbr2/lean/Assembly.lean`
- `/tmp/dimred_cbr2/lean/InstCheck.lean`

Pins match (HEAD b4d606d = snapshot project commit, Mathlib 25730c7c, SimonGMT 2b366308), and Submission.lean is byte-identical to the frozen contract and to the snapshot copy. The snapshot has no dmcbr declaration and no proved closure, deformation or isoperimetric theorem; its Chapter 6 matches are contract definitions only. Every Mathlib and SimonGMT name cited by the child proofs exists in the pinned sources. The five dependency types in dag.json are unchanged since attempt 1. cbr_isoperimetric_filling is accepted but owned by another parent and was reported reserved, so it is not reused; dmcbr_isoperimetric_filling and the other dmcbr_ names match no DAG node. All 12 child types elaborate, and the sorry-free conditional assembly proves the exact parent type with axioms propext, Classical.choice, Quot.sound.
