# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.pointwise-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.pointwise-a1.limit_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: n = d + 1, B_r(x) = ball x r, D(r) := ω_n·ofReal(rⁿ) with ω_n = unitBallVolume n; all quantities below are in [0, ∞].

1. Put c := ofReal θ₀. Since θ₀ > 0: c ≠ 0, c ≠ ∞ and c.toReal = θ₀. Let μ' := c • ν, so μ'(S) = c·ν(S) (Measure.smul_apply). Let ξ be the constant field ξ(x) := ζ₀.

2. Apply the hypothesis LD_{η₀} to C' := C, μ := μ' and this ξ. Its hypotheses hold:
 (a) ∂C = 0 by hypothesis.
 (b) For compact K, μ'(K) = c·ν(K) < ∞, because c < ∞ and ν(K) < ∞ (ENNReal.mul_lt_top).
 (c) For open W, M_W(C) = ofReal(θ₀)·ν(W) = μ'(W), by the mass hypothesis and Measure.smul_apply.
 (d) ξ is constant, hence μ'-a.e. strongly measurable (aestronglyMeasurable_const).
 (e) |ξ(x)(α)| = |ζ₀(α)| ≤ |α| for all x and α, in particular μ'-a.e.
 (f) For every test n-form ω: ∫ξ(x)(ω(x))dμ'(x) = c.toReal·∫ζ₀(ω(x))dν(x) (integral_smul_measure) = θ₀·∫ζ₀(ω(x))dν(x) = ∫θ₀ζ₀(ω(x))dν(x) (integral_const_mul) = C(ω), by the representation hypothesis.
 (g) C has ISP by hypothesis. This is exactly the ISP premise of LD_{η₀} for C' = C.
 Hence, for μ'-a.e. x: ofReal η₀ ≤ liminf_{r→0⁺} μ'(B_r(x))/D(r).

3. Since c ≠ 0, ν ≪ μ' = c • ν (Measure.absolutelyContinuous_smul). So the conclusion of step 2 holds for ν-a.e. x. Fix such an x.

4. For every r, μ'(B_r(x))/D(r) = (c·ν(B_r(x)))/D(r) = c·(ν(B_r(x))/D(r)), by Measure.smul_apply and mul_div_assoc in [0, ∞]. Let g(r) := ν(B_r(x))/D(r) and ℓ := liminf_{r→0⁺} g(r). Since c ≠ ∞ and 𝓝[>] 0 is a nontrivial filter, liminf_{r→0⁺} c·g(r) = c·ℓ (ENNReal.liminf_const_mul_of_ne_top). Step 2 therefore gives ofReal η₀ ≤ c·ℓ.

5. Two cases.
 - If η₀ ≤ 0, then η₀/θ₀ ≤ 0, so ofReal(η₀/θ₀) = 0 ≤ ℓ.
 - If η₀ > 0, then ofReal(η₀/θ₀) = ofReal η₀ / ofReal θ₀ = ofReal η₀ / c (ENNReal.ofReal_div_of_pos, θ₀ > 0). Since c ∉ {0, ∞}, ofReal η₀ / c ≤ ℓ is equivalent to ofReal η₀ ≤ ℓ·c (ENNReal.div_le_iff), which holds by step 4.
 In both cases ofReal(η₀/θ₀) ≤ ℓ = liminf_{r→0⁺} ν(B_r(x))/(ω_n·ofReal(rⁿ)). This holds for ν-a.e. x, which is the claim. ∎

## Key steps

1. Apply LD_{η₀} to C with the measure ofReal θ₀ • ν and the constant field ζ₀: finite on compacts, mass identity via Measure.smul_apply, representation via integral_smul_measure and integral_const_mul, and the ISP of C.
2. Transfer the a.e. statement from ofReal θ₀ • ν to ν (ν ≪ c • ν since c ≠ 0).
3. Rewrite (c·ν(B))/D = c·(ν(B)/D), pull the finite constant c out of the liminf (ENNReal.liminf_const_mul_of_ne_top), and divide by c = ofReal θ₀ (case η₀ ≤ 0 trivial).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean (identical) and Contract.lean with Submission.lean (identical)`
- `python3 -I scan of dag.json: frozen lean_statement of the selected node and of siblings cbr_ci_blowup_limit, cbr_ci_constant_cycle_planes, cbr_ci_plane_weight_ge_one, cbr_ci_plane_multiplicity_nat, split at top-level arrows (LD_{P,d} body and ISP blocks extracted verbatim); search of accepted orientation/covector lemmas (rsdic_unitOrientation_eq_or_eq_neg, regcomp_unit_orientation_pairing, unit_orientations_common_unit_covector, cmr_cc_det_covector_exists, covectorEuclideanNorm_gram_bounds): none states that a unit orientation determines its plane`
- `grep -n 'blowUpMap|HasApproximateTangentSpaceAt' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap x r y = r⁻¹(y−x); HasApproximateTangentSpaceAt n M x P := finrank P = n ∧ ∀ f : C_c, Tendsto along 𝓝[>] 0); grep 'Covector|covectorEuclideanNorm|GeometricCurrentOn|boundary_apply|exteriorDerivativeTestOn' in SimonGMT Chapter06 Forms/Mass/Currents`
- `grep in snapshot mathlib: 'theorem liminf_const_mul_of_ne_top' (Mathlib/Order/Filter/ENNReal.lean:190), 'lemma ae_smul_measure_iff' (Mathlib/MeasureTheory/Measure/Module.lean:204, needs IsDomain so unusable for ℝ≥0∞), 'lemma absolutelyContinuous_smul' (Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean:169), 'theorem cramer_apply'/'theorem cramer_one' (Mathlib/LinearAlgebra/Matrix/Adjugate.lean:96,120), 'theorem det_eq_zero_of_column_eq_zero' (Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:365), 'def updateCol' (Mathlib/LinearAlgebra/Matrix/RowCol.lean:205); 'def toContinuousAlternatingMap' (no match, so continuity is obtained via AlternatingMap.mkContinuous)`
- `git show fee01ff86c9de6b32f7cfc6b3f5088750ef5af7e:GMT/Ch07/Submission.lean (accepted cmr_cc_det_covector_exists: Matrix.detRowAlternating.compLinearMap plus mkContinuous with a Leibniz bound)`
- `rg -l 'cbr_ci_pw' over the snapshot project, lake-packages-25730c7c/simongmt, GMT/, the run's nodes/ directory and dag.json (no match; the four proposed names are fresh)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py check_source_delta (one appended theorem, no helper declarations) and runtime.py _overlay_accepted_children (parent prerequisites = children + depends_on); verifier/lean_contract.py validate_lean_statement on the four child types (all pass)`
- `lake env lean /tmp/pw-decomp/lean/Check.lean (the four child types elaborate; pw_assembly_check proves the frozen selected type from the four sibling types and the four child types; axioms propext, Classical.choice, Quot.sound); lake env lean on ChkA.lean, ChkB.lean, ChkLD.lean, ChkSP.lean (each child type proved, standard axioms only)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-57440db406/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-57440db406/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-33509b6e86/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/RowCol.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/pw-decomp/lean/Check.lean`
- `/tmp/pw-decomp/lean/ChkA.lean`
- `/tmp/pw-decomp/lean/ChkB.lean`
- `/tmp/pw-decomp/lean/ChkLD.lean`
- `/tmp/pw-decomp/lean/ChkSP.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c).

No accepted DAG lemma states that a unit orientation determines its plane; the closest, rsdic_unitOrientation_eq_or_eq_neg, is the converse. So plane uniqueness is a new obligation (child plane_unique). Its determinant covectors are built as in the accepted cmr_cc_det_covector_exists: detRowAlternating.compLinearMap plus mkContinuous with a Leibniz bound.

All Mathlib lemmas cited in the child proofs exist in the snapshot and are reachable from import GMT.Ch07.Submission: cramer_apply, cramer_one, det_eq_zero_of_column_eq_zero, updateCol, liminf_const_mul_of_ne_top, absolutelyContinuous_smul, integral_smul_measure, tendsto_of_subseq_tendsto, tendsto_add_atTop_iff_nat. ae_smul_measure_iff needs IsDomain, so it is avoided.

HasApproximateTangentSpaceAt and blowUpMap come from SimonGMT Chapter03.Rectifiable and match the subsequence child.

No cbr_ci_pw_ declaration exists anywhere, so the four names are fresh. All four child types elaborate and pass validate_lean_statement. A hypothesis-only Lean assembly proves the frozen selected type from the four sibling types and the four child types. Each child type has a scratch Lean proof. All of these checks use only propext, Classical.choice and Quot.sound.
