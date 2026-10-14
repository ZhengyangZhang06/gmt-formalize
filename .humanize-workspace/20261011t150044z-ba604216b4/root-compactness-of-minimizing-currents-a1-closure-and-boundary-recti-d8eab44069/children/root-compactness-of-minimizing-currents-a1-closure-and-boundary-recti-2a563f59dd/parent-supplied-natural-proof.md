# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.density_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0 (fact (F2)) and step 1 of the parent proof.
Notation: ω_n := unitBallVolume n is the volume of the open unit ball of ℝⁿ; it is > 0 (Metric.measure_ball_pos) and < ∞ (measure_ball_lt_top). V(r) := ω_n·ofReal(rⁿ), so V(r) ∈ (0, ∞) for r > 0. θ₀ := θ(a) > 0 (a ∈ M); τ := θζ, i.e. τ(x) = θ(x)•ζ(x); τ₀ := τ(a) = θ(a)•ζ(a); o(r) := ∫⁻_{M∩B̄_r(a)} ‖τ − τ₀‖ₑ dHⁿ.
1. (F2, the half that is needed.) For x ∈ M: θ(x) ≤ θ₀ + Pⁿ‖τ(x) − τ₀‖. Take β with |β| ≤ 1 and ζ(x)(β) = 1. By the sibling covector_norm (cbr_ci_bl_covector_opNorm_le), ‖β‖ ≤ Pⁿ|β| ≤ Pⁿ, hence |(τ(x) − τ₀)(β)| ≤ ‖τ(x) − τ₀‖·‖β‖ ≤ Pⁿ‖τ(x) − τ₀‖ (ContinuousLinearMap.le_opNorm). Also ζ(a)(β) ≤ |ζ(a)(β)| ≤ |β| ≤ 1, so θ₀·ζ(a)(β) ≤ θ₀. Therefore θ(x) = θ(x)·ζ(x)(β) = θ₀·ζ(a)(β) + (τ(x) − τ₀)(β) ≤ θ₀ + Pⁿ‖τ(x) − τ₀‖. In [0,∞] (ENNReal.ofReal_le_ofReal, ENNReal.ofReal_add, ENNReal.ofReal_mul, ofReal_norm_eq_enorm): ofReal θ(x) ≤ ofReal θ₀ + ofReal(Pⁿ)·‖τ(x) − τ₀‖ₑ.
2. (Mass of balls.) For every r: μ(B_r(a)) ≤ ofReal θ₀·Hⁿ(M ∩ B_r(a)) + ofReal(Pⁿ)·o(r). Indeed, by the formula for μ, withDensity_apply and Measure.restrict_restrict (balls are Borel), μ(B_r(a)) = ∫⁻_{M∩B_r(a)} ofReal θ dHⁿ. By step 1, which holds Hⁿ⌞(M ∩ B_r(a))-a.e. (ae_restrict_mem, lintegral_mono_ae), this is ≤ ∫⁻_{M∩B_r(a)} (ofReal θ₀ + ofReal(Pⁿ)·‖τ − τ₀‖ₑ) dHⁿ = ofReal θ₀·Hⁿ(M ∩ B_r(a)) + ofReal(Pⁿ)·∫⁻_{M∩B_r(a)} ‖τ − τ₀‖ₑ dHⁿ (lintegral_add_left for the constant, setLIntegral_const, lintegral_const_mul' as ofReal(Pⁿ) < ∞), and the last integral is ≤ o(r) because B_r(a) ⊆ B̄_r(a).
3. (Three eventual inequalities as r ↓ 0, i.e. in the filter 𝓝[>] 0.)
 (a) ofReal(η₁/2) < ofReal η₁ ≤ liminf μ(B_r(a))/V(r) by (L), so eventually ofReal(η₁/2) < μ(B_r(a))/V(r) (eventually_lt_of_lt_liminf).
 (b) o(r)/V(r) → 0 by (D) and ofReal(Pⁿ) < ∞, so ofReal(Pⁿ)·(o(r)/V(r)) → 0 (ENNReal.Tendsto.const_mul); since ofReal(η₁/4) > 0, eventually ofReal(Pⁿ)·(o(r)/V(r)) < ofReal(η₁/4) (tendsto_order).
 (c) limsup Hⁿ(M ∩ B̄_r(a))/V(r) ≤ 1 < 2 by (U), so eventually Hⁿ(M ∩ B̄_r(a))/V(r) < 2 (eventually_lt_of_limsup_lt).
 The conjunction of (a), (b), (c) and r > 0 holds on a member of 𝓝[>] 0, so (Metric.mem_nhdsWithin_iff) there is r₀ > 0 such that (a), (b), (c) hold for every r with 0 < r < r₀.
4. (Conclusion for 0 < r < r₀.) As V(r) ∈ (0, ∞), (a), (b), (c) give ofReal(η₁/2)·V(r) ≤ μ(B_r(a)), ofReal(Pⁿ)·o(r) ≤ ofReal(η₁/4)·V(r) and Hⁿ(M ∩ B̄_r(a)) ≤ 2V(r) (ENNReal.lt_div_iff_mul_lt, ENNReal.div_lt_iff, mul_div_assoc). The last one is the asserted upper bound. For the lower bound write ofReal(η₁/2)V(r) = ofReal(η₁/4)V(r) + ofReal(η₁/4)V(r) (ENNReal.ofReal_add, add_mul). By step 2 and (b): ofReal(η₁/4)V(r) + ofReal(η₁/4)V(r) ≤ μ(B_r(a)) ≤ ofReal θ₀·Hⁿ(M ∩ B_r(a)) + ofReal(η₁/4)V(r); cancelling the finite summand ofReal(η₁/4)V(r) (ENNReal.add_le_add_iff_right) gives ofReal(η₁/4)V(r) ≤ ofReal θ₀·Hⁿ(M ∩ B_r(a)). Finally ofReal(η₁/(4θ₀)) = (ofReal θ₀)⁻¹·ofReal(η₁/4) (ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_mul, field_simp), so ofReal(η₁/(4θ₀))·V(r) = (ofReal θ₀)⁻¹·(ofReal(η₁/4)V(r)) ≤ (ofReal θ₀)⁻¹·(ofReal θ₀·Hⁿ(M ∩ B_r(a))) = Hⁿ(M ∩ B_r(a)) (ENNReal.inv_mul_cancel, ofReal θ₀ ∈ (0, ∞)). ∎

## Key steps

1. F2: for x ∈ M, θ(x) ≤ θ(a) + Pⁿ‖θ(x)ζ(x) − θ(a)ζ(a)‖, from the norming covector of ζ(x), |ζ(a)(β)| ≤ 1 and the covector_norm sibling.
2. μ(B_r(a)) ≤ θ(a)·Hⁿ(M ∩ B_r(a)) + Pⁿ·∫⁻_{M∩B̄_r(a)}‖τ − τ₀‖ dHⁿ.
3. For 0 < r < r₀: μ(B_r(a)) ≥ (η₁/2)ω_nrⁿ (L), Pⁿ·o(r) ≤ (η₁/4)ω_nrⁿ (D), Hⁿ(M ∩ B̄_r(a)) ≤ 2ω_nrⁿ (U).
4. Cancel (η₁/4)ω_nrⁿ and divide by θ(a) to get Hⁿ(M ∩ B_r(a)) ≥ (η₁/(4θ(a)))ω_nrⁿ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical)`
- `python3 -I scans of dag.json: frozen lean_statement of cbr_ci_blowup_limit, cbr_ci_dilation_calculus, cbr_ci_dilation_slice_property, cbr_ci_const_vector_massOn; existential current constructors (pattern '∃ X : GeometricCurrentOn … ∀ ω') -> accepted cmcs_restrict_current, identical type, reused; blowUpMap/dilation lemmas (dtc_hausdorff_dilation, rsd_cmr_ir_blowUp_image_measure, setIntegral_blowUpMap_image_eq_inv_pow_mul: available but not needed); bounds between the operator norm and covectorEuclideanNorm (only |α| ≤ C‖α‖ exists, e.g. rsd_mw_tfa_norm_props, so (F1) becomes a new child); lean_name collision check for the six new cbr_ci_bl_* names (none)`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: euclideanHausdorffMeasure_homothety_image, Measure.euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image, ContinuousAlternatingMap.opNorm_le_bound, limsup_const_mul_of_ne_top, ENNReal.limsup_add_le (requires CountableInterFilter, not available for atTop), le_limsup_of_frequently_le, le_of_forall_gt_imp_ge_of_dense, integrableOn_const, tendsto_measure_cthickening_of_isClosed`
- `sed/grep of lake-packages-25730c7c/simongmt/Poincare/SimonGMT: Chapter06/Currents.lean (GeometricCurrentOn, WeaklyConvergesOn, GeometricCurrentOn.boundary, GeometricCurrentOn.ext, zero_apply, WeaklyConvergesOn.boundary), Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, GeometricCurrentOn.massOn), Chapter06/Forms.lean (Covector), Chapter03/Rectifiable.lean (blowUpMap)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py (check_source_delta: one appended theorem, no helper declarations), runtime.py (_solve_children, _existing_lean_name_problem, _overlay_accepted_children: reuse of accepted identical-type theorems; children receive only their own depends_on), store.py (ensure)`
- `lake env lean /tmp/bl-decomp/Stmts.lean, /tmp/bl-decomp/Assembly.lean, /tmp/bl-decomp/EndToEnd.lean with #print axioms; python3 verifier/lean_contract.py validate_lean_statement on all seven child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-restrict-current-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/bl-decomp/Assembly.lean`
- `/tmp/bl-decomp/EndToEnd.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). The DAG already contains the accepted cmcs_restrict_current, whose frozen type is identical; it is reused for the limit current. No existing node gives the operator-norm bound ‖α‖ ≤ C·covectorEuclideanNorm α; only the reverse direction exists, so (F1) is a new child. The six new cbr_ci_bl_* names are fresh. Every Mathlib/SimonGMT lemma the child proofs cite exists in the pinned snapshot and is reachable from import GMT.Ch07.Submission. ENNReal.limsup_add_le needs a countable-intersection filter, so constant_limit uses an ε-argument instead. All seven types elaborate and pass the lexical validator. A scratch end-to-end Lean file proves each new child from its declared siblings only, and proves the frozen parent type from the children plus the frozen statements of dilation_calculus, dilation_isp and const_mass, using only propext, Classical.choice and Quot.sound beyond the stubbed prerequisites.
