# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.rescaled_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 4 (estimate (*)) of the parent proof, together with the rescaled density bounds that its step 7 uses.
Notation: ω_n ∈ (0, ∞) and V(r) := ω_n·ofReal(rⁿ) ∈ (0, ∞) for r > 0 as in the sibling density_bounds; θ₀ := θ(a) > 0; τ := θζ, τ₀ := θ(a)ζ(a); for i ∈ ℕ: D_i := dilation a λ_i (= blowUpMap a λ_i), c_i := ofReal(λ_i^{−n}) = ENNReal.ofReal(λ_i⁻¹ ^ n).
1. (Change of variables.) By the sibling blowup_measure (cbr_ci_bl_blowUp_restrict_scaling), part (ii) (M Borel, θ Borel, λ_i > 0): ν_i = c_i·(D_i)_#(Hⁿ⌞M). D_i is a measurable embedding — it is the homeomorphism y ↦ −λ_i⁻¹a + λ_i⁻¹y (Homeomorph.smulOfNeZero followed by Homeomorph.addLeft) — and a + λ_i·D_i(x) = x. Consequently, for every Borel S, ν_i(S) = c_i·Hⁿ(M ∩ D_i⁻¹S) (Measure.smul_apply, MeasurableEmbedding.map_apply, Measure.restrict_apply, inter_comm); and for every g : ℝ^P → [0,∞] and Borel S, ∫⁻_S g dν_i = c_i·∫⁻_{M∩D_i⁻¹S} g(D_i(x)) dHⁿ(x) (Measure.restrict_smul, lintegral_smul_measure, MeasurableEmbedding.restrict_map, MeasurableEmbedding.lintegral_map, Measure.restrict_restrict).
2. (Balls and constants.) D_i(y) = λ_i⁻¹(y − a), so ‖D_i(y)‖ = λ_i⁻¹·dist(y, a) and, for R ∈ ℝ, D_i⁻¹(B̄_R(0)) = B̄_{λ_iR}(a) and D_i⁻¹(B_R(0)) = B_{λ_iR}(a) (inv_mul_le_iff₀, inv_mul_lt_iff₀). For R > 0, c_i·V(λ_iR) = V(R) because (λ_i⁻¹)ⁿ(λ_iR)ⁿ = Rⁿ (ENNReal.ofReal_mul, mul_pow); equivalently c_i = V(R)/V(λ_iR) (ENNReal.mul_div_cancel_right, V(λ_iR) ∈ (0, ∞)).
3. (Small scales.) Apply the sibling density_bounds (cbr_ci_bl_density_bounds) with the same hypotheses: there is r₀ > 0 with ofReal(η₁/(4θ₀))·V(r) ≤ Hⁿ(M ∩ B_r(a)) and Hⁿ(M ∩ B̄_r(a)) ≤ 2V(r) for 0 < r < r₀. For R > 0 we have λ_iR > 0 and λ_iR → 0, i.e. λ_iR → 0 in 𝓝[>] 0 (tendsto_nhdsWithin_iff, Tendsto.mul_const); in particular λ_iR < r₀ for all large i.
4. (Part (a).) Let K be compact. Choose R > 0 with K ⊆ B̄_R(0) (K is bounded, Bornology.IsBounded.subset_closedBall; take R := max(R₀, 1)) and N with λ_iR < r₀ for i ≥ N. For every i, ν_i(K) ≤ ν_i(B̄_R(0)) = c_i·Hⁿ(M ∩ B̄_{λ_iR}(a)) (steps 1–2). If i ≥ N this is ≤ c_i·2V(λ_iR) = 2V(R). If i < N it is ≤ c_i·Hⁿ(M) ≤ Σ_{j<N} c_j·Hⁿ(M) (Finset.single_le_sum). Hence sup_i ν_i(K) ≤ max(2V(R), Σ_{j<N} c_jHⁿ(M)) < ∞, since V(R) < ∞, every c_j < ∞ and Hⁿ(M) < ∞ (ENNReal.sum_lt_top).
5. (Part (b).) Let R > 0 and h(r) := Hⁿ(M ∩ B̄_r(a))/V(r). By steps 1–2, ν_i(B̄_R(0)) = c_i·Hⁿ(M ∩ B̄_{λ_iR}(a)) = V(R)·h(λ_iR). As V(R) < ∞, limsup_i V(R)·h(λ_iR) = V(R)·limsup_i h(λ_iR) (ENNReal.limsup_const_mul_of_ne_top; note that ENNReal.limsup_const_mul would need a countable-intersection filter). Let c > 1. By (U), limsup_{r↓0} h(r) ≤ 1 < c, so eventually in 𝓝[>] 0, h(r) < c (eventually_lt_of_limsup_lt); by step 3, eventually in i, h(λ_iR) < c; hence limsup_i h(λ_iR) ≤ c (limsup_le_of_le). Since c > 1 is arbitrary, limsup_i h(λ_iR) ≤ 1 (le_of_forall_gt_imp_ge_of_dense), and limsup_i ν_i(B̄_R(0)) ≤ V(R)·1 = ω_n·ofReal(Rⁿ).
6. (Part (c).) Let R > 0. For every i with λ_iR < r₀ (eventually, step 3): ofReal(η₁/(4θ₀))·V(R) = c_i·(ofReal(η₁/(4θ₀))·V(λ_iR)) ≤ c_i·Hⁿ(M ∩ B_{λ_iR}(a)) = ν_i(B_R(0)) ≤ ν_i(B̄_R(0)) (steps 1–3, ball_subset_closedBall).
7. (Part (d).) Let R > 0 and g_i(y) := ‖θ(a + λ_iy)ζ(a + λ_iy) − θ(a)ζ(a)‖ₑ = ‖τ(a + λ_iy) − τ₀‖ₑ. Since a + λ_iD_i(x) = x, g_i(D_i(x)) = ‖τ(x) − τ₀‖ₑ. By step 1 with S = B̄_R(0) and step 2, ∫⁻_{B̄_R(0)} g_i dν_i = c_i·∫⁻_{M∩B̄_{λ_iR}(a)} ‖τ − τ₀‖ₑ dHⁿ = V(R)·(o(λ_iR)/V(λ_iR)), where o(r) := ∫⁻_{M∩B̄_r(a)} ‖τ − τ₀‖ₑ dHⁿ. By (D), o(r)/V(r) → 0 as r ↓ 0; composing with λ_iR → 0 in 𝓝[>] 0 (Tendsto.comp, step 3) gives o(λ_iR)/V(λ_iR) → 0, and multiplying by the finite constant V(R) (ENNReal.Tendsto.const_mul) gives ∫⁻_{B̄_R(0)} g_i dν_i → V(R)·0 = 0. ∎

## Key steps

1. blowup_measure: ν_i = λ_i^{−n}·(dilation a λ_i)_#(Hⁿ⌞M), so ν_i(S) = λ_i^{−n}Hⁿ(M ∩ D_i⁻¹S) and lintegrals over S pull back to M ∩ D_i⁻¹S.
2. D_i⁻¹(B̄_R(0)) = B̄_{λ_iR}(a), D_i⁻¹(B_R(0)) = B_{λ_iR}(a) and λ_i^{−n}·ω_n(λ_iR)ⁿ = ω_nRⁿ.
3. density_bounds gives r₀; λ_iR → 0 in 𝓝[>] 0, so eventually λ_iR < r₀.
4. (a) uniform compact bounds from Hⁿ(M ∩ B̄_r(a)) ≤ 2ω_nrⁿ and Hⁿ(M) < ∞; (b) limsup ≤ ω_nRⁿ from (U); (c) eventual lower bound from density_bounds; (d) rescaled deviation = ω_nRⁿ·o(λ_iR)/(ω_n(λ_iR)ⁿ) → 0 by (D).

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
