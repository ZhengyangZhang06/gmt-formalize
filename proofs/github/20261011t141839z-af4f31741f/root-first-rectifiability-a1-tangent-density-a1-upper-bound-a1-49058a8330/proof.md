# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.tangent_density-a1`
- Child DAG node: `root.first_rectifiability-a1.tangent_density-a1.upper_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 2, 4 and 6 of the parent proof. This is the upper cutoff (f ≡ 1 on B_1(0), f ≡ 0 off B_{1+ε}(0)) of Simon Ch. 3, Remark 1.8(2). The passage κ ↓ 1 of Step 7 is performed here by choosing κ in terms of c.

Notation: ω := unitBallVolume n; ν := μHE[n].restrict T.plane; B_t(x) := closedBall x t; μ.real s := (μ s).toReal.

Hypotheses: θ > 0, r₀ > 0, μ(B_{r₀}(x)) ≠ ∞, and (Blow): for every g ∈ C_c(ℝ^N, ℝ), t⁻¹^n ∫ g(t⁻¹ • (z − x)) dμ(z) → θ ∫_T g dH^n as t → 0⁺. Fix c ∈ [0, ∞] with ofReal(θ) · ω < c.

1. ω ∈ (0, ∞) and ω.toReal > 0, by measure_ball_pos and measure_ball_lt_top on EuclideanSpace ℝ (Fin n) and ENNReal.toReal_pos.

2. The case c = ∞. For every t > 0, ofReal(t)^n ≠ 0, so ∞ · ofReal(t)^n = ∞ (ENNReal.top_mul) and μ(B_t(x)) ≤ ∞. Since {t | t > 0} ∈ 𝓝[>] 0 (self_mem_nhdsWithin), the claim holds. Assume from now on that c ≠ ∞.

3. θ · ω.toReal < c.toReal. We have ofReal θ · ω = ofReal(θ ω.toReal) (ENNReal.ofReal_mul, ENNReal.ofReal_toReal), so ofReal(θ ω.toReal) < c with both sides finite. Applying toReal (ENNReal.toReal_lt_toReal, then ENNReal.toReal_ofReal with θ ω.toReal > 0) gives the claim.

4. Choice of κ. The map κ ↦ θ ω.toReal κ^n is continuous and equals θ ω.toReal < c.toReal at κ = 1. So along 𝓝[>] 1 it eventually satisfies θ ω.toReal κ^n < c.toReal (gt_mem_nhds), and eventually κ > 1 (self_mem_nhdsWithin). Pick such a κ: κ > 1 (hence κ > 0) and θ ω.toReal κ^n < c.toReal.

5. Cutoff. For y ∈ ℝ^N let χ(y) := max(0, min(1, (κ − ‖y‖)/(κ − 1))).
- χ is continuous and 0 ≤ χ ≤ 1.
- χ(y) = 1 if ‖y‖ ≤ 1, because then (κ − ‖y‖)/(κ − 1) ≥ 1.
- χ(y) = 0 if ‖y‖ ≥ κ, because then the quotient is ≤ 0.
So χ vanishes off the compact set closedBall 0 κ and has compact support (HasCompactSupport.intro). Let g ∈ C_c(ℝ^N, ℝ) be χ, so that g y = χ y.

6. Plane side: ∫_T g dH^n ≤ ω.toReal · κ^n. By the sibling lemma frt_td_plane_closedBall_hausdorff with r = κ, and Measure.restrict_apply, ν(closedBall 0 κ) = H^n(T.plane ∩ closedBall 0 κ) = ω · ofReal(κ)^n < ∞. Hence 1_{closedBall 0 κ} is ν-integrable (integrable_indicator_iff, integrableOn_const). Moreover 0 ≤ g ≤ 1_{closedBall 0 κ} pointwise, since g ≤ 1 everywhere and g(y) = 0 when ‖y‖ > κ. By integral_mono_of_nonneg and integral_indicator_one, ∫ g dν ≤ ν.real(closedBall 0 κ) = (ω · ofReal(κ)^n).toReal = ω.toReal · κ^n.

7. The limit is below c. By θ ≥ 0, step 6 and step 4, θ ∫_T g dH^n ≤ θ ω.toReal κ^n < c.toReal. Applying (Blow) to g (gt_mem_nhds), ∀ᶠ t in 𝓝[>] 0, t⁻¹^n ∫ g(t⁻¹ • (z − x)) dμ(z) < c.toReal. Also ∀ᶠ t in 𝓝[>] 0, t ∈ (0, r₀/κ) (Ioo_mem_nhdsGT, since r₀/κ > 0). Fix t with both properties.

8. Finiteness. From t < r₀/κ we get κt ≤ r₀; from κ ≥ 1 and t > 0 we get t ≤ κt. Hence B_t(x) ⊆ B_{κt}(x) ⊆ B_{r₀}(x) (closedBall_subset_closedBall), and μ(B_t(x)) ≤ μ(B_{κt}(x)) ≤ μ(B_{r₀}(x)) < ∞ (measure_mono).

9. Integrability of the rescaled cutoff. For every z, ‖t⁻¹ • (z − x)‖ = ‖z − x‖/t (norm_smul, t > 0). The function z ↦ g(t⁻¹ • (z − x)) is continuous, hence AE-strongly measurable. It satisfies |g(t⁻¹ • (z − x))| ≤ 1_{B_{κt}(x)}(z): if z ∉ B_{κt}(x) then ‖z − x‖ > κt, so ‖t⁻¹ • (z − x)‖ > κ and g(·) = 0; otherwise |g| ≤ 1. Since μ(B_{κt}(x)) < ∞ the indicator is μ-integrable, so Integrable.mono' shows that z ↦ g(t⁻¹ • (z − x)) is μ-integrable.

10. Comparison. For every z, 0 ≤ 1_{B_t(x)}(z) ≤ g(t⁻¹ • (z − x)): if z ∈ B_t(x) then ‖t⁻¹ • (z − x)‖ = ‖z − x‖/t ≤ 1 and g(·) = 1; otherwise the indicator is 0 ≤ g(·). By integral_mono_of_nonneg (using step 9) and integral_indicator_one, μ.real(B_t(x)) ≤ ∫ g(t⁻¹ • (z − x)) dμ.

11. Conclusion. With t^n > 0, μ.real(B_t(x)) ≤ ∫ g(t⁻¹ • (z − x)) dμ = (t⁻¹^n ∫ g(t⁻¹ • (z − x)) dμ) · t^n < c.toReal · t^n by step 7. Since μ(B_t(x)) ≠ ∞, μ(B_t(x)) = ofReal(μ.real(B_t(x))) ≤ ofReal(c.toReal · t^n) = ofReal(c.toReal) · ofReal(t)^n = c · ofReal(t)^n (ENNReal.ofReal_le_ofReal, ENNReal.ofReal_mul, ENNReal.ofReal_pow, and ENNReal.ofReal_toReal with c ≠ ∞). ∎

## Key steps

1. ω ∈ (0,∞); the case c = ∞ is trivial; otherwise θ·ω.toReal < c.toReal.
2. Choose κ > 1 with θ·ω.toReal·κ^n < c.toReal by continuity of κ^n at κ = 1.
3. Cutoff g(y) = max(0, min(1, (κ−‖y‖)/(κ−1))) ∈ C_c: equals 1 on closedBall 0 1, vanishes for ‖y‖ ≥ κ, 0 ≤ g ≤ 1.
4. Sibling plane lemma: ∫_T g ≤ H^n(T ∩ B_κ(0)).toReal = ω.toReal·κ^n, so θ∫_T g < c.toReal.
5. Blow-up limit: eventually t⁻¹^n ∫ g(t⁻¹(z−x)) dμ < c.toReal with t ∈ (0, r₀/κ).
6. B_t ⊆ B_{κt} ⊆ B_{r₀} have finite mass; 1_{B_t(x)} ≤ g(t⁻¹(z−x)) ≤ 1_{B_{κt}(x)} gives integrability and μ.real(B_t(x)) ≤ ∫ g(t⁻¹(z−x)) dμ; convert to μ(B_t(x)) ≤ c·ofReal(t)^n.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean and GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'def unitBallVolume|def densityRatio|def HasDensity|def HasTangentPlane|def planeVarifoldMeasure' project/GMT/Ch08/Contract.lean (lines 41, 45, 51, 108, 102)`
- `rg -n '^theorem Isometry.euclideanHausdorffMeasure_image|^theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (131, 187)`
- `rg -n '^theorem addHaar_closedBall \(' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean (500; no Nontrivial hypothesis, so n = 0 included)`
- `rg -n '^theorem integral_indicator_one' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean (533); rg -n '^lemma integral_mono_of_nonneg' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean (676); rg -n '^theorem integrableOn_const ' mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean (119, finiteness autoparam)`
- `rg -n 'protected theorem le_div_iff_mul_le|^theorem div_le_of_le_mul \(|protected theorem mul_lt_mul_left' mathlib/Mathlib/Basic/ENNReal/Inv.lean mathlib/Mathlib/Basic/ENNReal/Operations.lean (Inv 369, 392; Operations 62)`
- `rg -n 'theorem tendsto_order' mathlib/Mathlib/Topology/Order/Basic.lean (139); rg -n '^theorem measure_ball_pos' mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean (212); rg -n '^theorem measure_ball_lt_top' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean (373); rg -n 'theorem Ioo_mem_nhdsLT ' mathlib/Mathlib/Topology/Order/OrderClosed.lean (282); rg -n 'Ioo_mem_nhdsGT' mathlib/Mathlib/Topology/Order/ (used in Monotone.lean:141,464)`
- `rg -n 'theorem finrank_euclideanSpace_fin|irreducible_def stdOrthonormalBasis' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean (205, 1073)`
- `rg -l -i varifold mathlib/Mathlib/MeasureTheory mathlib/Mathlib/Geometry mathlib/Mathlib/Analysis (0 files); rg -n 'frt_td_|hasDensity_of_ball_mass|plane_closedBall_hausdorff' project (no match, exit 1)`
- `rg -n in pinned SimonGMT .lake/packages/simongmt/Poincare/SimonGMT: Chapter08/Varifold.lean 'theorem finrank_plane' (126), 'isOpen_domain : IsOpen U' (336), 'theorem weight_finite_on_compact' (576); Chapter04/TangentDensity.lean 'locallyFinite_planeMeasure' (76), 'planeMeasure_unit_closedBall' (93, requires 0 < n and lies outside the Submission import closure), 'tangentDensityCutoff' (116)`
- `git show b951e87:GMT/Ch08/Submission.lean (proved Submission.frt_weight_blowup_tendsto, reused verbatim in scratch); git show 922b480 (speculative allard_tc_tangent_plane_density draft with this node's type, depending on unaccepted allard_tc_flat_blowup_ball_limits)`
- `python3 dag.json scan: tgc_plane_closedBall_hausdorff has the identical type to plane_ball but status decomposing; none of frt_td_plane_closedBall_hausdorff / frt_td_ball_mass_lower_of_blowup / frt_td_ball_mass_upper_of_blowup / frt_td_hasDensity_of_ball_mass_bounds among 77 nodes; grep -rl frt_td_ .humanize/github-theorem-prover and cluster-state JSON (no match); git log --all -S frt_td_ (no match)`
- `python3 -I: verifier lean_contract.validate_lean_statement and gmt-compare.contract_scope/child_modules for the 4 children (scope: open Set Filter MeasureTheory Metric; open scoped Topology ENNReal CompactlySupported Pointwise; namespace GMT.Ch08; open Poincare.SimonGMT; open Poincare.SimonGMT.Chapter08; section Definitions; end Definitions)`
- `lake env lean /tmp/td-decomp/Check.lean (uncle + 4 children sorry'd; parent assembly compiles with no sorry of its own)`
- `lake env lean /tmp/td-decomp/Full.lean (uncle proof + 4 child proofs + parent, no sorry; #print axioms of all five: propext, Classical.choice, Quot.sound)`
- `lake env lean on the 4 generated NodeChallenge files (all exit 0); lean -o scratch GMT/Ch08/Submission.olean from a pure 368-line insertion before main_theorem, then the 5 generated NodeSolution files (4 children + parent frt_tangent_plane_hasDensity) with LEAN_PATH prefixed: all exit 0 with axioms propext, Classical.choice, Quot.sound`
- `sed -n 50,80p and 145,200p book/chapter-08.txt (Def. 1.1, proof of 1.2); sed -n 284,330p book/chapter-03.txt (Def. 1.7, Remark 1.8(2): cutoff f ≡ 1 on B_1(0), f ≡ 0 off B_{1+ε}(0) gives the density)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-tangent-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-tangent-density-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`

Snapshot provenance: project 63436ae6 with Mathlib 25730c7c; its Contract.lean is byte-identical to the workspace Contract and Submission.

Mathlib contains no varifold theory. It does contain every analytic tool the children need: Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:131,187); Measure.addHaar_closedBall (EqHaar.lean:500, with no Nontrivial hypothesis, so n = 0 is covered); integral_indicator_one, integral_mono_of_nonneg and integrableOn_const; and ENNReal.le_div_iff_mul_le, div_le_of_le_mul and mul_lt_mul_left, plus tendsto_order, measure_ball_pos/lt_top, Ioo_mem_nhdsLT/GT, finrank_euclideanSpace_fin and stdOrthonormalBasis.

From pinned SimonGMT the children use Grassmannian.finrank_plane, Varifold.isOpen_domain and Varifold.weight_finite_on_compact (all inside Submission's import closure). SimonGMT's planeMeasure_unit_closedBall needs 0 < n and is outside the import closure, so the plane-ball formula is proved directly; no new import is needed.

All four child statements elaborate in the exact comparator scope. Each was fully proved in a scratch file, the parent assembles from them together with the already-proved frt_weight_blowup_tendsto, and comparator-form NodeChallenge/NodeSolution replays pass with only propext, Classical.choice and Quot.sound. The proposed names collide with nothing.
