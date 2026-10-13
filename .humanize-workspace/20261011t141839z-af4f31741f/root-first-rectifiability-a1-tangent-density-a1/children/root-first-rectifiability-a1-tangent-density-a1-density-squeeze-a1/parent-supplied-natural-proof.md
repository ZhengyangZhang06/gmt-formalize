# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.tangent_density-a1`
- Child DAG node: `root.first_rectifiability-a1.tangent_density-a1.density_squeeze-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 2, 7 and 8 of the parent proof. This is the final squeeze of Simon Ch. 3, Remark 1.8(2), carried out directly in [0, ∞].

Notation: ω := unitBallVolume n = volume(ball (0 : EuclideanSpace ℝ (Fin n)) 1); B_t(x) := closedBall x t. By definition, densityRatio n μ x t = μ(B_t(x)) / (ω · ENNReal.ofReal t ^ n), and HasDensity n μ x a means Tendsto (densityRatio n μ x) (𝓝[>] 0) (𝓝 a).

Hypotheses:
(H₋) for every c < a · ω, ∀ᶠ t in 𝓝[>] 0, c · ofReal(t)^n ≤ μ(B_t(x));
(H₊) for every c > a · ω, ∀ᶠ t in 𝓝[>] 0, μ(B_t(x)) ≤ c · ofReal(t)^n.

1. 0 < ω < ∞. The open unit ball of EuclideanSpace ℝ (Fin n) is nonempty and open, and volume there is an additive Haar measure, hence positive on nonempty open sets: ω > 0 (measure_ball_pos volume 0 one_pos). The ball is bounded in a proper space, so ω < ∞ (measure_ball_lt_top). (For n = 0 the space is a point, the ball is the whole space and ω = 1.)

2. The normalizer. For t > 0 put D_t := ω · ofReal(t)^n.
- D_t ≠ 0: ofReal(t) > 0 (ENNReal.ofReal_pos), so ofReal(t)^n ≠ 0, and ω ≠ 0.
- D_t ≠ ∞: ω ≠ ∞ and ofReal(t)^n ≠ ∞ (ENNReal.pow_ne_top, ENNReal.ofReal_ne_top).
By definition densityRatio n μ x t = μ(B_t(x)) / D_t.

3. Reduction. [0, ∞] carries the order topology, so by tendsto_order it suffices to show:
(a) for every b < a, ∀ᶠ t in 𝓝[>] 0, b < densityRatio n μ x t;
(b) for every b > a, ∀ᶠ t in 𝓝[>] 0, densityRatio n μ x t < b.

4. Proof of (a). Let b < a. Since [0, ∞] is densely ordered, pick b' with b < b' < a (exists_between). By step 1, right multiplication by ω is strictly monotone (ENNReal.mul_lt_mul_left with ω ≠ 0, ω ≠ ∞), so c := b' · ω < a · ω. By (H₋), ∀ᶠ t in 𝓝[>] 0, c · ofReal(t)^n ≤ μ(B_t(x)). Also ∀ᶠ t in 𝓝[>] 0, t > 0 (self_mem_nhdsWithin). For such t, by associativity, b' · D_t = (b' · ω) · ofReal(t)^n = c · ofReal(t)^n ≤ μ(B_t(x)). Hence b' ≤ μ(B_t(x)) / D_t by ENNReal.le_div_iff_mul_le, using D_t ≠ 0 and D_t ≠ ∞ from step 2. Therefore b < b' ≤ densityRatio n μ x t.

5. Proof of (b). Let b > a. Pick b' with a < b' < b (exists_between). As in step 4, c := b' · ω > a · ω. By (H₊), ∀ᶠ t in 𝓝[>] 0, μ(B_t(x)) ≤ c · ofReal(t)^n = b' · (ω · ofReal(t)^n). ENNReal.div_le_of_le_mul (no side conditions) then gives μ(B_t(x)) / (ω · ofReal(t)^n) ≤ b', i.e. densityRatio n μ x t ≤ b' < b.

6. Conclusion. Steps 3–5 give Tendsto (densityRatio n μ x) (𝓝[>] 0) (𝓝 a), which is HasDensity n μ x a. If a = ∞ then (b) is vacuous, and if a = 0 then (a) is vacuous, so the argument covers every a ∈ [0, ∞]. ∎

## Key steps

1. 0 < ω < ∞; for t > 0 the normalizer ω·ofReal(t)^n lies in (0,∞).
2. tendsto_order reduces the claim to: eventually b < ratio for every b < a, and eventually ratio < b for every b > a.
3. For b < a pick b < b' < a; apply the lower hypothesis with c = b'ω < aω and use ENNReal.le_div_iff_mul_le.
4. For b > a pick a < b' < b; apply the upper hypothesis with c = b'ω > aω and use ENNReal.div_le_of_le_mul.

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
