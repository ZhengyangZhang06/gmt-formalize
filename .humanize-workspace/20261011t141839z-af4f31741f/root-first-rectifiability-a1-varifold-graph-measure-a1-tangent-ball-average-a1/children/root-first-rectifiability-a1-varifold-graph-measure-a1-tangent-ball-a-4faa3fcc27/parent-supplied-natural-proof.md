# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1`
- Child DAG node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.nonneg_ball_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 2, 3 and 7 (squeeze for β ≥ 0) of the parent proof. Its three ingredients are supplied by siblings: the blow-up limit for product test functions g(y)β(S) (product_blowup), the pointwise cut-off squeeze integrated against V (ball_cutoff_sandwich), and the bounds for the plane integrals of the cut-offs (plane_cutoff_bounds).

Notation: G := Grassmannian N n; ω := (unitBallVolume n).toReal ≥ 0; J(t) := t⁻¹^n ∫_{B_t(x)×G} β(z.2) dV(z); c := θ β(T) ω. Since θ > 0 (second clause of HasTangentPlane) and β(T) ≥ 0, θβ(T) ≥ 0 and c ≥ 0. The asserted limit θ ω β(T) equals c, so we must show J(t) → c as t → 0⁺.

1. Local finiteness (parent Step 2). By the first clause of HasTangentPlane, x ∈ U, and U is open (V.isOpen_domain), so there is δ > 0 with ball x δ ⊆ U (Metric.isOpen_iff). For 0 < t < δ/2 we have 2t < δ, so B_{2t}(x) ⊆ ball x δ ⊆ U (closedBall_subset_ball). Since (0, δ/2) ∈ 𝓝[>] 0: eventually as t → 0⁺, t > 0 and B_{2t}(x) ⊆ U.

2. Cut-offs in C_c (parent Step 3). Let κ > 0 and a ∈ ℝ, and χ_a(y) := max(0, min(1, (a − |y|)/κ)) for y ∈ ℝ^N. χ_a is continuous, and it vanishes outside the compact ball B_a(0): if |y| > a then (a − |y|)/κ < 0, so the min is < 0 and the max is 0. By HasCompactSupport.intro (with isCompact_closedBall), χ_a has compact support, so it defines g_{a,κ} ∈ C_c(ℝ^N, ℝ) with g_{a,κ}(y) = χ_a(y) for all y (definitionally). We use g⁻ := g_{1,κ}, i.e. χ⁻(y) = max(0, min(1, (1 − |y|)/κ)), and g⁺ := g_{1+κ,κ}, i.e. χ⁺(y) = max(0, min(1, (1 + κ − |y|)/κ)). These are exactly the cut-offs appearing in the siblings ball_cutoff_sandwich and plane_cutoff_bounds.

3. Reduction. By tendsto_order it suffices to prove: (L) for every a' < c, eventually a' < J(t); and (U) for every b' > c, eventually J(t) < b' (both as t → 0⁺).

4. Proof of (L). Let a' < c and ε := c − a' > 0. The map κ ↦ c(1 − κ)^n is continuous, with value c at κ = 0, and c − ε/2 < c; so eventually as κ → 0⁺, c(1 − κ)^n > c − ε/2. Also eventually 0 < κ < 1. As 𝓝[>] 0 is a nontrivial filter, we can fix κ with 0 < κ < 1 and c(1 − κ)^n > c − ε/2.
 (a) By the sibling product_blowup applied to g⁻ and β: I⁻(t) := t⁻¹^n ∫ χ⁻(t⁻¹ • (z.1 − x)) β(z.2) dV(z) → θ(β(T) c⁻) as t → 0⁺, where c⁻ := ∫_{T.plane} χ⁻ dH^n (H^n = μHE[n]); here g⁻(t⁻¹ • (z.1 − x)) = χ⁻(t⁻¹ • (z.1 − x)) and ∫_{T.plane} g⁻ dH^n = c⁻ by definition of g⁻.
 (b) By the first conjunct of the sibling plane_cutoff_bounds (0 < κ < 1), ω(1 − κ)^n ≤ c⁻. Multiplying by θβ(T) ≥ 0: c(1 − κ)^n = θβ(T)(ω(1 − κ)^n) ≤ θβ(T)c⁻ = θ(β(T)c⁻).
 (c) Since θ(β(T)c⁻) − ε/2 < θ(β(T)c⁻), (a) gives: eventually I⁻(t) > θ(β(T)c⁻) − ε/2 ≥ c(1 − κ)^n − ε/2 > c − ε = a'.
 (d) Eventually (by 1) t > 0 and B_{2t}(x) ⊆ U; then the first conjunct of the sibling ball_cutoff_sandwich (with this κ ∈ (0,1), this t and β ≥ 0) gives ∫ χ⁻(t⁻¹ • (z.1 − x)) β(z.2) dV ≤ ∫_{B_t(x)×G} β(z.2) dV, and multiplying by t⁻¹^n ≥ 0 gives I⁻(t) ≤ J(t).
 Intersecting the two eventual events of (c) and (d): eventually a' < I⁻(t) ≤ J(t).

5. Proof of (U). Let b' > c and ε := b' − c > 0. The map κ ↦ c(1 + κ)^n is continuous with value c at κ = 0, and c < c + ε/2; so eventually as κ → 0⁺, c(1 + κ)^n < c + ε/2, and also eventually 0 < κ < 1. As 𝓝[>] 0 is nontrivial, fix κ with 0 < κ < 1 and c(1 + κ)^n < c + ε/2.
 (a) product_blowup applied to g⁺ and β: I⁺(t) := t⁻¹^n ∫ χ⁺(t⁻¹ • (z.1 − x)) β(z.2) dV(z) → θ(β(T)c⁺), where c⁺ := ∫_{T.plane} χ⁺ dH^n.
 (b) The second conjunct of plane_cutoff_bounds gives c⁺ ≤ ω(1 + κ)^n, so θ(β(T)c⁺) = θβ(T)c⁺ ≤ θβ(T)ω(1 + κ)^n = c(1 + κ)^n.
 (c) Eventually I⁺(t) < θ(β(T)c⁺) + ε/2 ≤ c(1 + κ)^n + ε/2 < c + ε = b'.
 (d) Eventually t > 0, B_{2t}(x) ⊆ U, and the second conjunct of ball_cutoff_sandwich times t⁻¹^n ≥ 0 gives J(t) ≤ I⁺(t).
 Hence eventually J(t) ≤ I⁺(t) < b'.

6. By 3–5, J(t) → c = θ ω β(T) as t → 0⁺, which is the claim (θ ω β(T) = θ β(T) ω by commutativity). ∎

## Key steps

1. x ∈ U open gives δ > 0 with ball x δ ⊆ U, so eventually t > 0 and B_{2t}(x) ⊆ U
2. the radial cut-offs χ⁻ = max(0,min(1,(1−|y|)/κ)) and χ⁺ = max(0,min(1,(1+κ−|y|)/κ)) are elements of C_c(ℝ^N)
3. tendsto_order: for a' < θβ(T)ω put ε := θβ(T)ω − a' and pick κ ∈ (0,1) with θβ(T)ω(1−κ)^n > a' + ε/2; product_blowup and plane_cutoff_bounds bound I⁻(t) from below eventually; ball_cutoff_sandwich gives I⁻(t) ≤ J(t)
4. symmetrically for b' > θβ(T)ω put ε := b' − θβ(T)ω and pick κ ∈ (0,1) with θβ(T)ω(1+κ)^n < b' − ε/2; product_blowup with χ⁺ and plane_cutoff_bounds bound I⁺(t) from above eventually; ball_cutoff_sandwich gives J(t) ≤ I⁺(t)
5. hence t⁻¹^n ∫_{B_t(x)×G} β dV → θ ω_n β(T)

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'def HasTangentPlane|def rescaledMeasure|def planeVarifoldMeasure|def unitBallVolume' project/GMT/Ch08/Contract.lean`
- `cmp project/GMT/Ch08/Contract.lean project/GMT/Ch08/Submission.lean (identical)`
- `rg -n 'theorem Isometry.euclideanHausdorffMeasure_image|theorem euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem addHaar_closedBall ' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n 'theorem integral_smul_measure|^theorem integral_map |theorem integral_mul_const |theorem integral_sub ' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean mathlib/Mathlib/MeasureTheory/Integral/Bochner/*.lean`
- `rg -n 'theorem integral_indicator |theorem setIntegral_const|theorem integral_indicator_one' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `rg -n 'integrableOn_of_bounded' mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean; rg -n 'theorem IntegrableOn.integrable_of_forall_notMem_eq_zero|theorem integrableOn_const|theorem integrable_indicator_iff' mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `rg -n '^theorem tendsto_order ' mathlib/Mathlib/Topology/Order/Basic.lean; rg -n 'theorem Filter.Tendsto.div ' mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean; rg -n 'theorem finrank_euclideanSpace_fin' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; rg -n 'theorem norm_coe_le_norm' mathlib/Mathlib/Topology/ContinuousMap/Compact.lean; rg -n 'theorem intro' mathlib/Mathlib/Topology/Algebra/Support.lean`
- `rg -n 'theorem measure_ball_pos|theorem measure_ball_lt_top' mathlib/Mathlib/MeasureTheory`
- `grep -rn 'lemma mul_div_mul_left' mathlib/Mathlib/Algebra/GroupWithZero/`
- `rg -n 'frt_vgm_tba|frt_td_plane' project/ (no match)`
- `grep -n 'structure Varifold|isOpen_domain|finite_on_compact|theorem weight_apply|finrank_plane|instCompactSpace|abbrev Grassmannian' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `python3 -I scan of dag.json nodes with lean_name containing closedBall_hausdorff/plane_ball (ids, status, lean_statement); grep -c frt_vgm_tba in all 8 chapter dag.json files (0 each)`
- `for r in $(git for-each-ref --format='%(refname)'); git grep -q frt_vgm_tba $r -- GMT (0 hits over 617 refs)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint' /runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py`
- `python3 -I /tmp/tba_decomp3/scripts/scope.py and stmts3.py (gmt-compare.py contract_scope/child_modules mode='contract'; lean_contract.validate_lean_statement on all six types)`
- `lake env lean /tmp/tba_decomp3/Full3.lean, Stub3.lean, Emu3.lean, Challenge_0..5.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-tangent-ball-average-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-varifold-graph-measure-a1-tangent-ball-average-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/tmp/tba_decomp3/Full3.lean`
- `/tmp/tba_decomp3/Stub3.lean`
- `/tmp/tba_decomp3/Emu3.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract.lean is identical to Submission.lean. It defines HasTangentPlane (l.108), rescaledMeasure (l.96), planeVarifoldMeasure (l.102) and unitBallVolume (l.41) exactly as the children's prose describes them.

Every library fact the children need exists in the pinned Mathlib/SimonGMT:
- plane_ball: Isometry.euclideanHausdorffMeasure_image (Volume/Measure.lean:131), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (:187), Measure.addHaar_closedBall (EqHaar.lean:500), finrank_euclideanSpace_fin (PiL2.lean:205), and SimonGMT Grassmannian.finrank_plane (Varifold.lean:126).
- plane_cutoff_bounds and ball_cutoff_sandwich: Measure.integrableOn_of_bounded (IntegrableOn.lean:716), IntegrableOn.integrable_of_forall_notMem_eq_zero (:453), integrable_indicator_iff (:340), integrableOn_const (:119), integral_indicator and integral_indicator_one (Bochner/Set.lean:185/533), ContinuousMap.norm_coe_le_norm (ContinuousMap/Compact.lean:196), and Varifold.finite_on_compact (Varifold.lean:339).
- product_blowup: integral_smul_measure and integral_map (Bochner/Basic.lean:1052/1081), integral_mul_const (:294), HasCompactSupport.intro (Topology/Algebra/Support.lean:232), and Grassmannian.instCompactSpace (Varifold.lean:271).
- nonneg_ball_limit: tendsto_order (Topology/Order/Basic.lean:139) and Varifold.isOpen_domain (Varifold.lean:336).
- Parent assembly: integral_sub (Bochner/Basic.lean:263), setIntegral_const (Bochner/Set.lean:524), Varifold.weight_apply (Varifold.lean:565), Filter.Tendsto.div (GroupWithZero.lean:189), mul_div_mul_left (GroupWithZero/Units/Basic.lean:460), measure_ball_pos (OpenPos.lean:212) and measure_ball_lt_top (Typeclasses/Finite.lean:373).

Names: no frt_vgm_tba or frt_td_plane name occurs in the snapshot project. The plane-ball type is held by three DAG nodes under distinct names: frt_td_plane_closedBall_hausdorff (another parent; rejected for reuse by the controller), intcpt_canon_plane_closedBall_hausdorff and tgc_plane_closedBall_hausdorff. So the fresh, globally unique name frt_vgm_tba_plane_closedBall_hausdorff is used. No frt_vgm_tba_* name occurs in any chapter dag.json or on any local git ref, so the controller's _existing_lean_name_problem accepts all five.

Lean checks: all five children and the parent's exact frozen type compile in Full3.lean with only propext, Classical.choice and Quot.sound. The parent compiles from the sorry'd children in Stub3.lean. The comparator challenge files built by the verifier's child_modules elaborate every type standalone, and validate_lean_statement accepts all six.
