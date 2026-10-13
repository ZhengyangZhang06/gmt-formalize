# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1`
- Child DAG node: `root.first_rectifiability-a1.varifold_graph_measure-a1.tangent_ball_average-a1.plane_cutoff_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 6 (plane integrals) of the parent proof, with the cut-off facts of its Step 3; it uses only the sibling plane_ball (Submission.frt_vgm_tba_plane_closedBall_hausdorff).

Notation: μ := H^n ⌞ T.plane = μHE[n].restrict T.plane, so ∫_{T.plane} f dH^n = ∫ f dμ for every f : ℝ^N → ℝ. B_r(0) is the closed ball in ℝ^N. For a ∈ ℝ let χ_a(y) := max(0, min(1, (a − |y|)/κ)); thus χ⁻ = χ_1 and χ⁺ = χ_{1+κ}.

1. Balls. Let r ≥ 0. B_r(0) is closed, hence Borel, so μ(B_r(0)) = H^n(B_r(0) ∩ T.plane) (Measure.restrict_apply) = H^n(T.plane ∩ B_r(0)) = unitBallVolume n · ENNReal.ofReal(r)^n by the sibling plane_ball, i.e. Submission.frt_vgm_tba_plane_closedBall_hausdorff N n T r (applicable as r ≥ 0). unitBallVolume n = volume(ball (0 : EuclideanSpace ℝ (Fin n)) 1) < ∞ (measure_ball_lt_top), and ENNReal.ofReal(r)^n < ∞, so μ(B_r(0)) < ∞. Taking real parts (ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal with r ≥ 0): μ.real(B_r(0)) = (μ(B_r(0))).toReal = ω_n r^n.

2. Cut-off facts. Let a ∈ ℝ and y ∈ ℝ^N. (i) 0 ≤ χ_a(y) ≤ 1 (outer max with 0, inner min with 1). (ii) If |y| ≥ a, then (a − |y|)/κ ≤ 0 because κ > 0, so min(1, (a − |y|)/κ) ≤ 0 and χ_a(y) = 0. (iii) If |y| ≤ a − κ, then a − |y| ≥ κ, so (a − |y|)/κ ≥ 1, min(1, ·) = 1 and χ_a(y) = 1. (iv) χ_a is continuous (norm, affine maps, division by the constant κ, min and max).

3. Integrability. Let a ≤ 2. χ_a is continuous, hence AE-strongly measurable; |χ_a| ≤ 1 by 2(i); and if y ∉ B_2(0) then |y| > 2 ≥ a, so χ_a(y) = 0 by 2(ii). Since μ(B_2(0)) < ∞ by 1, χ_a is integrable on B_2(0) (Measure.integrableOn_of_bounded with bound 1), hence μ-integrable because it vanishes off B_2(0) (IntegrableOn.integrable_of_forall_notMem_eq_zero). This applies to χ⁻ = χ_1 and to χ⁺ = χ_{1+κ} (1 + κ < 2 since κ < 1). For r ≥ 0 the indicator 1_{B_r(0)} is μ-integrable (integrable_indicator_iff for the Borel set B_r(0), and integrableOn_const using μ(B_r(0)) < ∞ from 1).

4. Lower bound. Pointwise 1_{B_{1−κ}(0)} ≤ χ⁻: if |y| ≤ 1 − κ, then χ⁻(y) = χ_1(y) = 1 by 2(iii) with a = 1; otherwise the indicator is 0 ≤ χ⁻(y) by 2(i). By integral_mono (both sides integrable by 3), ∫ 1_{B_{1−κ}(0)} dμ ≤ ∫ χ⁻ dμ, and ∫ 1_{B_{1−κ}(0)} dμ = μ.real(B_{1−κ}(0)) (integral_indicator_one) = ω_n(1 − κ)^n by 1 with r = 1 − κ ≥ 0 (as κ < 1). This is the first conjunct: ω_n(1 − κ)^n ≤ ∫_{T.plane} χ⁻ dH^n.

5. Upper bound. Pointwise χ⁺ ≤ 1_{B_{1+κ}(0)}: if |y| ≤ 1 + κ, then χ⁺(y) ≤ 1 = 1_{B_{1+κ}(0)}(y) by 2(i); otherwise |y| > 1 + κ and χ⁺(y) = χ_{1+κ}(y) = 0 = 1_{B_{1+κ}(0)}(y) by 2(ii) with a = 1 + κ. By integral_mono (integrability from 3) and integral_indicator_one, ∫ χ⁺ dμ ≤ μ.real(B_{1+κ}(0)) = ω_n(1 + κ)^n by 1 with r = 1 + κ ≥ 0. This is the second conjunct: ∫_{T.plane} χ⁺ dH^n ≤ ω_n(1 + κ)^n. ∎

## Key steps

1. For r ≥ 0, (μHE[n]⌞T.plane)(B_r(0)) = unitBallVolume n · ofReal(r)^n < ∞ (Measure.restrict_apply and sibling plane_ball = Submission.frt_vgm_tba_plane_closedBall_hausdorff), with real value ω_n r^n
2. Cut-off facts for χ_a(y) = max(0, min(1, (a − |y|)/κ)): 0 ≤ χ_a ≤ 1, χ_a = 0 where |y| ≥ a, χ_a = 1 where |y| ≤ a − κ
3. χ⁻, χ⁺ and ball indicators are integrable for μHE[n]⌞T.plane (bounded, vanishing off B_2(0) of finite measure)
4. 1_{B_{1−κ}(0)} ≤ χ⁻, integral_mono and integral_indicator_one: ω_n(1−κ)^n ≤ ∫_{T.plane} χ⁻ dH^n
5. χ⁺ ≤ 1_{B_{1+κ}(0)}: ∫_{T.plane} χ⁺ dH^n ≤ ω_n(1+κ)^n

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
