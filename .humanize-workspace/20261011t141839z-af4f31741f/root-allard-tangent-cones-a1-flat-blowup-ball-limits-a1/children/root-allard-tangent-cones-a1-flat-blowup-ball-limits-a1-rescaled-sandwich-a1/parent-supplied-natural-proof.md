# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`
- Child DAG node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.rescaled_sandwich-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2, 3, 5 (items (5a), (5c)) and the first display of step 7 of the parent-supplied proof: monotonicity of the integral after the change of variables, at one fixed radius r. The index k is replaced by k + 1.

Notation.
- G := Grassmannian N n, a compact space.
- a := k + 1 ≥ 1. For w ∈ ℝ^N, φ⁺(w) := max(0, 1 − a·max(0, ‖w‖ − 1)) and φ⁻(w) := min(1, a·max(0, 1 − ‖w‖)).
- Φ(y,S) := (r⁻¹(y − x), S). By definition, rescaledMeasure V x r = c • (V.measure.map Φ) with c := ofReal(r⁻¹^n).
- B := B_r(x) × G and K := B_{2r}(x) × G (closed balls).
- ‖β‖ := sup_S |β(S)| < ∞, since G is compact; so |β(S)| ≤ ‖β‖ for all S (ContinuousMap.norm_coe_le_norm).

1. Finite mass on K. B_{2r}(x) is a closed ball in ℝ^N, hence compact, and B_{2r}(x) ⊆ U by hypothesis. So V.measure(K) < ∞ by the varifold axiom finite_on_compact.

2. Cut-off facts, for all w (as in the parent's step 5):
 - 0 ≤ φ^± ≤ 1;
 - φ⁺(w) = 1 if ‖w‖ ≤ 1, since then max(0, ‖w‖ − 1) = 0;
 - φ⁺(w) = 0 if ‖w‖ > 2, since then a(‖w‖ − 1) > 1;
 - φ⁻(w) = 0 if ‖w‖ > 1, since then max(0, 1 − ‖w‖) = 0;
 - φ^± are continuous.

3. Geometry of Φ. Since r > 0, ‖Φ(y,S).1‖ = ‖r⁻¹(y − x)‖ = ‖y − x‖/r. Hence:
 - (y,S) ∈ B ⟺ ‖y − x‖ ≤ r ⟺ ‖Φ(y,S).1‖ ≤ 1;
 - if (y,S) ∉ K, then ‖y − x‖ > 2r, so ‖Φ(y,S).1‖ > 2.

4. Change of variables. For every continuous g : ℝ^N × G → ℝ,
  ∫ g d(rescaledMeasure V x r) = r⁻¹^n · ∫ g∘Φ dV.measure.
 - integral_smul_measure gives ∫ g d(c•ν) = c.toReal · ∫ g dν for every g. Since r⁻¹^n ≥ 0, c.toReal = r⁻¹^n.
 - Φ is continuous, hence measurable, and g is continuous, hence a.e.-strongly measurable for V.measure.map Φ. So integral_map gives ∫ g d(V.measure.map Φ) = ∫ g∘Φ dV.measure.
 Neither identity needs integrability.

5. The middle term. B is measurable (closed ball × univ), so integral_indicator gives ∫_B β(S) dV = ∫ 1_B(y,S)β(S) dV(y,S). Also (r^n)⁻¹ = r⁻¹^n. Hence
  (∫_B β(S) dV)/r^n = r⁻¹^n · ∫ h_B dV, where h_B(y,S) := 1_B(y,S)·β(S).

6. Integrability. Let h be a.e.-strongly measurable with |h| ≤ ‖β‖ everywhere and h = 0 outside K. Then h is integrable on K (bounded on a set of finite measure: Measure.integrableOn_of_bounded with step 1), and it vanishes off K, so h is V.measure-integrable (IntegrableOn.integrable_of_forall_notMem_eq_zero). This applies to three functions:
 - h⁻(y,S) := φ⁻(Φ(y,S).1)·β(S) and h⁺(y,S) := φ⁺(Φ(y,S).1)·β(S). Both are continuous, and |h^±| ≤ 1·‖β‖ by step 2. Off K we have ‖Φ.1‖ > 2 > 1, so φ^±(Φ.1) = 0 by step 2.
 - h_B. It is the indicator of a measurable set times a continuous function, and |h_B| ≤ ‖β‖. Off K the point is not in B, since ‖Φ.1‖ > 2 > 1 (step 3), so h_B = 0.

7. Pointwise sandwich: h⁻ ≤ h_B ≤ h⁺ everywhere.
 - If (y,S) ∈ B: h_B = β(S). Since ‖Φ.1‖ ≤ 1, φ⁺(Φ.1) = 1, so h⁺ = β(S). Also h⁻ = φ⁻(Φ.1)·β(S) ≤ 1·β(S), because φ⁻ ≤ 1 and β(S) ≥ 0.
 - If (y,S) ∉ B: h_B = 0. Since ‖Φ.1‖ > 1, φ⁻(Φ.1) = 0, so h⁻ = 0. And h⁺ = φ⁺(Φ.1)·β(S) ≥ 0, as both factors are ≥ 0.

8. Conclusion.
 - By step 6 and integral_mono, ∫ h⁻ dV ≤ ∫ h_B dV ≤ ∫ h⁺ dV. Multiplying by r⁻¹^n ≥ 0 preserves both inequalities.
 - Apply step 4 to the continuous functions g^±(y,S) := φ^±(y)·β(S). Φ does not change the second coordinate, so g^±∘Φ = h^±. Hence r⁻¹^n · ∫ h^± dV = ∫ φ^±(y)β(S) d(rescaledMeasure V x r)(y,S).
 - By step 5, the middle term is (∫_{B_r(x)×G} β(S) dV)/r^n.
 Together these give both inequalities. ∎

## Key steps

1. V(B_{2r}(x)×G) < ∞, since B_{2r}(x) is compact and contained in U (finite_on_compact).
2. Change of variables: ∫ g dV_{x,r} = r⁻¹^n ∫ g∘Φ dV for continuous g (integral_smul_measure, integral_map).
3. Middle term: (∫_{B_r(x)×G} β dV)/r^n = r⁻¹^n ∫ 1_{B_r(x)×G}·β dV (integral_indicator).
4. All three integrands are bounded by ‖β‖ and vanish off B_{2r}(x)×G, hence are integrable.
5. Pointwise φ⁻(Φ.1)β ≤ 1_Bβ ≤ φ⁺(Φ.1)β, because β ≥ 0 and ‖Φ.1‖ ≤ 1 ⟺ (y,S) ∈ B; integrate and multiply by r⁻¹^n ≥ 0.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum <snapshot>/project/GMT/Ch08/Contract.lean GMT/Ch08/Contract.lean GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n "theorem (Isometry\.euclideanHausdorffMeasure_image|EuclideanSpace\.euclideanHausdorffMeasure_eq_volume)" <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem (addHaar_ball_of_pos|addHaar_ball|addHaar_closedBall) " <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n "theorem tendsto_integral_of_dominated_convergence" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `rg -n "lemma Measure\.integrableOn_of_bounded|theorem IntegrableOn\.integrable_of_forall_notMem_eq_zero" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `rg -n "^theorem (integral_smul_measure|integral_map) " <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean; rg -n "^theorem (integral_indicator|setIntegral_const) " <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `rg -n "theorem intro \[R1Space" Topology/Algebra/Support.lean; rg -n "theorem measure_ball_lt_top" Measure/Typeclasses/Finite.lean; rg -n "theorem finrank_euclideanSpace_fin" InnerProductSpace/PiL2.lean; rg -n "theorem norm_coe_le_norm" Topology/ContinuousMap/Compact.lean (all under <snapshot>/mathlib/Mathlib)`
- `rg -n "^theorem [A-Za-z_.]*(le_measure_isOpen|measure_isClosed_le|tendsto_measure_of_null_frontier)[A-Za-z_]* " <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `rg -n "^theorem tendsto_of_tendsto_of_tendsto_of_le_of_le'? " <snapshot>/mathlib/Mathlib/Topology/Order/Basic.lean`
- `rg -n "plane_ball|allard_tc" <snapshot>/project/GMT (no match)`
- `grep -n '^structure|^theorem|^def|^noncomputable def|^instance' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean (Varifold, finite_on_compact, weight_apply, finrank_plane, instCompactSpace)`
- `grep -rn closedBall Poincare/SimonGMT | grep -i 'plane|μHE|euclideanHausdorff|submodule' (finds Chapter04/TangentDensity.lean planeMeasure_unit_closedBall, locallyFinite_planeMeasure)`
- `lake env lean /tmp/fbl-decomp/ImpCheck.lean (#check Poincare.SimonGMT.Chapter04.planeMeasure_unit_closedBall after import GMT.Ch08.Submission: unknown identifier)`
- `python3 dag.json lean_name scan (77 nodes; no allard_tc_fbl_*); grep -rl allard_tc_fbl GMT .humanize (no match); git log --all --oneline -S allard_tc_fbl (no commit)`
- `verifier gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch08.main_theorem') replay and lean_contract.validate_lean_statement on all 6 statements`
- `lake env lean /tmp/fbl-decomp/{Stmts,Glue,Leaves,Sandwich,Full,FullCheck}.lean (statement elaboration, glue, sorry-free leaf proofs, comparator-form exact Submission.X checks, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Portmanteau.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-flat-blowup-ball-limits-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-flat-blowup-ball-limits-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/fbl-decomp/Stmts.lean`
- `/tmp/fbl-decomp/Glue.lean`
- `/tmp/fbl-decomp/Leaves.lean`
- `/tmp/fbl-decomp/Sandwich.lean`
- `/tmp/fbl-decomp/Full.lean`
- `/tmp/fbl-decomp/FullCheck.lean`
- `/tmp/fbl-decomp/ImpCheck.lean`

Snapshot provenance:
- The snapshot is project 63436ae6 with Mathlib 25730c7c.
- Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (2e5cd5b3…).

Mathlib in the snapshot provides every lemma the five child proofs need:
- Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume;
- Measure.addHaar_ball_of_pos (no Nontrivial needed for r > 0), addHaar_ball and addHaar_closedBall;
- tendsto_integral_of_dominated_convergence;
- Measure.integrableOn_of_bounded and IntegrableOn.integrable_of_forall_notMem_eq_zero;
- integral_smul_measure and integral_map;
- integral_indicator and setIntegral_const;
- HasCompactSupport.intro, measure_ball_lt_top, finrank_euclideanSpace_fin and ContinuousMap.norm_coe_le_norm.

No existing result covers these children:
- Mathlib's Portmanteau.lean treats only finite or probability measures (tendsto_measure_of_null_frontier).
- Its squeeze lemma tendsto_of_tendsto_of_tendsto_of_le_of_le' needs fixed bounds. So neither the C_c ball limit nor the k-indexed squeeze exists.
- The snapshot project has no plane_ball or allard_tc names.
- SimonGMT Chapter04.planeMeasure_unit_closedBall (n > 0, realUnitBallVolume) is not in scope after import GMT.Ch08.Submission. The children therefore use Mathlib directly.

From SimonGMT Varifold.lean the proofs use Varifold.isOpen_domain, finite_on_compact, weight_apply, Grassmannian.finrank_plane and instCompactSpace.

Lean checks in /tmp/fbl-decomp, all after import GMT.Ch08.Submission in the comparator's replayed scope:
- All 5 child statements elaborate (autoImplicit false) and pass validate_lean_statement.
- Each child and the parent have sorry-free scratch proofs. The parent's type matches the frozen type exactly and follows from nonneg_limit, which follows from its three siblings.
- The comparator form `exact Submission.X` succeeds for all six declarations.
- #print axioms shows only propext, Classical.choice and Quot.sound.

The names allard_tc_fbl_* are globally unique: no DAG node, file or git commit uses them.
