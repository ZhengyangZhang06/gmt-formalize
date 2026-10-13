# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`
- Child DAG node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.plane_cutoff_limits-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 (the cut-offs, items (5a)–(5b)) and step 6 (dominated convergence) of the parent-supplied proof. The index k is replaced by k + 1, so every k ∈ ℕ is allowed.

Notation.
- P := T.plane and H := μHE[n] on ℝ^N.
- μ := H restricted to P, a measure on ℝ^N. By definition of the set integral, ∫_P f dH = ∫ f dμ.
- For k ∈ ℕ put a_k := k + 1 ≥ 1. For y ∈ ℝ^N with s := ‖y‖, put φ_k⁺(y) := max(0, 1 − a_k·max(0, s − 1)) and φ_k⁻(y) := min(1, a_k·max(0, 1 − s)).
- ω := (unitBallVolume n).toReal.

1. Masses of balls under μ.
 - unitBallVolume n = vol_n(B°_1(0)) < ∞, because Lebesgue measure on the proper space ℝ^n is locally finite and gives balls finite mass (measure_ball_lt_top).
 - Let ρ > 0. Closed and open balls are measurable, so μ(B_ρ(0)) = H(B_ρ(0) ∩ P) = H(P ∩ B_ρ(0)), and likewise μ(B°_ρ(0)) = H(P ∩ B°_ρ(0)).
 - By the sibling plane_ball_measure, both equal unitBallVolume n · ofReal(ρ)^n.
 - Hence μ(B_2(0)) = unitBallVolume n · ofReal(2)^n < ∞. Since ofReal(1)^n = 1, also μ(B_1(0)) = μ(B°_1(0)) = unitBallVolume n.

2. Dominating function. Let g := 1_{B_2(0)}, the indicator of the closed ball of radius 2 with value 1. The constant 1 is integrable on B_2(0) because μ(B_2(0)) < ∞ (step 1). Since B_2(0) is measurable, g is μ-integrable (integrable_indicator_iff).

3. Elementary properties, for every k and y (with s = ‖y‖):
 (a) 0 ≤ φ_k⁺(y) ≤ 1. It is a max with 0, and 1 − a_k·max(0, s − 1) ≤ 1 because a_k ≥ 0 and max(0, s − 1) ≥ 0.
 (b) 0 ≤ φ_k⁻(y) ≤ 1. It is a min with 1, and a_k·max(0, 1 − s) ≥ 0.
 (c) If s > 2, then φ_k⁺(y) = 0. Indeed max(0, s − 1) = s − 1 > 1 and a_k ≥ 1, so a_k(s − 1) > 1 and 1 − a_k(s − 1) < 0.
 (d) If s ≥ 1, then φ_k⁻(y) = 0, because max(0, 1 − s) = 0.
 (e) φ_k^± are continuous, being built from the norm, constants, products, max and min. Hence they are a.e.-strongly measurable.
 From (a)–(d), |φ_k^±(y)| ≤ g(y) for all y: if s ≤ 2 then g(y) = 1, and if s > 2 then φ_k^±(y) = 0.

4. Pointwise limits as k → ∞, for every y (with s = ‖y‖).
 (a) φ_k⁺(y) → 1_{B_1(0)}(y).
  - If s ≤ 1, then max(0, s − 1) = 0, so φ_k⁺(y) = max(0, 1) = 1 = 1_{B_1(0)}(y) for every k.
  - If s > 1, choose k₀ ∈ ℕ with k₀ > 1/(s − 1). For k ≥ k₀, a_k(s − 1) ≥ (k₀ + 1)(s − 1) > 1, so φ_k⁺(y) = 0 = 1_{B_1(0)}(y).
  In both cases the sequence is eventually equal to its limit.
 (b) φ_k⁻(y) → 1_{B°_1(0)}(y).
  - If s < 1, choose k₀ ∈ ℕ with k₀ > 1/(1 − s). For k ≥ k₀, a_k(1 − s) ≥ 1, so φ_k⁻(y) = min(1, a_k(1 − s)) = 1 = 1_{B°_1(0)}(y).
  - If s ≥ 1, then φ_k⁻(y) = 0 = 1_{B°_1(0)}(y) for every k.

5. Dominated convergence. Apply tendsto_integral_of_dominated_convergence with the bound g from step 2, measurability from 3(e), domination from step 3 and the limits from step 4. As k → ∞:
  ∫ φ_k⁺ dμ → ∫ 1_{B_1(0)} dμ and ∫ φ_k⁻ dμ → ∫ 1_{B°_1(0)} dμ.

6. Value of the limits. For a measurable set A, ∫ 1_A dμ = ∫_A 1 dμ = μ.real(A) = (μ(A)).toReal (integral_indicator and setIntegral_const). By step 1, (μ(B_1(0))).toReal = (μ(B°_1(0))).toReal = (unitBallVolume n).toReal = ω. Since ∫ φ dμ is ∫_{T.plane} φ dμHE[n], both limits in the statement hold. ∎

## Key steps

1. Under μ = μHE[n]⌞T.plane, μ(B_2(0)) < ∞ and μ(B_1(0)) = μ(B°_1(0)) = unitBallVolume n, by sibling plane_ball_measure and unitBallVolume n < ∞ (measure_ball_lt_top).
2. The cut-offs are continuous with |φ_k^±| ≤ 1_{B_2(0)}, and this indicator is μ-integrable.
3. Pointwise, φ_k⁺ → 1_{B_1(0)} and φ_k⁻ → 1_{B°_1(0)}; each sequence is eventually constant in k.
4. Dominated convergence: the limits are ∫1_{B_1(0)} dμ = ∫1_{B°_1(0)} dμ = (unitBallVolume n).toReal.

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
