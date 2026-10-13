# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1.cone_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied proof (the test function f = φχ with properties (a) and (b)), with the supplied parameter s chosen as s := δ/4, so that the supplied radius 4s equals δ. Notation: p_Q := Q.starProjection (the orthogonal projection of ℝ^P onto Q, a continuous linear map), |·| the Euclidean norm.

1. Definition. Put s := δ/4 > 0. For y ∈ ℝ^P let h(y) := (3/4)|y| − |p_Q y|, φ(y) := max(0, min(1, 1 + h(y)/s)), χ(y) := max(0, min(1, 2 − |y|)) and f(y) := φ(y)·χ(y).
2. Continuity. y ↦ |y| is continuous, and y ↦ |p_Q y| is continuous because p_Q is a continuous linear map. Constants, sums, differences, constant multiples, division by the nonzero constant s, min, max and products of continuous real-valued functions are continuous. Hence f is continuous.
3. Compact support. If |y| > 2, then 2 − |y| < 0 < 1, so min(1, 2 − |y|) = 2 − |y| and χ(y) = max(0, 2 − |y|) = 0, whence f(y) = φ(y)·0 = 0. Thus f vanishes outside the closed ball B̄₂(0), which is compact because ℝ^P is finite-dimensional (proper). Therefore f has compact support (HasCompactSupport.intro with K = closedBall 0 2), and f together with the proofs of steps 2–3 is an element of CompactlySupportedContinuousMap (Euclid P) ℝ.
4. Bounds 0 ≤ f ≤ 1. For every real a, max(0, min(1, a)) lies in [0, 1]: it is ≥ 0 by max, and ≤ 1 since 0 ≤ 1 and min(1, a) ≤ 1. Hence 0 ≤ φ(y) ≤ 1 and 0 ≤ χ(y) ≤ 1. Therefore f(y) = φ(y)χ(y) ≥ 0 as a product of nonnegative numbers, and f(y) = φ(y)χ(y) ≤ φ(y)·1 = φ(y) ≤ 1, using χ(y) ≤ 1 and φ(y) ≥ 0.
5. Property (a): f = 1 on X ∩ B₁(0). Let 2|p_Q y| < |y| and |y| < 1. Then |p_Q y| < |y|/2, so h(y) = (3/4)|y| − |p_Q y| > (3/4)|y| − |y|/2 = |y|/4 ≥ 0. Hence h(y)/s ≥ 0 (as s > 0), so 1 + h(y)/s ≥ 1, min(1, 1 + h(y)/s) = 1 and φ(y) = max(0, 1) = 1. Moreover 2 − |y| > 1, so min(1, 2 − |y|) = 1 and χ(y) = 1. Therefore f(y) = 1·1 = 1.
6. Property (b): f = 0 on Q outside B̄_δ(0). Let y ∈ Q with |y| > δ. Since y ∈ Q, p_Q y = y (Mathlib Submodule.starProjection_eq_self_iff), so h(y) = (3/4)|y| − |y| = −|y|/4 and h(y)/s = −|y|/(4s) = −|y|/δ. Because |y| > δ > 0 we have |y|/δ > 1, so 1 + h(y)/s = 1 − |y|/δ < 0. Then min(1, 1 + h(y)/s) = 1 + h(y)/s < 0 and φ(y) = max(0, 1 + h(y)/s) = 0, hence f(y) = 0·χ(y) = 0.
7. Steps 3–6 show that f satisfies all four required properties: 0 ≤ f, f ≤ 1, f(y) = 1 whenever 2‖p_Q y‖ < ‖y‖ and ‖y‖ < 1, and f(y) = 0 whenever y ∈ Q and δ < ‖y‖. ∎

## Key steps

1. Set s = δ/4, h(y) = (3/4)|y| − |p_Q y|, φ = max(0, min(1, 1 + h/s)), χ = max(0, min(1, 2 − |y|)), f = φχ.
2. f is continuous, vanishes outside B̄₂(0), and takes values in [0, 1], so f ∈ C_c(ℝ^P, ℝ).
3. If 2|p_Q y| < |y| < 1 then h(y) > |y|/4 ≥ 0 gives φ(y) = 1, and χ(y) = 1, so f(y) = 1.
4. If y ∈ Q and |y| > δ then p_Q y = y, so 1 + h(y)/s = 1 − |y|/δ < 0, φ(y) = 0 and f(y) = 0.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); grep -n 'def unitBallVolume|abbrev Euclid' GMT/Ch07/Contract.lean (lines 143, 40)`
- `rg -n 'theorem addHaar_closedBall|theorem addHaar_ball' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean (addHaar_closedBall :500 needs no Nontrivial; addHaar_ball :456 does)`
- `sed -n 60,200p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.euclideanHausdorffMeasure_image :131, euclideanHausdorffMeasure_smul₀ :152, euclideanHausdorffMeasure_homothety_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume :187)`
- `rg -n 'starProjection_eq_self_iff' Analysis/InnerProductSpace/Projection/Basic.lean (:290); rg -n 'lemma integrable' MeasureTheory/Integral/CompactlySupported.lean (:30, needs IsFiniteMeasureOnCompacts); rg -n 'IsFiniteMeasureOnCompacts|isFiniteMeasure_restrict' MeasureTheory/Measure/Typeclasses/Finite.lean (:40, :562); rg -n 'ofReal_integral_eq_lintegral_ofReal|integral_eq_lintegral_of_nonneg_ae' MeasureTheory/Integral/Bochner/Basic.lean (:739, :515); rg -n 'image_inter_preimage' Data/Set/Image.lean (:454); rg -n 'restrict_apply|le_restrict_apply' MeasureTheory/Measure/Restrict.lean (:75, :171); rg -n 'lintegral_indicator_one' MeasureTheory/Integral/Lebesgue/Basic.lean (:572); rg -n 'ofReal_lt_iff_lt_toReal' Basic/ENNReal/Real.lean (:267); rg -n 'image_smul' Algebra/Group/Pointwise/Set/Scalar.lean (:155); rg -n 'smul_def|ofReal_coe_nnreal|top_mul' Basic/ENNReal/{Action,Basic,Operations}.lean`
- `rg -n 'starProjection|unitBallVolume|realUnitBallVolume' <snapshot>/project -g '*.lean'; rg -n -i 'cone|cutoff' <snapshot>/project/GMT/Ch03/Contract.lean (no match)`
- `sed -n 1,400p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt, regular_euclideanHausdorffMeasure_restrict_submodule)`
- `python3 -I scan of dag.json lean_name/lean_statement/status (rsd_cmr_ir_blowUp_image_measure accepted at 6d5fb477 with byte-identical type; open-ball plane-measure nodes codim1_subspace_ball_euclideanHausdorff [rlcr-lean] and idtp_tdc_subspace_ball_measure [decomposing] are unaccepted with different types; no lean_name cbrr_tcd_*); git show 6d5fb477cd67 and git show a0c1e365af06 (accepted scaling proof and accepted analogous lower-density proof); grep -n '_existing_lean_name_problem' -A 40 and the accepted-reuse branch near line 4404 in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `sed -n 77,110p and 175,190p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the four child types; contract_scope replay (verifier/gmt-compare.py); lake env lean /tmp/cbrr-cd-decomp-k7q/lean/{Types,Children,Assembly,All,Exact,WithScale}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Action.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Scalar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d692d7eef5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d692d7eef5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/cbrr-cd-decomp-k7q/lean/Types.lean`
- `/tmp/cbrr-cd-decomp-k7q/lean/Children.lean`
- `/tmp/cbrr-cd-decomp-k7q/lean/Assembly.lean`
- `/tmp/cbrr-cd-decomp-k7q/lean/Exact.lean`
- `/tmp/cbrr-cd-decomp-k7q/lean/WithScale.lean`

The snapshot Contract.lean is identical to the workspace Contract.lean and Submission.lean. It provides Euclid (line 40) and unitBallVolume = volume(ball (0 : Euclid n) 1) (line 143). The pinned Mathlib has every lemma the child proofs cite: Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall (valid for r ≥ 0 with no Nontrivial hypothesis), euclideanHausdorffMeasure_smul₀, Submodule.starProjection_eq_self_iff, CompactlySupportedContinuousMap.integrable, isFiniteMeasure_restrict, ofReal_integral_eq_lintegral_ofReal, integral_eq_lintegral_of_nonneg_ae, lintegral_indicator_one, Set.image_inter_preimage and ENNReal.ofReal_lt_iff_lt_toReal. Neither the snapshot project nor SimonGMT Chapter03 contains a plane-ball measure lemma, a cone cutoff, or a blow-up upper-bound lemma; Chapter03 supplies only blowUpMap, HasApproximateTangentSpaceAt and the regularity of Hⁿ⌞Q. The open-ball plane-measure nodes elsewhere in the DAG are unaccepted, so they cannot be shared. The scaling theorem rsd_cmr_ir_blowUp_image_measure is accepted with a byte-identical type and is reused as child blowup_scaling. All child types elaborate in the replayed contract scope and pass the lexical validator. The scratch proofs of the three new children and the hypothesis-only assembly compile. The chain built on the real accepted scaling theorem proves the exact frozen parent type with axioms propext, Classical.choice and Quot.sound only.
