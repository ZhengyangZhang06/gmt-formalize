# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1.blowup_upper-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 3 (second half), 4, 5 and 6 of the supplied proof, carried out for an arbitrary measurable set U and an arbitrary nonnegative test function f ∈ C_c with f ≥ 1 on U (the supplied proof uses U = X ∩ B₁(0) and its explicit f). Notation: η_r := Poincare.SimonGMT.Chapter03.blowUpMap x r, so η_r(z) = r⁻¹(z − x); Hⁿ := μHE[n]; L := ∫ y in Q, f y ∂Hⁿ (Bochner integral for Hⁿ⌞Q); I(r) := ∫ y in η_r '' M, f y ∂Hⁿ. The sibling blowup_scaling states: for r > 0 and every S ⊆ ℝ^P, Hⁿ(η_r '' S) = ENNReal.ofReal (r⁻¹ ^ n) * Hⁿ(S).

1. Case t = ∞. For r > 0 we have rⁿ > 0, so ENNReal.ofReal (rⁿ) ≠ 0 and t * ENNReal.ofReal (rⁿ) = ∞ (ENNReal.top_mul); the inequality then holds trivially. Since Ioi 0 ∈ 𝓝[>] 0 (self_mem_nhdsWithin), the claim holds. From now on t ≠ ∞.
2. The limit is below t. Since f ≥ 0 everywhere, L ≥ 0 (integral_nonneg). As L ≥ 0 and t ≠ ∞, the hypothesis ENNReal.ofReal L < t is equivalent to L < t.toReal (ENNReal.ofReal_lt_iff_lt_toReal). So L < t.toReal.
3. Eventually I(r) < t.toReal. The second component of HasApproximateTangentSpaceAt n M x Q, applied to f, says I(r) → L as r → 0 in 𝓝[>] 0. Since (−∞, t.toReal) is a neighbourhood of L, the set {r : I(r) < t.toReal} belongs to 𝓝[>] 0 (Tendsto.eventually with gt_mem_nhds). Intersecting with Ioi 0 ∈ 𝓝[>] 0, it suffices to fix r with r > 0 and I(r) < t.toReal and to prove Hⁿ(M ∩ η_r⁻¹(U)) ≤ t * ENNReal.ofReal (rⁿ).
4. Finiteness and integrability. Put S := η_r '' M. By blowup_scaling, Hⁿ(S) = ENNReal.ofReal (r⁻¹ ^ n) * Hⁿ(M), a product of two finite factors (ENNReal.ofReal is never ∞ and Hⁿ(M) ≠ ∞ by hypothesis), so Hⁿ(S) ≠ ∞. Hence ν := Hⁿ.restrict S is a finite measure (isFiniteMeasure_restrict), hence locally finite and finite on compact sets, and the continuous compactly supported f is ν-integrable (CompactlySupportedContinuousMap.integrable). Since f ≥ 0 as well, ENNReal.ofReal (I(r)) = ∫⁻ y, ENNReal.ofReal (f y) ∂ν (ofReal_integral_eq_lintegral_ofReal).
5. Comparison. For every y, U.indicator 1 y ≤ ENNReal.ofReal (f y): if y ∈ U then f y ≥ 1, so ENNReal.ofReal (f y) ≥ 1 (ENNReal.one_le_ofReal); if y ∉ U the left side is 0. Since U is measurable, Hⁿ(S ∩ U) = ν(U) (Measure.restrict_apply gives ν(U) = Hⁿ(U ∩ S)) = ∫⁻ U.indicator 1 dν (lintegral_indicator_one) ≤ ∫⁻ ENNReal.ofReal ∘ f dν (lintegral_mono) = ENNReal.ofReal (I(r)) ≤ ENNReal.ofReal (t.toReal) (I(r) < t.toReal and monotonicity of ofReal) = t (ENNReal.ofReal_toReal, t ≠ ∞). So Hⁿ(S ∩ U) ≤ t.
6. Rescaling the set. (η_r '' M) ∩ U = η_r '' (M ∩ η_r⁻¹(U)) (Set.image_inter_preimage). By blowup_scaling applied to the set M ∩ η_r⁻¹(U), Hⁿ(S ∩ U) = ENNReal.ofReal (r⁻¹ ^ n) * Hⁿ(M ∩ η_r⁻¹(U)). With step 5: ENNReal.ofReal (r⁻¹ ^ n) * Hⁿ(M ∩ η_r⁻¹(U)) ≤ t.
7. Conclusion. Since rⁿ ≥ 0, ENNReal.ofReal (rⁿ) * ENNReal.ofReal (r⁻¹ ^ n) = ENNReal.ofReal (rⁿ · r⁻¹ ^ n) = ENNReal.ofReal ((r · r⁻¹)ⁿ) = ENNReal.ofReal 1 = 1 (ENNReal.ofReal_mul, mul_pow, r ≠ 0). Hence Hⁿ(M ∩ η_r⁻¹(U)) = ENNReal.ofReal (rⁿ) * (ENNReal.ofReal (r⁻¹ ^ n) * Hⁿ(M ∩ η_r⁻¹(U))) ≤ ENNReal.ofReal (rⁿ) * t = t * ENNReal.ofReal (rⁿ), using step 6 and monotonicity of multiplication in ℝ≥0∞. This holds for every r in the set chosen in step 3, which belongs to 𝓝[>] 0. ∎

## Key steps

1. If t = ∞ the bound is trivial for r > 0; otherwise ofReal(L) < t with L = ∫_Q f ≥ 0 gives L < t.toReal.
2. HasApproximateTangentSpaceAt gives ∫_{η_r(M)} f → L, so ∫_{η_r(M)} f < t.toReal for all small r > 0.
3. blowup_scaling gives Hⁿ(η_r(M)) < ∞, so f is integrable for Hⁿ⌞η_r(M) and Hⁿ(η_r(M) ∩ U) ≤ ofReal(∫_{η_r(M)} f) ≤ t because 1_U ≤ ofReal ∘ f.
4. η_r(M) ∩ U = η_r(M ∩ η_r⁻¹U) and blowup_scaling give ofReal(r⁻ⁿ)·Hⁿ(M ∩ η_r⁻¹U) ≤ t; multiplying by ofReal(rⁿ) yields Hⁿ(M ∩ η_r⁻¹U) ≤ t·ofReal(rⁿ).

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
