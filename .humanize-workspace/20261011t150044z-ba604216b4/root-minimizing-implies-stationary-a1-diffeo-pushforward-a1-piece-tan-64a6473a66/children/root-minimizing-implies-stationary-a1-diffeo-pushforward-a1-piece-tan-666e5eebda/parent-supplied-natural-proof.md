# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_image_tangent-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_image_tangent-a1.rescaled_integral_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3, 5 and 6 of the parent proof (setup, localisation, three-term convergence), with the Jacobian kept abstract. In the parent, J = areaJacobianAt F, K = L^n, and (iii) is the conclusion of step 2.
Notation:
- λ := volume on ℝ^n; Φ_r(c) := r^{-1}(F(b + rc) − F(b));
- X_r(c) := 1_B(b + rc)·J(b + rc)·f(Φ_r(c)), which is B.indicator J (b + r • c) · f(Φ_r(c));
- Y(c) := J(b)·f(Lc) and I(r) := ∫ X_r dλ.
1. Setup.
- f has compact support, so there is R > 0 with f(w) = 0 whenever |w| ≥ R (HasCompactSupport.exists_pos_le_norm).
- f is continuous with compact support, so |f| ≤ M for some M ≥ 0.
- K ≥ J(b) ≥ 0.
- Let D := B̄_{R/m}(0) ⊆ ℝ^n; then λ(D) < ∞.
2. Localisation. Let r > 0 and c ∉ D, i.e. |c| > R/m.
- If X_r(c) ≠ 0, then b + rc ∈ B and f(Φ_r(c)) ≠ 0. So |Φ_r(c)| < R, i.e. |F(b + rc) − F(b)| < rR. By (i) with a := b + rc, m·r|c| = m|(b + rc) − b| ≤ |F(b + rc) − F(b)| < rR, so |c| < R/m, a contradiction.
- If Y(c) ≠ 0, then f(Lc) ≠ 0, so |Lc| < R, and by (iii) m|c| ≤ |Lc| < R, again a contradiction.
- Hence X_r and Y vanish outside D. So I(r) = ∫_D X_r and ∫Y = ∫_D Y (setIntegral_eq_integral_of_forall_compl_eq_zero). Also ∫Y = J(b)·∫ f(Lc) dλ(c) (integral_const_mul).
3. Integrability. Fix r.
- X_r is Borel: c ↦ b + rc is continuous, 1_B·J is Borel because B and J are, and c ↦ f(Φ_r(c)) is continuous because F and f are. Also |X_r| ≤ KM.
- Y is continuous with |Y| ≤ KM.
- The functions c ↦ 1_{ℝ^n∖B}(b + rc) (≤ 1), c ↦ |J(b + rc) − J(b)| (≤ K) and c ↦ |f(Φ_r(c)) − f(Lc)| (≤ 2M) are Borel and bounded.
- Bounded Borel functions are integrable on D because λ(D) < ∞ (Measure.integrableOn_of_bounded).
4. Pointwise estimate. Fix r and c, and write u := f(Φ_r(c)) and v := f(Lc).
- If b + rc ∈ B: X_r(c) − Y(c) = (J(b + rc) − J(b))·u + J(b)·(u − v).
- If b + rc ∉ B: X_r(c) − Y(c) = −J(b)·v = −J(b)·u + J(b)·(u − v), and J(b)|u| ≤ KM.
- In both cases |X_r(c) − Y(c)| ≤ KM·1_{ℝ^n∖B}(b + rc) + M·|J(b + rc) − J(b)| + J(b)·|f(Φ_r(c)) − f(Lc)|.
5. Integrated estimate. Define
- T₁(r) := ∫_D 1_{ℝ^n∖B}(b + rc) dλ(c);
- T₂(r) := ∫_D |J(b + rc) − J(b)| dλ(c);
- T₃(r) := ∫_D |f(Φ_r(c)) − f(Lc)| dλ(c).
For r > 0, steps 2–4 give |I(r) − J(b)∫ f(Lc) dλ(c)| = |∫_D (X_r − Y)| ≤ ∫_D |X_r − Y| ≤ KM·T₁(r) + M·T₂(r) + J(b)·T₃(r) (norm_integral_le_of_norm_le, integral_add, integral_const_mul).
6. T₁ → 0. Apply the sibling pit_integral_closedBall_rescale_tendsto with h := 1_{ℝ^n∖B} and radius R/m > 0. Its hypothesis holds:
- For s > 0, B is Borel and 0 < λ(B̄_s(b)) < ∞. So ⨍_{B̄_s(b)} 1_{ℝ^n∖B} = λ(B̄_s(b) ∖ B)/λ(B̄_s(b)) = 1 − λ(B ∩ B̄_s(b))/λ(B̄_s(b)) (setAverage_eq, integral_indicator_one, measureReal_inter_add_sdiff).
- This real ratio is the toReal of the [0,∞]-valued ratio in (iv), which tends to toReal(1) = 1 (ENNReal.tendsto_toReal). So the averages tend to 0.
7. T₂ → 0. Apply the same sibling with h := |J(·) − J(b)| (= ‖J(·) − J(b)‖) and radius R/m. Its hypothesis is exactly (v).
8. T₃ → 0. Let ε > 0.
- f is uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous), so there is η > 0 with |f(w) − f(w')| < ε whenever |w − w'| < η.
- Put θ := ηm/(2R) > 0. By (ii) there is ρ_θ > 0 with |F(b + k) − F(b) − Lk| ≤ θ|k| whenever |k| < ρ_θ.
- For 0 < r < ρ_θ m/R and c ∈ D, |rc| ≤ rR/m < ρ_θ. Hence |Φ_r(c) − Lc| = r^{-1}|F(b + rc) − F(b) − L(rc)| ≤ θ|c| ≤ θR/m = η/2 < η, and so |f(Φ_r(c)) − f(Lc)| < ε.
- Thus T₃(r) ≤ ε·λ(D) for all such r (norm_setIntegral_le_of_norm_le_const). As ε is arbitrary, T₃(r) → 0.
- Alternatively, use dominated convergence on D. For each fixed c, Φ_r(c) → Lc as r → 0⁺ (HasLineDerivAt.tendsto_slope_zero_right), so the integrand tends to 0 pointwise, and it is bounded by 2M.
9. Conclusion. By steps 5–8, |I(r) − J(b)∫ f(Lc) dλ(c)| ≤ KM·T₁(r) + M·T₂(r) + J(b)·T₃(r) for r > 0, and the right side tends to 0. Hence I(r) → J(b)∫ f(Lc) dλ(c) as r → 0⁺ (tendsto_iff_norm_sub_tendsto_zero, squeeze_zero').
For n = 0 everything holds as written, with ℝ^0 = {0} = D.

## Key steps

1. Choose R with f = 0 off B_R(0) and M ≥ sup|f|, and set D := B̄_{R/m}(0).
2. Localisation: by (i) and (iii) both integrands vanish off D, and both are bounded Borel, hence integrable on D.
3. Pointwise three-term bound: |X_r − Y| ≤ KM·1_{B^c}(b+rc) + M|J(b+rc) − J(b)| + J(b)|f(Φ_r c) − f(Lc)|.
4. T₁ and T₂ tend to 0 by the rescaled-average sibling, using density (iv) and the Lebesgue point (v).
5. T₃ tends to 0 by uniform convergence Φ_r → L on D and uniform continuity of f.
6. Squeeze.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'HasApproximateTangentSpaceAt|blowUpMap|areaJacobianAt|normDet' project --glob '*.lean'`
- `rg -n 'pit_' project --glob '*.lean' (no match)`
- `rg -n 'theorem integral_comp_smul \(|theorem setAverage_eq \(|theorem addHaar_real_closedBall. |theorem addHaar_ball_of_pos|theorem addHaar_closedBall. |theorem integral_withDensity_eq_integral_smul |theorem ae_tendsto_measure_inter_div \(|theorem ae_tendsto_average_norm_sub|theorem integral_smul_nnreal_measure|theorem image_preimage_eq_inter_range|uniformContinuous_of_continuous|theorem measure_sdiff|integral_add_left_eq_self' mathlib/Mathlib --glob '*.lean'`
- `rg -n 'euclideanHausdorffMeasure_smul₀|euclideanHausdorffMeasure_image_eq_normDet_mul_volume|norm_fderiv_le_of_lipschitz|finrank_range_of_inj|tendsto_slope_zero_right|euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib --glob '*.lean'`
- `rg -n 'theorem weighted_area_formula_lipschitz_injOn|theorem measurable_areaJacobianAt|theorem areaJacobianAt_eq_normDet|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `grep -n 'def HasApproximateTangentSpaceAt|def blowUpMap' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 -I dag.json scans: lean_statements containing blowUpMap/withDensity; sibling statements under piece_tangent_density-a1; depth-1 depends_on; 'pit_' prefix and the six proposed names over all eight chapter DAGs (2,620 nodes) and stored node JSON proposals (no match)`
- `git grep -l -E 'pit_(setIntegral_blowUpMap_image|blowUp_image_setIntegral_eq_rescaled|fderiv_lower_bound_of_density|integral_closedBall_rescale_tendsto|rescaled_integral_tendsto|setIntegral_range_linear)|Submission\.pit_' <2,909 refs> -- 'GMT/*.lean' (no match; control query setIntegral_blowUpMap_image_eq_inv_pow_mul matched 14 refs)`
- `git show 713eebc5c1a6b6da58d0d5ede7e1174c7c83e7cc:GMT/Ch07/Submission.lean (accepted setIntegral_blowUpMap_image_eq_inv_pow_mul proof)`
- `gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem'); lean_contract.validate_lean_statement on the six child types and the parent type`
- `lake env lean /tmp/pit-decomp-k7/Scope.lean (LinearMap.normDet, areaJacobianAt unknown after import GMT.Ch07.Submission)`
- `lake env lean /tmp/pit-decomp-k7/Types.lean (six child types + parent type in the exact challenge scope)`
- `lake env lean /tmp/pit-decomp-k7/Assembly.lean (#print axioms pit_assembly_conditional)`
- `lake env lean /tmp/pit-decomp-k7/C12.lean, C4.lean, C6.lean, agent3/C3.lean, agent5/C5.lean (#print axioms of each child)`
- `lake env lean /tmp/pit-decomp-k7/EndToEnd.lean (#print axioms Submission.ptd_piece_image_approxTangent_ae)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-64a6473a66/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-64a6473a66/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/pit-decomp-k7/Scope.lean`
- `/tmp/pit-decomp-k7/Types.lean`
- `/tmp/pit-decomp-k7/Assembly.lean`
- `/tmp/pit-decomp-k7/C12.lean`
- `/tmp/pit-decomp-k7/C4.lean`
- `/tmp/pit-decomp-k7/C6.lean`
- `/tmp/pit-decomp-k7/agent3/C3.lean`
- `/tmp/pit-decomp-k7/agent5/C5.lean`
- `/tmp/pit-decomp-k7/EndToEnd.lean`

The snapshot has no proof of the selected statement or of any proposed child. The project supplies only the frozen contract, the definitions HasApproximateTangentSpaceAt and blowUpMap (via SimonGMT Chapter03) and Euclid.

Every lemma cited in the child proofs exists in the pinned Mathlib 25730c7c with compatible hypotheses:
- Measure.integral_comp_smul (valid for every f) and integral_add_left_eq_self;
- setAverage_eq, Measure.addHaar_real_closedBall', addHaar_ball_of_pos and addHaar_closedBall;
- integral_withDensity_eq_integral_smul, integral_map, integral_smul_measure and integral_smul_nnreal_measure;
- Measure.euclideanHausdorffMeasure_smul₀, image_preimage_eq_inter_range and measure_sdiff;
- HasCompactSupport.uniformContinuous_of_continuous and HasLineDerivAt.tendsto_slope_zero_right;
- for the parent assembly: Besicovitch.ae_tendsto_measure_inter_div, IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, norm_fderiv_le_of_lipschitz, LinearMap.finrank_range_of_inj and EuclideanSpace.euclideanHausdorffMeasure_eq_volume.
SimonGMT 2b36630 supplies weighted_area_formula_lipschitz_injOn, measurable_areaJacobianAt, areaJacobianAt_eq_normDet and euclideanHausdorffMeasure_image_le_of_lipschitzOn. Only the parent assembly uses them, after adding imports.

LinearMap.normDet and areaJacobianAt are unknown after import GMT.Ch07.Submission, so every child type keeps the Jacobian abstract.

The only DAG overlap is that blowup_scaling's type equals the accepted setIntegral_blowUpMap_image_eq_inv_pow_mul (proof at 713eebc5). That declaration sits under a depth-1 branch that depends on this node's ancestor, so this split uses a fresh name. No proposed name collides anywhere.

Lean checks: all six types and the parent type elaborate in the comparator's replayed scope. The conditional assembly and all six child proofs use only propext, Classical.choice and Quot.sound, and the end-to-end file proves Submission.ptd_piece_image_approxTangent_ae with those axioms.
