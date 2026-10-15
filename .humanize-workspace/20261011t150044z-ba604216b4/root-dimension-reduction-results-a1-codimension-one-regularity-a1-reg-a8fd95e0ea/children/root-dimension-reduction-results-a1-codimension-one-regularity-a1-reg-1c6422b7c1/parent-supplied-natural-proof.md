# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.piece_tangent-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.piece_tangent-a1.area_jacobian-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 0(b) and 0(c) of the parent proof, together with the linear area formula H^n(Λ(S)) = normDet Λ·λ(S) used in its step 6. The Jacobian J = areaJacobianAt F = normDet DF is quantified existentially because LinearMap.normDet and areaJacobianAt are not in scope after `import GMT.Ch07.Submission`. Departure (library form only): property (2) is SimonGMT's lintegral area formula for injective Lipschitz maps, weighted_area_formula_lipschitz_injOn, instead of the Bochner form integral_area_formula_of_injective_derivative cited in 0(c). It needs only the Lipschitz bound and InjOn F B, and the sibling rescaled_formula consumes exactly this lintegral form. Lean note: the proof needs `import Poincare.SimonGMT.Chapter02.AreaLipschitz` in Submission.lean; accepted candidates in this run already add that import.

Notation. H^n := μHE[n]; λ := volume on ℝ^n. finrank ℝ ℝ^n = n (finrank_euclideanSpace_fin), so μHE[finrank ℝ ℝ^n] = μHE[n]. On ℝ^n itself μHE[n] = λ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n). For a linear T : ℝ^n → ℝ^P, normDet T := (det(T*T))^{1/2} ≥ 0 (Mathlib LinearMap.normDet).

1. (Choice of J.) Put J(a) := areaJacobianAt F a (SimonGMT Chapter02/Area.lean). Then J(a) = normDet DF(a) (areaJacobianAt_eq_normDet, which holds by rfl). J is Borel (measurable_areaJacobianAt F), and J(a) ≥ 0 for every a (areaJacobianAt_nonneg).
2. (Property (3).) Let a ∈ ℝ^n and S ⊆ ℝ^n. Apply Mathlib's LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume to the linear map DF(a) : ℝ^n → ℝ^P (both spaces carry their Borel σ-algebras). It gives μHE[finrank ℝ ℝ^n](DF(a)(S)) = ofReal(normDet DF(a))·λ(S). Rewriting finrank ℝ ℝ^n = n and normDet DF(a) = J(a) gives H^n(DF(a)(S)) = ofReal(J(a))·λ(S). S need not be measurable.
3. (Upper bound J ≤ L^n.) Fix a and let D₁ := closedBall(0, 1) ⊆ ℝ^n.
(a) Since F is L-Lipschitz, norm_fderiv_le_of_lipschitz gives ‖fderiv ℝ F a‖ ≤ L. This also holds where F is not differentiable, since fderiv = 0 there. Hence ‖DF(a)‖₊ ≤ L.
(b) A continuous linear map is Lipschitz with constant its operator norm, so DF(a) is ‖DF(a)‖₊-Lipschitz on D₁. SimonGMT's euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean) gives H^n(DF(a)(D₁)) ≤ ‖DF(a)‖₊^n·H^n(D₁). By (a) and monotonicity of t ↦ t^n on [0, ∞], this is ≤ L^n·H^n(D₁).
(c) By step 2 and H^n = λ on ℝ^n: ofReal(J(a))·λ(D₁) = H^n(DF(a)(D₁)) ≤ L^n·λ(D₁) in [0, ∞].
(d) 0 < λ(D₁) < ∞ (measure_closedBall_pos with radius 1 > 0; measure_closedBall_lt_top). Cancelling λ(D₁) (ENNReal.mul_le_mul_iff_left) gives ofReal(J(a)) ≤ (L : [0, ∞])^n = ofReal(L^n) (ENNReal.ofReal_pow with L ≥ 0, ENNReal.ofReal_coe_nnreal). As L^n ≥ 0, ENNReal.ofReal_le_ofReal_iff yields J(a) ≤ L^n. With step 1 this is property (1).
4. (Property (2).) Apply SimonGMT's weighted_area_formula_lipschitz_injOn (Chapter02/AreaLipschitz.lean) to the L-Lipschitz map F, the Borel set B, the hypothesis InjOn F B and g. It gives ∫⁻_{F(B)} g dμHE[finrank ℝ ℝ^n] = ∫⁻_B ofReal(areaJacobianAt F x)·g(F(x)) dλ(x). That theorem already accounts for critical points and the Rademacher exceptional set, so no differentiability hypothesis is needed. Rewriting finrank ℝ ℝ^n = n gives (2) for this J.
5. (Conclusion.) J is Borel and satisfies (1), (2) and (3). ∎

## Key steps

1. J := areaJacobianAt F = normDet DF is Borel and nonnegative (SimonGMT measurable_areaJacobianAt, areaJacobianAt_nonneg).
2. Mathlib's linear area formula gives H^n(DF(a)(S)) = ofReal(J(a))·λ(S) for every a and S.
3. ‖DF(a)‖ ≤ L and the Lipschitz image bound on closedBall(0,1) give ofReal(J(a))·λ(D₁) ≤ L^n·λ(D₁), hence J(a) ≤ L^n.
4. SimonGMT weighted_area_formula_lipschitz_injOn gives ∫⁻_{F(B)} g dH^n = ∫⁻_B ofReal(J)·g∘F dλ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; python3 read of <snapshot>/project/lake-manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem LinearMap.exists_antilipschitzWith|theorem bound_of_antilipschitz|theorem HasCompactMulSupport.uniformContinuous_of_continuous|theorem UniformContinuous.comp_tendstoUniformlyOn |theorem tendstoUniformlyOn_iff \{F : ι → β → α\}|theorem setIntegral_eq_integral_of_forall_compl_eq_zero \(h|theorem norm_setIntegral_le_of_norm_le_const \{C|theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume|theorem norm_fderiv_le_of_lipschitz \{|theorem ae_tendsto_average_norm_sub' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'finrank_range_of_inj|bounded_above_of_compact_support|integrableOn_of_bounded|euclideanHausdorffMeasure_eq_volume|exists_antilipschitzWith' <snapshot>/mathlib/Mathlib --glob '*.lean'; rg -n 'theorem coe_range|theorem range_coe' <snapshot>/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `rg -n 'codim1_lurpt|Submission\.' <snapshot>/project --glob '*.lean' (no match); rg -n 'def HasApproximateTangentSpaceAt|def blowUpMap' <snapshot>/project <snapshot>/mathlib (no match)`
- `grep -rn 'theorem weighted_area_formula_lipschitz_injOn|theorem measurable_areaJacobianAt|theorem areaJacobianAt_nonneg|theorem areaJacobianAt_eq_normDet|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' .lake/packages/simongmt/Poincare/SimonGMT; rg -n 'def HasApproximateTangentSpaceAt|def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `python3 scans of dag.json (902 to 976 nodes): accepted lean_statements containing ⨍, TendstoUniformly, 'r • c', fderiv+Tendsto, closedBall+Tendsto, '∃ J', '∫⁻ y in F'; children and statuses of piece_image_tangent-a1 and weighted_blowup_limit-a1; lean_name/statement scan for codim1_lurpt_* (no hit); depth-1 depends_on (no cycle)`
- `git grep -l -E 'codim1_lurpt_' <1663 unique ref tips> -- 'GMT/*.lean' (no match)`
- `git show {c70c9020,3e383ca4,ed6259bb,af5e0757,6858d683}:GMT/Ch07/Submission.lean and git diff -U0 against their audit base commits; appended '#print axioms' and ran lean -DautoImplicit=false with LEAN_PATH = .lake/build/lib/lean plus .lake/packages/*/.lake/build/lib/lean; git show 990fac9a (ptd speculative assembly draft)`
- `python3 scan of the imports in the Submission.lean of all 584 accepted candidate commits (15 add imports, 7 of them Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `lean -DautoImplicit=false /tmp/cpt-split/final/{Types,Assembly,ChildA,ChildB,EndToEnd}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a8fd95e0ea/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-96e209f8f6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-96e209f8f6/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-791b230798/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-3b627dcae9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-3b627dcae9/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-57d04995e6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-57d04995e6/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db8cbeb1bd/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db8cbeb1bd/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cpt-split/final/Types.lean`
- `/tmp/cpt-split/final/Assembly.lean`
- `/tmp/cpt-split/final/ChildA.lean`
- `/tmp/cpt-split/final/ChildB.lean`
- `/tmp/cpt-split/final/EndToEnd.lean`
- `/tmp/cpt-split/reuse/Check_pit_blowUp_image_setIntegral_eq_rescaled.lean`
- `/tmp/cpt-split/reuse/Check_pit_setIntegral_range_linear.lean`
- `/tmp/cpt-split/reuse/Check_doraggt_ae_rescaled_lebesgue_point.lean`
- `/tmp/cpt-split/reuse/Check_dorwbl_diff_quotient_tendstoUniformlyOn.lean`

Pins match. The snapshot manifest gives project b4d606db and Mathlib 25730c7c, which equal the workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest gives simongmt 2b366308, which equals .lake/packages/simongmt. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

The snapshot project contains no proof of the selected statement or of either new child. rg finds no match for codim1_lurpt or Submission.; HasApproximateTangentSpaceAt and blowUpMap are defined in simongmt Chapter03/Rectifiable.lean:102 and :96.

Every cited lemma exists in the snapshot Mathlib:
- LinearMap.exists_antilipschitzWith (Analysis/Normed/Module/FiniteDimension.lean:231) and ContinuousLinearMap.bound_of_antilipschitz (Normed/Operator/ContinuousLinearMap.lean:106);
- HasCompactSupport.uniformContinuous_of_continuous (HeineCantor.lean:91, to_additive), UniformContinuous.comp_tendstoUniformlyOn (UniformConvergence.lean:252) and Metric.tendstoUniformlyOn_iff (Pseudo/Basic.lean:142);
- setIntegral_eq_integral_of_forall_compl_eq_zero and norm_setIntegral_le_of_norm_le_const (Integral/Bochner/Set.lean:486, 613), and Measure.integrableOn_of_bounded (IntegrableOn.lean:716);
- Continuous.bounded_above_of_compact_support (Normed/Group/Bounded.lean:153) and LinearMap.finrank_range_of_inj (Dimension/Finrank.lean:127);
- LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (NormDet.lean:433), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:187) and norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
- ae_tendsto_average_norm_sub (DensityTheorem.lean:150) and LinearMap.coe_range (Submodule/Range.lean:60; there is no range_coe).

SimonGMT 2b366308 supplies weighted_area_formula_lipschitz_injOn (AreaLipschitz.lean:101), measurable_areaJacobianAt, areaJacobianAt_eq_normDet, areaJacobianAt_nonneg and euclideanHausdorffMeasure_image_le_of_lipschitzOn. These are in scope only after adding import Poincare.SimonGMT.Chapter02.AreaLipschitz; 7 accepted candidates in this run already add that import.

DAG: four accepted declarations are reused with byte-identical frozen types:
- pit_blowUp_image_setIntegral_eq_rescaled (3e383ca4);
- pit_setIntegral_range_linear (ed6259bb);
- doraggt_ae_rescaled_lebesgue_point (af5e0757);
- dorwbl_diff_quotient_tendstoUniformlyOn (6858d683).
Recompiling each candidate with #print axioms gives only propext, Classical.choice and Quot.sound. The new names codim1_lurpt_piece_area_jacobian and codim1_lurpt_rescaled_integral_tendsto occur in no DAG node (976 nodes), in no node JSON, and in no GMT/*.lean at any of 1663 ref tips. ptd_piece_image_approxTangent_ae has the same type as the selected node but is only speculative-ready, so it is not reused.

Lean: Types.lean elaborates all 6 child types and the parent type. Assembly.lean proves the frozen parent from the five directly used children; #print axioms lists only those five plus the standard axioms. ChildA.lean proves area_jacobian with standard axioms only. ChildB.lean proves rescaled_limit from diff_quotient_uniform alone. EndToEnd.lean uses the real accepted proofs plus both new proofs and proves Submission.codim1_lur_piece_image_approxTangent_ae with only propext, Classical.choice and Quot.sound. An independent reviewer re-ran these files and accepted the split.
