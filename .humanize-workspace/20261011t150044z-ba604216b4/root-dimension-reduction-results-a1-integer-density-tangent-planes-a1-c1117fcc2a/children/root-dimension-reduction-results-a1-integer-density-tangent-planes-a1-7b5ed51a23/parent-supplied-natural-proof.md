# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1.imrep_formulas-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 4 (“R represents X”) and 5 (“Mass measure”), stated for any IMRep with the explicit carrier, multiplicity and θ·ξ identity. Uses the ancestor dependency idtp_fons_odc_line_hausdorff (the parent's dependency line_param).
Notation: γ_k(t) := p_k + t·v_k, S_k := γ_k(I_k), C := R.carrier, θ := R.mult, ξ := R.orient, H¹ := μHE[1], ℒ¹ := volume on ℝ, and ev_v(α) := α(fun _ => v).
0. (Tools.) By idtp_fons_odc_line_hausdorff (second conjunct, for p_k, v_k with ‖v_k‖ = 1), γ_k is a measurable embedding, and for every J ⊆ ℝ, H¹⌞γ_k(J) = (γ_k)_#(ℒ¹⌞J) and H¹(γ_k(J)) = ℒ¹(J). Also γ_k is an isometry, since dist(γ_k s, γ_k t) = |s − t|·‖v_k‖ = |s − t|; hence it is continuous and a closed embedding.
1. S_k is measurable, as the image of the measurable set I_k under the measurable embedding γ_k. By the hypothesis C = ⋃_k ⋃_{c_k≠0} S_k, we have S_k ⊆ C whenever c_k ≠ 0.
2. (Integrability.) Fix ω ∈ 𝒟¹(ℝ^P) and set g_k(x) := ω(x)(fun _ => v_k) = ev_{v_k}(ω(x)). Since ω is smooth with compact support and ev_{v_k} is continuous linear with ev_{v_k}(0) = 0, g_k is continuous with compact support. g_k is H¹-integrable on S_k: by the Tool, H¹⌞S_k = (γ_k)_#(ℒ¹⌞I_k). Since γ_k is a measurable embedding, integrability for this push-forward is equivalent to integrability of g_k∘γ_k for ℒ¹⌞I_k (MeasurableEmbedding.integrable_map_iff). And g_k∘γ_k is continuous with compact support because γ_k is a closed embedding, hence integrable on ℝ and on I_k.
3. (Action.) By definition, R.action(ω) = ∫_C θ(x)·ξ(x)(ω(x)) dH¹(x). By the θ·ξ hypothesis with α = ω(x), the integrand equals Σ_k 1_{S_k}(x)·c_k·g_k(x). Each summand can be written 1_{S_k}(x)·(c_k·g_k(x)), the indicator of the function c_k g_k. Each summand is integrable for H¹⌞C: by integrable_indicator_iff and Measure.restrict_restrict this reduces to integrability of c_k g_k on S_k ∩ C ⊆ S_k, which follows from step 2. Interchanging the finite sum with the integral (integral_finsetSum) gives R.action(ω) = Σ_k ∫_C 1_{S_k}(c_k g_k) dH¹ = Σ_k c_k·∫_{S_k ∩ C} g_k dH¹ (integral_indicator, Measure.restrict_restrict, integral_const_mul).
 - If c_k = 0, the k-th term is 0 = c_k·∫_{I_k} g_k(γ_k t) dt.
 - If c_k ≠ 0, then S_k ∩ C = S_k by step 1, and ∫_{S_k} g_k dH¹ = ∫ g_k d((γ_k)_#(ℒ¹⌞I_k)) = ∫_{I_k} g_k(γ_k t) dt (Tool and MeasurableEmbedding.integral_map).
 Hence R.action(ω) = Σ_k c_k ∫_{I_k} ω(p_k + t·v_k)(fun _ => v_k) dt, which is (i).
4. (Mass measure.) Let A be measurable. By definition R.measure = (H¹⌞C).withDensity θ, so R.measure(A) = ∫⁻_A θ d(H¹⌞C) = ∫⁻_{A ∩ C} θ dH¹ (withDensity_apply, Measure.restrict_restrict). By the multiplicity hypothesis, as ℝ≥0∞-valued functions θ(x) = Σ_k 1_{S_k}(x)·|c_k|: cast the natural-number sum termwise (Nat.cast_sum), and the indicator commutes with the cast by a case split on x ∈ S_k. Then ∫⁻_{A∩C} θ dH¹ = Σ_k |c_k|·H¹(S_k ∩ (A ∩ C)) (lintegral_finsetSum, lintegral_indicator_const, Measure.restrict_apply). For each k, (|c_k| : ℝ≥0∞) = ENNReal.ofReal |(c_k : ℝ)| (Int.cast_abs, Nat.cast_natAbs, ENNReal.ofReal_natCast).
 - If c_k = 0, both k-th terms are 0.
 - If c_k ≠ 0, then S_k ⊆ C gives S_k ∩ (A ∩ C) = S_k ∩ A = γ_k(I_k ∩ γ_k⁻¹A) (image_inter_preimage). Its H¹-measure is ℒ¹(I_k ∩ γ_k⁻¹A) by the Tool with J = I_k ∩ γ_k⁻¹A.
 Summing, R.measure(A) = Σ_k ENNReal.ofReal |(c_k : ℝ)|·ℒ¹(I_k ∩ γ_k⁻¹(A)), which is (ii). ∎

## Key steps

1. Each S_k is measurable and S_k ⊆ carrier when c_k ≠ 0; x ↦ ω(x)(v_k) is H¹-integrable on S_k by line_param transport.
2. R.action ω = ∫_C Σ 1_{S_k} c_k ω(x)(v_k) dH¹ = Σ c_k ∫_{S_k} ω(x)(v_k) dH¹ = Σ c_k ∫_{I_k} ω(γ_k t)(v_k) dt.
3. R.measure A = ∫⁻_{A∩C} θ dH¹ = Σ |c_k| H¹(S_k ∩ A ∩ C) = Σ |c_k| ℒ¹(I_k ∩ γ_k⁻¹A), where the c_k = 0 terms vanish on both sides.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `rg -n "theorem tendsto_integral_filter_of_dominated_convergence|theorem Isometry.euclideanHausdorffMeasure_image|theorem Isometry.map_euclideanHausdorffMeasure|theorem lintegral_indicator_const|theorem integral_finsetSum|theorem lintegral_finsetSum|theorem finrank_span_singleton|theorem eventually_all |theorem integral_indicator |theorem image_inter_preimage|theorem withDensity_apply " <snapshot>/mathlib/Mathlib`
- `rg -n "theorem _root_.MeasurableEmbedding.integral_map|_root_.MeasurableEmbedding.integrable_map_iff|theorem eventually_nhds_iff |theorem le_opNorm" <snapshot>/mathlib/Mathlib`
- `rg -n "HasApproximateTangentSpaceAt|blowUpMap" <snapshot>/mathlib/Mathlib (no match)`
- `rg -n "HasApproximateTangentSpaceAt|idtp_fons_odc|polygonal" <snapshot>/project/GMT`
- `grep -rn HasApproximateTangentSpaceAt (theorem|lemma) .lake/packages/simongmt/Poincare/SimonGMT; sed -n 50,260p Chapter03/Rectifiable.lean; sed -n 1,200p Chapter06/Currents.lean; grep Covector|DifferentialForm|IsTestForm Chapter06/Forms.lean`
- `git show 75f499358:GMT/Ch07/Submission.lean > /tmp/pc_split/draft.lean (speculative draft of the grandparent): odc_line_*, odc_polycurrent_*, odc_tangent_*, odc_approxTangent_of_locally_line, odc_polyimrep_*, odc_polygonal_imrep`
- `python3 -I scans of dag.json: nodes under the selected parent, sibling line_param-a1 frozen type, all idtp_fons_odc* lean_names, occurrences of the five proposed names, accepted statements with HasApproximateTangentSpaceAt and ball, accepted line-integral currents`
- `grep -n max_depth runtime.py (_decompose line 1393); sed -n 60,200p leaf_verification.py (check_source_delta forbidden regex); sed -n 1,140p inherited.py (cited_inherited)`
- `grep -n "1.4 Definition|3.1 Definition|1-dimensional minimizing" book/chapter-03.txt book/chapter-06.txt book/chapter-07.txt`
- `lake env lean /tmp/pc_split/{Types,Alpha,Beta,Eps,Gamma,Delta,All,AllClean}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c1117fcc2a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/pc_split/draft.lean`
- `/tmp/pc_split/Types.lean`
- `/tmp/pc_split/Alpha.lean`
- `/tmp/pc_split/Beta.lean`
- `/tmp/pc_split/Eps.lean`
- `/tmp/pc_split/Gamma.lean`
- `/tmp/pc_split/Delta.lean`
- `/tmp/pc_split/All.lean`
- `/tmp/pc_split/AllClean.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, which equal the workspace HEAD and .lake/packages/mathlib; SimonGMT is 2b366308. The snapshot Contract.lean is byte-identical to the workspace Submission.lean. Every Mathlib lemma used by the child proofs exists in the snapshot: tendsto_integral_filter_of_dominated_convergence (MeasureTheory/Integral/DominatedConvergence.lean:67), Isometry.euclideanHausdorffMeasure_image and map_euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:131 and :141), MeasurableEmbedding.integral_map (Integral/Bochner/Basic.lean:1093), MeasurableEmbedding.integrable_map_iff (Function/L1Space/Integrable.lean:374), integral_finsetSum (Bochner/Basic.lean:248), integral_indicator (Bochner/Set.lean:185), lintegral_finsetSum (Lebesgue/Add.lean:356), lintegral_indicator_const (Lebesgue/Basic.lean:541), withDensity_apply (Measure/WithDensity.lean:44), finrank_span_singleton (LinearAlgebra/FiniteDimensional/Basic.lean:535), Filter.eventually_all (Order/Filter/Finite.lean:247), Metric.eventually_nhds_iff (Topology/MetricSpace/Pseudo/Defs.lean:779), ContinuousAlternatingMap.le_opNorm (Analysis/Normed/Module/Alternating/Basic.lean:212) and image_inter_preimage (Data/Set/Image.lean:454). The snapshot Mathlib has no HasApproximateTangentSpaceAt or blowUpMap (no match). SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap (:96), HasApproximateTangentSpaceAt (:102), countablyRectifiable_range (:64), countablyRectifiable_sUnion (:416), and only the flat-model lemma hasApproximateTangentSpaceAt_submodule (:125), which covers points of a linear subspace with no locality; Chapter06/Currents.lean defines TestFormOnConverges and GeometricCurrentOn. The snapshot project GMT has no idtp_fons_odc or polygonal declaration. The DAG has no node with any of the five proposed lean_names, and no accepted statement equals any child type. The accepted codim1_ac_sat_approxTangent_of_local_eq proves locality but not the affine model, so it is not reused. The sibling line_param (idtp_fons_odc_line_hausdorff, frozen type read from dag.json) is the only external prerequisite and is cited by name in two children. Lean: all child types elaborate and the frozen parent type follows from three of them. Each child has a verified one-theorem proof that respects the leaf delta regex; the proofs are adapted from draft 75f499358. With a one-theorem proof of the line_param type, the whole chain uses only propext, Classical.choice and Quot.sound.
