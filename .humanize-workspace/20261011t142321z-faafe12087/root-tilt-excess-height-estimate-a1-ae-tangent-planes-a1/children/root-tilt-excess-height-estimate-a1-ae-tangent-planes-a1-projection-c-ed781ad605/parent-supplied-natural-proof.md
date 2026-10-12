# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1`
- Child DAG node: `root.tilt_excess_height_estimate-a1.ae_tangent_planes-a1.projection_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof's step 8a (for injective L, the orthogonal projection onto L(ℝⁿ) is L(LᵀL)^(−1)Lᵀ, which depends continuously on L), with details filled in.

Notation. ℝⁿ = Rn n and ℝ^{n+ℓ} = Amb n ℓ are finite-dimensional real inner product spaces; L† := ContinuousLinearMap.adjoint L; p_S := S.starProjection is the orthogonal projection onto a subspace S; End(ℝⁿ) := ℝⁿ →L[ℝ] ℝⁿ is a complete normed ring; Ring.inverse is the inverse on units and 0 elsewhere.

Proof.
1. The set 𝓘 := {L : ℝⁿ →L[ℝ] ℝ^{n+ℓ} | L injective} is open (ContinuousLinearMap.isOpen_injective; ℝⁿ is finite-dimensional).
2. For L ∈ 𝓘 let A_L := L† ∘ L ∈ End(ℝⁿ). For v ≠ 0, ⟨A_L v, v⟩ = ⟨Lv, Lv⟩ = |Lv|² > 0, so A_L is injective, hence bijective (finite dimension), hence a unit of End(ℝⁿ).
3. Define Q_L := L ∘ Ring.inverse(A_L) ∘ L† : ℝ^{n+ℓ} →L[ℝ] ℝ^{n+ℓ}. For L ∈ 𝓘 and w ∈ ℝ^{n+ℓ}: Q_L w = L(A_L^(−1) L† w) ∈ L(ℝⁿ), and for every v ∈ ℝⁿ, ⟨w − Q_L w, Lv⟩ = ⟨L†w − L†L A_L^(−1) L†w, v⟩ = ⟨L†w − L†w, v⟩ = 0. So w − Q_L w is orthogonal to L(ℝⁿ), and Q_L w = p_{L(ℝⁿ)} w (Submodule.eq_starProjection_of_mem_of_inner_eq_zero). Thus Q_L = p_{L(ℝⁿ)} for all L ∈ 𝓘.
4. Continuity of Q at L₀ ∈ 𝓘. L ↦ L† is continuous (the adjoint is a linear isometric equivalence), and composition of continuous linear maps is jointly continuous, so L ↦ A_L is continuous. Ring.inverse is continuous at the unit A_{L₀} (NormedRing.inverse_continuousAt). Hence L ↦ Q_L = L ∘ Ring.inverse(A_L) ∘ L† is continuous at L₀.
5. For L₀ ∈ 𝓘, the map L ↦ p_{L(ℝⁿ)} agrees with Q on 𝓘 and Q is continuous at L₀, so L ↦ p_{L(ℝⁿ)} is continuous within 𝓘 at L₀ (ContinuousAt.continuousWithinAt and ContinuousWithinAt.congr, using p_{L₀(ℝⁿ)} = Q_{L₀}). Hence the map is ContinuousOn 𝓘. ∎

## Key steps

1. Injective maps form an open set
2. A_L = L†L is a unit of End(ℝⁿ) for injective L
3. Q_L = L ∘ A_L^(−1) ∘ L† equals the orthogonal projection onto L(ℝⁿ)
4. L ↦ Q_L is continuous at injective L (adjoint, composition, NormedRing.inverse_continuousAt)
5. ContinuousOn by congruence on the set of injective maps

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; diff -q GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; diff -q GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `python3 -I scan of .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json nodes[*].lean_name and nodes/*/decomposition-v*.json subproblems[*].lean_name (reserved names); grep -rn 'aetp_' .lake/packages/simongmt/Poincare GMT dag.json nodes`
- `python3 -I print of dag.json lean_statement for rsod_rectifiable_subset_c1_cover, rsod_ae_exists_approxTangent, ae_weightedApproximateTangent_density_eq_mult and the *_tangent_* proposals of other branches`
- `grep -n '^theorem\|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/{Rectifiable,SubmanifoldCover,Differential,DisjointCover,CoordinateProjection}.lean`
- `grep -n 'theorem simon_theorem_3_6\|ae_dimensionalUpperDensity_eq_zero_outside' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean; grep -n '^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `grep -rn 'theorem measure_toOuterMeasure_isBorelRegular\|theorem simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n '^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{AreaLipschitz,AreaCritical,WeightedArea,AreaLinearWeighted,AreaApproximation,AreaNormalization,Area,Lipschitz,WhitneyExtension}.lean; grep -n 'structure HasWhitneyC1Compatibility' -A 8 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `grep -n '^theorem\|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{TangentDensity,WeightedBlowUp,ClassicalTangent}.lean`
- `rg -n -i lusin -g '*.lean' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (eq_starProjection_of|starProjection_eq_self_iff|isStarProjection_iff)|theorem tendstoUniformlyOn_of_ae_tendsto\b|theorem measurable_fderiv\b|theorem finrank_range_of_inj\b|theorem tendsto_integral_filter_of_dominated_convergence\b|exists_isClosed_diff_lt' -g '*.lean' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem addHaar_sphere\|norm_image_sub_le_of_norm_fderiv_le\|isOpen_iUnion_countable\|continuousOn_clm_apply\|isClosed_iUnion\|injective_iff_antilipschitz\|isOpen_injective\|inverse_continuousAt\|of_pseudoMetrizableSpace_of_isFiniteMeasure\|withDensity_apply_le\|exists_measurable_subset_ae_eq\|image_of_continuousOn_injOn\|infEDist_pos_iff_notMem_closure\|norm_fderiv_le_of_lipschitz\|ofReal_rpow_of_pos\|mul_div_mul_left' .lake/packages/mathlib/Mathlib`
- `sed -n 150,330p book/chapter-02.txt (Thm 1.5, Whitney 1.6); sed -n 1,400p book/chapter-03.txt (1.1-1.9)`
- `sed -n 430,600p verifier/gmt-compare.py; validate_lean_statement from verifier/lean_contract.py run on all 8 child types`
- `lake env lean GMT/Ch05/Submission.lean -o /tmp/aetp-decomp/mybuild/GMT/Ch05/Submission.olean; lean /tmp/aetp-decomp/check/NodeCheck.lean (import GMT.Ch05.Submission + replayed contract scope + the 8 frozen child types)`
- `lean /tmp/aetp-decomp/check/Skel.lean (parent frozen type from children 2-8 as hypotheses; #print axioms GMT.Ch05.skeleton)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1-ae-tangent-planes-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/CoordinateProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/aetp-decomp/check/NodeCheck.lean`
- `/tmp/aetp-decomp/check/Skel.lean`
- `/tmp/aetp-decomp/draft.md`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; the workspace .lake/packages/mathlib is at the same commit and simongmt at 2b3663083f3fe399b6296fb8eaee52169170e197 (lake-manifest). Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical. No proposed aetp_* name occurs in SimonGMT, the project, dag.json (51 reserved names) or any decomposition proposal; other branches' tangent nodes (aal_tangent_structure, any_radius_tangent_ae, allard52_tangent_ae, lip_approx_tangent_structure, lgc_tangent_plane_ae, ae_weightedApproximateTangent_density_eq_mult, rsod_ae_exists_approxTangent, rsod_rectifiable_subset_c1_cover) have different statements, so no child duplicates a DAG node. Library facts: SimonGMT Chapter03 defines the tangent predicates and proves HasWeightedApproximateTangentSpaceAt.unique but not existence (Rectifiable.lean says 1.6/1.9 are not asserted; SubmanifoldCover.lean has only the easy direction of Lemma 1.2). Available and used by the children: Lusin (Chapter01.exists_isClosed_continuousOn_of_measurable, finite measure with closed inner regularity), Upper Density 3.6 (Chapter01.ae_dimensionalUpperDensity_eq_zero_outside, Simon normalization, bridged by Chapter02.simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure and Chapter01.measure_toOuterMeasure_isBorelRegular), Whitney C¹ extension (Chapter02.exists_contDiff_one_extension_of_whitney with HasWhitneyC1Compatibility), the critical-image theorem (Chapter02.area_image_criticalSet_eq_zero, no hypotheses), the injective-derivative area formula in Bochner form (Chapter02.integral_area_formula_of_injective_derivative), the linear area formula (Chapter02.measurePreserving_linearMap_normDet_smul), continuous_normDet, the Lipschitz image bound, and the blow-up scaling lemmas (Chapter04.hausdorff_blowUp_image, hausdorff_blowUp_ball, map_inverse_blowUp_carrier). Missing: the C¹ approximation theorem (Simon Ch. 2, 1.5) — Mathlib has no continuity-Lusin and SimonGMT has only Whitney; it becomes child c1_approximation with the printed proof (an audit in this run rejected a proof that merely cited it). Mathlib supplies Rademacher, measurable_fderiv, Egorov, dominated convergence, WeaklyRegular for finite measures, isOpen_injective, injective_iff_antilipschitz, mean value inequality, Lindelöf, NormedRing.inverse_continuousAt, eq_starProjection_of_mem_of_inner_eq_zero, Metric.infEDist API. Lean checks: all 8 child types elaborate after import GMT.Ch05.Submission in the replayed contract scope (only sorry warnings) and pass verifier/lean_contract.py unchanged; Skel.lean proves the parent's exact frozen type sorry-free from children 2-8 as hypotheses, axioms propext, Classical.choice, Quot.sound. An independent review agent re-compiled the skeleton, spot-checked every cited lemma and found no defects.
