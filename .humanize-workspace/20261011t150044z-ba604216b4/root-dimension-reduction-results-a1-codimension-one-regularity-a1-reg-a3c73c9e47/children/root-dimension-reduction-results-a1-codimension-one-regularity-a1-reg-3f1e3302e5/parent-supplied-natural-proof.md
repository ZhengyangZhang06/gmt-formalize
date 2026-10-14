# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1.field_regularity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 6 of the parent's supplied proof of codim1_lur_chart_divergence_formula, stated for an arbitrary open set D and a map G that is C² on D. The parent proves in its step 5 that C = D ∩ G^{-1}(tsupport ω) is compact; here that is a hypothesis.

Notation. K := tsupport ω (a closed set); C := D ∩ G^{-1}(K); e_i := EuclideanSpace.single i 1. For y ∈ ℝ^{n+1} put c_j(y) := (−1)^j ω(G(y))(DG(y)e_{j.succAbove 0}, …, DG(y)e_{j.succAbove(n−1)}) and Ψ(y) := Σ_j c_j(y)e_j, so that Φ = 1_D·Ψ.

1. (Ψ is C¹ on D.)
(a) ω is C^∞, in particular C², and G is C² on D, so y ↦ ω(G(y)) is C² on D (ContDiff.comp_contDiffOn). Composing with the continuous linear map ContinuousAlternatingMap.toContinuousMultilinearMapCLM, the map y ↦ ω(G(y)), viewed as a continuous multilinear map, is C² on D, hence C¹ on D.
(b) G is C² on the open set D, so y ↦ DG(y) is C¹ on D (ContDiffOn.fderiv_of_isOpen, since 1 + 1 ≤ 2). Hence for every fixed vector a, y ↦ DG(y)a is C¹ on D (ContDiffOn.clm_apply with a constant), and so is y ↦ (DG(y)e_{j.succAbove k})_{k<n} ∈ (ℝ^P)^n (contDiffOn_pi).
(c) The evaluation map ev(α, b) := α(b_0, …, b_{n−1}), from (continuous n-linear forms on ℝ^P) × (ℝ^P)^n to ℝ, is C^∞, because it is the restriction of a continuous multilinear map to the diagonal. Concretely, in Mathlib:
- for B := ContinuousLinearMap.id on continuous multilinear forms, B.continuousMultilinearMapOption is a continuous multilinear map on the constant family indexed by Option (Fin n);
- it satisfies B.continuousMultilinearMapOption (fun _ ↦ (α, b)) = α b (continuousMultilinearMapOption_apply_eq_self, true by rfl);
- continuous multilinear maps are C^∞ (ContinuousMultilinearMap.contDiff);
- the diagonal p ↦ (fun _ ↦ p) is continuous linear, hence C^∞ (contDiff_pi of contDiff_id).
Composing the last two gives that ev is C^∞.
(d) Hence c_j(y) = (−1)^j ev(ω(G(y)), (DG(y)e_{j.succAbove k})_{k<n}) is C¹ on D: a C^∞ map composed with a map that is C¹ on D (ContDiff.comp_contDiffOn, ContDiffOn.prodMk), times a constant. Then Ψ = Σ_j c_j e_j is C¹ on D (finite sums of C¹ scalars times constant vectors).

2. (Φ vanishes off C.) Let v ∉ C.
- If v ∉ D, then Φ(v) = 0 by definition.
- If v ∈ D, then G(v) ∉ K, so ω(G(v)) = 0, since a function vanishes outside its topological support (image_eq_zero_of_notMem_tsupport). Then every c_j(v) = 0 and Φ(v) = Ψ(v) = 0.
Hence support Φ ⊆ C.

3. (C is closed.) C is compact in the Hausdorff space ℝ^{n+1}, hence closed. So V := ℝ^{n+1} ∖ C is open, Φ ≡ 0 on V by step 2, and in particular Φ is C¹ on V.

4. (Φ is C¹ on D.) On D, Φ = Ψ, so Φ is C¹ on D by step 1 (ContDiffOn.congr).

5. (Φ is C¹ on ℝ^{n+1}.) Since C ⊆ D, the open sets D and V cover ℝ^{n+1}. Φ is C¹ on each of them, and C¹ is a local property on open sets, so Φ is C¹ on ℝ^{n+1} (Mathlib contDiff_of_contDiffOn_union_of_isOpen).

6. (Support.) C is closed and contains support Φ (step 2), so tsupport Φ = closure(support Φ) ⊆ C ⊆ D (closure_minimal). tsupport Φ is closed and contained in the compact set C, hence compact (IsCompact.of_isClosed_subset); that is, Φ has compact support. ∎

## Key steps

1. Each coefficient c_j = (−1)^j ev(ω∘G, (DG e_{j.succAbove k})_k) is C¹ on D: ev is C^∞ (a continuous multilinear map restricted to the diagonal), ω∘G is C² on D and DG is C¹ on D.
2. Φ vanishes off C = D ∩ G⁻¹(tsupport ω), which is compact and hence closed.
3. The open sets D and ℝ^{n+1} ∖ C cover ℝ^{n+1}, and Φ is C¹ on each (Φ = Ψ on D, Φ = 0 off C), so Φ is C¹.
4. tsupport Φ ⊆ C ⊆ D, so Φ has compact support.

## Reference use

### local-project

Queries:
- `cat <run>/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem extDeriv_pullback|theorem extDeriv_apply|theorem extDerivWithin_pullback' <snapshot>/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `rg -n 'continuousAlternatingMapCompContinuousLinearMap|ContinuousAlternatingMap.compContinuousLinearMapCLM|compContinuousLinearMapL|theorem compContinuousLinearMap_apply' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (ContDiff|ContDiffOn|ContDiffAt)[A-Za-z_.]*(continuousAlternatingMap|continuousMultilinearMap|ContinuousMultilinearMap|ContinuousAlternatingMap|multilinear|Multilinear)' <snapshot>/mathlib/Mathlib (no match); rg -n 'continuousMultilinearMapOption' <snapshot>/mathlib/Mathlib; rg -n 'lemma contDiff' <snapshot>/mathlib/Mathlib/Analysis/Calculus/ContDiff/CPolynomial.lean; sed -n 560,720p <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`
- `rg -n 'normDet_sq_eq_det_gram|def normDet' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean; grep -n euclideanHausdorffMeasure_eq_volume <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem ContinuousOn.measurable_piecewise|theorem IsOpen.and |theorem ContinuousOn.preimage_isClosed_of_isClosed|theorem LinearIsometry.inner_map_map|lemma contDiff_of_contDiffOn_union_of_isOpen|lemma continuousMultilinearMapOption_apply_eq_self|theorem DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem finrank_euclideanSpace_fin|lemma minSmoothness_of_isRCLikeNormedField|theorem ContDiffOn.fderiv_of_isOpen' <snapshot>/mathlib/Mathlib`
- `sed -n 1,200p simongmt/Chapter02/WeightedArea.lean; sed -n 1,70p simongmt/Chapter02/Area.lean; sed -n 1,160p simongmt/Chapter06/Forms.lean; sed -n 1,230p simongmt/Chapter06/Currents.lean; rg -n compContinuousLinearMap simongmt/Chapter06/*.lean; rg 'theorem .*contDiff' simongmt | rg -i 'pullback|alternat|multilinear|form' (no pullback-smoothness lemma for variable L)`
- `python3 scans of dag.json: lean_statement keyword scan (succAbove, LinearMap.trace, Matrix.det (Matrix.of, extDeriv, exteriorDerivative); exact normalized-type match of the 4 child types (none); lean_name lookup of the 4 new codim1_lur_cd_* names (none of 949 nodes); parent and sibling statuses`
- `git grep -l codim1_lur_cd_ <1707 unique ref tips> -- 'GMT/*.lean' (no match); git show c2cf4bd9:GMT/Ch07/Submission.lean | grep ^import (accepted solution adds a SimonGMT Chapter02 import); git show 9db6769e:GMT/Ch07/Submission.lean (handoff base, 457-line contract copy)`
- `sed -n 1,700p verifier/gmt-compare.py (child comparator: NodeChallenge/NodeSolution import GMT.Ch07.Submission in the contract scope; Submission.lean and new GMT/Ch07 files may change)`
- `lake env lean -DautoImplicit=false /tmp/cdiv-split/{Types,AssemblyAx,ChildC,agentA/ChildA,agentB/ChildB,childD/ChildD,Combined,FinalTypes,SubmissionTrial}.lean`
- `sed -n 560,640p book/chapter-06.txt (Simon Ch. 6, 2.34 Constancy Theorem proof and 2.35 Remark: omega = sum (-1)^j a_j dx^1..^dx^j..dx^n, d omega = div a dx^1...dx^n)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a3c73c9e47/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a3c73c9e47/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cdiv-split/Types.lean`
- `/tmp/cdiv-split/AssemblyAx.lean`
- `/tmp/cdiv-split/ChildC.lean`
- `/tmp/cdiv-split/agentA/ChildA.lean`
- `/tmp/cdiv-split/agentB/ChildB.lean`
- `/tmp/cdiv-split/childD/ChildD.lean`
- `/tmp/cdiv-split/Combined.lean`
- `/tmp/cdiv-split/FinalTypes.lean`
- `/tmp/cdiv-split/SubmissionTrial.lean`

Pins match.
- The snapshot manifest (project b4d606db, Mathlib 25730c7c) equals workspace HEAD and .lake/packages/mathlib; simongmt is at 2b366308.
- GMT/Ch07/Contract.lean and Submission.lean are identical. The handoff base 9db6769e Submission.lean is the 457-line contract copy.

Library (what exists).
- Snapshot Mathlib, forms: extDeriv_apply and extDeriv_pullback (DifferentialForm/Basic.lean:198, 259); DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap (FDeriv/ContinuousAlternatingMap.lean:137).
- Snapshot Mathlib, area: LinearMap.normDet_sq_eq_det_gram (InnerProductSpace/NormDet.lean:303); InnerProductSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:191); finrank_euclideanSpace_fin (PiL2.lean:205).
- Snapshot Mathlib, smoothness: ContinuousLinearMap.continuousMultilinearMapOption_apply_eq_self (Normed/Module/Multilinear/Curry.lean:710); ContinuousMultilinearMap.contDiff (ContDiff/CPolynomial.lean); contDiff_of_contDiffOn_union_of_isOpen (ContDiff/Basic.lean:612); ContDiffOn.fderiv_of_isOpen (ContDiff/Defs.lean:907).
- Snapshot Mathlib, topology and measure: ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean:523); ContinuousOn.preimage_isClosed_of_isClosed (Topology/ContinuousOn.lean:197); IsOpen.and (Topology/Basic.lean:121).
- Snapshot Mathlib, other: LinearIsometry.inner_map_map (InnerProductSpace/LinearMap.lean:112); setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Integral/Bochner/Set.lean:466); minSmoothness_of_isRCLikeNormedField (FDeriv/Symmetric.lean:495).
- SimonGMT: integral_area_formula_of_injective_derivative (Chapter02/WeightedArea.lean:151); areaJacobianAt and areaJacobianAt_eq_normDet (Chapter02/Area.lean:26, 35); tsupport_exteriorDerivative_subset (Chapter06/Currents.lean:182); Covector, DifferentialForm, IsSmoothForm and exteriorDerivative = extDeriv (Chapter06/Forms.lean).

Library (what is missing).
- There is no ContDiff lemma for jointly evaluating a continuous alternating map (rg: no match), so field_regularity uses continuousMultilinearMapOption with ContinuousMultilinearMap.contDiff.
- SimonGMT has smoothness only for affine pull-backs (affinePullbackForm), not for pull-backs along a variable linear map.

DAG.
- Related nodes have different types: dgcr_bwd_graph_pullback_extDeriv, dpf_raf_piece_area_formula_gram, cmr_coordinate_divergence_form, codim1_lur_rectifiable_area_formula.
- No node in the 949-node DAG has a type identical to any child, so nothing can be reused.
- The 4 new codim1_lur_cd_* names occur in no node, and in no GMT/*.lean at any of 1707 ref tips.
- Accepted commit c2cf4bd9 adds a SimonGMT Chapter02 import to Submission.lean, so the WeightedArea import has precedent.

Lean.
- All four child types elaborate, and so do the comparator-style exact Submission.X targets.
- Complete scratch proofs of all four children compile with only propext, Classical.choice and Quot.sound.
- The handoff Submission.lean, extended with the WeightedArea import, the four proofs and the parent assembly, proves the exact frozen parent type with only those three axioms; the only sorry is the root main_theorem.
