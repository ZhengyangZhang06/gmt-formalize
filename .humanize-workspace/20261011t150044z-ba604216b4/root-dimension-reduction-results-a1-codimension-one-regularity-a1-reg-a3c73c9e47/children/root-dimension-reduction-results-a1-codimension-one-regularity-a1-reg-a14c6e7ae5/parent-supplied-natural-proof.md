# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1.field_trace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 11–12 of the parent's supplied proof of codim1_lur_chart_divergence_formula: (1d) pull-back commutes with d, and (1e) d becomes divergence (Simon 7.5.2 with Ch. 6, 2.34–2.35). The statement is for an arbitrary open set D and a map G that is C² on D. Of the C^∞ hypothesis on ω, only differentiability at the points G(v) is used.

Notation. e_i := EuclideanSpace.single i 1. For every y ∈ ℝ^{n+1} put:
- β(y) := ω(G(y))∘DG(y), the n-covector β(y)(b_0, …, b_{n−1}) = ω(G(y))(DG(y)b_0, …, DG(y)b_{n−1}) (Mathlib: (ω (G y)).compContinuousLinearMap (fderiv ℝ G y));
- ê^j := Fin.removeNth j e = (e_{j.succAbove 0}, …, e_{j.succAbove(n−1)});
- c_j(y) := (−1)^j ω(G(y))(DG(y)e_{j.succAbove 0}, …, DG(y)e_{j.succAbove(n−1)});
- Ψ(y) := Σ_j c_j(y)e_j.
Thus Φ = 1_D·Ψ.

1. (Localize.) Fix v ∈ D. D is open, so it is a neighbourhood of v, and Φ = Ψ on D. Hence Φ and Ψ agree on a neighbourhood of v, and DΦ(v) = DΨ(v) (Filter.EventuallyEq.fderiv_eq).

2. (Coefficients through β.) For all y and j, β(y)(ê^j) = ω(G(y))(DG(y)e_{j.succAbove 0}, …, DG(y)e_{j.succAbove(n−1)}), by ContinuousAlternatingMap.compContinuousLinearMap_apply and (Fin.removeNth j e)(k) = e_{j.succAbove k}. Therefore c_j(y) = (−1)^j β(y)(ê^j).

3. (Differentiability at v.)
- G is C² on the open set D ∋ v, hence C² at v (ContDiffOn.contDiffAt). So G is differentiable at v, and DG = fderiv ℝ G is C¹ at v (ContDiffAt.fderiv_right, since 1 + 1 ≤ 2), hence differentiable at v.
- ω is C^∞, hence differentiable at G(v), so y ↦ ω(G(y)) is differentiable at v (chain rule).
- The pull-back (α, L) ↦ α∘L is differentiable jointly in both arguments, so β is differentiable at v (Mathlib DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap).
- Evaluating a covector at the fixed tuple ê^j is continuous linear in the covector, so y ↦ β(y)(ê^j) is differentiable at v.
- By step 2, c_j is differentiable at v with Dc_j(v) = (−1)^j D[y ↦ β(y)(ê^j)](v).

4. (Derivative of Ψ.) Ψ = Σ_j c_j e_j is a finite sum of differentiable scalars times constant vectors. So Ψ is differentiable at v with DΨ(v)a = Σ_j (Dc_j(v)a)e_j for all a ∈ ℝ^{n+1}. In particular the i-th coordinate of DΨ(v)e_i is Dc_i(v)e_i.

5. (Trace.) For a linear endomorphism L of ℝ^{n+1}, trace L = Σ_i (Le_i)_i, the trace of the matrix of L in the standard basis (LinearMap.trace_eq_matrix_trace with the standard basis, LinearMap.toMatrix_apply). By steps 1, 4 and 3:
trace DΦ(v) = trace DΨ(v) = Σ_i Dc_i(v)e_i = Σ_i (−1)^i D[y ↦ β(y)(ê^i)](v)e_i.

6. (d of β in coordinates.) β is differentiable at v (step 3), so Mathlib extDeriv_apply gives dβ(v)(e_0, …, e_n) = Σ_i (−1)^i D[y ↦ β(y)(Fin.removeNth i e)](v)(e_i). Here the integer (−1)^i acts on reals as multiplication by the real number (−1)^i. Comparing with step 5: trace DΦ(v) = dβ(v)(e_0, …, e_n).

7. (Pull-back commutes with d.) Apply Mathlib extDeriv_pullback with ω differentiable at G(v), G C² at v, and minSmoothness ℝ 2 = 2 (minSmoothness_of_isRCLikeNormedField). It gives dβ(v) = dω(G(v))∘DG(v) as (n+1)-covectors, where β is exactly the map x ↦ (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) of that lemma. Evaluating at (e_0, …, e_n): dβ(v)(e_0, …, e_n) = dω(G(v))(DG(v)e_0, …, DG(v)e_n).

8. (Conclusion.) Steps 6 and 7 give trace DΦ(v) = dω(G(v))(DG(v)e_0, …, DG(v)e_n) for every v ∈ D. ∎

## Key steps

1. Near v ∈ D (D open), Φ equals Ψ = Σ_j c_j e_j, so trace DΦ(v) = Σ_i Dc_i(v)e_i.
2. c_j(y) = (−1)^j β(y)(removeNth j e) for the pulled-back form β(y) = ω(G(y))∘DG(y), which is differentiable at v because G is C² at v.
3. extDeriv_apply: dβ(v)(e_0, …, e_n) = Σ_i (−1)^i D[β(·)(removeNth i e)](v)e_i, which equals trace DΦ(v).
4. extDeriv_pullback (G C² at v): dβ(v)(e_0, …, e_n) = dω(G(v))(DG(v)e_0, …, DG(v)e_n).

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
