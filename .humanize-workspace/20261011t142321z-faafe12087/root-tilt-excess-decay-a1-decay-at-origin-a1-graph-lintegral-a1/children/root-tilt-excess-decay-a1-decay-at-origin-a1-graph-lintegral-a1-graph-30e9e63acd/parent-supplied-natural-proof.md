# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_lintegral-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_lintegral-a1.graph_map_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1-2 of the parent proof, with every computation written out.

Notation:
- F(x) = q(graphPoint x (f x)).
- Norms are Euclidean norms, and dist(u, v) = |u - v| in every Euclidean space.

1. Coordinates of graphPoint.
- For a in R^n and b in R^l, graphPoint a b = toLp 2 (Fin.append (ofLp a) (ofLp b)).
- Its coordinate at index Fin.castAdd l i (i in Fin n) is a_i, and at index Fin.natAdd n j (j in Fin l) it is b_j (Fin.append_left, Fin.append_right).
- Every index k in Fin (n+l) has exactly one of these two forms (Fin.addCases).

2. Difference identity: for a, a' in R^n and b, b' in R^l, graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b').
- Subtraction in EuclideanSpace is coordinatewise.
- By step 1, at an index castAdd l i both sides have coordinate a_i - a'_i.
- At an index natAdd n j both sides have coordinate b_j - b'_j.
- By extensionality over the two forms of indices, the two vectors are equal.

3. Norm identity: for a in R^n and b in R^l, |graphPoint a b|^2 = |a|^2 + |b|^2.
- For w in a Euclidean space, |w|^2 = sum_k |w_k|^2 (EuclideanSpace.norm_sq_eq).
- Split the sum over Fin (n+l) into the castAdd part and the natAdd part (Fin.sum_univ_add).
- By step 1, the first part is sum_i |a_i|^2 = |a|^2 and the second is sum_j |b_j|^2 = |b|^2.

4. Reduction.
- By LipschitzOnWith.of_dist_le_mul, it suffices to show dist(F x, F y) <= K dist(x, y) for all x, y in D.
- Here K is the real number underlying NNReal.sqrt(1 + L^2).
- K = Real.sqrt(1 + L^2): use Real.coe_sqrt, and note that the real cast of 1 + L^2 is 1 + (L:R)^2.

5. Fix x, y in D. Then
dist(F x, F y) = |q(graphPoint x (f x)) - q(graphPoint y (f y))|
= |q(graphPoint x (f x) - graphPoint y (f y))| (q is linear, map_sub)
= |graphPoint x (f x) - graphPoint y (f y)| (q is a linear isometry, LinearIsometryEquiv.norm_map)
= |graphPoint (x - y) (f x - f y)| (step 2).
Also dist(x, y) = |x - y|.

6. Since f is L-Lipschitz on D and x, y lie in D, |f x - f y| <= L |x - y| (LipschitzOnWith.norm_sub_le). Both sides are nonnegative, so squaring preserves the inequality: |f x - f y|^2 <= L^2 |x - y|^2.

7. By steps 3 and 6,
|graphPoint (x - y) (f x - f y)|^2 = |x - y|^2 + |f x - f y|^2 <= |x - y|^2 + L^2 |x - y|^2 = (1 + L^2) |x - y|^2.

8. Take square roots, using that Real.sqrt is monotone and that sqrt(t^2) = t for t >= 0:
|graphPoint (x - y) (f x - f y)| = sqrt(|graphPoint (x - y) (f x - f y)|^2)
<= sqrt((1 + L^2) |x - y|^2) (step 7, Real.sqrt_le_sqrt)
= sqrt(1 + L^2) sqrt(|x - y|^2) (Real.sqrt_mul, since 1 + L^2 >= 0)
= sqrt(1 + L^2) |x - y|.

9. Combining steps 5 and 8 gives dist(F x, F y) <= sqrt(1 + L^2) dist(x, y) for all x, y in D. By step 4, this is LipschitzOnWith (NNReal.sqrt (1 + L^2)) F D.

## Key steps

1. Coordinates of graphPoint via Fin.append: graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b'), and |graphPoint a b|^2 = |a|^2 + |b|^2 (Fin.sum_univ_add)
2. Reduce LipschitzOnWith with constant NNReal.sqrt(1 + L^2) to dist(F x, F y) <= sqrt(1 + L^2) dist(x, y) on D (of_dist_le_mul, Real.coe_sqrt)
3. Linearity and isometry of q give |F x - F y| = |graphPoint (x - y) (f x - f y)|
4. |graphPoint (x - y) (f x - f y)|^2 = |x - y|^2 + |f x - f y|^2 <= (1 + L^2)|x - y|^2 by the Lipschitz hypothesis; take square roots

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `sed -n 1,260p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `sed -n 700,790p <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "theorem ContinuousOn.aemeasurable|theorem map_apply_of_aemeasurable|theorem restrict_apply'|theorem lintegral_map'|theorem lintegral_smul_measure|theorem lintegral_mono'|theorem le_iff " <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'LipschitzOnWith.norm_sub_le|LipschitzOnWith.norm_div_le|norm_div_le_of_le' <snapshot>/mathlib/Mathlib; sed -n 440,460p <snapshot>/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean; sed -n 50,60p <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n 'theorem coe_sqrt|theorem EuclideanSpace.norm_sq_eq' <snapshot>/mathlib/Mathlib/Analysis/Real/Sqrt.lean <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `grep -rn 'euclideanHausdorffMeasure_image_le_of_lipschitzOn' .lake/packages/simongmt/Poincare; sed -n 200,232p .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean; head -30 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean | grep import; grep -rn 'theorem|lemma' Chapter02/*.lean | grep -i lintegral`
- `python3 -I: scan <run>/dag.json lean_name/status/lean_statement for graphPoint/graphOver/lipschitz/lintegral nodes (rsod_norm_graphPoint_sq, lip_approx_graph_coordinates, lip_approx_gm_graph_map_lipschitz, allard52_cft_graph_map_sqrt_two, anyrad_gc_graph_lintegral_transfer, gwe_lipschitz_graph_area_formula, dohr_vel_graph_area_formula)`
- `rg -l -e 'tdo_gl_graph_map_lipschitzOn|tdo_gl_lintegral_image_le' <run>/dag.json <run>/nodes <snapshot>/project <snapshot>/mathlib/Mathlib GMT .lake/packages/simongmt/Poincare (no match, exit 1)`
- `python3 -I: verifier/gmt-compare.py contract_scope(GMT/Ch05/Contract.lean, 'GMT.Ch05.main_theorem'); verifier/lean_contract.py validate_lean_statement on both child statements`
- `lake env lean -o /tmp/tdo-gl-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/tdo-gl-decomp/olean lean /tmp/tdo-gl-decomp/checks/Split.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-lintegral-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-graph-measure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tdo-gl-decomp/checks/Split.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean, workspace Contract.lean and workspace Submission.lean all have sha256 c966f51e....

Declarations used by the children (paths under mathlib/Mathlib unless stated):
- Euclidean Hausdorff measure (Geometry/Euclidean/Volume/Measure.lean):
  - euclideanHausdorffMeasure_def (:74): muHE[d] = addHaarScalarFactor(volume on EuclideanSpace R (Fin d), muH[d]) * muH[d], on any Borel (e)metric space.
  - EuclideanSpace.euclideanHausdorffMeasure_eq_volume (:187).
- LipschitzOnWith.hausdorffMeasure_image_le (MeasureTheory/Measure/Hausdorff.lean:733).
- ContinuousOn.aemeasurable (MeasureTheory/Integral/IntegrableOn.lean:754).
- Measure.map_apply_of_aemeasurable (MeasureTheory/Measure/Map.lean:166).
- Measure.restrict_apply' (MeasureTheory/Measure/Restrict.lean:111).
- Measure.le_iff (MeasureTheory/Measure/CompleteLattice.lean:41).
- Lebesgue integrals: lintegral_mono' (MeasureTheory/Integral/Lebesgue/Basic.lean:74), lintegral_smul_measure (same file :418), lintegral_map' (MeasureTheory/Integral/Lebesgue/Map.lean:36).
- LipschitzOnWith.norm_sub_le (to_additive of LipschitzOnWith.norm_div_le, Analysis/Normed/Group/Uniform.lean:451).
- LipschitzOnWith.of_dist_le_mul (Topology/MetricSpace/Lipschitz.lean:57).
- Real.coe_sqrt (Analysis/Real/Sqrt.lean:121).
- EuclideanSpace.norm_sq_eq (Analysis/InnerProductSpace/PiL2.lean:149).

Pinned simongmt package (in the import closure of GMT.Ch05.Submission via Chapter03/Rectifiable.lean -> Chapter02.Lipschitz):
- Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216) gives muHE[n](F '' A) <= K^n muHE[n](A) for any metric spaces. Child 2 uses it for its image bound.
- The simongmt area-formula files (AreaCritical, AreaLiteral, ...) are not imported by Submission and are not needed.

DAG:
- Related accepted nodes (rsod_norm_graphPoint_sq, lip_approx_graph_coordinates, lip_approx_gm_graph_map_lipschitz) are in other branches, so they are not available as sibling dependencies.
- Their types also differ from the new children: global/1-Lipschitz versions, or bare coordinate facts.
- No match: the new names tdo_gl_graph_map_lipschitzOn and tdo_gl_lintegral_image_le occur nowhere searched.

Lean (Split.lean, sha256 549d6282...):
- Both children are proved, and the frozen parent is proved from them, in the exact verifier contract scope. Axioms are only propext, Classical.choice and Quot.sound.
- Comparator-style `exact Submission.X` targets succeed for both children and for the parent.
- validate_lean_statement accepts both statements.
