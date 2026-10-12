# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1`
- Child DAG node: `root.density_one_regularity-a1.open_graph_domain-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (choice W := {x in the open ball B'^n_s(0) : |(x, u(x))| < s}), i.e. the passage from the closed-ball identity of Theorem 5.2 to 'graph u = spt V cap B'_sigma(0)' in Simon's proof of 7.1 (display (1), p. 127). Write (x, y) for graphPoint x y in R^(n+l).
1. For x in R^n and y in R^l, |(x, y)|^2 = |x|^2 + |y|^2 (the Euclidean norm squared is the sum of the squares of the n coordinates of x and the l coordinates of y). In particular |x| <= |(x, y)|.
2. Define W := {x in B'^n_s(0) : |(x, u(x))| < s}. Then W is contained in B'^n_s(0) by definition. 0 is in W: s > 0 gives 0 in B'^n_s(0), and (0, u(0)) = (0, 0) = 0 has norm 0 < s.
3. W is open: g(x) := |(x, u(x))| is continuous on the open set B'^n_s(0), because u is continuous on B^n_s(0), which contains B'^n_s(0), and the map (x, y) -> (x, y) in R^(n+l) is linear, hence continuous. Thus W = B'^n_s(0) cap g^{-1}((-infinity, s)) is the intersection of an open set with the preimage of an open set under a function continuous on that open set, hence open.
4. q^{-1}(S) cap B'_s(0) is contained in graph_W u. Let z be in B'_s(0) with z = q^{-1}(y), y in S. Since q is a linear isometry, |y| = |z| < s, so y is in S cap B_s(0) = q(graph_{B^n_s(0)} u) cap B_s(0). Hence y = q(g) with g = (x, u(x)) for some x with |x| <= s, and z = q^{-1}(q(g)) = g. Now |(x, u(x))| = |z| < s, so |x| < s by step 1, i.e. x is in B'^n_s(0); thus x is in W and z = (x, u(x)) is in graph_W u.
5. graph_W u is contained in q^{-1}(S) cap B'_s(0). Let x be in W and z := (x, u(x)). Then |z| < s, so z is in B'_s(0). Also |x| < s, so z is in graph_{B^n_s(0)} u and q(z) is in q(graph_{B^n_s(0)} u); moreover |q(z)| = |z| < s, so q(z) is in q(graph_{B^n_s(0)} u) cap B_s(0) = S cap B_s(0). Thus q(z) is in S and z = q^{-1}(q(z)) is in q^{-1}(S).
6. Steps 2-5 show that W is open, contains 0, is contained in B'^n_s(0), and q^{-1}(S) cap B'_s(0) = graph_W u.

## Key steps

1. |(x, y)|^2 = |x|^2 + |y|^2, so |x| <= |(x, y)|
2. W := {x in open ball : |(x, u(x))| < s} contains 0 (u(0) = 0)
3. W is open by continuity of u on the open ball
4. Two inclusions using that q is a norm-preserving bijection and the closed-ball identity

## Reference use

### local-project

Queries:
- `sed -n 1280,1400p book/chapter-05.txt (Theorem 7.1 and its printed proof)`
- `sed -n 215,575p book/chapter-04.txt (3.1-3.17, 4.1-4.11); sed -n 1,200p and 270,340p book/chapter-03.txt (1.1-1.9); sed -n 560,720p book/chapter-01.txt (3.1-3.7); grep -n 'Approximation Theorem' book/chapter-02.txt`
- `grep -n '^def \|^theorem ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn 'ae_hasWeightedApproximateTangent\|ae_hasApproximateTangent\|Theorem 1.9\|1\.9' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n '^theorem \|^def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{Densities,DensityComparison,LowerDensityComparison,HausdorffDensityBounds,RelativeDensityComparison,GeneralDensity,EuclideanNormalization,Hausdorff}.lean`
- `cat .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{LpLowerDensity,MultiplicityBridge}.lean; sed -n 1,227p .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `grep -n '^theorem \|^lemma \|^def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,WhitneyExtension}.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/{SubmanifoldCover,Differential}.lean; grep -n 'injective_area_formula_lipschitz_simon' -A 12 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean; grep -n '^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `grep -rn 'μHE\[' <snapshot>/mathlib/Mathlib --include=*.lean; sed -n 1,200p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n image_symmDiff <snapshot>/mathlib/Mathlib/Data/Set/Image.lean; rg -n 'inf_symmDiff_distrib_right|symmDiff_inf_distrib|inter_symmDiff_distrib' <snapshot>/mathlib/Mathlib/Order/SymmDiff.lean <snapshot>/mathlib/Mathlib/Data/Set/*.lean`
- `grep -n 'divRight\|mulRight\|to_additive' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `rg -n 'theorem fderivWithin_of_mem_nhds|theorem ball_subset_interior_closedBall|theorem closedBall_mem_nhds ' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `rg -n 'isometry_sub_const|isometry_add_const|IsometryEquiv.subRight|def subRight|def addRight' <snapshot>/mathlib/Mathlib/Topology <snapshot>/mathlib/Mathlib/Analysis/Normed`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/README.md GMT/Ch05/README.md`
- `grep -rl '<the seven proposed lean_names>' .humanize GMT; python3 scan of dag.json nodes for reserved children/theorems`
- `lake env lean /tmp/dor-a1-check/Check2.lean (contract lines 1-460, namespace Submission with allard_regularity_theorem and the 7 children as sorry placeholders, full proof of density_one_regularity : DensityOneRegularity, sanity example transferring tangentProj measurability to V.weight)`
- `lake env lean /tmp/dor-a1-check/verify/FormalAll.lean (reviewer's sorry-free proofs of four children with the frozen types; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/tmp/dor-a1-check/Check2.lean`
- `/tmp/dor-a1-check/verify/FormalAll.lean`

Snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot's Contract.lean and README.md are byte-identical to the workspace copies (cmp).

No prior work: there is no existing proof of DensityOneRegularity or of any proposed child. The seven proposed names occur nowhere in .humanize or GMT, and dag.json reserves no child names yet.

SimonGMT, Chapter03/Rectifiable.lean: defines HasWeightedApproximateTangentSpaceAt (l.330) and proves uniqueness (l.345), but the grep finds no a.e.-existence result (Ch. 3, 1.9 is not formalized) and nothing on measurability of the tangent field. Hence child tangent_ae.

SimonGMT Chapter04 L^p density results (LpLowerDensity.lean: one_le_stationaryDensityReal_of_mem_support_lp) are stated for Chapter04.RectifiableVarifold. That structure stores a tangent field, a measurable carrier and a globally locally finite weight (Chapter04/Basic.lean), so they do not apply to the contract varifold. Hence child density_ge_one, proved from the contract's first variation following Simon 4.1-4.10(1).

SimonGMT Chapter01/DensityComparison.lean has the Upper Density Theorem (simon_theorem_3_6) and the comparison theorem (simon_theorem_3_3, mul_simonHausdorff_le_of_le_dimensionalUpperDensity). Both are stated for simonHausdorffOuterMeasureReal, a positive multiple of μH[n] (Hausdorff.lean: simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure). Since μHE[n] is also a nonzero multiple of μH[n] (Mathlib Geometry/Euclidean/Volume/Measure.lean), null sets agree; this is used by carrier_support_null.

SimonGMT also provides, for tangent_ae: Lusin (Chapter01/Lusin.lean, simon_theorem_1_17), the injective Lipschitz area formula (Chapter02/AreaLipschitz.lean:126) and Whitney C^1 extension (Chapter02/WhitneyExtension.lean).

Mathlib items used by the parent assembly:
- Isometry.euclideanHausdorffMeasure_image and IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (Measure.lean)
- Set.image_symmDiff (Data/Set/Image.lean:388)
- Set.inter_symmDiff_distrib_right (Data/Set/SymmDiff.lean:46)
- IsometryEquiv.subRight, via to_additive of divRight (IsometricSMul.lean:166-172)
- fderivWithin_of_mem_nhds (FDeriv/Basic.lean:522)
- ball_subset_interior_closedBall (Pseudo/Defs.lean:1216) and closedBall_mem_nhds (Pseudo/Defs.lean:842)
The names isometry_sub_const / isometry_add_const / def subRight have no match in Topology or Analysis/Normed.

Lean checks:
- All 7 child types elaborate in the contract scope.
- density_one_regularity : DensityOneRegularity compiles from the children plus the sibling AllardRegularityTheorem. The only warnings are the 8 sorry warnings on the placeholders; an independent reviewer reproduced this.
- The reviewer's sorry-free Lean proofs of allard_scale, translate_varifold, open_graph_domain and holder_class use exactly the frozen types and recompile with axioms propext, Classical.choice, Quot.sound.
