# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_approximation-a1`
- Child DAG node: `root.lipschitz_approximation-a1.graph_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (Gr) of the parent proof (Lipschitz images and H^n = L^n on R^n; Simon Ch. 2, 1.8(i) and Ch. 1, 2.10).

1. Let Gamma : R^n -> R^(n+l), Gamma(x) := q(graphPoint x (f x)). Since graphOver f D is the image of D under x -> graphPoint x (f x), q '' graphOver f (closedBall c r) = Gamma(closedBall c r).
2. Gamma is sqrt(2)-Lipschitz: by the graph-coordinates child (lip_approx_graph_coordinates), (i) and (ii), and since q is a linear isometry, |Gamma(x) - Gamma(z)|^2 = |graphPoint (x - z) (f x - f z)|^2 = |x - z|^2 + |f x - f z|^2 <= 2 |x - z|^2.
3. A K-Lipschitz map multiplies the n-dimensional Hausdorff measure by at most K^n (Mathlib LipschitzOnWith.hausdorffMeasure_image_le; for the normalised muHE[n], which is a constant multiple of muH[n], SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn). Hence H^n(Gamma(closedBall c r)) <= (sqrt 2)^n H^n(closedBall c r), where on the right H^n = muHE[n] on R^n.
4. On R^n, muHE[n] equals Lebesgue measure (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume), and for r >= 0, Lebesgue measure of closedBall c r is r^n pi^(n/2)/Gamma(n/2 + 1) = omega_n r^n (Mathlib EuclideanSpace.volume_closedBall, with sqrt(pi)^n = pi^(n/2) and omega_n = unitBallVolume n).
5. Therefore H^n(q '' graphOver f (closedBall c r)) <= (sqrt 2)^n omega_n r^n = 2^(n/2) omega_n r^n.

## Key steps

1. Write the set as the image of closedBall c r under Gamma(x) = q(graphPoint x (f x))
2. Gamma is sqrt(2)-Lipschitz by the graph-coordinates identities and 1-Lipschitz f
3. Lipschitz image bound for muHE[n]: factor (sqrt 2)^n
4. muHE[n] = volume on R^n and volume of the closed r-ball is omega_n r^n

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `diff GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean (identical)`
- `grep -n 'def C1Approximation|def WhitneyExtension|def Rademacher' GMT/Ch02/Contract.lean; grep -n sorry GMT/Ch02/Submission.lean`
- `grep -o 'lip_approx_[a-z_]*' dag.json DAG.md dag.mmd issue-workers.json problem.json (no matches)`
- `python3 -I: list dag.json nodes with 'tangent' in id (aal_tangent_structure, rectifiableVarifold_ae_tangentProj_starProjection)`
- `grep -n 'theorem LipschitzWith.ae_differentiableAt' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `grep -n 'theorem tendstoUniformlyOn_of_ae_tendsto' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `grep -n 'theorem measurableSet_of_differentiableAt|theorem measurable_fderiv' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `grep -rn 'exists_isClosed_diff_lt' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem isClosed_iUnion' <snapshot>/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `grep -rn 'theorem contDiff_euclidean|theorem contDiff_piLp' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem norm_fderiv_le_of_lipschitz' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `grep -rn 'theorem ContinuousOn.measurable_piecewise' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `grep -rn 'norm_image_sub_le_of_norm_fderiv_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `grep -n 'theorem hausdorffMeasure_homothety_image' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'euclideanHausdorffMeasure_eq_volume|def MeasureTheory.Measure.euclideanHausdorffMeasure' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn sorry .lake/packages/simongmt/Poincare/SimonGMT (0 matches); git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `grep -n '^theorem|^structure' SimonGMT/Chapter02/WhitneyExtension.lean SimonGMT/Chapter02/WhitneyJet.lean`
- `grep -n '^theorem' -A 12 SimonGMT/Chapter01/Lusin.lean`
- `grep -rn 'theorem simon_theorem_3_6' -A 30 SimonGMT/Chapter01/; grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity' SimonGMT/Chapter01/Densities.lean`
- `grep -n 'theorem measure_toOuterMeasure_isBorelRegular' SimonGMT/Chapter01/Basic.lean; grep -n 'simonAreaNormalization' SimonGMT/Chapter02/AreaNormalization.lean`
- `grep -n '^theorem' SimonGMT/Chapter02/{AreaLipschitz,AreaCritical,AreaFormula,AreaNoninjective,Area}.lean; grep -rn 'theorem weighted_area_formula_volume_of_injective_derivative|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' SimonGMT/Chapter02`
- `grep -n '^theorem|^def' SimonGMT/Chapter03/{SubmanifoldCover,DisjointCover,Rectifiable}.lean`
- `sed -n 150,290p book/sources/chapter-02-source.txt (printed proof of Thm 1.5); sed -n 1,360p book/sources/chapter-03-source.txt (1.1-1.9)`
- `lean --root=/tmp/lipapprox-dec-v2 -o GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean -o LipApproxAux/WhitneyExtension.olean LipApproxAux/WhitneyExtension.lean (verbatim copy of SimonGMT Chapter02/WhitneyExtension.lean)`
- `lean --root=/tmp/lipapprox-dec-v2 c1a/Api.lean (#check of cited APIs and #print axioms for Whitney and Lusin)`
- `lean --root=/tmp/lipapprox-dec-v2 c1a/C1A.lean (C1ACheck.c1_approx_scalar, C1ACheck.c1_approx; #print axioms)`
- `python3 -I scripts/gen_checks.py decomposition statements (verifier/lean_contract.validate_lean_statement); lean check/lip_approx_*.lean; lean check/All.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-tangent-structure-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lipapprox-dec-v2/c1a/C1A.lean`
- `/tmp/lipapprox-dec-v2/c1a/Api.lean`
- `/tmp/lipapprox-dec-v2/LipApproxAux/WhitneyExtension.lean`
- `/tmp/lipapprox-dec-v2/check/All.lean`

Pinned versions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The pinned SimonGMT, 2b3663083f3fe399b6296fb8eaee52169170e197, lies outside the snapshot and contains no sorry. The workspace GMT/Ch05/Submission.lean is byte-identical to the snapshot copy.

C1A has no usable proof anywhere:
- GMT/Ch02/Contract.lean:199 defines C1Approximation, but GMT/Ch02/Submission.lean:377 proves its main_theorem by sorry.
- SimonGMT Chapter03/SubmanifoldCover.lean proves only the C^1-to-rectifiable direction of Lemma 1.2.
So the proof is supplied as Part A of tangent_structure.

Checked ingredients located in Mathlib (paths under mathlib/Mathlib):
- LipschitzWith.ae_differentiableAt (Analysis/Calculus/Rademacher.lean:385);
- measurableSet_of_differentiableAt and measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:372, 378);
- tendstoUniformlyOn_of_ae_tendsto (MeasureTheory/Function/Egorov.lean:205);
- MeasurableSet.exists_isClosed_sdiff_lt (MeasureTheory/Measure/Regular.lean, alias exists_isClosed_diff_lt at :1044);
- LocallyFinite.isClosed_iUnion (Topology/LocallyFinite.lean:128);
- contDiff_euclidean (Analysis/InnerProductSpace/Calculus.lean:339);
- norm_fderiv_le_of_lipschitz (Analysis/Calculus/FDeriv/Basic.lean:947);
- Convex.norm_image_sub_le_of_norm_fderiv_le (Analysis/Calculus/MeanValue.lean:499);
- ContinuousOn.measurable_piecewise (MeasureTheory/Constructions/BorelSpace/Basic.lean:523);
- hausdorffMeasure_homothety_image (MeasureTheory/Measure/Hausdorff.lean:1060);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187).

Checked ingredients located in SimonGMT (paths under Poincare/SimonGMT):
- Chapter02.exists_contDiff_one_extension_of_whitney (WhitneyExtension.lean:373); its hypothesis HasWhitneyC1Compatibility (WhitneyJet.lean:34) has the fields continuous_value, continuous_derivative and remainder;
- Chapter01.exists_isClosed_continuousOn_of_measurable, the finite-measure Lusin theorem (Lusin.lean:127);
- Chapter01.simon_theorem_3_6 (DensityComparison.lean:332), with its density quotient over closed balls (Densities.lean);
- Chapter01.measure_toOuterMeasure_isBorelRegular (Basic.lean:309);
- simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure and simonAreaNormalization_pos/_ne_top (Chapter02/AreaNormalization.lean:45, 31, 37);
- Chapter02.area_image_criticalSet_eq_zero (AreaCritical.lean:185);
- Chapter02.weighted_area_formula_volume_of_injective_derivative (WeightedArea.lean:120);
- Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz.lean:216);
- Chapter03.simon_remark_1_3_nullMeasurable (DisjointCover.lean:109);
- Chapter03.HasWeightedApproximateTangentSpaceAt.unique (Rectifiable.lean:345).
None of these is the Chapter04.RectifiableVarifold that the chapter README excludes.

The book's printed proofs are followed: Thm 1.5 at book/sources/chapter-02-source.txt lines 165-270, and Ch. 3, 1.1-1.9.

Lean results:
- /tmp/lipapprox-dec-v2/c1a/C1A.lean compiles with 0 errors and no sorry.
- C1ACheck.c1_approx_scalar, C1ACheck.c1_approx, exists_contDiff_one_extension_of_whitney and exists_isClosed_continuousOn_of_measurable depend only on propext, Classical.choice and Quot.sound.
- All 11 child types elaborate in the contract scope with 0 errors and only sorry warnings, and pass validate_lean_statement.

No lip_approx_ name is reserved anywhere in the DAG. The tangent nodes of other branches, aal_tangent_structure and rectifiableVarifold_ae_tangentProj_starProjection, have different Lean types, so there is no collision and no reuse.
