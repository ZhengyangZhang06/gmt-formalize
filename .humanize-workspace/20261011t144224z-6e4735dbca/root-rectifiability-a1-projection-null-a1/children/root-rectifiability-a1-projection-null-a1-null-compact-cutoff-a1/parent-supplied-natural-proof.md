# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.projection_null-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1.null_compact_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the cutoff construction in Step 5 of the parent proof. Notation: dist(y, F) = infDist y F and G_ε := {y : dist(y, F) < ε} = thickening ε F.

0. If F = ∅, then b := 0 works, since tsupport 0 = ∅. Assume F ≠ ∅ from now on.

1. Small neighbourhoods. Each G_ε (ε > 0) is open and bounded (F is bounded), and G_ε ⊆ G_{ε'} for ε ≤ ε'. F is closed, so ⋂_{k≥1} G_{1/k} = closure F = F. Since L^N(G_1) < ∞, continuity of measure from above gives L^N(G_{1/k}) → L^N(F) = 0; this is Mathlib's tendsto_measure_thickening_of_isClosed. Fix ε := 1/k > 0 with L^N(G_ε) ≤ δ.

2. Mollifier. Let φ_ε ∈ C^∞(ℝ^N) with φ_ε ≥ 0, ∫φ_ε = 1 and support φ_ε ⊆ B_{ε/4}(0); for example, the normalized smooth bump function ContDiffBump.normed with centre 0, inner radius ε/8 and outer radius ε/4.

3. Definition. Put b(y) := (1_{G_{ε/2}} ⋆ φ_ε)(y) = ∫ 1_{G_{ε/2}}(t)·φ_ε(y − t) dt = ∫ 1_{G_{ε/2}}(y − z)·φ_ε(z) dz. The indicator 1_{G_{ε/2}} is bounded and Borel, hence locally integrable, and φ_ε is C^∞ with compact support. So b is C^∞ (HasCompactSupport.contDiff_convolution_right).

4. Range. Since 0 ≤ 1_{G_{ε/2}} ≤ 1, φ_ε ≥ 0 and ∫φ_ε = 1, we have 0 ≤ b(y) ≤ 1.

5. b = 1 on F. Let y ∈ F and |z| < ε/4. Then dist(y − z, F) ≤ |z| < ε/2, so 1_{G_{ε/2}}(y − z) = 1 wherever φ_ε(z) ≠ 0. Hence b(y) = ∫φ_ε = 1.

6. Support. Suppose dist(y, F) ≥ 3ε/4. For |z| < ε/4 we get dist(y − z, F) ≥ dist(y, F) − |z| > ε/2, so 1_{G_{ε/2}}(y − z) = 0 wherever φ_ε(z) ≠ 0, and b(y) = 0. Thus support b ⊆ {dist(·, F) < 3ε/4}, and tsupport b ⊆ {dist(·, F) ≤ 3ε/4} ⊆ G_ε. The set tsupport b is closed and bounded, hence compact, so b has compact support.

7. Measure. L^N(tsupport b) ≤ L^N(G_ε) ≤ δ < ∞, so (volume (tsupport b)).toReal ≤ δ.

Remark (an equivalent route that may replace Steps 2–6). By outer regularity, choose an open G ⊇ F with L^N(G) < δ. Choose an open V with F ⊆ V ⊆ closure V ⊆ G and closure V compact (exists_open_between_and_isCompact_closure). Take a C^∞ function b : ℝ^N → [0, 1] with b = 1 on F and b = 0 on ℝ^N ∖ V (exists_contMDiffMap_zero_one_of_isClosed, then contMDiff_iff_contDiff). Then tsupport b ⊆ closure V ⊆ G. ∎

## Key steps

1. Choose ε with L^N({dist(·, F) < ε}) ≤ δ, by continuity from above (F is compact and Lebesgue-null).
2. b := 1_{G_{ε/2}} ⋆ φ_ε, with a mollifier φ_ε supported in B_{ε/4}; b is C^∞ and 0 ≤ b ≤ 1.
3. b = 1 on F, and tsupport b ⊆ {dist(·, F) ≤ 3ε/4} ⊆ G_ε is compact, so L^N(tsupport b) ≤ δ.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c95; mathlib_commit 25730c7c)`
- `sha256sum GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (all ea3ee0dd…)`
- `rg -n 'def CompactlyContainedOpen|def IsMassMeasure|def IsMeasureRepresentation|abbrev Eucl|^theorem main_theorem|RectifiabilityTheorem' project/GMT/Ch06/Contract.lean`
- `rg -n 'theorem toSphere_apply_univ|theorem measurePreserving_homeomorphUnitSphereProd' Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `rg -n 'integral_fun_norm_addHaar|integrableOn_fun_norm_addHaar' Mathlib/MeasureTheory`
- `rg -n 'contDiff_convolution_right|hasFDerivAt_convolution_right' Mathlib/Analysis/Calculus/ContDiff/Convolution.lean Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem integral_Ioi_of_hasDerivAt_of_tendsto' Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `rg -n 'theorem tendsto_measure_thickening_of_isClosed' Mathlib/MeasureTheory`
- `rg -n 'MeasurableSet.exists_isClosed_lt_add|of_pseudoMetrizableSpace_of_isFiniteMeasure' Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'theorem sign_cycleRange|theorem cycleRange_symm_zero|theorem cycleRange_symm_succ' Mathlib/GroupTheory/Perm/Fin.lean`
- `rg -n 'def extDeriv' Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `rg -n 'IsCompact.exists_cthickening_subset_open' Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'exists_contMDiffMap_zero_one_of_isClosed' Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `timeout 100 rg -il 'newtonian potential|fundamental solution of (the )?laplace|riesz potential' Mathlib/Analysis Mathlib/MeasureTheory (no match)`
- `rg -n 'compact' simongmt Chapter02/BV.lean (module header: compactness remains a separate obligation)`
- `rg -n 'massOn|def massAdmissibleOn|def covectorEuclideanNorm|abbrev SimonMultiIndex|def euclideanNVectorCoordinate|def wedgeCovectors|abbrev TestFormOn|def exteriorDerivativeTestOn|theorem wedgeCovectors_apply_det|theorem covectorPullback_wedgeCovectors' simongmt Chapter06/{Mass,FormsDuality,Currents}.lean`
- `python3 verifier/lean_contract.py validate_lean_statement on the 9 lean_statements`
- `python3 verifier/gmt-compare.py contract_scope + child_modules (mode contract) for the 9 children, the frozen parent and the sibling`
- `lean -o build/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean (exit 0, 252 s)`
- `lean Chal3/AllStatements.lean (11 frozen statements under the comparator header; exit 0)`
- `lean ExactMatch3.lean (13 exact-type witnesses, #print axioms; exit 0)`
- `lean -o Scratch/{C1Rev,C2Sign,C2Full,C3Full,C4Glue,C5Full,C6Full,C7Glue,C8Full,C9Full,Assembly,JsonConsistency,EndToEnd}.lean, sequential fresh rebuild`
- `grep -nE 'sorry|admit|axiom|native_decide|implemented_by|@[extern|unsafe|opaque' Scratch/*.lean (no match)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (378 reserved names)`
- `python3 audit of nodes/root-rectifiability-a1-projection-null-a1/decomposition-v{1,2}.json and decomposition-audit-v{1,2}.json; dag.json status/children of all nodes`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `GMT/Ch06/Submission.lean`
- `GMT/Ch06/Contract.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-v1.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-v2.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-audit-v1.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch06/4c8bd8bda7ad4cc398208c0ce88a9677.log`
- `/tmp/rpn_v3_nmhI8O1x/src/Chal3/AllStatements.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/ExactMatch3.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C1Rev.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C2Sign.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C2Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C3Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C4Glue.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C5Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C6Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C7Glue.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C8Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C9Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/Assembly.lean`
- `/tmp/rpn_v3_nmhI8O1x/logs/AllStatements.log`
- `/tmp/rpn_v3_nmhI8O1x/logs/ExactMatch3.log`
- `/tmp/rpn_v3_nmhI8O1x/logs/ExactMatch3_fresh.log`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract and Submission (sha256 ea3ee0dd…). IsMassMeasure T μ is μ(Uᶜ) = 0 ∧ μ(W) = M_W(T) for open W ⊂⊂ U, and IsMeasureRepresentation requires integrability and T(ω) = ∫ξ(x)(ω(x))dμ. These are exactly the facts the parent assembly uses.
The pinned Mathlib supplies every analytic tool the children cite:
 – polar coordinates: toSphere_apply_univ and measurePreserving_homeomorphUnitSphereProd (HaarToSphere.lean:87,142), integral_fun_norm_addHaar and integrableOn_fun_norm_addHaar (:296,273);
 – smoothness of convolutions: HasCompactSupport.contDiff_convolution_right and hasFDerivAt_convolution_right (ContDiff/Convolution.lean:420,61);
 – ray FTC: integral_Ioi_of_hasDerivAt_of_tendsto (IntegralEqImproper.lean:786);
 – shrinking neighbourhoods: tendsto_measure_thickening_of_isClosed (BorelSpace/Metric.lean:160), IsCompact.exists_cthickening_subset_open (Thickening.lean:426);
 – inner regularity: MeasurableSet.exists_isClosed_lt_add and WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure (Regular.lean:1031,1072);
 – signs and exterior derivative: Fin.sign_cycleRange, cycleRange_symm_zero/succ (Perm/Fin.lean:225,258,262) and extDeriv (DifferentialForm/Basic.lean:72);
 – smooth Urysohn functions: exists_contMDiffMap_zero_one_of_isClosed (PartitionOfUnity.lean:492).
SimonGMT supplies massOn, le_massOn, massAdmissibleOn, covectorEuclideanNorm (Chapter06/Mass.lean), wedgeCovectors, wedgeCovectors_apply_det, covectorPullback_wedgeCovectors, SimonMultiIndex, euclideanNVectorCoordinate (FormsDuality.lean), and TestFormOn and exteriorDerivativeTestOn (Currents.lean).
No match: there is no Newtonian or Riesz potential and no fundamental solution of the Laplacian in Mathlib/Analysis or Mathlib/MeasureTheory. Chapter02/BV.lean states that compactness remains a separate obligation. Hence the self-contained potential_estimate child replaces Remark 2.35.
Re-verification. The nine frozen types, the frozen parent type and the sibling type elaborate under the comparator's own header. A generated exact-match harness proves every child type and the parent implication with only propext, Classical.choice and Quot.sound.
Formalization aid for child workers (not part of any natural proof). Sorry-free Lean witnesses of each child's exact frozen type are in /tmp/rpn_v3_nmhI8O1x/src/Scratch (identical copies in /tmp/rpn_v2_Yfpb0s4j/src/Scratch); all build on GMT.Ch06.Submission:
 – potential_estimate: C1Rev.lean, theorem rpn_potential_estimate_review;
 – potential_form_derivative: C2Sign.lean, then C2Full.lean, theorem c2_full;
 – mass_bound_opnorm: C3Full.lean, c3_full;
 – pullback_top_form_bound: C4Glue.lean, c4_glue, taking the three dependency types as hypotheses;
 – covector_rotated_expansion: C5Full.lean, c5_full;
 – null_compact_cutoff: C6Full.lean, c6_full;
 – mass_off_compact: C7Glue.lean, c7_glue, from its three dependencies;
 – compact_null: C8Full.lean, c8_full;
 – borel_null: C9Full.lean, c9_full;
 – the selected node's glue: Assembly.lean, assembly.
JsonConsistency.lean and EndToEnd.lean restate the exact JSON types.
