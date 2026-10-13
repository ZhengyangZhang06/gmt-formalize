# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.projection_null-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1.pullback_top_form_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 of the parent proof (its Claim and that Claim's proof), for a general linear map L in place of π_α = p_α∘Q.
Notation: λ_i := y^i∘L for i ∈ Fin n, and λ := wedgeCovectors n λ = L^*dy. For j ∈ Fin n, θ_j := wedgeCovectors m (λ∘j.succAbove) is an (n−1)-covector and η_j(x) := wedgeCovectors n (Fin.cons (Df(x)) (λ∘j.succAbove)) is an n-covector. ‖·‖ is the operator norm on covectors.

1. Constants. Let C₁ be the constant of the sibling potential_estimate for this m. Let F₀ := sup_x |f(x)| < ∞, finite because f is continuous with compact support. The map Λ_j : γ ↦ wedgeCovectors n (Fin.cons γ (λ∘j.succAbove)) = Alt(γ.smulRight θ_j) is a continuous linear map on the finite-dimensional space of 1-covectors (Alt = alternatizeUncurryFin), and η_j(x) = Λ_j(Df(x)). Since f is C^∞, x ↦ Df(x) is continuous. It vanishes outside tsupport f, because f vanishes on the open set ℝ^P ∖ tsupport f. Hence η_j is continuous with compact support, η_j(x) = 0 for x ∉ tsupport f, and H_j := sup_x ‖η_j(x)‖ < ∞. Let B₀ and B₁ be M_W(T) and M_W(∂T) as real numbers. Both are finite, so B₀, B₁ ≥ 0, M_W(T) ≤ ofReal B₀ and M_W(∂T) ≤ ofReal B₁. Define
 C := C₁·(P^m·B₁·F₀·Σ_j‖θ_j‖ + P^{m+1}·B₀·Σ_j H_j).
 C depends only on T, W, f and L.

2. The potential. Fix a, M and φ as in the statement. The sibling potential_estimate gives C^∞ functions ψ_j : ℝⁿ → ℝ (j ∈ Fin n) with Σ_j ∂_jψ_j = a on ℝⁿ and |ψ_j(y)| ≤ R := C₁·M·Lⁿ(tsupport a)^{1/n} for all j and y. Note R ≥ |ψ_0(0)| ≥ 0.

3. The (n−1)-form Φ. Define Φ(z) := Σ_j (−1)^j f(z)ψ_j(Lz)·θ_j. Each coefficient z ↦ (−1)^j f(z)ψ_j(Lz) is C^∞, so Φ is C^∞. If f(z) = 0 then Φ(z) = 0, so support Φ ⊆ support f. Hence tsupport Φ ⊆ tsupport f ⊆ W ⊆ U, and tsupport Φ is compact. So Φ ∈ D^m(U) = D^{n−1}(U).

4. dΦ = φ + Ξ. f is differentiable at every x and ψ_j at every Lx, and Σ_j ∂_jψ_j(Lx) = a(Lx). So the sibling potential_form_derivative gives, for every x,
 dΦ(x) = f(x)a(Lx)·λ + Σ_j (−1)^jψ_j(Lx)·η_j(x) = φ(x) + Σ_j (−1)^jψ_j(Lx)·η_j(x).
 dΦ = exteriorDerivativeTestOn U m Φ is a test form, and Dⁿ(U) is a vector space, so Ξ := dΦ − φ ∈ Dⁿ(U). For every x, Ξ(x) = Σ_j (−1)^jψ_j(Lx)·η_j(x). In particular Ξ(x) = 0 for x ∉ tsupport f, so tsupport Ξ ⊆ tsupport f ⊆ W.

5. Splitting. Since φ = dΦ − Ξ and T is linear, T(φ) = T(dΦ) − T(Ξ) = ∂T(Φ) − T(Ξ), where ∂T(Φ) = T(dΦ) by the definition of ∂T.

6. Pointwise bounds. For every z,
 ‖Φ(z)‖ ≤ Σ_j |f(z)|·|ψ_j(Lz)|·‖θ_j‖ ≤ F₀·R·Σ_j‖θ_j‖, and
 ‖Ξ(z)‖ ≤ Σ_j |ψ_j(Lz)|·‖η_j(z)‖ ≤ R·Σ_j H_j.

7. Mass bounds. Apply the sibling mass_bound_opnorm to the m-current ∂T, the test form Φ (tsupport Φ ⊆ W) and B₁: |∂T(Φ)| ≤ P^m·B₁·F₀·R·Σ_j‖θ_j‖. Apply it to T, Ξ (tsupport Ξ ⊆ W) and B₀: |T(Ξ)| ≤ P^{m+1}·B₀·R·Σ_j H_j.

8. Conclusion. By Steps 5 and 7,
 |T(φ)| ≤ |∂T(Φ)| + |T(Ξ)| ≤ R·(P^m B₁ F₀ Σ_j‖θ_j‖ + P^{m+1} B₀ Σ_j H_j) = C·M·Lⁿ(tsupport a)^{1/n}. ∎

## Key steps

1. Fix constants that do not depend on a: C₁ from potential_estimate, F₀ = sup|f|, H_j = sup_x‖Df(x)∧θ_j‖ (continuous with compact support), B₀ = M_W(T) and B₁ = M_W(∂T).
2. Take ψ from potential_estimate: Σ_j∂_jψ_j = a and |ψ_j| ≤ R = C₁·M·Lⁿ(tsupport a)^{1/n}.
3. Φ := Σ_j(−1)^j f·(ψ_j∘L)·θ_j is a test (n−1)-form with tsupport Φ ⊆ tsupport f ⊆ W.
4. potential_form_derivative gives dΦ = φ + Ξ with Ξ = Σ_j(−1)^j(ψ_j∘L)·(Df∧θ_j), and tsupport Ξ ⊆ W.
5. T(φ) = ∂T(Φ) − T(Ξ). Bound both terms with mass_bound_opnorm, using ‖Φ‖ ≤ F₀RΣ_j‖θ_j‖ and ‖Ξ‖ ≤ RΣ_jH_j.

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
