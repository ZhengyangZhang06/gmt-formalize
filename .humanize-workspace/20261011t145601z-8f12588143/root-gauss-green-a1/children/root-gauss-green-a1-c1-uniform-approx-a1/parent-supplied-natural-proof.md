# Parent-supplied natural-language proof

- Parent DAG node: `root.gauss_green-a1`
- Child DAG node: `root.gauss_green-a1.c1_uniform_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the mollification step behind Simon Ch. 2, §2, (2.1): the remark that ∫ u div g extends from C¹ fields to continuous compactly supported fields (chapter-02.txt lines 485-490). The mollifier φ_σ(x) = σ^{-n} φ(x/σ) is introduced at chapter-02.txt lines 530-534. Step 4 of the parent proof fills this in: “the mollifications g_σ := φ_σ * g are C^∞ with support in the σ-neighbourhood of K ⊆ W and g_σ → g uniformly as σ → 0”.

1. Notation. Let S := tsupport g; S is compact and S ⊆ W. For r > 0 let S_r := {x ∈ ℝ^N : dist(x, S) ≤ r} (S_r := ∅ if S = ∅). Each S_r is closed and bounded, hence compact.

2. Choice of K. Since S is compact, W is open and S ⊆ W, there is δ > 0 with S_δ ⊆ W. If S = ∅ or W = ℝ^N this is trivial. Otherwise the continuous function x ↦ dist(x, ℝ^N ∖ W) is positive on S because ℝ^N ∖ W is closed, so it attains a positive minimum 2δ on S. If dist(x, S) ≤ δ, pick s ∈ S with |x − s| ≤ δ; then dist(x, ℝ^N ∖ W) ≥ 2δ − δ > 0, so x ∈ W. (Mathlib: IsCompact.exists_cthickening_subset_open.) Put K := S_δ. Then K is compact and tsupport g = S ⊆ K ⊆ W.

3. Uniform continuity. A continuous map with compact support is uniformly continuous on ℝ^N (Mathlib: HasCompactSupport.uniformContinuous_of_continuous). For each k ∈ ℕ fix ε_k with 0 < ε_k ≤ δ such that |g(x) − g(y)| ≤ 1/(k+1) whenever |x − y| < ε_k.

4. Mollifiers. Fix φ ∈ C_c^∞(ℝ^N) with φ ≥ 0, φ = 0 outside B_1(0) and ∫ φ dL^N = 1. For σ > 0 set φ_σ(z) := σ^{−N} φ(z/σ); then φ_σ ≥ 0, φ_σ = 0 outside B_σ(0) and ∫ φ_σ dL^N = 1. Define h_k := φ_{ε_k} * g, i.e. h_k(x) = ∫ φ_{ε_k}(x − y) g(y) dL^N(y) = ∫ φ_{ε_k}(z) g(x − z) dL^N(z).

5. Smoothness. g is bounded, continuous and compactly supported, hence locally integrable, and φ_{ε_k} is C^∞ with compact support. Differentiating under the integral sign, h_k is C^∞ with D^α h_k = (D^α φ_{ε_k}) * g (Mathlib: HasCompactSupport.contDiff_convolution_left). In particular each h_k is C¹.

6. Supports. Let x satisfy dist(x, S) ≥ ε_k.
- If |z| < ε_k, then dist(x − z, S) ≥ dist(x, S) − |z| > 0, so x − z ∉ S and g(x − z) = 0.
- If |z| ≥ ε_k, then φ_{ε_k}(z) = 0.
Hence h_k(x) = 0. Thus {h_k ≠ 0} ⊆ {x : dist(x, S) < ε_k} ⊆ S_{ε_k}. As S_{ε_k} is closed, tsupport h_k ⊆ S_{ε_k} ⊆ S_δ = K. Since tsupport h_k is a closed subset of the compact set K, h_k has compact support.

7. Uniform convergence. Fix x ∈ ℝ^N. Since ∫ φ_{ε_k} = 1, φ_{ε_k} ≥ 0 and φ_{ε_k}(z) = 0 for |z| ≥ ε_k,
|h_k(x) − g(x)| = |∫ φ_{ε_k}(z) (g(x − z) − g(x)) dz| ≤ ∫_{|z| < ε_k} φ_{ε_k}(z) |g(x − z) − g(x)| dz ≤ 1/(k+1).
Hence sup_x |h_k(x) − g(x)| ≤ 1/(k+1) → 0, i.e. h_k → g uniformly on ℝ^N.

8. Conclusion. K from step 2 and (h_k) from steps 4-7 have all the required properties:
- K is compact with tsupport g ⊆ K ⊆ W;
- each h_k is C¹ with compact support and tsupport h_k ⊆ K;
- h_k → g uniformly.
If S = ∅ then g = 0, K = ∅ and every h_k = 0, consistent with the above.

Formalization note (does not change the argument): Mathlib's Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean), applied with radius ε_k, produces exactly such a C^∞ convolution h_k. It satisfies dist(h_k(a), g(a)) ≤ η whenever dist(g(x), g(a)) ≤ η for all x ∈ B_{ε_k}(a). Taking η = 0 at points a with dist(a, S) ≥ ε_k gives step 6, and η = 1/(k+1) gives step 7.

## Key steps

1. Choose δ > 0 so that the closed δ-neighbourhood K of S = tsupport g lies in W; K is compact and contains S.
2. Using uniform continuity of g pick ε_k ≤ δ and mollify: h_k := φ_{ε_k} * g is C^∞.
3. h_k vanishes wherever dist(·, S) ≥ ε_k, so tsupport h_k ⊆ K and h_k has compact support.
4. sup_x |h_k(x) − g(x)| ≤ 1/(k+1), so h_k → g uniformly.

## Reference use

### local-project

Queries:
- `diff project/GMT/Ch03/Contract.lean <workspace>/GMT/Ch03/Contract.lean (identical); grep -n '### 11' -A 6 project/GMT/Ch03/README.md`
- `cat Poincare/SimonGMT/Chapter02/BV.lean (IsLocallyBV, IsRelativelyCompactIn, IsC1TestField, euclideanDivergence, support_euclideanDivergence_subset, compactlySupportedSupNorm)`
- `cat Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `grep -n 'theorem simon_theorem_4_14' -A 40 Poincare/SimonGMT/Chapter01/*.lean`
- `grep -n '^theorem\|^def\|^noncomputable def\|^instance' Poincare/SimonGMT/Chapter01/{RadonFieldGluing,RadonLocalDualField,LocalFiniteL1Dual,FiniteL1Dual,VectorFunctionalL1,PolarFieldNorm,RadonLocalMeasurability,RadonCompactDecomposition,RadonRepresentation,VectorFunctionalEnvelope}.lean`
- `grep -n 'def \|theorem \|instance' Poincare/SimonGMT/Chapter01/{RadonOuterMeasure,RadonCaratheodoryIntegral,Radon,RegularityCompletion,Regularity}.lean; sed -n 180,236p RadonOuterMeasure.lean`
- `grep -n 'exists_isClosed_continuousOn_of_measurable\|simon_theorem_1_17' Poincare/SimonGMT/Chapter01/Lusin.lean`
- `rg -n 'convolution_tendsto_right|dist_normed_convolution_le|exists_contDiff_dist_le_of_forall_mem_ball_dist_le|HasCompactSupport.contDiff_convolution_left' mathlib/Mathlib/Analysis`
- `rg -n -i 'lusin' mathlib/Mathlib`
- `rg -n 'instance.*TietzeExtension|TietzeExtension.of' mathlib/Mathlib`
- `rg -n 'exists_hasCompactSupport_integral_sub_le|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|Subtype.borelSpace|NullMeasurable.aemeasurable|MeasurableEmbedding.integral_map' mathlib/Mathlib`
- `rg -n 'exists_cthickening_subset_open|IsCompact.cthickening|uniformContinuous_of_continuous|exists_continuousMap_one_of_isCompact_subset_isOpen|exists_open_between_and_isCompact_closure|IsOpen.locallyCompactSpace|ext_of_generate_finite|isPiSystem_isOpen|integral_indicator₀|tendsto_integral_of_dominated_convergence|sigmaCompactSpace_of_locallyCompact_secondCountable' mathlib/Mathlib`
- `rg -n 'borel_eq_generateFrom_isOpen|^def borel|theorem BorelSpace.measurable_eq' mathlib/Mathlib`
- `lake env lean on a scratch file: import GMT.Ch03.Submission + contract scope; elaborate the 8 child statements and an assembly theorem (children 2-8 as hypotheses ⇒ GaussGreenRepresentation); #print axioms`
- `python3 dag.json scan for reserved lean_name collisions with prefix gaussGreenRep_`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Complex/Tietze.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RegularityCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Radon.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonLocalDualField.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`

The snapshot (project d09bc8a, Mathlib 25730c7c; Contract.lean identical to the workspace contract) marks GaussGreenRepresentation as new. SimonGMT's Chapter03.FinitePerimeterRepresentation only packages a pair as data and is not used.

Available and cited by the children:
- SimonGMT Chapter02.IsLocallyBV, euclideanDivergence, support_euclideanDivergence_subset and compactlySupportedSupNorm (children 2, 3).
- The vector Riesz theorem Chapter01.simon_theorem_4_14 / simon_theorem_4_14_caratheodory on arbitrary locally compact Hausdorff X, with vectorFunctionalEnvelopeMeasure (Regular, isRadon), radonCaratheodoryMeasure_apply, integral_radonCaratheodoryMeasure, measure_toOuterMeasure_isBorelRegular, isOpenSigmaFinite_of_finite_compacts and IsBorelRegularOuterMeasure.exists_borel_subset_mod_null (child 4).
- The real-valued Lusin theorem Chapter01.exists_isClosed_continuousOn_of_measurable (child 6).
- Mathlib Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le, HasCompactSupport.contDiff_convolution_left, IsCompact.exists_cthickening_subset_open, IsCompact.cthickening and HasCompactSupport.uniformContinuous_of_continuous (child 1).
- Mathlib Tietze instances RCLike.instTietzeExtensionTVS and Set.instTietzeExtensionUnitClosedBall, and Urysohn exists_continuousMap_one_of_isCompact_subset_isOpen (children 6, 8).
- Mathlib Integrable.exists_hasCompactSupport_integral_sub_le with Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (child 8).
- Mathlib ext_of_generate_finite and isPiSystem_isOpen, with borel defined as generateFrom of the open sets (child 7).
- Mathlib NullMeasurable.aemeasurable, MeasurableEmbedding.integral_map, Subtype.borelSpace, IsOpen.locallyCompactSpace and sigmaCompactSpace_of_locallyCompact_secondCountable (child 4).
- Mathlib tendsto_integral_of_dominated_convergence and integral_indicator₀ (children 2, 3, 5).

No match, hence supplied as children: Mathlib has no Lusin continuity theorem (only Lusin separation / Lusin–Souslin in Constructions/Polish/Basic.lean), no lemma named borel_eq_generateFrom_isOpen, and no vector Riesz representation on open subsets. SimonGMT has no mollification extension of BV functionals, no Riesz theorem pushed forward to the ambient space with a Borel normal, no total-variation formula, and no uniqueness of Gauss–Green pairs.

All 8 frozen statements elaborate against GMT.Ch03.Submission in the contract scope. The assembly from children 2-8 to GaussGreenRepresentation compiles using only the axioms propext, Classical.choice and Quot.sound.
