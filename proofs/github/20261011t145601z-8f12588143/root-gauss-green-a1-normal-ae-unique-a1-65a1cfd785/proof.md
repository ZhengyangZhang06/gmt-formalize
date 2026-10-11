# Parent-supplied natural-language proof

- Parent DAG node: `root.gauss_green-a1`
- Child DAG node: `root.gauss_green-a1.normal_ae_unique-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 9 of the parent proof (uniqueness, step 4): continuous compactly supported fields are dense in L¹(μ⌞L; ℝ^N) for compact L ⊆ U, so the pairings determine the field μ-a.e. Details written out here.

1. Setup. Let w := ν − ν'; w is μ-a.e. strongly measurable and |w| ≤ 2 μ-a.e. Call g admissible if g is continuous with compact support and tsupport g ⊆ U. For admissible g, |⟨g, ν⟩| ≤ sup|g| · 1_{tsupport g} μ-a.e., and μ(tsupport g) < ∞ because tsupport g is a compact subset of U. So ⟨g, ν⟩ and likewise ⟨g, ν'⟩ are μ-integrable. By hypothesis and linearity of the integral, ∫⟨g, w⟩ dμ = 0 for every admissible g.

2. A compact neighbourhood. Fix a compact K ⊆ U; if K = ∅, the conclusion of step 5 is trivial. Choose δ > 0 with L := {x : dist(x, K) ≤ δ} ⊆ U (K compact, U open). L is compact, and V := {x : dist(x, K) < δ} is open with K ⊆ V ⊆ L. The measure μ⌞L is a finite Borel measure on ℝ^N, since μ(L) < ∞. Hence it is regular: finite, so locally finite, Borel measures on the σ-compact metric space ℝ^N are regular (Mathlib Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure).

3. Density. F := 1_K w is bounded and μ⌞L-integrable. Continuous compactly supported functions are dense in L¹ of a regular measure on a locally compact space (Mathlib Integrable.exists_hasCompactSupport_integral_sub_le). So for each i ≥ 1 there is a continuous compactly supported φ_i : ℝ^N → ℝ^N with ∫_L |F − φ_i| dμ ≤ 1/i.

4. Cut-off. By Urysohn's lemma (Mathlib exists_continuousMap_one_of_isCompact_subset_isOpen) let χ : ℝ^N → [0, 1] be continuous with χ = 1 on K, tsupport χ compact and tsupport χ ⊆ V. Put g_i := χ φ_i. Then g_i is continuous with tsupport g_i ⊆ tsupport χ ⊆ V ⊆ U compact, so g_i is admissible. Pointwise:
- on K, χ = 1 and F − g_i = F − φ_i;
- on L ∖ K, F = 0 and |F − g_i| = χ |φ_i| ≤ |φ_i| = |F − φ_i|;
- outside L, F = 0 = g_i.
Hence ∫|F − g_i| dμ ≤ ∫_L |F − φ_i| dμ ≤ 1/i. (The parent proof additionally truncates g_i by the radial retraction onto the ball of radius 2. That is harmless but unnecessary, because the estimate in step 5 only uses |w| ≤ 2.)

5. Passage to the limit. ⟨F, w⟩ = 1_K |w|² is μ-integrable, being bounded by 4 · 1_K with μ(K) < ∞. Moreover |∫⟨F, w⟩ dμ − ∫⟨g_i, w⟩ dμ| ≤ ∫ |F − g_i| |w| dμ ≤ 2/i. Since ∫⟨g_i, w⟩ dμ = 0 by step 1, letting i → ∞ gives ∫_K |w|² dμ = ∫⟨F, w⟩ dμ = 0. Therefore w = 0 μ-a.e. on K.

6. Globalization. U is open in ℝ^N, hence σ-compact: U = ⋃_j K_j with compact K_j ⊆ U. The set {x : w(x) ≠ 0} is contained in (ℝ^N ∖ U) ∪ ⋃_j (K_j ∩ {w ≠ 0}). Here μ(ℝ^N ∖ U) = 0 by hypothesis, and each K_j ∩ {w ≠ 0} is μ-null by step 5. Hence w = 0 μ-a.e., i.e. ν = ν' μ-a.e.

## Key steps

1. w := ν − ν' is bounded by 2 a.e. and ∫⟨g, w⟩dμ = 0 for all continuous compactly supported g with tsupport g ⊆ U.
2. For compact K ⊆ U, approximate 1_K w in L¹(μ⌞L) (L ⊆ U a compact neighbourhood, μ⌞L regular) by continuous compactly supported fields, then cut off inside L.
3. Pass to the limit to get ∫_K |w|² dμ = 0, so w = 0 μ-a.e. on K.
4. Exhaust U by compact sets and use μ(ℝ^N ∖ U) = 0 to conclude ν = ν' μ-a.e.

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
