# Parent-supplied natural-language proof

- Parent DAG node: `root.gauss_green-a1`
- Child DAG node: `root.gauss_green-a1.riesz_on_open-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 1, Theorem 4.14 (Riesz Representation Theorem, chapter-01.txt lines 1654-1663): “Suppose X is a locally compact Hausdorff space, and L : C_c(X; H) → ℝ is linear with sup_{f ∈ C_c(X;H), |f| ≤ 1, support f ⊂ K} L(f) < ∞ whenever K ⊂ X is compact. Then there is a Radon measure μ on X and μ-measurable ν : X → H with |ν| = 1 μ-a.e. on X, and L(f) = ∫_X ⟨f, ν⟩ dμ for any f ∈ C_c(X; H)”. It is used with X := U and H := ℝ^N exactly as in Simon Ch. 2, (2.1)-(2.2) (chapter-02.txt lines 485-496). The passage from U to ℝ^N and the Borel version of ν are Step 5 of the parent proof, written out here. Call g : ℝ^N → ℝ^N admissible if g is continuous with compact support and tsupport g ⊆ U.

1. The space U. With the subspace topology, U is:
- Hausdorff;
- locally compact, as an open subset of the locally compact space ℝ^N (in Lean this instance is supplied by IsOpen.locallyCompactSpace);
- second countable, hence σ-compact (Mathlib sigmaCompactSpace_of_locallyCompact_secondCountable).
Its Borel σ-algebra is the trace {B ∩ U : B Borel in ℝ^N}. The inclusion ι : U → ℝ^N is a measurable embedding whose range U is Borel. A set A ⊆ U is compact in U iff ι(A) is compact in ℝ^N.

2. Extension by zero. For f ∈ C_c(U; ℝ^N) define f̃ : ℝ^N → ℝ^N by f̃(x) := f(x) if x ∈ U and f̃(x) := 0 otherwise. T := ι(tsupport f) is compact in ℝ^N and contained in U, hence closed in ℝ^N. Since f̃ = 0 on ℝ^N ∖ T, tsupport f̃ ⊆ T ⊆ U and f̃ has compact support. f̃ is continuous: on the open set U it coincides with the continuous map f, on the open set ℝ^N ∖ T it is identically 0, and these two open sets cover ℝ^N. Thus f̃ is admissible. Moreover:
- (f + f')~ = f̃ + f̃' and (c f)~ = c f̃;
- |f̃| ≤ 1 if |f| ≤ 1;
- tsupport f̃ ⊆ ι(K) whenever tsupport f ⊆ K with K ⊆ U compact, since ι(K) is closed in ℝ^N.

3. Restriction. If g is admissible then f := g ∘ ι is continuous on U and vanishes outside ι^{-1}(tsupport g). That set is compact in U (tsupport g is a compact subset of U) and closed in U; hence f ∈ C_c(U; ℝ^N). Moreover f̃ = g, since g(x) = 0 for x ∉ U (such x lie outside tsupport g ⊆ U).

4. The functional on U. Define L : C_c(U; ℝ^N) → ℝ by L(f) := Λ(f̃). By step 2 and the additivity and homogeneity of Λ on admissible fields, L is ℝ-linear. It satisfies the hypothesis of Theorem 4.14. If K ⊆ U is compact, ι(K) is a compact subset of ℝ^N contained in U, so there is C with Λ(g) ≤ C for every continuous g with tsupport g ⊆ ι(K) and |g| ≤ 1. For f ∈ C_c(U; ℝ^N) with |f| ≤ 1 and tsupport f ⊆ K, f̃ is such a g (step 2), so L(f) ≤ C. (This is SimonGMT's IsLocallyBoundedCcFunctional L.)

5. Riesz representation on U. Apply Theorem 4.14, formalized for arbitrary locally compact Hausdorff X and finite-dimensional H as SimonGMT Chapter01.simon_theorem_4_14. The version with the Borel measure made explicit is Chapter01.simon_theorem_4_14_caratheodory, used with X := U (with its Borel σ-algebra) and H := ℝ^N. Let μ₀ := vectorFunctionalEnvelopeMeasure L, a regular Borel measure on U, in particular finite on compact subsets of U. There is ν₁ : U → ℝ^N, measurable for the Carathéodory σ-algebra of the outer measure μ₀* induced by μ₀, such that |ν₁| = 1 μ̄₀-a.e. and L(f) = ∫_U ⟨f, ν₁⟩ dμ̄₀ for every f ∈ C_c(U; ℝ^N). Here μ̄₀ (SimonGMT radonCaratheodoryMeasure μ₀) is μ₀* restricted to its Carathéodory σ-algebra. So μ̄₀(A) = μ₀*(A) for every A ⊆ U, and μ̄₀ = μ₀ on Borel sets.

6. A Borel version of ν₁.
(a) The outer measure μ₀* of the Borel measure μ₀ is Borel regular (SimonGMT measure_toOuterMeasure_isBorelRegular, equivalently (vectorFunctionalEnvelopeMeasure_isRadon L).borel_regular).
(b) Since U is σ-compact and μ₀ is finite on compact sets, μ₀* is σ-finite on open sets (SimonGMT isOpenSigmaFinite_of_finite_compacts).
(c) Hence every μ₀*-Carathéodory-measurable A ⊆ U contains a Borel set B with μ₀*(A ∖ B) = 0 (SimonGMT IsBorelRegularOuterMeasure.exists_borel_subset_mod_null), so A is μ₀-null-measurable.
(d) Apply (c) to the sets ν₁^{-1}(B), B Borel in ℝ^N; each is Carathéodory-measurable because ν₁ is measurable for the Carathéodory σ-algebra. So ν₁ is μ₀-null-measurable.
(e) The Borel σ-algebra of ℝ^N is countably generated, so ν₁ is μ₀-a.e. measurable (Mathlib NullMeasurable.aemeasurable). That is, there are a Borel map ν₂ : U → ℝ^N and a μ₀-null set Z with ν₁ = ν₂ on U ∖ Z.
(f) As μ̄₀(Z) = μ₀*(Z) = 0, also ν₁ = ν₂ μ̄₀-a.e. Consequently {y : |ν₂(y)| ≠ 1} ⊆ Z ∪ {y : |ν₁(y)| ≠ 1} is μ̄₀-null. Being Borel, it is μ₀-null, so |ν₂| = 1 μ₀-a.e.
(g) For f ∈ C_c(U; ℝ^N): L(f) = ∫⟨f, ν₁⟩ dμ̄₀ = ∫⟨f, ν₂⟩ dμ̄₀ = ∫⟨f, ν₂⟩ dμ₀. The last equality holds because ⟨f, ν₂⟩ is Borel measurable and μ̄₀ restricted to the Borel σ-algebra is μ₀ (SimonGMT integral_radonCaratheodoryMeasure).

7. Push-forward to ℝ^N. Let μ := ι_# μ₀, i.e. μ(B) := μ₀(ι^{-1}(B)) = μ₀(B ∩ U) for Borel B ⊆ ℝ^N. Define ν : ℝ^N → ℝ^N by ν(x) := ν₂(x) for x ∈ U and ν(x) := 0 for x ∉ U. Then:
(a) μ(ℝ^N ∖ U) = μ₀(∅) = 0;
(b) for compact K ⊆ U, ι^{-1}(K) is compact in U (step 1), so μ(K) = μ₀(ι^{-1}(K)) < ∞;
(c) ν is Borel measurable (ν₂ is Borel on U and U is a Borel set), hence strongly measurable (ℝ^N is second countable), in particular μ-a.e. strongly measurable;
(d) μ({x : |ν(x)| ≠ 1}) = μ₀({y : |ν₂(y)| ≠ 1}) = 0 (the set is Borel), so |ν| = 1 μ-a.e.;
(e) for admissible g, let f := g ∘ ι (step 3, so f̃ = g). Then Λ(g) = Λ(f̃) = L(f) = ∫_U ⟨g(ι y), ν₂(y)⟩ dμ₀(y) = ∫_U ⟨g(ι y), ν(ι y)⟩ dμ₀(y) = ∫_{ℝ^N} ⟨g(x), ν(x)⟩ dμ(x). The last step is the change-of-variables formula for the push-forward under the measurable embedding ι (Mathlib MeasurableEmbedding.integral_map).

8. Conclusion. μ and ν satisfy:
- μ(ℝ^N ∖ U) = 0;
- μ(K) < ∞ for every compact K ⊆ U;
- ν is μ-a.e. strongly measurable and |ν| = 1 μ-a.e.;
- Λ(g) = ∫⟨g, ν⟩ dμ for every admissible g.

## Key steps

1. Extension by zero identifies C_c(U; ℝ^N) with the admissible fields; L(f) := Λ(f̃) is linear and bounded on unit fields supported in each compact K ⊆ U.
2. Simon Ch. 1, Theorem 4.14 (SimonGMT simon_theorem_4_14 / simon_theorem_4_14_caratheodory) on X = U gives the Radon measure μ₀ and a Carathéodory-measurable unit field ν₁ representing L.
3. σ-compactness of U makes Carathéodory-measurable sets μ₀-null-measurable, so ν₁ has a Borel version ν₂ with the same integrals and |ν₂| = 1 μ₀-a.e.
4. Push forward: μ := ι_#μ₀, ν := ν₂ on U and 0 off U; μ vanishes off U, is finite on compacts of U, ν is Borel with |ν| = 1 μ-a.e.
5. Change of variables under the measurable embedding ι gives Λ(g) = ∫⟨g, ν⟩dμ for every admissible g.

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
