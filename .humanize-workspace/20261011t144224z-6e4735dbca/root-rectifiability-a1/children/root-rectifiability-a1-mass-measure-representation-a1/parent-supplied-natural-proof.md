# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1`
- Child DAG node: `root.rectifiability-a1.mass_measure_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, (2.7)-(2.8) (p. 136): ‘by the Riesz Representation Theorem 4.14 of Ch. 1 we have that if T ∈ D_n(U) satisfies M_W(T) < ∞ for every open W ⊂⊂ U, then there is a Radon measure μ_T on U and μ_T-measurable T⃗ with values in Λ_n(ℝ^P), |T⃗| = 1 μ_T-a.e., such that T(ω) = ∫_U ⟨ω(x), T⃗(x)⟩ dμ_T(x); μ_T is characterized by μ_T(W) = M_W(T) = sup_{ω ∈ D^n(U), |ω| ≤ 1, spt ω ⊆ W} T(ω) for any open W with closure a compact subset of U’ (printed with n in place of our k). The printed argument is expanded below (extension of T to continuous forms, the mass formula (2.8), a Borel version of T⃗); part (ii) adds the identification of an arbitrary measure μ with IsMassMeasure T μ with μ_T (uniqueness of measures that agree on a generating π-system). Throughout, |·| is the Euclidean coefficient norm of Simon 6, Remark 2.6: covectorEuclideanNorm on covectors (the norm used in massOn) and its dual norm on k-vectors.

1. Coordinates and norms. Let I := I(k,P) be the set of strictly increasing α : {1,…,k} → {1,…,P} (SimonMultiIndex k P), N := #I = binom(P,k), e_α := (e_{α(1)},…,e_{α(k)}) and dx^α := dx^{α(1)}∧⋯∧dx^{α(k)} (wedgeCovectors k (proj ∘ α)). By the determinant formula (wedgeCovectors_apply_det), dx^α(e_β) = δ_{αβ} for α, β ∈ I. A k-covector φ (continuous alternating k-linear form) is determined by its values on increasing tuples of basis vectors, hence φ = Σ_{α∈I} φ(e_α) dx^α and |φ| = (Σ_α φ(e_α)²)^{1/2} = covectorEuclideanNorm φ. Put c(φ) := (φ(e_α))_{α∈I} ∈ ℝ^N; c is a linear isometric bijection from (k-covectors, |·|) onto Euclidean ℝ^N. For a k-vector w (continuous linear functional on k-covectors) put w_α := w(dx^α) = euclideanNVectorCoordinate w α and |w| := (Σ_α w_α²)^{1/2}. Then w(φ) = Σ_α φ(e_α) w_α = ⟨c(φ), (w_α)_α⟩, so |w(φ)| ≤ |φ| |w|, and w ↦ (w_α)_α is a linear bijection onto ℝ^N.

2. Degenerate case N = 0 (k > P). Then every k-covector is 0, every test form is 0, T = 0 and M_W(T) = 0 for all W. The zero measure satisfies IsMassMeasure T 0, proving (i). If μ satisfies IsMassMeasure T μ, then μ(W) = 0 for every open W ⊂⊂ U and μ(ℝ^P∖U) = 0; as U is a countable union of such W (step 3), μ = 0, and ξ :≡ 0 satisfies (ii) (the a.e. condition is vacuous for the zero measure and T(ω) = 0 = ∫ 0 dμ). From now on N ≥ 1.

3. Exhaustion. U is open in ℝ^P, hence locally compact and σ-compact: there are compact K_q with ⋃_q K_q = U and, by local compactness, open W_q with K_q ⊆ W_q ⊆ closure(W_q) ⊆ U and closure(W_q) compact; replacing W_q by W_1 ∪ ⋯ ∪ W_q we may assume W_q ↑. Each W_q is open and W_q ⊂⊂ U (CompactlyContainedOpen), U = ⋃_q W_q, every compact K ⊆ U lies in some W_q (finitely many W_q cover K), and M_{W_q}(T) < ∞.

4. Mass bound. If W ⊂⊂ U is open, ω ∈ D^k(U), tsupport ω ⊆ W and s := sup_x |ω(x)| > 0, then ±ω/s are admissible in the definition of M_W(T) (massOn: smooth test forms with tsupport in W and |·| ≤ 1 everywhere), so |T(ω)| ≤ s·M_W(T). If s = 0 then ω = 0 and T(ω) = 0.

5. Extension to continuous forms. Let K^k(U) be the space of continuous k-forms g on ℝ^P whose support is a compact subset of U; via c it is C_c(U, ℝ^N). Given g, choose an open W ⊂⊂ U containing spt g and a standard mollifier ϕ_σ (smooth, ≥ 0, ∫ϕ_σ = 1, spt ϕ_σ ⊆ B_σ(0)). For σ < dist(spt g, ℝ^P∖W) the coefficientwise convolution g_σ := ϕ_σ * g is a smooth form with compact support in W (so g_σ ∈ D^k(U) and tsupport g_σ ⊆ W), |g_σ(x)| ≤ sup|g| (g_σ(x) is an average of values of g and |·| is a norm), and g_σ → g uniformly as σ ↓ 0. By step 4, |T(g_σ) − T(g_{σ′})| ≤ M_W(T) sup|g_σ − g_{σ′}| → 0, so L(g) := lim_{σ↓0} T(g_σ) exists; by step 4 again it does not depend on W or on the smooth approximations supported in a fixed W ⊂⊂ U. L is linear; L(ω) = T(ω) for ω ∈ D^k(U) (|T(ω_σ) − T(ω)| ≤ M_W(T) sup|ω_σ − ω| → 0); and |L(g)| ≤ M_W(T) sup|g| whenever spt g ⊆ W ⊂⊂ U. In particular, for each compact K ⊆ U (say K ⊆ W_q), sup{L(g) : g ∈ K^k(U), |g| ≤ 1, spt g ⊆ K} ≤ M_{W_q}(T) < ∞.

6. Riesz representation (Simon Ch. 1, Theorem 4.14, with X := U, a locally compact Hausdorff space, and H := ℝ^N; SimonGMT simon_theorem_4_14_caratheodory, with the local boundedness hypothesis hL supplied by step 5). Let μ_T := vectorFunctionalEnvelopeMeasure L hL, a Radon measure on U. There is a Carathéodory-measurable ν : U → ℝ^N with |ν| = 1 μ_T-a.e. and L(g) = ∫_U ⟨c(g(x)), ν(x)⟩ dμ_T(x) for all g ∈ K^k(U), the integral being taken for the completion radonCaratheodoryMeasure μ_T. Moreover, by SimonGMT simon_theorem_4_14_positive_envelope (the equality (†) in the printed proof of 4.14), ∫ f dμ_T = λ(f) := sup{L(g) : g ∈ K^k(U), |g| ≤ f} for every f ∈ C_c(U, [0,∞)). Hence for every open W ⊆ U:
 μ_T(W) = sup{∫ f dμ_T : f ∈ C_c(W), 0 ≤ f ≤ 1} = sup{λ(f) : f ∈ C_c(W), 0 ≤ f ≤ 1} = sup{L(g) : g ∈ K^k(U), |g| ≤ 1, spt g ⊆ W};
 the first equality is inner regularity of Radon measures on open sets together with Urysohn's lemma; for the last, |g| ≤ f ≤ 1 with spt f ⊆ W gives |g| ≤ 1 and spt g ⊆ W, and conversely, for |g| ≤ 1 with compact spt g ⊆ W, Urysohn's lemma gives f ∈ C_c(W) with 0 ≤ f ≤ 1 and f = 1 on spt g, so |g| ≤ f.

7. Mass identity (2.8). Let W ⊂⊂ U be open. Every form ω admissible for M_W(T) lies in K^k(U) with |ω| ≤ 1 and spt ω ⊆ W, and L(ω) = T(ω); hence M_W(T) ≤ μ_T(W) (massOn is the supremum of ofReal(T(ω)) over admissible ω; since ω = 0 is admissible this is the supremum of the T(ω)). Conversely, for g ∈ K^k(U) with |g| ≤ 1 and spt g ⊆ W, the forms g_σ of step 5 (σ < dist(spt g, ℝ^P∖W)) are admissible for M_W(T) and T(g_σ) → L(g), so L(g) ≤ M_W(T). By step 6, μ_T(W) = M_W(T).

8. Proof of (i). Define the Borel measure μ₀ on ℝ^P by μ₀(A) := μ_T(A ∩ U). Then μ₀(ℝ^P∖U) = 0, and μ₀(W) = μ_T(W) = M_W(T) for every open W ⊂⊂ U by step 7. Hence IsMassMeasure T μ₀.

9. Uniqueness. Let μ be any Borel measure on ℝ^P with IsMassMeasure T μ. Let 𝒞 := {W : W open, W ⊂⊂ U} ∪ {A : A Borel, A ∩ U = ∅}. 𝒞 is closed under finite intersections: W₁ ∩ W₂ is open with closure contained in the compact set closure(W₁) ⊆ U; W ∩ A = ∅, and ∅ is an open set ⊂⊂ U; (A ∩ A′) ∩ U = ∅. 𝒞 generates the Borel σ-algebra: every open O equals (O∖U) ∪ ⋃_q (O ∩ W_q), where O∖U ∈ 𝒞 and each O ∩ W_q is open and ⊂⊂ U. μ and μ₀ agree on 𝒞 (both equal M_W(T) on open W ⊂⊂ U and both vanish on Borel subsets of ℝ^P∖U). The sets W_q (q ∈ ℕ) and ℝ^P∖U belong to 𝒞, have finite μ-measure (M_{W_q}(T) < ∞, resp. 0) and cover ℝ^P. By the uniqueness theorem for measures agreeing on a generating π-system with such a cover (Mathlib Measure.ext_of_generateFrom_of_iUnion), μ = μ₀. In particular μ(K) < ∞ for every compact K ⊆ U.

10. The field ξ. Since ν is μ_T-measurable with values in ℝ^N, there is a Borel map ν̃ : ℝ^P → ℝ^N with ν̃ = ν μ_T-a.e. on U. Redefine ν̃(x) := (1, 0, …, 0) on the Borel set (ℝ^P∖U) ∪ {x : |ν̃(x)| ≠ 1}; the new ν̃ is Borel, |ν̃| ≡ 1, and still ν̃ = ν μ_T-a.e. on U (because |ν| = 1 μ_T-a.e.). Define ξ(x) ∈ Λ_k(ℝ^P) by ξ(x)(φ) := ⟨c(φ), ν̃(x)⟩ = Σ_α φ(e_α) ν̃_α(x). The map x ↦ ξ(x) is Borel into the finite-dimensional normed space Λ_k(ℝ^P) (its coordinates are Borel), hence strongly measurable; and ξ(x)(dx^α) = ν̃_α(x), since c(dx^α) is the α-th unit vector, so Σ_α (euclideanNVectorCoordinate (ξ x) α)² = |ν̃(x)|² = 1 for every x, in particular for μ-a.e. x.

11. Representation. Let ω ∈ D^k(U); its support is a compact subset of U, contained in some W_q. The function x ↦ ξ(x)(ω(x)) = ⟨c(ω(x)), ν̃(x)⟩ is Borel, bounded by sup|ω|, and vanishes outside spt ω, which has finite μ-measure (step 9); so it is μ-integrable. By steps 5, 6 and 9, and since ω vanishes outside U: T(ω) = L(ω) = ∫_U ⟨c(ω(x)), ν(x)⟩ dμ_T(x) = ∫_U ⟨c(ω(x)), ν̃(x)⟩ dμ_T(x) = ∫_{ℝ^P} ξ(x)(ω(x)) dμ₀(x) = ∫ ξ(x)(ω(x)) dμ(x). Thus IsMeasureRepresentation T μ ξ, which together with step 10 proves (ii). ∎

## Key steps

1. Identify k-covectors with ℝ^N isometrically via φ ↦ (φ(e_α))_α (covectorEuclideanNorm) and k-vectors via w ↦ (w(dx^α))_α; the case k > P gives T = 0 and μ = 0.
2. The mass bound |T(ω)| ≤ sup|ω|·M_W(T) and mollification extend T to a locally bounded linear functional L on continuous compactly supported forms in U.
3. Simon Ch. 1, 4.14 (vector Riesz) gives a Radon measure μ_T on U and a unit field ν with L(g) = ∫⟨c(g), ν⟩dμ_T and μ_T(W) = sup{L(g) : |g| ≤ 1, spt g ⊆ W}.
4. Mollification shows this supremum equals M_W(T) for open W ⊂⊂ U, so μ₀ := μ_T(· ∩ U) satisfies IsMassMeasure T μ₀.
5. Any μ with IsMassMeasure T μ equals μ₀: both agree on the π-system of open W ⊂⊂ U and Borel sets missing U, which generates the Borel sets and has a countable finite-measure cover.
6. A Borel unit version ν̃ of ν defines a strongly measurable ξ with Σ_α ξ(x)(dx^α)² = 1, and T(ω) = ∫ξ(ω)dμ with μ-integrable integrand.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean; cmp Contract.lean Submission.lean (all identical)`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurePreserving_homeomorphUnitSphereProd|theorem ae_tendsto_average_norm_sub|theorem exists_disjoint_subfamily_covering_enlargement|theorem haarMeasure_unique|theorem addHaar_image_linearMap' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'euclideanHausdorffMeasure_eq_volume|LipschitzOnWith.extend_real|contDiff_convolution_right|LipschitzWith.ae_differentiableAt|toSphere_apply_univ :|theorem ae_tendsto_measure_inter_div|theorem hausdorffMeasure_apply|measure_toMeasurable_inter|hausdorffMeasure_smul₀' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -c 'Besicovitch.Federer|purely unrectifiable|PurelyUnrectifiable|Mickle' local-references/197bdd4b88278494/mathlib/Mathlib (no match)`
- `grep -n '^theorem\|^def' simongmt Chapter03/{Rectifiable,SubmanifoldCover}.lean, Chapter02/{AreaLipschitz,AreaCritical,Area,AreaBranches,Lipschitz,BV,WhitneyExtension}.lean, Chapter01/{DensityComparison,HausdorffDensityBounds,HausdorffContentDensity,Lusin,Densities,RadonPolarRepresentation,VectorFunctionalEnvelope}.lean, Chapter06/{Mass,FormsDuality,Currents}.lean`
- `grep -n 'def massOn|def massAdmissibleOn|def covectorEuclideanNorm|abbrev SimonMultiIndex|def HasWeightedApproximateTangentSpaceAt|def PurelyUnrectifiable|def CountablyRectifiable' simongmt Chapter06/Mass.lean, Chapter06/FormsDuality.lean, Chapter03/Rectifiable.lean`
- `sed -n chapter-02.txt 140,330 (Ch.2 1.5-1.8); chapter-03.txt 1,560 (Ch.3 §1 and §3); chapter-06.txt 560,720 and 2130,2300 (2.34-2.37, 8.1)`
- `lake build GMT.Ch06.Submission (scratch /tmp/rect_a1_v2_check, frozen commit d8d46c9, pinned packages lake-packages-25730c7c)`
- `lake env lean Scratch/V2_Names.lean and Scratch/V2_Names2.lean (#check and #print axioms of every cited Mathlib/SimonGMT declaration)`
- `lake env lean Scratch/V2_Challenge.lean (12 child statements generated with verifier/gmt-compare.py contract_scope/child_modules; 0 errors)`
- `lake env lean Scratch/Assembly.lean, Scratch/C4fromC3.lean, Scratch/C5Check.lean, Scratch/V2_Glue.lean (#print axioms)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (86 DAG names; no rectifiability_* or mickle_* collision)`
- `python3 audit of nodes/root-rectifiability-a1/decomposition-v1.json and decomposition-audit-v1.json (accepted and rejected children, required changes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffContentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-audit-v1.json`
- `/tmp/rect_a1_v2_check/Scratch/V2_Challenge.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Names.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Names2.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Glue.lean`
- `/tmp/rect_a1_v2_check/Scratch/Assembly.lean`
- `/tmp/rect_a1_v2_check/Scratch/C4fromC3.lean`
- `/tmp/rect_a1_v2_check/Scratch/C5Check.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract; it is byte-identical to the workspace Contract and Submission. The pinned Mathlib has no Besicovitch-Federer, purely-unrectifiable or Mickle-Radó result (rg: no match), and SimonGMT has neither BV compactness (Chapter02/BV.lean proves only closure statements) nor the rectifiable-to-C¹ cover (SubmanifoldCover.lean proves only the converse). This confirms the three gaps the v1 audit identified. The pinned libraries do contain every ingredient that the rewritten proofs cite. Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255), MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821), LipschitzWith.ae_differentiableAt (Rademacher.lean:385), Measure.measurePreserving_homeomorphUnitSphereProd and toSphere_apply_univ (HaarToSphere.lean), IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub and ae_tendsto_measure_inter_div (DensityTheorem.lean), Besicovitch.ae_tendsto_measure_inter_div, Vitali.exists_disjoint_subfamily_covering_enlargement, Measure.haarMeasure_unique, Measure.addHaar_image_linearMap, hausdorffMeasure_apply, Measure.hausdorffMeasure_smul₀, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, LipschitzOnWith.extend_real, HasCompactSupport.contDiff_convolution_right and hasFDerivAt_convolution_right. SimonGMT: weighted_area_formula_lipschitz_injOn, area_image_criticalSet_eq_zero, linear_area_formula, euclideanHausdorffMeasure_image_le_of_lipschitzOn, simon_theorem_3_3, simon_theorem_3_6, IsBorelRegularOuterMeasure.simon_theorem_1_17, measurable_rectifiable_purelyUnrectifiable_decomposition, countablyRectifiable_range, simon_theorem_4_14_caratheodory and simon_theorem_4_14_positive_envelope. #print axioms gives [propext, Classical.choice, Quot.sound] for all of them. In the scratch build of the frozen project, all 12 child statements elaborate in the comparator's exact child scope (0 errors). Re-run with standard axioms only: the parent assembly from mass_measure_representation, mass_measure_rectifiable and orientation, the C4-from-C3 reduction, the C5 proof, and the glue lemmas v2_glue_rows, v2_glue_volume and v2_glue_infinite_density. The product-measure instance on Fin (m+1) → Eucl N was confirmed by rfl. No proposed lean_name collides with the 86 names in dag.json. These checks certify the statements, the assembly, the glue and the library inputs, not the new analytic proofs; three independent referees reviewed those (all ACCEPT after the minor fixes, which were applied).
