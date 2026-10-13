# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1`
- Child DAG node: `root.rectifiability-a1.bf_trichotomy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: P. Mattila, Geometry of Sets and Measures in Euclidean Spaces, Lemma 18.9. We use the version for transversal families of maps in R. Hovila, E. Järvenpää, M. Järvenpää and F. Ledrappier, Geom. Dedicata 161 (2012), arXiv:1104.3453, Lemma 2.4, whose alternatives (2.1)/(2.2)/(2.3) are (T1)/(T2)/(T3) here and whose proof is followed. The family is {L_v : v ∈ (ℝ^N)^k}, parametrized by the row vectors v. For it, the k-dimensional slices of the parameter space used in that proof are the affine families v ⊕_j c (c ∈ ℝᵏ) defined below, and the comparison between cones and unions of fibres becomes the exact inclusions (i), (ii) of step 4. The Mickle-Radó theorem used there ([Ma, 18.5]) is the sibling mickle_rado.

Notation: k := m + 1, Hᵏ := μHE[k], and μ := Hᵏ⌞E, i.e. μ(S) := Hᵏ(E ∩ S). Since E is σ-compact (hence Borel) and Hᵏ(E) < ∞, μ is a finite Borel measure on ℝ^N with Hᵏ(E ∩ S) = μ(S) for Borel S. X_v(a,r,s) is an open set not containing a. Further, F(a,v,s) := sup_{0<r<δ}(rs)^{−k}μ(X_v(a,r,s)), Φ(a,v) := limsup_{s↓0}F(a,v,s) ∈ [0,∞], and ℒ denotes Lebesgue measure on (ℝ^N)^k ≅ ℝ^{kN}.

1. Reduction to Φ ∈ {0,∞}. Let a ∈ E.
 If Φ(a,v) = 0, then (T1) holds. Given η > 0, F(a,v,s) < η for all small s > 0; pick such an s ∈ (0,1). Then for r ∈ (0,δ), Hᵏ(E ∩ X_v(a,r,s)) = μ(X_v(a,r,s)) ≤ F(a,v,s)(rs)ᵏ ≤ η(rs)ᵏ.
 If Φ(a,v) = ∞, then (T2) holds. Given Λ > 0 and ρ₀ > 0, there is s ∈ (0,ρ₀/δ) with F(a,v,s) > Λ, hence some r ∈ (0,δ) with μ(X_v(a,r,s)) > Λ(rs)ᵏ. Put ρ := rs < ρ₀. Every x ∈ X_v(a,r,s) has |L_vx − L_va| < s|x − a| < ρ. So ν_v(B̄(L_va,ρ)) ≥ μ(L_v^{−1}(B(L_va,ρ))) ≥ μ(X_v(a,r,s)) > Λρᵏ. Thus the density quotient ν_v(univ ∩ B̄(L_va,ρ))/(ω_kρᵏ) of dimensionalUpperDensity exceeds Λ/ω_k for arbitrarily small ρ > 0, so dimensionalUpperDensity ν_v k univ (L_va) = ∞.
 Hence it suffices to show: for ℒ-a.e. v and μ-a.e. a, either Φ(a,v) ∈ {0,∞} or (T3) holds. If N = 0, then ℝ^N is a point, X_v(a,r,s) = ∅, Φ ≡ 0, and (T1) always holds; so assume N ≥ 1 from now on.

2. Measurability.
 (a) The set {(x,a,v) : |x − a| < r, |L_v(x − a)| < s|x − a|} is open in ℝ^N × ℝ^N × (ℝ^N)^k. By Fatou's lemma, (a,v) ↦ μ(X_v(a,r,s)) is lower semicontinuous, hence Borel.
 (b) For fixed (a,v,s), r ↦ μ(X_v(a,r,s)) is nondecreasing and left continuous, because X_v(a,r,s) = ⋃_{r′<r}X_v(a,r′,s). So the supremum defining F may be taken over rational r ∈ (0,δ), and F is Borel in (a,v).
 (c) If 0 < s ≤ s′, then X_v(a,r,s) ⊆ X_v(a,r,s′), hence F(a,v,s) ≤ (s′/s)ᵏF(a,v,s′). Therefore the limsup defining Φ may be taken along rational s: for s_l ↓ 0 choose rational s′_l ∈ (s_l, s_l(1 + 1/l)). So Φ is Borel.
 (d) Write E = ⋃_iK_i with each K_i compact. The set T3 := {(a,v) : some x ∈ E has 0 < |x − a| < δ and L_v(x − a) = 0} is the union over i, l ∈ ℕ of the projections to (a,v) of the compact sets {(x,a,v) : x ∈ K_i, 1/l ≤ |x − a| ≤ δ − 1/l, |a| ≤ l, |v| ≤ l, L_v(x − a) = 0}. So T3 is σ-compact, hence Borel.
 Hence 𝔅 := {(a,v) : 0 < Φ(a,v) < ∞}∖T3 is Borel.

3. Fixed a: slices and Mickle-Radó. Fix a ∈ ℝ^N; we show ℒ({v : (a,v) ∈ 𝔅}) = 0.
 For j ∈ {1, …, N}, w ∈ (ℝ^N)^k and c ∈ ℝᵏ let w ⊕_j c := (w₁ + c₁e_j, …, w_k + c_ke_j). Then L_{w⊕_jc}(y) = L_w(y) + y_jc, where y_j := ⟨e_j,y⟩, and (w ⊕_j c) ⊕_j c′ = w ⊕_j (c + c′). For C ⊆ ℝᵏ let
 K_{j,w}(C) := {x ≠ a : L_{w⊕_jc}(x − a) = 0 for some c ∈ C} and ψ_{j,w}(C) := sup_{0<r<δ}r^{−k}Hᵏ(E ∩ B(a,r) ∩ K_{j,w}(C)).
 (a) ψ_{j,w} is an outer measure on ℝᵏ. It vanishes on ∅ and is monotone. Since K_{j,w}(⋃_iC_i) = ⋃_iK_{j,w}(C_i) and Hᵏ is countably subadditive, each set function C ↦ r^{−k}Hᵏ(E ∩ B(a,r) ∩ K_{j,w}(C)) is countably subadditive, and so is their supremum.
 (b) Let τ > 0. Solving L_w(x − a) + (x − a)_jc′ = 0 for c′ shows that K_{j,w}(B(c,τ)) = {x : |L_{w⊕_jc}(x − a)| < τ|(x − a)_j|} ∪ {x ≠ a : (x − a)_j = 0, L_w(x − a) = 0}, a Borel set. Also K_{j,w}(B(c,τ)) = ⋃_{τ′<τ}K_{j,w}(B(c,τ′)), an increasing union. By continuity from below of μ and interchanging suprema, ψ_{j,w}(B(c,τ)) = sup_{0<τ′<τ}ψ_{j,w}(B(c,τ′)). For τ ≤ 0 both sides are 0. Moreover K_{j,w}(B(c,t)) = K_{j,w⊕_jc}(B(0,t)), hence ψ_{j,w}(B(c,t)) = ψ_{j,w⊕_jc}(B(0,t)).
 (c) Let D_{j,w} := {c ∈ ℝᵏ : (T3) fails at (a, w ⊕_j c)}, i.e. the set of c for which no x ∈ E has 0 < |x − a| < δ and L_{w⊕_jc}(x − a) = 0. It is Borel, since its complement is the preimage of the Borel set T3 (step 2(d)) under the continuous map c ↦ (a, w ⊕_j c). Moreover ψ_{j,w}(D_{j,w}) = 0: for r < δ, any point of E ∩ B(a,r) ∩ K_{j,w}(D_{j,w}) would witness (T3) at some (a, w ⊕_j c) with c ∈ D_{j,w}.
 (d) Apply the sibling mickle_rado with ψ := ψ_{j,w} and D := D_{j,w}; its hypotheses are (a)-(c). It gives: for Lᵏ-a.e. c ∈ D_{j,w}, ϑ_{j,w}(c) := limsup_{t↓0}ψ_{j,w}(B(c,t))/tᵏ ∈ {0,∞}. By (b), ϑ_{j,w}(c) = ϑ_j(w ⊕_j c), where ϑ_j(u) := limsup_{t↓0}ψ_{j,u}(B(0,t))/tᵏ. Also c ∈ D_{j,w} iff (T3) fails at (a, w ⊕_j c).
 (e) The function u ↦ ϑ_j(u) is Borel. By (b), the set {(x,u) : x ∈ B(a,r) ∩ K_{j,u}(B(0,t))} is Borel in ℝ^N × (ℝ^N)^k, so u ↦ μ(B(a,r) ∩ K_{j,u}(B(0,t))) is Borel (Tonelli). The supremum over r may be taken over rationals (left continuity in r), and the limsup over t along rationals (monotonicity in t, as in 2(c)).
 Hence 𝔅_j := {u : (T3) fails at (a,u) and 0 < ϑ_j(u) < ∞} is Borel. Let W_j be the set of w ∈ (ℝ^N)^k whose rows have zero j-th coordinate. The map (w,c) ↦ w ⊕_j c identifies W_j × ℝᵏ with (ℝ^N)^k; it is a linear isomorphism that permutes coordinates, so ℒ is the product of the Lebesgue measures. For each w ∈ W_j, {c : w ⊕_j c ∈ 𝔅_j} = {c ∈ D_{j,w} : 0 < ϑ_{j,w}(c) < ∞}, which is Lᵏ-null by (d). By Fubini, ℒ(𝔅_j) = 0.

4. Cones versus unions of fibres. For every u ∈ (ℝ^N)^k, r ∈ (0,δ) and s > 0:
 (i) X_u(a,r,s) ⊆ ⋃_{j=1}^N(B(a,r) ∩ K_{j,u}(B(0,√N s))). Indeed, let x ∈ X_u(a,r,s); then x ≠ a. Choose j with |(x − a)_j| ≥ |x − a|/√N and put c := −L_u(x − a)/(x − a)_j. Then |c| < s|x − a|·√N/|x − a| = √N s, and L_{u⊕_jc}(x − a) = L_u(x − a) + (x − a)_jc = 0.
 (ii) B(a,r) ∩ K_{j,u}(B(0,s)) ⊆ X_u(a,r,s) for each j. Indeed, if x ≠ a, |x − a| < r and L_{u⊕_jc}(x − a) = 0 with |c| < s, then |L_u(x − a)| = |c||(x − a)_j| ≤ |c||x − a| < s|x − a|.
 By (ii), ψ_{j,u}(B(0,s)) ≤ sup_rr^{−k}μ(X_u(a,r,s)) = sᵏF(a,u,s), so ϑ_j(u) ≤ Φ(a,u).
 By (i) and subadditivity, (rs)^{−k}μ(X_u(a,r,s)) ≤ s^{−k}Σ_jψ_{j,u}(B(0,√N s)). Hence F(a,u,s) ≤ N^{k/2}Σ_jψ_{j,u}(B(0,√N s))/(√N s)ᵏ and Φ(a,u) ≤ N^{k/2}Σ_jϑ_j(u).
 Consequently, suppose (T3) fails at (a,u) and u ∉ ⋃_j𝔅_j. Then each ϑ_j(u) ∈ {0,∞}. If some ϑ_j(u) = ∞, then Φ(a,u) = ∞; otherwise Φ(a,u) = 0. Thus {u : (a,u) ∈ 𝔅} ⊆ ⋃_j𝔅_j, which is ℒ-null by 3(e).

5. Fubini in (a,v). 𝔅 is Borel (step 2) and every section {v : (a,v) ∈ 𝔅} is ℒ-null (step 4). So (μ ⊗ ℒ)(𝔅) = 0, and by Fubini, for ℒ-a.e. v the section {a : (a,v) ∈ 𝔅} is μ-null. For such v and μ-a.e. a, i.e. for a.e. a with respect to μHE[k] restricted to E, either Φ(a,v) ∈ {0,∞} or (T3) holds. Step 1 then gives (T1) ∨ (T2) ∨ (T3). ∎

## Key steps

1. Φ(a,v) = 0 gives (T1). Φ(a,v) = ∞ gives an infinite projected density (T2), since X_v(a,r,s) ⊆ L_v⁻¹(B(L_va, rs)).
2. All functions and sets involved are Borel (semicontinuity, reduction to rationals, σ-compact projections), so Fubini applies.
3. Fix a. Along each slice w ⊕_j c (c ∈ ℝᵏ), the outer measure ψ_{j,w}(C) = sup_r r⁻ᵏHᵏ(E ∩ B(a,r) ∩ ⋃_{c∈C}fibres) vanishes on the 'fibre not hit' set. So mickle_rado gives slice densities in {0,∞} a.e., and Fubini over the remaining coordinates extends this to a.e. matrix.
4. Exact inclusions between the cones X_u(a,r,s) and the fibre unions over B(0,s), resp. B(0,√N s), give ϑ_j ≤ Φ ≤ N^{k/2}Σ_jϑ_j, so Φ ∈ {0,∞} unless (T3) holds.
5. Fubini on Hᵏ⌞E ⊗ ℒ turns 'for every a, a.e. v' into 'for a.e. v, a.e. a'.

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
