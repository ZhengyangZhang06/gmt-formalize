# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_cap_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2.1 (a)–(c) of the supplied proof (Dall'Alba, Lemma 4.15; Mattila Ch. 18), written out. Notation: E := ℝ^{n+ℓ} = EuclideanSpace ℝ (Fin (n+ℓ)), x·y inner product, |·| norm, B(x, ρ) open ball, Hᵐ := μHE[m] (Euclidean Hausdorff measure, an outer measure on all subsets), S(H) := {θ ∈ H : |θ| = 1}, ofReal := ENNReal.ofReal. Two standard facts are used. (L) If f is L-Lipschitz on a set Y (L ≥ 0), then Hⁿ(f(Y)) ≤ Lⁿ Hⁿ(Y) (Mathlib LipschitzOnWith.hausdorffMeasure_image_le for μH[n], and μHE[n] is a positive constant multiple of μH[n]; SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn). (I) Hⁿ(f(Y)) = Hⁿ(Y) for an isometry f (Mathlib Isometry.euclideanHausdorffMeasure_image).

1. Flat balls. Let ℝⁿ := EuclideanSpace ℝ (Fin n) and ω_n := Hⁿ(B_{ℝⁿ}(0, 1)). On ℝⁿ, Hⁿ equals Lebesgue measure (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so 0 < ω_n < ∞ (a nonempty bounded open set; n ≥ 1). Also Hⁿ(B_{ℝⁿ}(z, ρ)) = ρⁿω_n for z ∈ ℝⁿ and ρ > 0 (Measure.addHaar_ball). Claim: for every n-dimensional subspace T ⊆ E, every w ∈ T and every ρ > 0, Hⁿ(T ∩ B(w, ρ)) = ω_nρⁿ. Proof: an orthonormal basis of T gives a linear isometry ι : ℝⁿ → E with ι(ℝⁿ) = T. Since ι is isometric onto T, T ∩ B(w, ρ) = ι(B_{ℝⁿ}(ι⁻¹w, ρ)). By (I) the measure is Hⁿ(B_{ℝⁿ}(ι⁻¹w, ρ)) = ω_nρⁿ.

2. Geometry at a point ζ. Fix ζ ∈ S(H). T_ζ := {w ∈ H : w·ζ = 0} is the kernel of the linear functional w ↦ w·ζ on H. This functional is nonzero (ζ·ζ = 1), so dim T_ζ = n. Let π_ζ : E → E be the orthogonal projection onto T_ζ; it is linear with operator norm ≤ 1, hence 1-Lipschitz, and π_ζζ = 0 since ζ ⊥ T_ζ. For ξ ∈ H we have π_ζξ = ξ − (ξ·ζ)ζ. Indeed ξ − (ξ·ζ)ζ ∈ H is orthogonal to ζ, so it lies in T_ζ, and ξ − (ξ − (ξ·ζ)ζ) = (ξ·ζ)ζ is orthogonal to T_ζ. For w ∈ T_ζ with |w| ≤ 1 put f(w) := (1 − |w|²)^{1/2} ∈ [0, 1] and Γ(w) := w + f(w)ζ. Then Γ(w) ∈ H, |Γ(w)|² = |w|² + f(w)² = 1 (w ⊥ ζ), so Γ(w) ∈ S(H), and π_ζΓ(w) = w.

3. Lower bound: c ρⁿ ≤ Hⁿ(S(H) ∩ B(ζ, ρ)) for 0 < ρ ≤ 2, with c := 2^{−n}ω_n > 0. Let w ∈ T_ζ with |w| < ρ/2 ≤ 1 and put t := |w|² ∈ [0, 1). Since 0 ≤ 1 − t ≤ 1, (1 − t)^{1/2} ≥ 1 − t, so 0 ≤ 1 − f(w) ≤ t and (1 − f(w))² ≤ t² ≤ t. As w ⊥ ζ, |Γ(w) − ζ|² = |w|² + (f(w) − 1)² ≤ 2t = 2|w|² < ρ²/2 < ρ². So Γ(w) ∈ S(H) ∩ B(ζ, ρ) and w = π_ζ(Γ(w)). Hence T_ζ ∩ B(0, ρ/2) ⊆ π_ζ(S(H) ∩ B(ζ, ρ)). By (L) with L = 1 and step 1 (T = T_ζ, w = 0): ω_n(ρ/2)ⁿ = Hⁿ(T_ζ ∩ B(0, ρ/2)) ≤ Hⁿ(π_ζ(S(H) ∩ B(ζ, ρ))) ≤ Hⁿ(S(H) ∩ B(ζ, ρ)).

4. Upper bound for small radii: Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ 2ⁿω_nρⁿ for 0 < ρ ≤ 1/2. Let ξ ∈ S(H) ∩ B(ζ, ρ). Then ξ·ζ = 1 − |ξ − ζ|²/2 > 1 − 1/8 > 0. Put w := π_ζξ = ξ − (ξ·ζ)ζ. Then |w|² = 1 − (ξ·ζ)², so ξ·ζ = f(w) (the positive root) and ξ = Γ(w). Moreover |w| = |π_ζ(ξ − ζ)| ≤ |ξ − ζ| < ρ. Hence S(H) ∩ B(ζ, ρ) ⊆ Γ(T_ζ ∩ B(0, ρ)). Let D := {w ∈ T_ζ : |w| ≤ 1/2}, which contains T_ζ ∩ B(0, ρ). On D, f ≥ (3/4)^{1/2} = √3/2. For w, w′ ∈ D, |f(w) − f(w′)| = ||w′|² − |w|²|/(f(w) + f(w′)) = (|w| + |w′|)·||w′| − |w||/(f(w) + f(w′)) ≤ 1·|w − w′|/√3 ≤ |w − w′|. Since w − w′ ⊥ ζ, |Γ(w) − Γ(w′)|² = |w − w′|² + (f(w) − f(w′))² ≤ 2|w − w′|². So Γ is 2-Lipschitz on D. By (L) and step 1, Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ Hⁿ(Γ(T_ζ ∩ B(0, ρ))) ≤ 2ⁿHⁿ(T_ζ ∩ B(0, ρ)) = 2ⁿω_nρⁿ.

5. Hⁿ(S(H)) < ∞. S(H) is closed and bounded in the finite-dimensional space E, hence compact. It is covered by the open balls B(ζ, 1/2), ζ ∈ S(H), so finitely many of them, B(ζ_1, 1/2), …, B(ζ_m, 1/2) with ζ_i ∈ S(H), cover it. By subadditivity and step 4 (with ρ = 1/2), Hⁿ(S(H)) ≤ Σ_i Hⁿ(S(H) ∩ B(ζ_i, 1/2)) ≤ m·2ⁿω_n2^{−n} = mω_n < ∞. Let σ ∈ [0, ∞) be the real number Hⁿ(S(H)).

6. Upper bound for all radii, with C := 2ⁿ max(ω_n, σ). Let ζ ∈ S(H) and ρ > 0. If ρ ≤ 1/2, step 4 gives Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ 2ⁿω_nρⁿ ≤ Cρⁿ. If ρ > 1/2, then 2ρ > 1, so (2ρ)ⁿ ≥ 1 and Hⁿ(S(H) ∩ B(ζ, ρ)) ≤ Hⁿ(S(H)) = σ ≤ σ(2ρ)ⁿ = 2ⁿσρⁿ ≤ Cρⁿ.

7. Conclusion. c = 2^{−n}ω_n > 0 and C depend only on n and H, not on ζ or ρ. Steps 3 and 6 give, for every ζ ∈ H with |ζ| = 1 and every ρ > 0: if ρ ≤ 2 then ofReal(cρⁿ) ≤ μHE[n]({θ | θ ∈ H ∧ |θ| = 1} ∩ B(ζ, ρ)); and μHE[n]({θ | θ ∈ H ∧ |θ| = 1} ∩ B(ζ, ρ)) ≤ ofReal(Cρⁿ). ∎

## Key steps

1. Hⁿ(T ∩ B(w, ρ)) = ω_nρⁿ for every n-plane T and w ∈ T (isometry with ℝⁿ, where Hⁿ is Lebesgue measure).
2. At ζ ∈ S(H), T_ζ := H ∩ ζ^⊥ is n-dimensional. The graph map Γ(w) = w + (1 − |w|²)^{1/2}ζ shows that T_ζ ∩ B(0, ρ/2) ⊆ π_ζ(S(H) ∩ B(ζ, ρ)). Since π_ζ is 1-Lipschitz, the lower bound 2^{−n}ω_nρⁿ follows for ρ ≤ 2.
3. For ρ ≤ 1/2, S(H) ∩ B(ζ, ρ) ⊆ Γ(T_ζ ∩ B(0, ρ)) and Γ is 2-Lipschitz on |w| ≤ 1/2, giving the upper bound 2ⁿω_nρⁿ.
4. Compactness of S(H) and finitely many caps of radius 1/2 give Hⁿ(S(H)) < ∞.
5. For ρ > 1/2 use Hⁿ(S(H)) ≤ Hⁿ(S(H))(2ρ)ⁿ, and set C := 2ⁿ max(ω_n, Hⁿ(S(H))).

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "^noncomputable def frameProjection|^def ForAlmostAllProjections|^abbrev Rn" project/GMT/Ch03/Contract.lean`
- `rg -n "instance instMeasurableSpace|instBorelSpace" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `rg -n "IsTopologicalGroup \(unitary|isClosed_unitary" mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `rg -l "CompactSpace \(unitary|instance.*CompactSpace.*orthogonalGroup" mathlib/Mathlib (no match)`
- `rg -n "isMulInvariant_eq_smul_of_compactSpace|isHaarMeasure_eq_of_isProbabilityMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `rg -n "theorem haarMeasure_self" mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `rg -n "μHE\[|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "theorem ae_tendsto_measure_inter_div" mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n "ext_of_forall_integral_eq_of_IsFiniteMeasure|ext_of_forall_lintegral_eq_of_IsFiniteMeasure" mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `rg -n "measurable_measure_prodMk_left|measurable_measure_prodMk_right" mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `rg -n "theorem hausdorffMeasure_image_le" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "exists_isClosed_sdiff_lt|exists_isClosed_diff_lt" mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n "theorem isClosedMap_fst_of_compactSpace" mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `grep -n isOpen_setOf_linearIndependent mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `rg -n "theorem inverse_continuousAt" mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `rg -n "theorem measurePreserving" mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; rg -n "theorem measurePreserving_pi" mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `rg -n "theorem addHaar_ball" mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n "theorem finrank_add_finrank_orthogonal" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `rg -n "theorem ContinuousOn.measurable_piecewise" mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `rg -n "theorem lintegral_liminf_le" mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `grep -n "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `grep dag.json for bf_coneExceptional_measurableSet, bf_sphereCap_measure_bounds, bf_sphere_ae_slabGood, bf_slabGood_imp_coneTrichotomy, bf_frameProjection_continuousOn, bf_frameAveraging_null (no match)`
- `lake env lean GMT/Scratch/ConeTrichotomySplitElab.lean and GMT/Scratch/ConeTrichotomySplitAssembly.lean (comparator scope: all child types elaborate; the parent assembly compiles without sorry)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ConeTrichotomySplitElab.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ConeTrichotomySplitAssembly.lean`

The snapshot fixes Rn, frameProjection and ForAlmostAllProjections (Contract.lean lines 56, 129, 138); the child types use them verbatim. Mathlib supplies every library ingredient that the child proofs cite: the Borel structure on E →L[ℝ] E (ContinuousLinearMap.instMeasurableSpace/instBorelSpace); the Haar measure with haarMeasure_self, and its uniqueness on compact groups (isMulInvariant_eq_smul_of_compactSpace, isHaarMeasure_eq_of_isProbabilityMeasure); and the unitary-group topology (IsTopologicalGroup (unitary R), isClosed_unitary), which needs a ContinuousStar instance on 𝓛 supplied locally from the continuity of the adjoint. It also supplies Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, the Lipschitz image bound (LipschitzOnWith.hausdorffMeasure_image_le; SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn), Vitali.exists_disjoint_subfamily_covering_enlargement, Besicovitch.ae_tendsto_measure_inter_div and MeasurableSet.exists_isClosed_sdiff_lt. Further cited results are measurable_measure_prodMk_left/right, isClosedMap_fst_of_compactSpace, isOpen_setOfPred_linearIndependent, NormedRing.inverse_continuousAt, LinearIsometryEquiv.measurePreserving, measurePreserving_pi, MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure, ContinuousOn.measurable_piecewise, Measure.addHaar_ball and Submodule.finrank_add_finrank_orthogonal. The searches found no CompactSpace instance for O(N), no Haar measure on O(N) and no Besicovitch–Federer material, so frame_averaging builds these itself. No existing declaration states any of the six children, and all six names are fresh in dag.json.
