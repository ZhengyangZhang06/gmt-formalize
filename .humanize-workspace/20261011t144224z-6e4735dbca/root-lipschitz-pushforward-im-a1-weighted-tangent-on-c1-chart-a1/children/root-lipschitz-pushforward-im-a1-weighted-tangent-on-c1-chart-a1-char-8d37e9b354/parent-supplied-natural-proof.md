# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions: ℝ^P = EuclideanSpace ℝ (Fin P) = Eucl P with norm |·|; Hⁿ = μHE[n] (Mathlib's Euclidean-normalized n-dimensional Hausdorff measure, = μHE[n] : Measure (Eucl P)); on ℝⁿ, Hⁿ = Lⁿ = volume (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). B̄_ρ(y) = closedBall y ρ. η_{y,λ}(x) = λ⁻¹(x − y) is `Poincare.SimonGMT.Chapter03.blowUpMap y λ`. ∫_A f dHⁿ is the Bochner set integral (0 when f is not integrable on A); ∫⁻ is the [0,∞]-valued lintegral. 'T is the approximate tangent space of S at y' means `Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y T` (Simon Ch. 3, Def. 1.4): finrank T = n and ∫_{η_{y,λ}(S)} φ dHⁿ → ∫_T φ dHⁿ as λ → 0+ for every φ ∈ C_c(ℝ^Q, ℝ). `HasWeightedApproximateTangentSpaceAt n M θ y T` (Def. 1.7) means finrank T = n and ∫_{η_{y,λ}(M)} φ(z) θ(y + λz) dHⁿ(z) → θ(y) ∫_T φ dHⁿ as λ → 0+ for every φ ∈ C_c(ℝ^Q, ℝ).

This is the injective area formula used in item 0(e) of the parent proof (Simon Ch. 2, (3.1), (3.2), (3.5)), specialized to a C¹ antilipschitz chart and test functions h ∈ C_c.

1. (The Jacobian.) For a linear map L : ℝⁿ → ℝ^Q, Mathlib's LinearMap.normDet satisfies normDet(L) ≥ 0 and normDet(L)² = det of the Gram matrix (⟨L b_i, L b_j⟩)_{i,j} for any orthonormal basis b of ℝⁿ (`LinearMap.normDet_nonneg`, `LinearMap.normDet_sq_eq_det_gram`). Using the orthonormal basis `EuclideanSpace.basisFun`, whose vectors are e_i = EuclideanSpace.single i 1 (`EuclideanSpace.basisFun_apply`), we get √det(⟨Le_i, Le_j⟩) = √(normDet(L)²) = normDet(L). Hence JΦ(v) = normDet(DΦ(v)) ≥ 0 for every v; this is Simon's Jacobian √det(DΦ(v)*DΦ(v)). In SimonGMT notation (Poincare/SimonGMT/Chapter02/AreaDomain.lean) areaJacobianWithin Φ s v := normDet(fderivWithin ℝ Φ s v), and for s open and v ∈ s we have fderivWithin ℝ Φ s v = fderiv ℝ Φ v, so areaJacobianWithin Φ s v = JΦ(v).
 Moreover JΦ is continuous: v ↦ DΦ(v) is continuous because Φ is C¹; each Gram entry ⟨DΦ(v)e_i, DΦ(v)e_j⟩ is therefore continuous in v; the determinant is a polynomial in the entries (`Continuous.matrix_det`); and √ is continuous.

2. (Reduction to a bounded open set.) Let K := tsupport h, a compact set; h(z) ≠ 0 implies z ∈ K. If Ω ∩ Φ⁻¹(K) = ∅, then h(Φ(v)) = 0 for all v ∈ Ω and h = 0 on Φ(Ω), so both sides are 0. Otherwise fix w₀ ∈ Ω ∩ Φ⁻¹(K), let ρ := diam(K)/c + 1 and s := Ω ∩ B_ρ(w₀) (open ball), an open bounded set. For v ∈ Ω ∩ Φ⁻¹(K), c|v − w₀| ≤ |Φ(v) − Φ(w₀)| ≤ diam K < cρ, so Ω ∩ Φ⁻¹(K) ⊆ s. Consequently:
 (a) the integrand v ↦ JΦ(v)h(Φ(v)) vanishes on Ω ∖ s, so ∫_Ω JΦ(v)h(Φ(v)) dLⁿ = ∫_s JΦ(v)h(Φ(v)) dLⁿ;
 (b) Φ(Ω) ∩ K ⊆ Φ(s) ⊆ Φ(Ω), so h vanishes on Φ(Ω) ∖ Φ(s) and ∫_{Φ(Ω)} h dHⁿ = ∫_{Φ(s)} h dHⁿ. Here Φ(Ω) and Φ(s) are Borel by the Lusin–Souslin theorem (`MeasurableSet.image_of_continuousOn_injOn`; Φ is continuous and, by step 3, injective on Ω).

3. (Φ on s.) Φ is injective on Ω (if Φ(v) = Φ(v′) then c|v − v′| ≤ 0), hence on s. DΦ is continuous, hence bounded by some Λ ∈ ℝ≥0 on the compact convex set B̄_ρ(w₀) ⊇ s, so by the mean value inequality (`Convex.lipschitzOnWith_of_nnnorm_fderiv_le`) Φ is Λ-Lipschitz on B̄_ρ(w₀), in particular on s. Let J_max := max of JΦ on B̄_ρ(w₀) (continuous on a compact set). Also Lⁿ(s) < ∞, and Hⁿ(Φ(s)) ≤ Λⁿ Lⁿ(B̄_ρ(w₀)) < ∞ (`LipschitzOnWith.hausdorffMeasure_image_le`, μHE[n] = κ_n • μH[n], and μHE[n] = Lⁿ on ℝⁿ).

4. (Injective weighted area formula.) SimonGMT `Chapter02.weighted_area_formula_lipschitzOn_fiberSum` (Simon Ch. 2, 3.2 and 3.5): if s ⊆ ℝⁿ is Lebesgue measurable, Φ is Lipschitz on s and ω : ℝⁿ → [0, ∞] is a.e.-measurable for Lⁿ⌞s, then
 ∫⁻ (∑_{x ∈ s, Φ(x) = z} ω(x)) dHⁿ(z) = ∫⁻_s ofReal(areaJacobianWithin Φ s x) · ω(x) dLⁿ(x),
 where the fibre sum is `weightedAreaFiberSum s Φ ω z` and Hⁿ = μHE[finrank ℝ ℝⁿ] = μHE[n]. Because Φ is injective on s, the fibre {x ∈ s : Φ(x) = z} has at most one element: the fibre sum equals ω(x_z) if z = Φ(x_z) with x_z ∈ s, and 0 if z ∉ Φ(s). Write h⁺ := max(h, 0), h⁻ := max(−h, 0) (continuous, compactly supported, ≥ 0) and apply the formula with ω := ofReal ∘ h⁺ ∘ Φ, resp. ω := ofReal ∘ h⁻ ∘ Φ (continuous, hence measurable). The fibre sum becomes the indicator of Φ(s) applied to ofReal ∘ h^±, and with step 1 (areaJacobianWithin Φ s = JΦ on s) we obtain
 ∫⁻_{Φ(s)} ofReal(h^±(z)) dHⁿ(z) = ∫⁻_s ofReal(JΦ(v)) · ofReal(h^±(Φ(v))) dLⁿ(v) = ∫⁻_s ofReal(JΦ(v)h^±(Φ(v))) dLⁿ(v).

5. (Finiteness and the signed identity.) The right-hand sides are ≤ J_max · sup|h| · Lⁿ(s) < ∞, so both identities are between finite numbers. Since h is continuous, bounded, and Hⁿ(Φ(s)) < ∞, h is Hⁿ-integrable on Φ(s); since JΦ·(h∘Φ) is continuous and bounded on s and Lⁿ(s) < ∞, it is Lⁿ-integrable on s. Because JΦ ≥ 0, the positive and negative parts of JΦ·(h∘Φ) are JΦ·(h⁺∘Φ) and JΦ·(h⁻∘Φ). Writing each Bochner integral as the difference of the lintegrals of the positive and negative parts (`integral_eq_lintegral_pos_part_sub_lintegral_neg_part`) and subtracting the two identities of step 4 gives ∫_{Φ(s)} h dHⁿ = ∫_s JΦ(v)h(Φ(v)) dLⁿ(v).

6. (Conclusion.) Combining with step 2(a),(b): ∫_{Φ(Ω)} h dHⁿ = ∫_{Φ(s)} h dHⁿ = ∫_s JΦ·(h∘Φ) dLⁿ = ∫_Ω JΦ(v)h(Φ(v)) dLⁿ(v), where Lⁿ is `volume` on EuclideanSpace ℝ (Fin n). ∎ (For n = 0: ℝ⁰ is a point, the empty Gram determinant is 1, H⁰ is counting measure and L⁰ the unit point mass, and the identity reads h(Φ(0)) = h(Φ(0)) or 0 = 0; the argument above covers this case. No case distinction between n ≤ Q and n > Q is needed.)

Lean note: `weighted_area_formula_lipschitzOn_fiberSum` and `areaJacobianWithin` live in Poincare.SimonGMT.Chapter02.AreaDomain, `LinearMap.normDet` in Mathlib.Analysis.InnerProductSpace.NormDet and `MeasurableSet.image_of_continuousOn_injOn` in Mathlib.MeasureTheory.Constructions.Polish.Basic; these modules are not imported by the frozen Contract, so import them where this lemma is proved and re-check that the frozen statement still elaborates unchanged.

## Key steps

1. JΦ(v) = √det Gram(DΦ(v)e_i) = normDet(DΦ(v)) ≥ 0 (normDet_sq_eq_det_gram with EuclideanSpace.basisFun), equal to SimonGMT's areaJacobianWithin on open sets, and continuous in v.
2. Reduce to the bounded open set s = Ω ∩ B(w₀, diam(tsupport h)/c + 1), which contains Ω ∩ Φ⁻¹(tsupport h); Φ is injective and Lipschitz on s.
3. Apply the injective weighted area formula (SimonGMT weighted_area_formula_lipschitzOn_fiberSum) with weights ofReal(h^±∘Φ); injectivity turns the fibre sum into the indicator of Φ(s).
4. All quantities are finite; subtract positive and negative parts and extend from s, Φ(s) back to Ω, Φ(Ω).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 listing of dag.json nodes (id, lean_name, status, lean_statement) for root.lipschitz_pushforward_im-a1.* (no lpf_wtc_* names reserved)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') loaded from verifier/gmt-compare.py to produce the child-scope prefix; lean_contract.validate_lean_statement on all 9 child statements`
- `lake build GMT.Ch06.Submission in /tmp/wtc_scratch_7f3a (packages symlinked to lake-packages-25730c7c); lake env lean Scratch/Stmts.lean, Scratch/Stmt3.lean (LinearMap.normDet not in scope, so the Gram-determinant Jacobian is used), Scratch/Names.lean, Scratch/Names2.lean (env.contains for every cited lemma), Scratch/NodeChallenges.lean, Scratch/NodeChallengesExtra.lean, Scratch/Assembly.lean (#print axioms tparent), Scratch/BlowupCheck.lean`
- `sed -n 1,420p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt, HasWeightedApproximateTangentSpaceAt, .unique)`
- `grep -n 'simon_theorem_3_6' -A30 simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean; sed -n 1,44p Chapter01/Densities.lean; grep -n 'def simonHausdorffMeasureReal|def realUnitBallVolume|def IsBorelRegularOuterMeasure' Chapter01/*.lean`
- `rg -n '^theorem' simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean; sed -n 1,146p Chapter02/AreaDomain.lean; rg -n 'def weightedAreaFiberSum|def areaFiber' Chapter02; rg -n 'simonAreaNormalization_eq_one|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure' Chapter02; sed -n 300,320p Chapter01/Basic.lean (measure_toOuterMeasure_isBorelRegular)`
- `rg -n '^theorem|^def|^instance' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean and mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean; sed -n 40,145p Measure.lean; sed -n 260,450p NormDet.lean`
- `rg -n 'exists_isClosed_sdiff_lt' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean; rg -n 'theorem rpow_natCast' mathlib/Mathlib/Analysis/SpecialFunctions/Pow/; rg -n 'MeasurableSet.image_of_continuousOn_injOn' mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `grep -n '1.6|1.7|1.8|Remark' book/chapter-03.txt; sed -n 55,145p and 270,330p book/chapter-03.txt (Remark 1.3, Def. 1.4, Remark 1.5(3), proof of 1.6 ⇒, Def. 1.7, Remark 1.8)`
- `git show humanize-recursive/gmt-ch06/20261011t144224z-6e4735dbca/root-compactness-mass-bounds-a1-exhaustion-a1-a1:GMT/Ch06/Submission.lean (accepted children are declared as theorem Submission.X inside namespace GMT.Ch06)`
- `sed -n 243,362p and 514,591p verifier/gmt-compare.py (child scope replay; Submission and new GMT/Ch06/*.lean files may change; frozen inputs byte-checked)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/wtc_scratch_7f3a/Scratch/Assembly.lean`
- `/tmp/wtc_scratch_7f3a/Scratch/NodeChallenges.lean`
- `/tmp/wtc_scratch_7f3a/Scratch/NodeChallengesExtra.lean`
- `/tmp/wtc_scratch_7f3a/Scratch/BlowupCheck.lean`

The snapshot pins project d8d46c95 and Mathlib 25730c7c; Submission.lean is byte-identical to the frozen Ch06 Contract.

The child scope (import GMT.Ch06.Submission plus the replayed opens) contains:
- SimonGMT Ch03 blowUpMap, HasApproximateTangentSpaceAt (Simon Def. 1.4, by full name) and HasWeightedApproximateTangentSpaceAt (1.7);
- Matrix.det, EuclideanSpace.single, inner;
- the μHE lemmas (euclideanHausdorffMeasure_smul₀, homothety_image, eq_volume).

It lacks LinearMap.normDet and SimonGMT Ch01 DensityComparison/Lusin and Ch02 AreaDomain/AreaLiteral. The area Jacobian is therefore written as the Gram determinant √det(⟨DΦ eᵢ, DΦ eⱼ⟩), which equals normDet by Mathlib normDet_sq_eq_det_gram. The child proofs may import those modules; all statements still elaborate with them.

Library support confirmed to exist:
- Mathlib Isometry.euclideanHausdorffMeasure_image, MeasurableEquiv.restrict_map, MeasurableEmbedding.integral_map, integral_smul_measure, LipschitzOnWith.hausdorffMeasure_image_le, Convex.lipschitzOnWith_of_nnnorm_fderiv_le, MeasurableSet.image_of_continuousOn_injOn, tendsto_integral_filter_of_dominated_convergence, MeasurableSet.exists_isClosed_sdiff_lt;
- SimonGMT weighted_area_formula_lipschitzOn_fiberSum (injective area formula), exists_isClosed_continuousOn_of_measurable (Lusin), simon_theorem_3_6 and ae_dimensionalUpperDensity_eq_zero_outside (Upper Density Theorem), measure_toOuterMeasure_isBorelRegular, and simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (Simon's Hⁿ = μHE[n]).

No existing declaration states the chart blow-up, the tangent transfers, or the Lusin pieces, so these become new children. Their lpf_wtc_* names are not reserved in dag.json.

All 9 statements pass the lexical validator and elaborate in the exact comparator scope. The frozen parent is kernel-checked from the 9 sorry'd child statements, and the blow-up child was fully proved in Lean with only standard axioms.
