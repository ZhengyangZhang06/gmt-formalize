# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.density_bound_of_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions: ℝ^P = EuclideanSpace ℝ (Fin P) = Eucl P with norm |·|; Hⁿ = μHE[n] (Mathlib's Euclidean-normalized n-dimensional Hausdorff measure, = μHE[n] : Measure (Eucl P)); on ℝⁿ, Hⁿ = Lⁿ = volume (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). B̄_ρ(y) = closedBall y ρ. η_{y,λ}(x) = λ⁻¹(x − y) is `Poincare.SimonGMT.Chapter03.blowUpMap y λ`. ∫_A f dHⁿ is the Bochner set integral (0 when f is not integrable on A); ∫⁻ is the [0,∞]-valued lintegral. 'T is the approximate tangent space of S at y' means `Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y T` (Simon Ch. 3, Def. 1.4): finrank T = n and ∫_{η_{y,λ}(S)} φ dHⁿ → ∫_T φ dHⁿ as λ → 0+ for every φ ∈ C_c(ℝ^Q, ℝ). `HasWeightedApproximateTangentSpaceAt n M θ y T` (Def. 1.7) means finrank T = n and ∫_{η_{y,λ}(M)} φ(z) θ(y + λz) dHⁿ(z) → θ(y) ∫_T φ dHⁿ as λ → 0+ for every φ ∈ C_c(ℝ^Q, ℝ).

This is the boundedness part of Simon Ch. 3, Remark 1.5(3) (the remark at the end of item 0(e) of the parent proof). It uses the sibling result
 (BLOWUP) for r′ > 0, any S and any g: ∫_{η_{y,r′}(S)} g dHⁿ = (r′ⁿ)⁻¹ ∫_S g(η_{y,r′}(x)) dHⁿ(x).
Let μ := μHE[n] on ℝ^Q and fix r > 0 with μ(S ∩ B̄_r(y)) < ∞.

1. (A cut-off function.) Let φ₀(z) := min(1, max(0, 2 − |z|)). Then φ₀ is continuous, 0 ≤ φ₀ ≤ 1, φ₀ = 1 on B̄_1(0) and φ₀ = 0 outside B̄_2(0); so φ₀ has compact support and defines an element of C_c(ℝ^Q, ℝ). Put L₀ := ∫_T φ₀ dHⁿ, a real number with L₀ ≥ 0 (φ₀ ≥ 0).

2. (Convergence.) By the tangent hypothesis, ∫_{η_{y,ρ}(S)} φ₀ dHⁿ → L₀ as ρ → 0+, so there is ρ₁ > 0 with ∫_{η_{y,ρ}(S)} φ₀ dHⁿ ≤ L₀ + 1 for all 0 < ρ < ρ₁.

3. (Comparison.) Let 0 < ρ < min(ρ₁, r/2). By (BLOWUP), ∫_{η_{y,ρ}(S)} φ₀ dHⁿ = (ρⁿ)⁻¹ ∫_S ψ dμ with ψ(x) := φ₀(η_{y,ρ}(x)) = φ₀(ρ⁻¹(x − y)). ψ is continuous, 0 ≤ ψ ≤ 1, ψ = 1 on B̄_ρ(y) and ψ = 0 outside B̄_{2ρ}(y). Since μ(S ∩ B̄_{2ρ}(y)) ≤ μ(S ∩ B̄_r(y)) < ∞, ψ is μ⌞S-integrable (bounded, measurable, vanishing outside a set of finite μ⌞S-measure), and so is the indicator 1_{B̄_ρ(y)} (μ⌞S(B̄_ρ(y)) = μ(S ∩ B̄_ρ(y)) < ∞). As 1_{B̄_ρ(y)} ≤ ψ pointwise,
 μ(S ∩ B̄_ρ(y)).toReal = ∫_S 1_{B̄_ρ(y)} dμ ≤ ∫_S ψ dμ = ρⁿ ∫_{η_{y,ρ}(S)} φ₀ dHⁿ ≤ (L₀ + 1) ρⁿ.

4. (Conclusion.) Because μ(S ∩ B̄_ρ(y)) < ∞, step 3 gives μ(S ∩ B̄_ρ(y)) ≤ ENNReal.ofReal((L₀ + 1)ρⁿ) = (L₀ + 1) · ENNReal.ofReal(ρⁿ) (`ENNReal.ofReal_mul`, L₀ + 1 ≥ 0). Put K := L₀ + 1 ∈ ℝ≥0. The inequality μ(S ∩ B̄_ρ(y)) ≤ K · ENNReal.ofReal(ρⁿ) holds for all ρ ∈ (0, min(ρ₁, r/2)), a set belonging to 𝓝[>]0; i.e. it holds eventually as ρ → 0+. ∎

## Key steps

1. Take the cut-off φ₀ ∈ C_c with 1_{B̄_1(0)} ≤ φ₀ ≤ 1_{B̄_2(0)}; its blow-up integrals converge to L₀ = ∫_T φ₀, so are ≤ L₀ + 1 for small ρ.
2. BLOWUP: ∫_{η_{y,ρ}(S)} φ₀ = ρ^{−n} ∫_S φ₀∘η_{y,ρ}; for 2ρ < r the integrand is integrable on S and dominates 1_{B̄_ρ(y)}.
3. Hence Hⁿ(S ∩ B̄_ρ(y)) ≤ (L₀ + 1)ρⁿ for all small ρ; K := L₀ + 1.

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
