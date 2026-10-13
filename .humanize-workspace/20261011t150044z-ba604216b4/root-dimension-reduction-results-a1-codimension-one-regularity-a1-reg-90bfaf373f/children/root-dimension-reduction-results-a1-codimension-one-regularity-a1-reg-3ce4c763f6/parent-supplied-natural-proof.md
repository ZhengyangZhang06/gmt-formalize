# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Printed proof of Simon Ch. 3, 4.3, steps (1) and (3)–(6) (chapter-03.txt lines 604–652); parent proof step 4 (1)–(6). Departures, made only so that the C¹ Gauss–Green identity suffices and no derivative of ρ ↦ L(F ∩ B_ρ) is needed: Simon's Lipschitz cut-offs decreasing to 1_{B̄_ρ} and the derivative in (4)–(6) are replaced by one C¹ cut-off per pair (ρ, δ) and a layer-cake (Fubini) argument, giving finite-difference forms of (5)–(6); the constant 2 in (6) becomes 3.

Notation. E := ℝ^{m+1}, L := L^{m+1}, B_r := B_r(y), B̄_r := B̄_r(y), A(r) := μ(B̄_r)_ℝ^{-1} ∫_{B̄_r} ν dμ, ω_{m+1} := L(B_1(0)).

1. Radii. As D is open, fix ρ₀ > 0 with B̄_{ρ₀} ⊆ D; then μ(B̄_r) ≤ μ(B̄_{ρ₀}) < ∞ for r ≤ ρ₀. Since ⟨A(r), v⟩ → |v|² = 1, choose ρ₂ ∈ (0, ρ₀] with ⟨A(r), v⟩ ≥ 1/2 for 0 < r < ρ₂. For such r, A(r) ≠ 0, so 0 < μ(B̄_r) < ∞ and (quantitative printed (1))
 (1′) ∫_{B̄_r} ⟨ν, v⟩ dμ = μ(B̄_r)⟨A(r), v⟩ ≥ ½ μ(B̄_r) for 0 < r < ρ₂.
 Put ρ₁ := ρ₂/2.

2. Cut-off. Let h(t) := 1 for t ≤ 0, h(t) := 1 − 3t² + 2t³ for 0 ≤ t ≤ 1, h(t) := 0 for t ≥ 1. h is C¹, nonincreasing, strictly decreasing on [0, 1], h′(0) = h′(1) = 0 and |h′| ≤ 3/2. For ρ, δ > 0 with ρ + δ < ρ₂ let ζ(z) := h((|z − y| − ρ)/δ). ζ ≡ 1 on the open ball B_ρ, a neighbourhood of y, and on E \ {y} it is a composition of C¹ maps; hence ζ is C¹ on E. Moreover 0 ≤ ζ ≤ 1, ζ = 1 on B̄_ρ, tsupport ζ ⊆ B̄_{ρ+δ} ⊆ D, and ∇ζ(z) = δ^{-1} h′((|z − y| − ρ)/δ)(z − y)/|z − y| vanishes unless ρ < |z − y| < ρ + δ, with |∇ζ| ≤ 3/(2δ).

3. Gauss–Green (printed (3)–(5)). φ := ζ v is C¹, compactly supported, tsupport φ ⊆ D, and div φ = ⟨∇ζ, v⟩. By (GG),
 ∫ ζ ⟨ν, v⟩ dμ = −∫_F ⟨∇ζ, v⟩ dL ≤ ∫_F |∇ζ| dL ≤ (3/(2δ)) L(F ∩ (B_{ρ+δ} \ B̄_ρ)).

4. Layer cake. For every z, ζ(z) = ∫_0^1 1{ζ(z) ≥ t} dt, and for t ∈ (0, 1], {ζ ≥ t} = B̄_{r(t)} with r(t) := ρ + δ s(t) ∈ [ρ, ρ + δ), where s(t) := max{s ∈ [0, 1] : h(s) ≥ t} (h is continuous and nonincreasing). The function (t, z) ↦ 1{ζ(z) ≥ t}⟨ν(z), v⟩ is Borel and bounded by 1_{B̄_{ρ+δ}}(z), which is integrable for dt ⊗ μ on (0, 1) × E. By Fubini and (1′) (note r(t) < ρ₂),
 ∫ ζ ⟨ν, v⟩ dμ = ∫_0^1 (∫_{B̄_{r(t)}} ⟨ν, v⟩ dμ) dt ≥ ∫_0^1 ½ μ(B̄_{r(t)}) dt ≥ ½ μ(B̄_ρ).

5. Annular bound for F (finite-difference form of printed (6)). Steps 3 and 4 give δ·μ(B̄_ρ) ≤ 3 L(F ∩ (B_{ρ+δ} \ B̄_ρ)) for all ρ, δ > 0 with ρ + δ < ρ₂.

6. Annular bound for the complement. For every C¹ compactly supported φ, ∫_E div φ dL = 0 (each ∫ ∂_i φ^i dL vanishes by Fubini and the fundamental theorem of calculus; alternatively by the divergence theorem on a box containing the support). Hence G := E \ F (Borel) satisfies ∫_G div φ = −∫_F div φ = ∫⟨φ, ν⟩ dμ = −∫⟨φ, −ν⟩ dμ for C¹ φ with compact support in D, i.e. (GG) holds for (G, μ, −ν); also |−ν| ≡ 1 and the averages of −ν are −A(r), with ⟨−A(r), −v⟩ = ⟨A(r), v⟩, so (1′) holds for (−ν, −v) with the same ρ₂. Steps 2–5 for (G, −ν, −v) give δ·μ(B̄_ρ) ≤ 3 L((B_{ρ+δ} \ B̄_ρ) \ F) for ρ, δ > 0 with ρ + δ < ρ₂.

7. Upper density (printed (6)). For 0 < ρ < ρ₁ apply step 5 with δ = ρ (then ρ + δ = 2ρ < ρ₂): ρ μ(B̄_ρ) ≤ 3 L(B_{2ρ}) = 3 ω_{m+1} 2^{m+1} ρ^{m+1}, so μ(B̄_ρ) ≤ 3·2^{m+1} ω_{m+1} ρ^m.

8. Conclusion. C := max(3, 3·2^{m+1} ω_{m+1}) ≥ 0 and ρ₁ = ρ₂/2 > 0 satisfy: B̄_{ρ₁} ⊆ B̄_{ρ₀} ⊆ D; for ρ, δ > 0 with ρ + δ < ρ₁ (< ρ₂) both annular inequalities hold by steps 5–6 (3 ≤ C); and μ(B̄_ρ) ≤ C ρ^m for 0 < ρ < ρ₁ by step 7. ∎

## Key steps

1. Normal averages → v give ∫_{B̄_r}⟨ν,v⟩dμ ≥ ½μ(B̄_r) for small r (printed (1)).
2. C¹ radial cut-off ζ = h((|z−y|−ρ)/δ) with |∇ζ| ≤ 3/(2δ) supported on the annulus.
3. Gauss–Green with ζv bounds ∫ζ⟨ν,v⟩dμ by (3/(2δ))·L(F ∩ annulus).
4. Layer cake over the closed balls {ζ ≥ t} gives ∫ζ⟨ν,v⟩dμ ≥ ½μ(B̄_ρ).
5. The complement satisfies Gauss–Green with −ν (∫ div φ = 0), giving the second annular bound.
6. Taking δ = ρ gives μ(B̄_ρ) ≤ 3·2^{m+1}ω_{m+1}ρ^m.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of dag.json: statements/status of all region_density_one-a1 children (incl. rectifiable_density_one frozen type); accepted nodes whose type mentions HasApproximateTangentSpaceAt; collision check of the 12 codim1_rdo_dg_* names (0 hits among 680 nodes)`
- `git show 376e5f48:GMT/Ch07/Submission.lean | grep namespace/theorem Submission.  (placement of child declarations inside namespace GMT.Ch07)`
- `grep -n "^theorem|^def|^structure" in SimonGMT Chapter01/{RadonPolarRepresentation,RadonRepresentation,VectorFunctionalEnvelope,DensityComparison,LowerDensityComparison,RelativeDensityComparison,RadonNikodymDensity,GeneralDifferentiation,Densities,Hausdorff,EuclideanNormalization}.lean, Chapter02/BV.lean, Chapter03/{FinitePerimeter,Rectifiable}.lean`
- `rg in snapshot mathlib: "theorem ae_tendsto_average ", "theorem ae_tendsto_rnDeriv", "theorem ae_tendsto_measure_inter_div", "lintegral_pow_le_pow_lintegral_fderiv", "theorem eLpNorm_le_eLpNorm_fderiv", "LipschitzOnWith.extend_real", "theorem exists_disjoint_subfamily_covering_enlargement_closedBall", "integral_lineDeriv_mul_eq", "theorem tendsto_filterAt", "contDiff_convolution_left", "exists_isCompact_lt_add", "theorem withDensity_rnDeriv_eq", "measurePreserving_repr", "theorem addHaar_preimage_smul", "theorem ae_eq_of_integral_contDiff_smul_eq", "def normed", "μHE\["`
- `sed -n of book chapter-03.txt 1-330 and 540-746, chapter-02.txt 470-640, chapter-01.txt 570-640, 1063-1145, 1654-1672`
- `lake env lean -DautoImplicit=false /tmp/dg-split-check/Types.lean (all 12 child types; sorry warnings only)`
- `lake env lean -DautoImplicit=false /tmp/dg-split-check/Assembly.lean (parent frozen type from the children + uncle stub; #print axioms)`
- `sed -n runtime.py _decompose/_solve_children/_existing_lean_name_problem; cat swarm-project.json (max_depth 6, max_children 12)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-90bfaf373f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/GeneralDifferentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonNikodymDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/dg-split-check/Types.lean`
- `/tmp/dg-split-check/Assembly.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`

Pins: snapshot manifest project b4d606db / Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib; simongmt 2b366308; snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). Library: SimonGMT already proves Simon Ch. 1, 4.14 for any locally compact Hausdorff X (simon_theorem_4_14_caratheodory, RadonPolarRepresentation.lean:150) and Borel versions of Carathéodory-measurable functions (IsBorelRegularOuterMeasure.aemeasurable_of_caratheodory, GeneralDifferentiation.lean:286), used by gauss_green_measure; it defines CountablyRectifiable, HasApproximateTangentSpaceAt and blowUpMap (Chapter03/Rectifiable.lean) and only the data of 4.1–4.2 (Chapter03/FinitePerimeter.lean), whose header states that existence of the representation and De Giorgi's theorem are not provided. Snapshot Mathlib supplies Besicovitch differentiation (Besicovitch.lean:1078 ae_tendsto_rnDeriv, :1105 ae_tendsto_measure_inter_div; Differentiation.lean:855 ae_tendsto_average), GNS (SobolevInequality.lean:439 eLpNorm_le_eLpNorm_fderiv_one), McShane extension (Lipschitz.lean:308), Vitali 5r covering (Vitali.lean:158), withDensity_rnDeriv_eq, OrthonormalBasis.measurePreserving_repr, ae_eq_of_integral_contDiff_smul_eq and μHE (Geometry/Euclidean/Volume/Measure.lean). No local declaration states the Gauss–Green measure, BV compactness, the BV Sobolev inequality, half-space rigidity, the blow-up theorem or the rectifiability criterion, so these become children. DAG: no accepted node has an identical type to any child, so no reuse; the 12 codim1_rdo_dg_* names occur nowhere in dag.json (680 nodes) or SimonGMT; the uncle rectifiable_density_one (frozen type ∀ P n M, 1 ≤ n → … → ∀ᵐ w, Tendsto (μHE[n] (M ∩ ball w t)/(unitBallVolume n * ofReal (t^n))) …) is used only through hypothesis (RD) of hausdorff_identification, which is its exact instance at P := m+1, n := m. Lean: Types.lean elaborates all 12 child types after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract opens (exit 0, sorry warnings only); Assembly.lean proves the parent's frozen type from gauss_green_measure, tangent_measure_ae, measure_eq_hausdorff and the uncle (stubs), #print axioms = propext, sorryAx, Classical.choice, Quot.sound. Runtime: max_depth 6 (children at depth 5 may split once more), max_children 12.
