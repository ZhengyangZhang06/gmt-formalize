# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1`
- Child DAG node: `root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 6 of the parent proof of Simon, Ch. 8, Theorem 1.2 (the printed "μ_V = H^n ⌞ θ in U", obtained from the Besicovitch differentiation theorem and the Radon–Nikodym theorem, Ch. 1, 3.23–3.24), together with the parts of Steps 3 and (0f) it needs; the case n = 0 is the corresponding part of Step 1. Notation: μ := V.weight; ω := unitBallVolume n ∈ (0, ∞) (ω = 1 if n = 0, Mathlib volume_euclideanSpace_eq_dirac); B_ρ(y) := closedBall y ρ; H^n := μHE[n]; K_p (p ≥ 1) a compact exhaustion of U: K_p := closedBall 0 p if U = ℝ^N, and otherwise K_p := {x : |x| ≤ p and infDist(x, ℝ^N ∖ U) ≥ 1/p}; each K_p is closed and bounded, hence compact; K_p ⊆ U (points of ℝ^N ∖ U have infDist 0); K_p ⊆ {x : |x| < p + 1, infDist(x, ℝ^N ∖ U) > 1/(p + 1)} ⊆ interior K_{p+1} (the middle set is open); K_p ⊆ K_{p+1}; and ⋃_p K_p = U (for x ∈ U, infDist(x, ℝ^N ∖ U) > 0 since ℝ^N ∖ U is closed and does not contain x).

0. Standing facts. U is open (V.isOpen_domain); μ(K) < ∞ for compact K ⊆ U (Varifold.weight_finite_on_compact); μ is σ-finite (Varifold.weight.instSigmaFinite). By frt_carrier_nullMeasurable, M is H^n-null-measurable.

1. Borel representative of θ. For r > 0, x ↦ μ(B_r(x)) is Borel (Mathlib measurable_measure_prodMk_left for the s-finite measure μ and the closed, hence Borel, set {(x, y) : dist y x ≤ r} ⊆ ℝ^N × ℝ^N, whose section at x is closedBall x r; SimonGMT Chapter01.measurable_closedBall_mass_of_sFinite states the same fact but under a local Borel instance, so it does not apply verbatim), hence so is x ↦ densityRatio n μ x r (division by a constant), and Θ̂(x) := liminf_{k→∞} densityRatio n μ x (1/(k + 1)) is a Borel function ℝ^N → [0, ∞] (Measurable.liminf). For x ∈ M, densityRatio n μ x (1/(k + 1)) → ENNReal.ofReal θ(x) (HasDensity composed with 1/(k + 1) → 0⁺), so Θ̂(x) = ENNReal.ofReal θ(x) and θ(x) = (Θ̂ x).toReal. Consequently, on every H^n-null-measurable subset of M, θ and ENNReal.ofReal ∘ θ agree everywhere with Borel functions, so they are a.e.-measurable for H^n restricted to such a set.

2. μ-null subsets of M are H^n-null. If Z ⊆ M and μ(Z) = 0, then for x ∈ Z, limsup_{ρ↓0} densityRatio n μ x ρ = ENNReal.ofReal θ(x) > 0 (Tendsto.limsup_eq), so frt_hausdorff_null_of_weight_null (with this μ and U) gives H^n(Z) = 0.

3. Pieces. For p ≥ 1 put M_p := {x ∈ M : θ(x) ≥ 1/p} ∩ K_p = M ∩ {x : (Θ̂ x).toReal ≥ 1/p} ∩ K_p (by 1); it is H^n-null-measurable (null-measurable ∩ Borel ∩ closed). M_p ⊆ M_{p+1}, and ⋃_p M_p = M because θ > 0 on M, M ⊆ U = ⋃_p K_p and the K_p increase.

4. H^n(M_p) < ∞.
 – n ≥ 1: let W := interior K_{p+1}, an open set with M_p ⊆ K_p ⊆ W and μ(W) ≤ μ(K_{p+1}) < ∞. For x ∈ M_p, W is a neighbourhood of x, so W ∩ B_ρ(x) = B_ρ(x) for small ρ > 0. Simon's upper density SimonGMT Chapter01.dimensionalUpperDensity μ.toOuterMeasure (n : ℝ) W x = limsup_{ρ↓0} μ(W ∩ B_ρ(x))/(realUnitBallVolume n · ENNReal.ofReal(ρ)^(n : ℝ)) (Chapter01/Densities.lean) therefore equals limsup_{ρ↓0} densityRatio n μ x ρ = ENNReal.ofReal θ(x) ≥ 1/p, because unitBallVolume n = volume(ball 0 1) = realUnitBallVolume n for n ≥ 1 (SimonGMT Chapter01.volume_euclidean_ball_eq with x = 0, r = 1, Chapter01/EuclideanHausdorffUpper.lean:71) and ENNReal.ofReal(ρ)^(n : ℝ) = ENNReal.ofReal(ρ)^n. SimonGMT Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity (Chapter01/DensityComparison.lean:251; its hypothesis borel ℝ^N ≤ μ.toOuterMeasure.caratheodory holds as μ is a Borel measure) with A₁ := M_p, A₂ := W, t := 1/p gives (1/p) · simonHausdorffOuterMeasureReal n (M_p) ≤ μ(W) < ∞; and simonHausdorffOuterMeasureReal n = (simonHausdorffMeasureReal n).toOuterMeasure (Chapter01.simonHausdorffMeasureReal_toOuterMeasure) with simonHausdorffMeasureReal (n : ℝ) = μHE[n] (Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, Chapter02/AreaLiteral.lean:42), so H^n(M_p) ≤ p μ(W) < ∞. (Import Poincare.SimonGMT.Chapter01.DensityComparison, Chapter01.EuclideanHausdorffUpper and Chapter02.AreaLiteral.)
 – n = 0: for x ∈ M, μ(B_ρ(x)) → μ({x}) as ρ ↓ 0 (continuity from above; μ(B_ρ(x)) < ∞ for small ρ since x ∈ U), while densityRatio 0 μ x ρ = μ(B_ρ(x)) → θ(x) (ω = 1); so μ({x}) = θ(x). Thus M_p ⊆ K_p consists of atoms of mass ≥ 1/p, so M_p is finite with #M_p ≤ p μ(K_p) < ∞, and H^0(M_p) = #M_p < ∞ (μHE[0] = μH[0] and μH[0]{a} = 1).
 In both cases λ_p := H^n.restrict M_p is a finite Borel measure.

5. Density one (α). M_p ⊆ M, so for every L ∈ (0, 1] the countable family of closed L-graphs covering M also covers M_p. With 3 and 4, frt_hausdorff_density_one_of_flat_covers (A := M_p) gives: for λ_p-a.e. x, λ_p(B_r(x))/(ω r^n) → 1 as r ↓ 0.

6. ρ_p := μ.restrict M_p is a finite measure (ρ_p(ℝ^N) = μ(M_p) ≤ μ(K_p) < ∞), and ρ_p ≪ λ_p: if B is Borel with λ_p(B) = H^n(B ∩ M_p) = 0, then every point of B ∩ M_p ⊆ M has the finite density ENNReal.ofReal θ(x) ≠ ∞, so μ(B ∩ M_p) = 0 by frt_weight_null_of_hausdorff_null, i.e. ρ_p(B) = 0.

7. Radon–Nikodym. By Mathlib Besicovitch.ae_tendsto_rnDeriv (Covering/Besicovitch.lean:1078) for the finite measures ρ_p and λ_p, for λ_p-a.e. x: ρ_p(B_r(x))/λ_p(B_r(x)) → (ρ_p.rnDeriv λ_p)(x) as r ↓ 0; and ρ_p = λ_p.withDensity (ρ_p.rnDeriv λ_p) by Measure.withDensity_rnDeriv_eq (Decomposition/RadonNikodym.lean:60), since ρ_p ≪ λ_p.

8. Identification of the derivative. Let W := interior K_{p+1}. By Besicovitch.ae_tendsto_measure_inter_div (Covering/Besicovitch.lean:1105) for the finite measure μ.restrict W and the set M_p: for ((μ.restrict W).restrict M_p)-a.e. x, (μ.restrict W)(M_p ∩ B_r(x))/(μ.restrict W)(B_r(x)) → 1. For x ∈ M_p ⊆ K_p ⊆ W and small r, B_r(x) ⊆ W, so this says (β): μ(M_p ∩ B_r(x))/μ(B_r(x)) → 1. The a.e. statement provides a Borel set E with ((μ.restrict W).restrict M_p)(E) = 0 containing every point at which (β) fails; since restricting to the Borel set E gives μ(E ∩ M_p ∩ W) = 0 (no measurability of M_p needed), the set E_β := {x ∈ M_p : (β) fails at x} ⊆ E ∩ M_p ∩ W is μ-null; as E_β ⊆ M, step 2 gives H^n(E_β) = 0 and hence λ_p(E_β) = 0. Also (γ): μ(B_r(x))/(ω r^n) → θ(x) ∈ (0, ∞) for every x ∈ M (hypothesis). Since M_p is H^n-null-measurable, λ_p-a.e. x lies in M_p (ae_restrict_mem₀). So for λ_p-a.e. x we have x ∈ M_p ∖ E_β, (α), (β), (γ) and the convergence of 7. At such x, for small r all of μ(B_r(x)), μ(M_p ∩ B_r(x)), λ_p(B_r(x)) are finite and positive, ρ_p(B_r(x)) = μ(B_r(x) ∩ M_p) (Measure.restrict_apply), and
 ρ_p(B_r(x))/λ_p(B_r(x)) = [μ(M_p ∩ B_r(x))/μ(B_r(x))] · [μ(B_r(x))/(ω r^n)] / [λ_p(B_r(x))/(ω r^n)] → 1 · ENNReal.ofReal θ(x) / 1.
 By uniqueness of limits, ρ_p.rnDeriv λ_p = ENNReal.ofReal ∘ θ λ_p-a.e., so ρ_p = λ_p.withDensity (ENNReal.ofReal ∘ θ) (withDensity_congr_ae). Evaluating on a Borel set B (withDensity_apply, Measure.restrict_restrict): μ(B ∩ M_p) = ∫⁻_{B} ENNReal.ofReal θ dλ_p = ∫⁻_{B ∩ M_p} ENNReal.ofReal θ dH^n.

9. Borel sets. Let B be Borel. The sets B ∩ M_p increase to B ∩ M, so μ(B ∩ M) = sup_p μ(B ∩ M_p) (Monotone.measure_iUnion, which needs no measurability), and ∫⁻_{B ∩ M} ENNReal.ofReal θ dH^n = sup_p ∫⁻_{B ∩ M_p} ENNReal.ofReal θ dH^n (write the integrals as lintegrals of the indicators (B ∩ M_p).indicator (ENNReal.ofReal ∘ θ), which by 1 and 3 coincide with indicators of null-measurable sets times the Borel function ENNReal.ofReal ∘ (Θ̂ ·).toReal and hence are H^n-a.e.-measurable, increase in p and converge pointwise to (B ∩ M).indicator (ENNReal.ofReal ∘ θ); apply the monotone convergence theorem lintegral_iSup'). By 8, μ(B ∩ M) = ∫⁻_{B ∩ M} ENNReal.ofReal θ dH^n, and μ(B) = μ(B ∩ M) because μ(B ∖ M) ≤ μ(ℝ^N ∖ M) = 0.

10. Null-measurable sets (b). Let B be μ-null-measurable and choose a Borel B₀ with B =ᵐ[μ] B₀ (NullMeasurableSet). Then μ(B) = μ(B₀) (measure_congr). The set (B ∩ M) Δ (B₀ ∩ M) is contained in {x : x ∈ B ↮ x ∈ B₀} ∩ M, a μ-null subset of M, hence H^n-null by 2; therefore B ∩ M =ᵐ[H^n] B₀ ∩ M, H^n.restrict (B ∩ M) = H^n.restrict (B₀ ∩ M) (Measure.restrict_congr_set), and by 9, ∫⁻_{B ∩ M} ENNReal.ofReal θ dH^n = ∫⁻_{B₀ ∩ M} ENNReal.ofReal θ dH^n = μ(B₀) = μ(B).

11. Integrability (a). Let K ⊆ U be compact. M ∩ K is H^n-null-measurable and θ = (Θ̂ ·).toReal on M ∩ K (1), so θ is a.e.-strongly measurable for H^n.restrict (M ∩ K). Since θ > 0 on M, ∫⁻_{M ∩ K} ‖θ‖ₑ dH^n = ∫⁻_{K ∩ M} ENNReal.ofReal θ dH^n = μ(K) < ∞ by 9 applied to the Borel set K. Hence IntegrableOn θ (M ∩ K) μHE[n]. ∎

## Key steps

1. M is H^n-null-measurable (frt_carrier_nullMeasurable); θ agrees on M with the Borel function (liminf of density ratios).toReal.
2. μ_V-null subsets of M are H^n-null (frt_hausdorff_null_of_weight_null).
3. Pieces M_p = {θ ≥ 1/p} ∩ K_p are null-measurable with H^n(M_p) < ∞ (Simon 3.3; atoms if n = 0).
4. λ_p = H^n⌞M_p has density one a.e. (frt_hausdorff_density_one_of_flat_covers); μ_V⌞M_p ≪ λ_p (frt_weight_null_of_hausdorff_null).
5. Besicovitch differentiation + Lebesgue density of M_p for μ_V: d(μ_V⌞M_p)/dλ_p = θ λ_p-a.e., so μ_V⌞M_p = θ H^n⌞M_p.
6. Monotone limit p → ∞ gives μ_V(B) = ∫_{B∩M} θ dH^n for Borel B; extend to μ_V-null-measurable B via step 2.
7. Integrability on M ∩ K from μ_V(K) < ∞ and the Borel representative.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean and workspace GMT/Ch08/{Contract,Submission}.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'def FirstRectifiabilityTheorem|def IsVarifoldOf|def HasTangentPlane|def HasDensity|def densityRatio|def rescaledMeasure|def planeVarifoldMeasure' project/GMT/Ch08/Contract.lean`
- `rg -n 'theorem ae_tendsto_measure_inter_div |theorem ae_tendsto_rnDeriv ' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem hausdorffMeasure_image_le|theorem hausdorffMeasure_apply|theorem hausdorffMeasure_zero_singleton' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety|euclideanHausdorffMeasure_zero |euclideanHausdorffMeasure_smul₀' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n 'theorem withDensity_rnDeriv_eq ' mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `rg -n 'ext_of_integral_eq_on_compactlySupported$' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'theorem ext_of_generateFrom_of_iUnion' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'of_pseudoMetrizableSpace_of_isFiniteMeasure' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'lemma measure_compl_support' mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'theorem addHaar_closedBall ' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean (no Nontrivial assumption)`
- `rg -n 'lemma volume_euclideanSpace_eq_dirac' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `rg -n 'theorem exists_countable_dense ' mathlib/Mathlib/Topology/Bases.lean`
- `rg -l -i 'varifold' mathlib/Mathlib | wc -l (0 files)`
- `grep -rn 'theorem eq_of_plane_eq|instance instCompactSpace|theorem simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|theorem volume_euclidean_ball_eq|theorem measurable_closedBall_mass_of_sFinite|theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|theorem simonHausdorffMeasureReal_toOuterMeasure' simongmt Poincare/SimonGMT`
- `sed Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasWeightedApproximateTangentSpaceAt(.unique), regular/support_euclideanHausdorffMeasure_restrict_submodule) and Chapter08/Varifold.lean (Varifold, Grassmannian, weight, finrank_plane)`
- `lake env lean Scratch/Final.lean (import GMT.Ch08.Submission + comparator scope replay: 2 sibling types + 12 child statements as sorry'd lemmas + parent assembly with no sorry)`
- `lake env lean Scratch/Ch_<key>.lean for each of the 12 children (comparator NodeChallenge form)`
- `lake env lean Scratch/Avail3.lean (#print axioms for 5 SimonGMT lemmas outside the Submission import closure: propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/Omega0.lean (unitBallVolume 0 = 1 via volume_euclideanSpace_eq_dirac)`
- `lake env lean Review/Mine2.lean (Borel ball mass via measurable_measure_prodMk_left; SimonGMT measurable_closedBall_mass_of_sFinite does not apply verbatim)`
- `python3 dag.json lean_name collision check (no collision among 45 nodes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/InfiniteDensitySet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1/parent-child-handoff.json`

The snapshot is project 63436ae6 with Mathlib 25730c7c. Its Contract.lean is byte-identical to the workspace Contract and Submission. Mathlib contains no varifold theory, and pinned SimonGMT has neither Ch. 3, 1.6/1.9 nor an area formula on rectifiable carriers. Each child therefore builds on library facts that do exist. The Mathlib facts are Besicovitch.ae_tendsto_measure_inter_div / ae_tendsto_rnDeriv (Besicovitch.lean:1105/1078), LipschitzOnWith/LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:733/745), hausdorffMeasure_apply (546), Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:131/187), euclideanHausdorffMeasure_homothety_preimage and _smul₀ (152–172), LipschitzOnWith.extend_real (Lipschitz.lean:308), withDensity_rnDeriv_eq (RadonNikodym.lean:60), Measure.ext_of_integral_eq_on_compactlySupported (RieszMarkovKakutani/Real.lean:412), ext_of_generateFrom_of_iUnion (Restrict.lean:491), WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure (Regular.lean:1072), measure_compl_support (Support.lean:202), addHaar_closedBall (EqHaar.lean:500, no Nontrivial assumption), volume_euclideanSpace_eq_dirac (ω_0 = 1) and measurable_measure_prodMk_left. The SimonGMT facts are Grassmannian.instCompactSpace and finrank_plane, Chapter03 regular/support_euclideanHausdorffMeasure_restrict_submodule and HasWeightedApproximateTangentSpaceAt.unique, Grassmannian.eq_of_plane_eq (ConstancyTangent.lean:33), mul_simonHausdorff_le_of_le_dimensionalUpperDensity (DensityComparison.lean:251), simonHausdorffMeasureReal_toOuterMeasure and simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (AreaLiteral.lean:42), and volume_euclidean_ball_eq (n > 0). The five SimonGMT lemmas outside Submission's import closure import cleanly and use only propext, Classical.choice and Quot.sound. SimonGMT measurable_closedBall_mass_of_sFinite is stated under a local Borel instance and does not apply verbatim, so the children cite measurable_measure_prodMk_left instead (checked in Lean). In a scratch copy importing GMT.Ch08.Submission with the comparator's replayed scope, all 12 child lean_statements elaborate, both together and as individual NodeChallenge files, and pass validate_lean_statement. The parent assembly checks against type FirstRectifiabilityTheorem with no sorry of its own. None of the frt_-prefixed names collides with any node of the 45-node DAG.
