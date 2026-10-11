# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1`
- Child DAG node: `root.varifold_tangents-a1.density_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: part B (steps B1–B6) of the parent proof — the blow-up application of the semicontinuity theorem 3.7 made in the proofs of 5.5 (steps (3)–(7), ERRATUM: printed (5) 'Θ^n(μ_{V_j}, y) ≤ θ0 − ε_j' must read '≥') and of 5.7. Hypotheses: (3.7) DensitySemicontinuity; V has locally bounded first variation (LBFV); x ∈ U; τ > 0; (5.1) γ(ρ) := ofReal ρ·‖δV‖(B_ρ(x))/ofReal ρ^n → 0 as ρ ↓ 0, where ‖δV‖ := variationMeasure V; (E) e(ρ) := μ_V(E ∩ B_ρ(x))/ofReal ρ^n → 0 as ρ ↓ 0, where E := {y : ¬∃θ, HasDensity n μ_V y θ ∧ ofReal τ ≤ θ} (E need not be measurable; {y | y ∈ B_ρ(x) ∧ y ∈ E} = E ∩ B_ρ(x) and μ_V is applied as a measure to an arbitrary set). Let C : Varifold N n univ with IsVarifoldTangent V x C: t_j > 0, t_j → 0 and V_j := rescaledMeasure V x t_j → C.measure vaguely. Write G := Grassmannian N n, a := ofReal τ ∈ (0,∞), ω := unitBallVolume n ∈ (0,∞), μ_W := W.weight.
0. (Reduction to balls.) It suffices to prove, for every R > 0, (★_R): for μ_C-a.e. y, if ‖y‖ < R then ∃θ, HasDensity n μ_C y θ ∧ a ≤ θ. Indeed, (★_{k+1}) for all k ∈ ℕ holds simultaneously for μ_C-a.e. y (countable intersection, ae_all_iff), and every y satisfies ‖y‖ < k+1 for some k. Fix R > 0 and let Ω := B°_R(0) (open ball, an open set).
1. (Choice of j0.) As U is open and x ∈ U there is r > 0 with B_r(x) ⊆ U. Since t_j > 0 and t_j → 0, t_jR → 0 within (0,∞), so by (5.1) γ(t_jR) → 0. Choose j0 such that for all j ≥ j0: t_jR ≤ r (so B_{t_jR}(x) ⊆ U) and γ(t_jR) ≤ 1. Put K_R := ofReal R^n/ofReal R < ∞ and β_j := a^{-1}·K_R·γ(t_jR) for j ≥ j0; then β_j < ∞ and β_j → 0.
2. (Rescaled masses.) For t > 0 let φ_t(z,S) := (t^{-1}•(z − x), S) (continuous). For measurable A ⊆ ℝ^N, rescaledMeasure V x t (A ×ˢ univ) = ofReal((t^{-1})^n)·μ_V({z : t^{-1}•(z − x) ∈ A}) (Measure.smul_apply, Measure.map_apply, φ_t^{-1}(A ×ˢ univ) = {z : t^{-1}(z−x) ∈ A} ×ˢ univ, Varifold.weight_apply). In particular, for y ∈ ℝ^N and ρ ≥ 0, since ‖t^{-1}(z − x) − y‖ = t^{-1}‖z − (x + t•y)‖: rescaledMeasure V x t (closedBall y ρ ×ˢ univ) = ofReal((t^{-1})^n)·μ_V(B_{tρ}(x + t•y)).
3. (Restricted varifolds.) For j ≥ j0 let W_j be the varifold on Ω (structure Varifold N n Ω) with measure a^{-1} • (V_j.restrict (Ω ×ˢ univ)), and let C_Ω be the varifold on Ω with measure a^{-1} • (C.measure.restrict (Ω ×ˢ univ)). The structure fields hold: Ω is open; both measures vanish on Ωᶜ ×ˢ univ (it is disjoint from Ω ×ˢ univ); for compact K ⊆ Ω, W_j(K ×ˢ univ) ≤ a^{-1}·V_j(closedBall 0 R ×ˢ univ) = a^{-1}·ofReal((t_j^{-1})^n)·μ_V(B_{t_jR}(x)) < ∞ by step 2 and Varifold.weight_finite_on_compact (B_{t_jR}(x) ⊆ U is compact), and C_Ω(K ×ˢ univ) ≤ a^{-1}·C.measure(K ×ˢ univ) < ∞ (C.finite_on_compact); a^{-1} < ∞ as τ > 0. Set W'_i := W_{j0+i} for i ∈ ℕ.
4. (Convergence on Ω.) The shifted sequence i ↦ V_{j0+i} still converges vaguely to C.measure (for each f ∈ C_c(ℝ^N × G, ℝ), compose the convergence of ∫ f dV_j with i ↦ j0 + i, which tends to ∞). By construction W'_i.measure = a^{-1} • (V_{j0+i}.restrict (Ω ×ˢ univ)) for every i and C_Ω.measure = a^{-1} • (C.measure.restrict (Ω ×ˢ univ)), with a^{-1} ≠ ∞. Hence the sibling restrict_radon_converges (with Ω, μs := (i ↦ V_{j0+i}), μ := C.measure, Ws := W', W := C_Ω, c := a^{-1}) gives Varifold.RadonConverges W' C_Ω.
5. (First variation of W'_i.) Let X ∈ TestVectorField Ω (C¹, compact support, tsupport X ⊆ Ω). Since div_S X(y) = 0 for y ∉ tsupport X (Varifold.support_tangentialDivergence_subset) and tsupport X ⊆ Ω, δW_j(X) = ∫ div_S X d(W_j.measure) = τ^{-1}∫_{Ω×G} div_S X dV_j = τ^{-1}∫ div_S X dV_j. If moreover ‖X‖ ≤ 1, the sibling rescaled_divergence_bound with (t, R, M, X) := (t_j, R, 1, X) (hypotheses: LBFV, t_j > 0, R > 0, B_{t_jR}(x) ⊆ U for j ≥ j0, X ∈ C¹ with compact support, tsupport X ⊆ Ω = B°_R(0), ‖X‖ ≤ 1) gives ofReal|∫ div_S X dV_j| ≤ ofReal 1·K_R·γ(t_jR), hence ofReal|δW_j(X)| = a^{-1}·ofReal|∫ div_S X dV_j| ≤ β_j. Taking the supremum in the definition of firstVariationNormOn: W_j.firstVariationNormOn O ≤ β_j for every set O and every j ≥ j0. Consequently: (a) every W'_i has locally bounded first variation (β_{j0+i} < ∞); (b) for every O with IsRelCompactOpenIn O Ω (O open, closure O compact and ⊆ Ω), variationMeasure W'_i = W'_i.firstVariationRieszMeasure _ (dif_pos) and SimonGMT Varifold.firstVariationRieszMeasure_eq_norm give variationMeasure W'_i O = W'_i.firstVariationNormOn O ≤ β_{j0+i} → 0; so variationMeasure W'_i O → 0 and liminf_i variationMeasure W'_i O = 0 ≠ ∞.
6. (Densities off the bad sets.) Let B_j := {y : x + t_j•y ∈ E}. Let j ≥ j0, y ∈ Ω and 0 < ρ < R − ‖y‖, so closedBall y ρ ⊆ Ω. By step 2, μ_{W_j}(B_ρ(y)) = W_j.measure(B_ρ(y) ×ˢ univ) = a^{-1}·V_j((B_ρ(y) ∩ Ω) ×ˢ univ) = a^{-1}·ofReal((t_j^{-1})^n)·μ_V(B_{t_jρ}(x + t_j•y)). Since ω·ofReal(t_jρ)^n = ω·ofReal(t_j)^n·ofReal(ρ)^n with all factors positive and finite, dividing by ω·ofReal ρ^n gives densityRatio n μ_{W_j} y ρ = a^{-1}·densityRatio n μ_V (x + t_j•y) (t_jρ) for 0 < ρ < R − ‖y‖. If y ∈ Ω \ B_j then x + t_j•y ∉ E, so there is θ with HasDensity n μ_V (x + t_j•y) θ and a ≤ θ. As ρ ↦ t_jρ maps 𝓝[>] 0 to 𝓝[>] 0, densityRatio n μ_V (x + t_j•y)(t_jρ) → θ; multiplying by the finite constant a^{-1} (ENNReal.Tendsto.const_mul) and using that the identity holds on (0, R − ‖y‖) ∈ 𝓝[>] 0, HasDensity n μ_{W_j} y (a^{-1}θ), and 1 = a^{-1}a ≤ a^{-1}θ. Thus for every i and y ∈ Ω \ B_{j0+i}: ∃θ', HasDensity n μ_{W'_i} y θ' ∧ 1 ≤ θ'.
7. (Bad sets have vanishing mass.) Let O ⊆ Ω (e.g. O with IsRelCompactOpenIn O Ω, as O ⊆ closure O ⊆ Ω). For j ≥ j0 put ρ_j := t_jR, E_j := {z : z ∈ B_{ρ_j}(x) ∧ ¬∃θ, HasDensity n μ_V z θ ∧ a ≤ θ} = E ∩ B_{ρ_j}(x), Ẽ_j := toMeasurable μ_V E_j (measurable, E_j ⊆ Ẽ_j, μ_V(Ẽ_j) = μ_V(E_j)) and A_j := {y : x + t_j•y ∈ Ẽ_j} (measurable). If y ∈ B_j ∩ O then ‖y‖ < R, x + t_j•y ∈ E and ‖(x + t_j•y) − x‖ = t_j‖y‖ < ρ_j, so x + t_j•y ∈ E_j ⊆ Ẽ_j: B_j ∩ O ⊆ A_j. Hence μ_{W_j}(B_j ∩ O) ≤ μ_{W_j}(A_j) = W_j.measure(A_j ×ˢ univ) ≤ a^{-1}·V_j(A_j ×ˢ univ) = a^{-1}·ofReal((t_j^{-1})^n)·μ_V({z : x + t_j•(t_j^{-1}•(z − x)) ∈ Ẽ_j}) = a^{-1}·ofReal((t_j^{-1})^n)·μ_V(Ẽ_j) = a^{-1}·ofReal((t_j^{-1})^n)·μ_V(E_j) (step 2). Since ofReal((t_j^{-1})^n) = ofReal(R)^n·(ofReal(ρ_j)^n)^{-1}, this bound equals a^{-1}·ofReal(R)^n·e(ρ_j). As ρ_j → 0 within (0,∞), (E) gives e(ρ_j) → 0, and the constant a^{-1}ofReal(R)^n is finite; so the bound tends to 0, and by the squeeze theorem μ_{W'_i}(B_{j0+i} ∩ O) → 0 as i → ∞.
8. (Apply 3.7.) By steps 4–7 the hypotheses of DensitySemicontinuity hold with U := Ω, Vi := W', V := C_Ω, B i := B_{j0+i}: RadonConverges (step 4), LBFV of each W'_i (5a), the liminf bound (5b), the densities (step 6) and the vanishing bad masses (step 7). Its last conclusion gives: for μ_{C_Ω}-a.e. y, ∃θ, HasDensity n μ_{C_Ω} y θ ∧ 1 ≤ θ.
9. (Back to C.) For measurable A, μ_{C_Ω}(A) = a^{-1}·C.measure((A ∩ Ω) ×ˢ univ) = a^{-1}·μ_C(A ∩ Ω), so μ_{C_Ω} = a^{-1}•(μ_C.restrict Ω); since a^{-1} ≠ 0 its null sets are those of μ_C.restrict Ω, and (ae_restrict_iff', Ω measurable) for μ_C-a.e. y: y ∈ Ω ⇒ ∃θ, HasDensity n μ_{C_Ω} y θ ∧ 1 ≤ θ. For such y ∈ Ω and 0 < ρ < R − ‖y‖, closedBall y ρ ⊆ Ω gives μ_{C_Ω}(B_ρ(y)) = a^{-1}μ_C(B_ρ(y)), hence densityRatio n μ_C y ρ = a·densityRatio n μ_{C_Ω} y ρ (a·a^{-1} = 1); so HasDensity n μ_C y (a·θ) (ENNReal.Tendsto.const_mul, a finite; equality on (0, R − ‖y‖) ∈ 𝓝[>] 0) and a·θ ≥ a·1 = a = ofReal τ. This is (★_R); by step 0 the proof is complete.

## Key steps

1. Reduce to μ_C-a.e. y ∈ B°_R(0) for each R; choose j0 with B_{t_jR}(x) ⊆ U and γ(t_jR) ≤ 1.
2. Restricted, τ⁻¹-scaled rescalings W'_i := τ⁻¹V_{x,t_{j0+i}}⌞(Ω×G) and C_Ω := τ⁻¹C⌞(Ω×G) are varifolds on Ω = B°_R(0); the sibling restrict_radon_converges gives RadonConverges W' C_Ω.
3. Sibling rescaled_divergence_bound: firstVariationNormOn W'_i O ≤ τ⁻¹(R^n/R)γ(t_{j0+i}R) → 0; LBFV and liminf ‖δW'_i‖(O) = 0 via firstVariationRieszMeasure_eq_norm.
4. densityRatio of W'_i at y equals τ⁻¹·densityRatio of μ_V at x+t_jy at radius t_jρ, so densities ≥ 1 off B_j = {y : x+t_jy ∈ E}; μ_{W'_i}(B_j ∩ O) ≤ τ⁻¹R^n e(t_jR) → 0 using toMeasurable.
5. DensitySemicontinuity on Ω, then transfer densities from C_Ω back to C (×τ) and take the union over R ∈ ℕ.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `grep -rn 'theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported' mathlib/Mathlib (RieszMarkovKakutani/Real.lean:412, requires [μ.Regular] [ν.Regular])`
- `grep -rn 'theorem dist_normed_convolution_le|theorem _root_.HasCompactSupport.contDiff_convolution_left|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|theorem ae_eq_of_integral_contDiff_smul_eq' mathlib/Mathlib`
- `grep -rn 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le' mathlib/Mathlib (Analysis/Calculus/ParametricIntegral.lean:286)`
- `grep -n '^theorem|^def|^structure|^abbrev' simongmt Chapter08/{Varifold,VarifoldConvergence,StationaryMonotonicity,RadialFirstVariation}.lean`
- `grep -n 'firstVariationRieszMeasure_eq_norm|isFirstVariationMeasure_riesz' simongmt Chapter08/FirstVariationRiesz.lean (:218, :226)`
- `grep -rn 'def StationaryOn|homogen|def.*Cone|ext_of_integral_eq_on_compactlySupported|dilat' simongmt (no homogeneity lemma for general stationary varifolds)`
- `read simongmt Chapter08/TangentRescaling.lean, TangentRadialRigidity.lean, TangentScalingCounterexample.lean, StationaryCutoff.lean`
- `python import-closure of GMT/Ch08/Submission.lean (TangentRescaling, TangentRadialRigidity, StationaryMonotonicity, RadialFirstVariation not in closure; DeformationIntegral, FirstVariationRiesz, VarifoldConvergence in closure)`
- `read verifier gmt-compare.py candidate_inputs/contract_scope/child_modules and lean_contract.validate_lean_statement`
- `lean test/Final.lean: import GMT.Ch08.Submission + replayed comparator scope; 7 child statements + 2 sibling placeholders; 'exact Submission.X' replays; parent assembly against the selected frozen type`
- `lean test/Axioms.lean: #print axioms for 18 cited SimonGMT lemmas and 6 Mathlib lemmas`
- `grep -o 'lean_name' entries over run dir and grep -rho 'varifold_tangents_[A-Za-z0-9_]*' over cluster-state and .humanize (no reservation with this prefix)`
- `reviewer replay: lean /tmp/vt-review-a1/Restrict2.lean (complete proof of restrict_radon_converges)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryMonotonicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/StationaryCutoff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRadialRigidity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentScalingCounterexample.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Radon.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-08-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1/parent-child-handoff.json`

Snapshot = project 63436ae6 + Mathlib 25730c7c. Its project/GMT/Ch08/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

What the children rely on:
- Mathlib (snapshot) supplies the tools for radial_homogeneity: Riesz uniqueness (Measure.ext_of_integral_eq_on_compactlySupported, RieszMarkovKakutani/Real.lean:412, with regularity from Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure, Regular.lean:1183), dominated differentiation (hasDerivAt_integral_of_dominated_loc_of_deriv_le, ParametricIntegral.lean:286) and mollifiers (ContDiffBump.dist_normed_convolution_le, HasCompactSupport.contDiff_convolution_left).
- SimonGMT (pinned) supplies:
  - the 2.5 identity firstVariationRieszMeasure_eq_norm (FirstVariationRiesz.lean:218), used by rescaled_divergence_bound and density_lower_bound;
  - tangentialDivergence_smul (RadialFirstVariation.lean:257) and Grassmannian.trace_eq, which give the identity (H);
  - continuous_/hasCompactSupport_/support_tangentialDivergence, firstVariation_const_smul, weight_apply, weight_finite_on_compact and map_domainMeasure;
  - the radial-rigidity lemma Stationary.ae_normalProject_eq_zero_of_constant_mass_ratio, used in the parent glue. TangentRadialRigidity is not in Submission's import closure, so the candidate must import it; gmt-compare allows this.

What is missing, and why the children exist: neither library has extraction of varifold tangents, stationarity of vague limits, the 5.2 ball-mass identity, homogeneity of stationary radial varifolds (corrected 5.3), restriction of vague convergence to RadonConverges, or the localized application of 3.7.

All cited lemmas use only propext, Classical.choice and Quot.sound.

Lean checks, in a scratch copy importing GMT.Ch08.Submission with the comparator's replayed scope:
- All 7 child statements elaborate, pass validate_lean_statement, and pass the 'exact Submission.X' replay.
- The parent glue proves the selected frozen type verbatim, with no sorry of its own.
- The reviewer fully proved restrict_radon_converges.

Names: no lean_name with the prefix varifold_tangents_ is reserved anywhere in the run.
