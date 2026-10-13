# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1`
- Child DAG node: `root.varifold_tangents-a1.limit_stationary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step A2 of the parent proof (Simon Ch. 8, p. 215: 'by definition of δV (in 2) ... C is stationary in ℝ^{n+ℓ}'). Notation as in the sibling rescaled_divergence_bound; γ(ρ) := ofReal ρ·variationMeasure V (closedBall x ρ)/ofReal ρ^n, so the hypothesis (5.1) says γ(ρ) → 0 as ρ ↓ 0.
1. (Data.) By IsVarifoldTangent V x C there is t : ℕ → ℝ with t_j > 0, t_j → 0, and VagueConverges (j ↦ V_j) C.measure, where V_j := rescaledMeasure V x t_j. Let X ∈ Varifold.TestVectorField univ (C¹, compact support). We must show C.firstVariation X = 0.
2. (Convergence of first variations.) f(z) := div_{z.2}X(z.1) = Varifold.tangentialDivergence X z.1 z.2 is continuous (Varifold.continuous_tangentialDivergence) and has compact support (Varifold.hasCompactSupport_tangentialDivergence), so f ∈ C_c(ℝ^N × G, ℝ). By VagueConverges, I_j := ∫ f dV_j → ∫ f dC.measure = C.firstVariation X.
3. (Constants.) tsupport X is compact, hence bounded: tsupport X ⊆ B_{R'}(0) for some real R' (possibly negative if tsupport X = ∅), so with R := max R' 0 + 1 > 0, tsupport X ⊆ B°_R(0). X is continuous with compact support, so there is M with ‖X y‖ ≤ M for all y. U is open and x ∈ U, so there is r > 0 with B_r(x) ⊆ U (closed ball; take half the radius of an open ball around x contained in U).
4. (Bound.) Since t_j → 0 there is j1 with t_jR ≤ r for all j ≥ j1; then B_{t_jR}(x) ⊆ B_r(x) ⊆ U. For j ≥ j1 the sibling rescaled_divergence_bound, applied with (t, R, M, X) := (t_j, R, M, X) (its hypotheses: LBFV, t_j > 0, R > 0, B_{t_jR}(x) ⊆ U, X ∈ C¹ with compact support, tsupport X ⊆ B°_R(0), ‖X‖ ≤ M), gives ofReal|I_j| ≤ K·γ(t_jR), where K := ofReal M·(ofReal R^n/ofReal R) is finite (ofReal R ≠ 0).
5. (Limit.) Because t_j > 0 and t_j → 0, also t_jR > 0 and t_jR → 0, i.e. Tendsto (j ↦ t_jR) atTop (𝓝[>] 0). By (5.1), γ(t_jR) → 0, and since K ≠ ∞, K·γ(t_jR) → K·0 = 0 (ENNReal.Tendsto.const_mul). As 0 ≤ ofReal|I_j| ≤ K·γ(t_jR) for j ≥ j1, the squeeze theorem in ℝ≥0∞ gives ofReal|I_j| → 0. Applying ENNReal.toReal, which is continuous at 0, |I_j| = (ofReal|I_j|).toReal → 0; hence I_j → 0.
6. (Conclusion.) By uniqueness of limits in ℝ, C.firstVariation X = lim_j I_j = 0. Since X was arbitrary, C.Stationary.

## Key steps

1. div_S X ∈ C_c(ℝ^N×G), so δC(X) = lim_j ∫ div_S X dV_{x,t_j} by vague convergence.
2. For large j, B_{t_jR}(x) ⊆ U and the sibling bound gives ofReal|∫ div_S X dV_{x,t_j}| ≤ M·(R^n/R)·γ(t_jR).
3. γ(t_jR) → 0 by (5.1) since t_jR → 0⁺; hence δC(X) = 0 for every test field.

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
