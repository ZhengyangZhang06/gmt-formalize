# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1`
- Child DAG node: `root.varifold_tangents-a1.limit_ball_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step A3 of the parent proof (Simon 5.2, p. 215, ERRATUM: printed μ_C(B_ρ(x)) must read μ_C(B_ρ(0))). Notation: G := Grassmannian N n (a compact space, SimonGMT Grassmannian.instCompactSpace); ω := unitBallVolume n ∈ (0,∞); θ := ofReal θ0 < ∞; for r > 0, L(r) := θ·ω·ofReal r^n < ∞ and K_r := closedBall 0 r ×ˢ univ ⊆ ℝ^N × G. Recall C.weight(closedBall 0 r) = C.measure(K_r) (Varifold.weight_apply) and C.measure(K_r) < ∞ (C.finite_on_compact with the compact set closedBall 0 r ⊆ univ).
1. (Data and mass limits.) By IsVarifoldTangent V x C there are t_j > 0, t_j → 0 with VagueConverges (j ↦ V_j) C.measure, V_j := rescaledMeasure V x t_j. Since t_j > 0 and t_j → 0, Tendsto t atTop (𝓝[>] 0). Composing with the sibling rescaled_ball_mass (applied with θ := ofReal θ0 and radius r) gives m_j(r) := V_j(K_r) → L(r) for every r > 0. In particular, as L(r) < ∞, m_j(r) < ∞ for all large j.
2. (Cut-off functions.) For 0 < a < b let h_{a,b}(y) := min(1, max(0, (b − ‖y‖)/(b − a))) and F_{a,b}(y,S) := h_{a,b}(y). F_{a,b} is continuous, 0 ≤ F_{a,b} ≤ 1, F_{a,b} = 1 on K_a and F_{a,b} = 0 off ball 0 b ×ˢ univ; its support lies in K_b, which is compact (closed ball times the compact G). So F_{a,b} ∈ C_c(ℝ^N × G, ℝ) and 1_{K_a} ≤ F_{a,b} ≤ 1_{K_b} pointwise.
3. (Integral comparison.) If ν is a measure on ℝ^N × G with ν(K_b) < ∞, then F_{a,b} is ν-integrable (bounded, measurable, supported in K_b) and ν(K_a) ≤ ofReal(∫ F_{a,b} dν) ≤ ν(K_b): indeed ofReal(∫ F_{a,b} dν) = ∫⁻ ofReal(F_{a,b}) dν (ofReal_integral_eq_lintegral_ofReal, F_{a,b} ≥ 0) and the lower integral is monotone, with ∫⁻ 1_{K_a} dν = ν(K_a) and ∫⁻ 1_{K_b} dν = ν(K_b).
4. (Upper bound.) Fix ρ > 0 and ρ' > ρ, and let F := F_{ρ,ρ'}. By step 3 with ν = C.measure, C.weight(closedBall 0 ρ) = C.measure(K_ρ) ≤ ofReal(∫ F dC.measure). By VagueConverges, ∫ F dV_j → ∫ F dC.measure, so ofReal(∫ F dV_j) → ofReal(∫ F dC.measure) (continuity of ofReal). For all large j, m_j(ρ') < ∞ and step 3 with ν = V_j gives ofReal(∫ F dV_j) ≤ m_j(ρ'). Passing to the limit (limits preserve eventual inequalities, le_of_tendsto_of_tendsto), ofReal(∫ F dC.measure) ≤ L(ρ'). Hence C.weight(closedBall 0 ρ) ≤ L(ρ') for every ρ' > ρ. As ρ' ↓ ρ, L(ρ') → L(ρ) (r ↦ ofReal r^n is continuous and θω is a finite constant), so C.weight(closedBall 0 ρ) ≤ L(ρ).
5. (Lower bound.) Fix ρ > 0, ρ' > ρ and F := F_{ρ,ρ'}. For all large j, m_j(ρ') < ∞ and step 3 gives m_j(ρ) ≤ ofReal(∫ F dV_j). Passing to the limit, L(ρ) = lim m_j(ρ) ≤ lim ofReal(∫ F dV_j) = ofReal(∫ F dC.measure) ≤ C.measure(K_{ρ'}) = C.weight(closedBall 0 ρ') (step 3 with ν = C.measure). So L(ρ) ≤ C.weight(closedBall 0 ρ') for every ρ' > ρ. Now closedBall 0 ρ = ⋂_{k≥1} closedBall 0 (ρ + 1/k), a decreasing sequence of measurable sets whose first member has finite C.weight; by continuity from above (tendsto_measure_iInter_atTop / measure_iInter_eq_iInf), C.weight(closedBall 0 (ρ + 1/k)) → C.weight(closedBall 0 ρ), hence L(ρ) ≤ C.weight(closedBall 0 ρ).
6. (Conclusion.) By steps 4 and 5, C.weight(closedBall 0 ρ) = L(ρ) = ofReal θ0 · unitBallVolume n · ofReal ρ^n for every ρ > 0.

## Key steps

1. t_j → 0⁺ and the sibling rescaled_ball_mass give V_{x,t_j}(B_r(0)×G) → θ0ω_n r^n for every r > 0.
2. Radial piecewise-linear cut-offs F with 1_{B_a×G} ≤ F ≤ 1_{B_b×G} lie in C_c(ℝ^N×G) because G is compact.
3. Upper bound: μ_C(B_ρ(0)) ≤ ∫F dC = lim ∫F dV_j ≤ θ0ω_nρ'^n, then ρ' ↓ ρ.
4. Lower bound: θ0ω_nρ^n ≤ ∫F dC ≤ μ_C(B_ρ'(0)), then continuity from above as ρ' ↓ ρ.

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
