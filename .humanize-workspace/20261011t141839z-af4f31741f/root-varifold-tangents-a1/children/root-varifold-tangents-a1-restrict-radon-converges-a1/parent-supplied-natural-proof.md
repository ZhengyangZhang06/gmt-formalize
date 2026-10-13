# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1`
- Child DAG node: `root.varifold_tangents-a1.restrict_radon_converges-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step B2 of the parent proof ('every f ∈ C_c(Ω × G) (subtype) extends by zero to f̃ ∈ C_c(ℝ^N × G) with tsupport ⊆ Ω × G, and ∫ f d(W_j)_dom = ∫ f̃ dV_{x,t_j} → ∫ f̃ dC = ∫ f d(C_Ω)_dom'), stated for general measures and a general constant. Notation: G := Grassmannian N n (compact Hausdorff); P := Ω ×ˢ univ ⊆ ℝ^N × G; val : P → ℝ^N × G the inclusion of the subspace; for a varifold Z on Ω, Z.domainMeasure = Z.measure.comap val (SimonGMT Varifold.lean). Varifold.RadonConverges Ws W means: for every f ∈ C_c(P, ℝ), ∫ f d(Ws i).domainMeasure → ∫ f dW.domainMeasure.
1. (P is open.) Ω is open because W is a varifold on Ω (field W.isOpen_domain), so P = Ω ×ˢ univ is open, in particular measurable, and val is an open embedding and a measurable embedding (MeasurableEmbedding.subtype_coe).
2. (Zero extension.) Fix f ∈ C_c(P, ℝ). Define f̃ : ℝ^N × G → ℝ by f̃(z) := f(⟨z, h⟩) if h : z ∈ P, and f̃(z) := 0 if z ∉ P. Then f̃ ∘ val = f and f̃ = 0 off P. Let Q := val(tsupport f); it is compact (continuous image of the compact set tsupport f), hence closed in the Hausdorff space ℝ^N × G, and Q ⊆ P.
 (a) f̃ is continuous at every z ∈ P: P is an open neighbourhood of z and, val being an open embedding, continuity of f̃ at z is equivalent to continuity of f̃ ∘ val = f at ⟨z, h⟩ (IsOpenEmbedding.continuousAt_iff), which holds.
 (b) f̃ is continuous at every z ∉ P: then z ∉ Q, and on the open neighbourhood Qᶜ of z we have f̃ ≡ 0 (for w ∈ Qᶜ: if w ∉ P then f̃ w = 0 by definition; if w ∈ P then ⟨w,_⟩ ∉ tsupport f, so f(⟨w,_⟩) = 0). A function that is locally constant near z is continuous at z.
 (c) support f̃ ⊆ Q, so tsupport f̃ ⊆ Q (Q closed) is compact. Hence f̃ ∈ C_c(ℝ^N × G, ℝ).
3. (Integrals against varifolds on Ω.) For any varifold Z on Ω, ∫ f dZ.domainMeasure = ∫ f̃ dZ.measure: indeed Z.domainMeasure.map val = Z.measure (SimonGMT Varifold.map_domainMeasure) and, val being a measurable embedding, ∫ f̃ d(Z.domainMeasure.map val) = ∫ f̃ ∘ val dZ.domainMeasure = ∫ f dZ.domainMeasure (MeasurableEmbedding.integral_map).
4. (Integrals against the restricted measures.) For any measure ν on ℝ^N × G, ∫ f̃ d(c • ν.restrict P) = c.toReal · ∫_P f̃ dν = c.toReal · ∫ f̃ dν, by integral_smul_measure and, since f̃ = 0 off P, setIntegral_eq_integral_of_forall_compl_eq_zero (neither identity needs integrability).
5. (Conclusion.) By steps 3, 4 and the hypotheses on the measures of Ws i and W, ∫ f d(Ws i).domainMeasure = c.toReal · ∫ f̃ dμ_i for every i, and ∫ f dW.domainMeasure = c.toReal · ∫ f̃ dμ. By VagueConverges μs μ applied to f̃ ∈ C_c(ℝ^N × G, ℝ), ∫ f̃ dμ_i → ∫ f̃ dμ; multiplying by the constant c.toReal (Tendsto.const_mul) gives ∫ f d(Ws i).domainMeasure → ∫ f dW.domainMeasure. Since f ∈ C_c(P, ℝ) was arbitrary, Varifold.RadonConverges Ws W. (The hypothesis c ≠ ∞ is not needed by this argument; it is part of the intended use c = τ^{-1}.)

## Key steps

1. P = Ω ×ˢ univ is open (W.isOpen_domain); val : P → ℝ^N×G is an open measurable embedding.
2. Extend f ∈ C_c(P) by zero: f̃ is continuous (open embedding on P; vanishes on the open complement of the compact closed set val(tsupport f)) with compact support.
3. ∫ f d Z.domainMeasure = ∫ f̃ dZ.measure (map_domainMeasure + MeasurableEmbedding.integral_map) and ∫ f̃ d(c•ν⌞P) = c.toReal∫ f̃ dν.
4. Vague convergence on f̃ gives Radon convergence on Ω.

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
