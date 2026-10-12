# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1`
- Child DAG node: `root.varifold_tangents-a1.rescaled_divergence_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact R2 of the parent proof (Simon Ch. 8: 'by definition of δV (in 2)', p. 215; the bound |δV(Y)| ≤ sup|Y|·‖δV‖(W) for spt Y ⊆ W ⊂⊂ U is the defining property 2.5 of ‖δV‖ — the parent derives the same inequality from 2.6). Notation: G := Grassmannian N n; div_S X(w) := Varifold.tangentialDivergence X w S = trace(S·DX(w)); ‖δV‖ := variationMeasure V; δV(Y) := V.firstVariation Y = ∫ div_S Y(z) dV(z,S).
1. (Set-up.) ψ(z) := t^{-1}•(z − x) is an affine homeomorphism of ℝ^N with inverse w ↦ x + t•w, and φ(z,S) := (ψ z, S) is continuous. f(w,S) := div_S X(w) is continuous (SimonGMT Varifold.continuous_tangentialDivergence, X ∈ C¹) with compact support (Varifold.hasCompactSupport_tangentialDivergence), hence bounded and Borel. Also M ≥ 0, because 0 ≤ ‖X 0‖ ≤ M.
2. (Change of variables.) By definition rescaledMeasure V x t = ofReal((t^{-1})^n) • V.measure.map φ. By integral_smul_measure (the real number (ofReal((t^{-1})^n)).toReal equals (t^{-1})^n ≥ 0) and integral_map (φ measurable, f continuous): ∫ f d(rescaledMeasure V x t) = (t^{-1})^n · ∫ f(φ(z,S)) dV.measure(z,S).
3. (The pulled-back field.) Put Y(z) := t • X(ψ z). Y is C¹ (C¹ map composed with an affine map, times a constant). By the chain rule DY(z) = t·DX(ψ z)∘(t^{-1}·Id) = DX(ψ z); hence the Jacobian matrix of Y at z equals that of X at ψ z and div_S Y(z) = trace(S·DY(z)) = div_S X(ψ z) = f(φ(z,S)) for all (z,S). Therefore ∫ f∘φ dV.measure = ∫ div_S Y(z) dV(z,S) = δV(Y), and by step 2, ∫ f d(rescaledMeasure V x t) = (t^{-1})^n·δV(Y).
4. (Support and size of Y.) Y(z) ≠ 0 iff X(ψ z) ≠ 0, so support Y = ψ^{-1}(support X), and since ψ is a homeomorphism, tsupport Y = ψ^{-1}(tsupport X). Thus tsupport Y is compact, and tsupport Y ⊆ ψ^{-1}(B°_R(0)) = B°_{tR}(x) (because ‖ψ z‖ < R ⟺ ‖z − x‖ < tR) ⊆ B_{tR}(x) ⊆ U. Hence Y (with these properties) is an element of Varifold.TestVectorField U. Moreover ‖Y z‖ = t‖X(ψ z)‖ ≤ tM for every z.
5. (Bound by the supremum in 2.5.) Let W := B°_{tR}(x). W is open, closure W ⊆ B_{tR}(x) ⊆ U, and closure W is compact (a closed subset of a compact closed ball). If M = 0, then X ≡ 0, so Y ≡ 0, div_S Y ≡ 0 (Varifold.tangentialDivergence_zero), δV(Y) = 0, the left side of the claim is 0 and there is nothing to prove. Let M > 0, c := (tM)^{-1} > 0 and Ŷ := c•Y. Then Ŷ is C¹ with compact support, tsupport Ŷ = tsupport Y ⊆ W ⊆ U and ‖Ŷ z‖ ≤ 1 for all z, i.e. Ŷ ∈ TestVectorField U with Ŷ.UnitSupportedIn W. By the definition of Varifold.firstVariationNormOn as the supremum, over such test fields, of ofReal|δV(·)|, we get ofReal|δV(Ŷ)| ≤ V.firstVariationNormOn W. By linearity (Varifold.firstVariation_const_smul) δV(Ŷ) = c·δV(Y), so ofReal|δV(Y)| = ofReal(tM)·ofReal|δV(Ŷ)| ≤ ofReal(tM)·V.firstVariationNormOn W.
6. (Identification with ‖δV‖.) Since V has locally bounded first variation, variationMeasure V = V.firstVariationRieszMeasure hV (definition of variationMeasure, dif_pos), and by Simon 2.5 in the kernel-checked form SimonGMT Varifold.firstVariationRieszMeasure_eq_norm (FirstVariationRiesz.lean:218; W open with compact closure contained in U) V.firstVariationRieszMeasure hV W = V.firstVariationNormOn W. As W ⊆ B_{tR}(x), monotonicity gives V.firstVariationNormOn W = ‖δV‖(W) ≤ ‖δV‖(B_{tR}(x)) =: A.
7. (Assembly.) By steps 3, 5, 6: ofReal|∫ f d(rescaledMeasure V x t)| = ofReal((t^{-1})^n)·ofReal|δV(Y)| ≤ ofReal((t^{-1})^n)·ofReal t·ofReal M·A. With a := ofReal t and r := ofReal R, both in (0,∞): ofReal((t^{-1})^n) = (a^n)^{-1}, ofReal(tR) = a·r and ofReal(tR)^n = a^n·r^n. In ℝ≥0∞, ofReal M·(r^n/r)·(a·r·A/(a^n·r^n)) = ofReal M·a·A·(a^n)^{-1}·(r^n·(r^n)^{-1})·(r^{-1}·r) = ofReal M·a·A·(a^n)^{-1}, using (a^n·r^n)^{-1} = (a^n)^{-1}(r^n)^{-1} (ENNReal.mul_inv, both factors nonzero and finite) and r^n(r^n)^{-1} = r^{-1}r = 1; this holds also when A = ∞. The right-hand side is exactly the bound obtained, which proves the claim.

## Key steps

1. Change of variables: ∫ div_S X dV_{x,t} = (t⁻¹)^n ∫ div_S X(t⁻¹(z−x)) dV(z,S).
2. Y(z) := t·X(t⁻¹(z−x)) has DY(z) = DX(t⁻¹(z−x)), so the integral is (t⁻¹)^n·δV(Y); Y ∈ K(U;ℝ^N), tsupport Y ⊆ B°_{tR}(x), |Y| ≤ tM.
3. Scale Y to a unit test field supported in W = B°_{tR}(x): |δV(Y)| ≤ tM·firstVariationNormOn V W (definition 2.5).
4. SimonGMT firstVariationRieszMeasure_eq_norm: firstVariationNormOn V W = ‖δV‖(W) ≤ ‖δV‖(B_{tR}(x)).
5. ENNReal arithmetic: (t⁻¹)^n·t·M·A = M·(R^n/R)·(tR·A/(tR)^n).

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
