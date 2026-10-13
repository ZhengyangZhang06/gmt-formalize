# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1`
- Child DAG node: `root.varifold_tangents-a1.radial_homogeneity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step A5 of the parent proof (Simon Ch. 8, p. 215: '5.3 by the same argument as in the proof of Theorem 6.1 of Ch. 4, except that we use 3.5'; the cited Ch. 4 Theorem 6.1 is not present in this edition, so the argument is written out; it is 3.5 with V = C, x = 0, φ(r/ρ) ≡ 1 on spt h, where the defect term vanishes because y ∈ S a.e. and δC = 0). ERRATUM: printed 5.3 'λ^{-n}μ_C(η_{0,λ}(A)) = μ_C(A)' has the wrong power; the correct statement is μ_C(sA) = s^nμ_C(A) (SimonGMT TangentScalingCounterexample). Notation: μ := C.weight = (C.measure).map Prod.fst, a Borel measure on ℝ^N that is finite on compact sets (Varifold.weight_finite_on_compact with U = ℝ^N); p_S := Grassmannian.project S; Dg(y) is the derivative of g at y.
1. (Identity (H).) Let g : ℝ^N → ℝ be C¹ with compact support. X(y) := g(y)•y is C¹, and support X ⊆ support g, so X has compact support and tsupport X ⊆ ℝ^N; thus X ∈ Varifold.TestVectorField univ, and stationarity gives C.firstVariation X = 0. By SimonGMT Varifold.tangentialDivergence_smul (RadialFirstVariation.lean:257) with h = g and the identity field, div_S X(y) = g(y)·div_S(id)(y) + Dg(y)(p_S y), and div_S(id)(y) = trace(S·Id) = trace S = n (the Jacobian matrix of the identity is the identity matrix; Grassmannian.trace_eq). So div_S X(y) = n·g(y) + Dg(y)(p_S y), and by hypothesis this equals n·g(y) + Dg(y)(y) for C-a.e. (y,S). The function y ↦ n·g(y) + Dg(y)(y) is continuous with compact support, and integrating a function of y alone against C.measure is integrating it against μ (integral_map along the measurable map Prod.fst). Hence
 (H) ∫ (n·g(y) + Dg(y)(y)) dμ(y) = 0 for every g ∈ C¹_c(ℝ^N).
2. (Scaling identity for C¹_c functions.) Fix g ∈ C¹_c(ℝ^N), choose R_g > 0 with tsupport g ⊆ B_{R_g}(0), and let L := sup_y ‖Dg(y)‖ < ∞ (Dg is continuous with compact support). For s > 0 put F(s) := ∫ g(s^{-1}y) dμ(y); the integrand is continuous and vanishes outside the compact set B_{sR_g}(0), so it is integrable.
 (a) F is differentiable at every s0 > 0 with F'(s0) = −s0^{-1}∫ Dg(s0^{-1}y)(s0^{-1}y) dμ(y). Indeed, for each y the map s ↦ g(s^{-1}y) has derivative Dg(s^{-1}y)(−s^{-2}y) = −s^{-1}·Dg(s^{-1}y)(s^{-1}y) at every s > 0. For s ∈ (s0/2, 2s0) this derivative vanishes unless ‖s^{-1}y‖ ≤ R_g, in which case ‖y‖ ≤ 2s0R_g and its absolute value is ≤ s^{-1}·L·R_g ≤ 2LR_g/s0. So all these derivatives are dominated by b(y) := (2LR_g/s0)·1_{B_{2s0R_g}(0)}(y), which is μ-integrable because μ(B_{2s0R_g}(0)) < ∞; the integrands are continuous (hence measurable) and F(s0) is finite. Differentiation under the integral sign (Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le on the neighbourhood (s0/2, 2s0) of s0) gives the claim.
 (b) For s > 0 let g_s(y) := g(s^{-1}y). Then g_s ∈ C¹_c(ℝ^N) and, by the chain rule, Dg_s(y)(v) = Dg(s^{-1}y)(s^{-1}v), so Dg_s(y)(y) = Dg(s^{-1}y)(s^{-1}y). Applying (H) to g_s and splitting the integral (both summands are continuous with compact support, hence integrable): n·F(s) + ∫ Dg(s^{-1}y)(s^{-1}y) dμ(y) = 0.
 (c) By (a) and (b), F'(s) = n·F(s)/s for all s > 0. Let G(s) := s^{-n}F(s) for s > 0. Then G'(s) = −n·s^{-n-1}F(s) + s^{-n}F'(s) = 0 for every s > 0, so G is constant on the interval (0,∞) (a function with zero derivative on an open interval is constant, e.g. is_const_of_deriv_eq_zero / IsOpen.is_const_of_deriv_eq_zero on the convex set (0,∞)). Hence F(s) = s^nG(s) = s^nG(1) = s^nF(1), i.e.
 (S) ∫ g(s^{-1}y) dμ(y) = s^n ∫ g dμ for all s > 0 and all g ∈ C¹_c(ℝ^N).
3. (Extension of (S) to C_c.) Let g ∈ C_c(ℝ^N) and s > 0. For k ∈ ℕ let φ_k be the normalized smooth bump function of Mathlib ContDiffBump (0 : ℝ^N) with rOut = 1/(k+1) (normed with respect to Lebesgue measure): φ_k ≥ 0, ∫ φ_k = 1, support φ_k = B°_{1/(k+1)}(0). Put g_k := φ_k ⋆ g. Then g_k is C^∞ (HasCompactSupport.contDiff_convolution_left: φ_k is smooth with compact support and g is locally integrable); support g_k ⊆ K₁ := tsupport g + B_1(0), a compact set independent of k, so g_k ∈ C¹_c(ℝ^N); and |g_k(y) − g(y)| ≤ ε_k := sup{|g(y') − g(y'')| : ‖y' − y''‖ ≤ 1/(k+1)} for every y (ContDiffBump.dist_normed_convolution_le), where ε_k → 0 by uniform continuity of the compactly supported continuous g. By (S), ∫ g_k(s^{-1}y) dμ(y) = s^n∫ g_k dμ for every k. Moreover |∫ g_k(s^{-1}y)dμ − ∫ g(s^{-1}y)dμ| ≤ ε_k·μ(s•K₁) and |∫ g_k dμ − ∫ g dμ| ≤ ε_k·μ(K₁), because the differences vanish outside the compact sets s•K₁ and K₁ respectively, and μ is finite on compact sets. Letting k → ∞ gives ∫ g(s^{-1}y) dμ(y) = s^n ∫ g dμ for every g ∈ C_c(ℝ^N) and s > 0.
4. (Equality of measures.) Fix s > 0 and let T(y) := s^{-1}•y, a linear homeomorphism of ℝ^N and hence a measurable equivalence. Put ν₁ := μ.map T and ν₂ := ofReal(s)^n • μ. Both are locally finite: for compact K, ν₁(K) = μ(T^{-1}K) = μ(s•K) < ∞ (s•K is compact) and ν₂(K) = ofReal(s)^n·μ(K) < ∞. On ℝ^N, a locally compact second-countable metric space, locally finite Borel measures are regular (Mathlib instance Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure). For g ∈ C_c(ℝ^N): ∫ g dν₁ = ∫ g(s^{-1}y) dμ(y) (integral_map) = s^n∫ g dμ (step 3) = (ofReal(s)^n).toReal·∫ g dμ = ∫ g dν₂ (integral_smul_measure). By uniqueness in the Riesz representation theorem (Mathlib Measure.ext_of_integral_eq_on_compactlySupported) ν₁ = ν₂.
5. (All sets.) Let A ⊆ ℝ^N be arbitrary (not necessarily measurable). Since T is a measurable equivalence, (μ.map T)(A) = μ(T^{-1}(A)) for every set A (MeasurableEquiv.map_apply), and T^{-1}(A) = {y : s^{-1}•y ∈ A} = s•A (y = s•(s^{-1}•y)). Hence μ(s•A) = ν₁(A) = ν₂(A) = ofReal(s)^n·μ(A), i.e. C.weight (s • A) = ENNReal.ofReal s ^ n * C.weight A.

## Key steps

1. Stationarity with X = g(y)y and tangentialDivergence_smul (div_S id = trace S = n), plus p_S(y) = y a.e.: ∫(n g + Dg(y)y) dμ_C = 0 for all g ∈ C¹_c.
2. F(s) = ∫ g(y/s) dμ_C is differentiable (dominated differentiation) with F'(s) = −s⁻¹∫Dg(y/s)(y/s)dμ_C = nF(s)/s by the identity applied to g(·/s); so s^{-n}F(s) is constant.
3. Mollification extends ∫ g(y/s) dμ_C = s^n∫ g dμ_C from C¹_c to C_c.
4. Riesz uniqueness: (y ↦ y/s)_#μ_C = s^nμ_C as regular measures; MeasurableEquiv.map_apply gives μ_C(s•A) = s^nμ_C(A) for every set A.

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
