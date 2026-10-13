# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1.first_variation_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 3, 4 and 6 of the parent proof, at one fixed radius t, with the nonnegative normal term Q(t) dropped. This is Simon 8.3.5 with the sign of δV(X) corrected (erratum E2: the coefficient of δV(X) is '−'; see SimonGMT Chapter08/WeightedRadialIdentity.lean). The divergence of the radial field comes from hypothesis (Div), the exact statement of the parent's dependency radial_field_divergence.
Notation. w := z − y; s(z) := ‖w‖²/t²; φ' := deriv φ; a(z) := h(z)·φ(s(z)), so X_t(z) = a(z)(z − y). Also p_S := Grassmannian.project S and Dh := fderiv ℝ h. K := B_{tA}(y) = closedBall y (tA) is compact, and K ⊆ U by hypothesis. G := Grassmannian N n is a compact space.

1. Sign and support of φ and φ'. φ is non-increasing, so φ'(s) ≤ 0 for all s (Antitone.deriv_nonpos). If s > A², then φ vanishes on the open neighbourhood (A², ∞) of s, so φ'(s) = 0. If ‖w‖ ≥ tA, then ‖w‖²/t² ≥ A² (as t, A > 0), so φ(s(z)) = 0. If ‖w‖ > tA, then s(z) > A², so also φ'(s(z)) = 0. In particular, φ(s(z)) = φ'(s(z)) = 0 whenever z ∉ K.

2. Regularity of a and X_t. z ↦ ‖z − y‖² is C^∞ with derivative v ↦ 2⟨w, v⟩. So s is C¹ with Ds(z)[v] = (2/t²)⟨w, v⟩. Since φ and h are C¹, a = h·(φ∘s) is C¹. By the product and chain rules, for all z and v:
  Da(z)[v] = h(z)·φ'(s(z))·(2/t²)⟨w, v⟩ + φ(s(z))·Dh(z)[v].
 X_t, the product of a C¹ scalar function with the C¹ field z ↦ z − y, is C¹.

3. Support of X_t. If X_t(z) ≠ 0, then φ(s(z)) ≠ 0, so ‖w‖ < tA by step 1, i.e. z ∈ K. So support(X_t) ⊆ K. As K is closed, tsupport X_t ⊆ K ⊆ U, and as K is compact, X_t has compact support.

4. Pointwise divergence. Fix (z, S) and write s := s(z). The map w ↦ a(w)(w − y) is X_t, and a is differentiable at z (step 2). So (Div) with c := y gives
  div_S X_t(z) = n·a(z) + Da(z)[p_S w]
       = n·h(z)φ(s) + h(z)φ'(s)·(2/t²)⟨w, p_S w⟩ + φ(s)·Dh(z)[p_S w].

5. Projection facts. p_S is the linear map with matrix S.1. It is symmetric (Grassmannian.projectionLinearMap_isSymmetric) and idempotent (Grassmannian.project_project). Hence ⟨w, p_S w⟩ = ⟨w, p_S(p_S w)⟩ = ⟨p_S w, p_S w⟩ = ‖p_S w‖². By Cauchy–Schwarz, ‖p_S w‖² = ⟨w, p_S w⟩ ≤ ‖w‖·‖p_S w‖, so ‖p_S w‖ ≤ ‖w‖. Hence ⟨w, p_S w⟩ ≤ ‖w‖².

6. Pointwise inequality. For (z,S) ∈ ℝ^N × G define
  E(z,S) := n·(φ(s)h(z)) − t·(φ'(s)·(−2‖w‖²/t³)·h(z)) + φ(s)·Dh(z)[p_S w].
 Since t·(−2‖w‖²/t³) = −2‖w‖²/t², step 4 gives
  div_S X_t(z) − E(z,S) = (2/t²)·h(z)·(−φ'(s))·(‖w‖² − ⟨w, p_S w⟩) ≥ 0,
 because h(z) ≥ 0, −φ'(s) ≥ 0 (step 1) and ‖w‖² − ⟨w, p_S w⟩ ≥ 0 (step 5). So E ≤ div_S X_t pointwise.

7. Integrability with respect to W.measure on ℝ^N × G.
 (a) (z,S) ↦ div_S X_t(z) is integrable by Varifold.integrable_tangentialDivergence: X_t is C¹ with compact support and tsupport X_t ⊆ U (steps 2–3).
 (b) Put f₁(z,S) := φ(s(z))h(z), f₂(z,S) := φ'(s(z))·(−2‖w‖²/t³)·h(z) and f₃(z,S) := φ(s(z))·Dh(z)[p_S w]. They are continuous on ℝ^N × G: φ, φ', h and Dh are continuous (φ and h are C¹). Also (S, v) ↦ p_S v is continuous, because its i-th coordinate is Σ_j S.1_{ij}·v_j (LinearMap.toMatrix_mulVec_repr), a polynomial in the entries of S.1 and v.
 (c) By step 1 each f_i vanishes outside K × G. K × G is compact (G is compact), so each f_i is bounded on it. W.measure(K × G) < ∞ (Varifold.finite_on_compact: K is compact and K ⊆ U). Hence f₁, f₂, f₃ are integrable, and so is E = n·f₁ − t·f₂ + f₃.

8. Integration. δW(X) = ∫ div_S X(z) dW(z,S) by definition (Varifold.firstVariation). By linearity (integral_add, integral_sub, integral_const_mul) and monotonicity (integral_mono, using steps 6–7):
  n∫f₁ dW − t∫f₂ dW + ∫f₃ dW = ∫E dW ≤ ∫ div_S X_t(z) dW(z,S) = δW(X_t).

9. Identification. μ_W = W.weight is the push-forward of W.measure under (z,S) ↦ z. So for continuous g : ℝ^N → ℝ, ∫ g dμ_W = ∫ g(z) dW(z,S) (integral_map). With g(z) = φ(s(z))h(z) this gives ∫f₁ dW = Ĩ(t). With g(z) = φ'(s(z))(−2‖w‖²/t³)h(z) it gives ∫f₂ dW = J(t). And ∫f₃ dW = G(t) by definition. Therefore n·Ĩ(t) − t·J(t) + G(t) ≤ δW(X_t). ∎

## Key steps

1. φ' ≤ 0; φ(s(z)) = 0 if ‖z−y‖ ≥ tA, and φ'(s(z)) = 0 if ‖z−y‖ > tA
2. a = h·φ(‖·−y‖²/t²) is C¹ with Da(z)[v] = hφ'(s)(2/t²)⟨w,v⟩ + φ(s)Dh(z)[v]; X_t is C¹ with tsupport in B_{tA}(y) ⊆ U
3. (Div) gives div_S X_t = n·a + Da[p_S w]; p_S symmetric and idempotent gives ⟨w, p_S w⟩ = ‖p_S w‖² ≤ ‖w‖²
4. div_S X_t − E = (2/t²)h(−φ')(‖w‖² − ⟨w, p_S w⟩) ≥ 0 pointwise
5. the integrands are continuous, vanish off B_{tA}(y) × G and have finite mass there, so they are integrable; div_S X_t is integrable
6. integral_mono, linearity and μ_W = π_# W give nĨ(t) − tJ(t) + G(t) ≤ δW(X_t)

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project; project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean vs workspace GMT/Ch08/Contract.lean and GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'def variationMeasure|def MonotonicityFormula|theorem main_theorem' project/GMT/Ch08/Contract.lean`
- `rg -n in snapshot mathlib/Mathlib: 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le', 'theorem monotoneOn_of_deriv_nonneg', 'deriv_nonpos', 'EventuallyEq.deriv_eq', 'theorem norm_integral_le_lintegral_norm', "theorem lintegral_const_mul'", 'theorem lintegral_indicator ', 'theorem toReal_mono', 'theorem ContDiff.norm_sq', 'theorem integral_map ', 'integrableOn_of_bounded', 'theorem IntegrableOn.integrable_of_forall_notMem_eq_zero', 'theorem HasDerivAt.div ', 'exists_bound_of_continuousOn', 'theorem real_inner_le_norm', 'toMatrix_mulVec_repr'`
- `rg -n 'weightedCutoffMass|hasDerivAt_integral_radialCutoff|weightedRadialVectorField|scaledRadialCutoff' mathlib/Mathlib project (no match: the SimonGMT weighted-radial files are not part of the snapshot)`
- `grep -n '^theorem|^def|^noncomputable def' on pinned SimonGMT Chapter08/{Varifold,WeightedRadialIdentity,RadialCutoffDifferentiation,RadialFirstVariation,DeformationFamily,FirstVariation*}.lean; python3 transitive scan of Submission's 'import Poincare…' lines (closure lacks WeightedRadialIdentity, RadialCutoffDifferentiation, RadialFirstVariation and Chapter04)`
- `lake env lean /tmp/wrm-decomp-v1/Probe.lean: #check from import GMT.Ch08.Submission of Varifold.integrable_tangentialDivergence, Varifold.weight_finite_on_compact, hasDerivAt_integral_of_dominated_loc_of_deriv_le, monotoneOn_of_deriv_nonneg, Antitone.deriv_nonpos, norm_integral_le_lintegral_norm, lintegral_const_mul', lintegral_indicator, ENNReal.toReal_mono, ContDiff.norm_sq, CompactSpace (Grassmannian N n) (all available); Varifold.hasDerivAt_normalized_weightedCutoffMass is an unknown constant`
- `python3 gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement on the 3 statements -> /tmp/wrm-decomp-v1/CompForm.lean; lake env lean CompForm.lean, Assembly.lean, Full.lean, c1/Proof.lean, c2/Proof.lean, c3/Proof.lean`
- `grep -n 'helper|import' nodes/root-plane-disintegration-a1-pointwise-measure-a1/rlcr-plan-v1.md (leaf policy: one theorem, no helpers, no import changes)`
- `python3 scans of dag.json: 173 unique lean_names, none intcpt_allard_wrm_*; no depends_on edge between non-siblings; grep -rl of the 3 names in the run directory and git grep over all refs (0 hits)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialCutoffDifferentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/RadialFirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-plane-disintegration-a1-pointwise-measure-a1/rlcr-plan-v1.md`
- `/tmp/wrm-decomp-v1/CompForm.lean`
- `/tmp/wrm-decomp-v1/Assembly.lean`
- `/tmp/wrm-decomp-v1/Full.lean`
- `/tmp/wrm-decomp-v1/c1/Proof.lean`
- `/tmp/wrm-decomp-v1/c2/Proof.lean`
- `/tmp/wrm-decomp-v1/c3/Proof.lean`

The snapshot is project 63436ae6 with Mathlib 25730c7c, and its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Every Mathlib lemma the child proofs cite is present in the snapshot at the listed paths and #checks from import GMT.Ch08.Submission: hasDerivAt_integral_of_dominated_loc_of_deriv_le, monotoneOn_of_deriv_nonneg, Antitone.deriv_nonpos, Filter.EventuallyEq.deriv_eq, norm_integral_le_lintegral_norm, lintegral_const_mul', lintegral_indicator, ENNReal.toReal_mono, ContDiff.norm_sq, integral_map, Measure.integrableOn_of_bounded, IntegrableOn.integrable_of_forall_notMem_eq_zero, HasDerivAt.div, real_inner_le_norm and LinearMap.toMatrix_mulVec_repr. SimonGMT's weighted-radial results (hasDerivAt_normalized_weightedCutoffMass, weightedRadial_firstVariation_identity, hasDerivAt_integral_radialCutoff_of_radius, continuous_project) served as the template. They are outside Submission's import closure and absent from the snapshot (no rg match), so the children re-derive what they need. The leaf policy is one theorem per node, no helpers and no import changes, and depends_on is sibling-only; hence radial_field_divergence enters first_variation_lower_bound as the hypothesis (Div). In scratch Lean, all 3 children are fully proved with only propext, Classical.choice and Quot.sound, and the parent's exact frozen type is proved from them plus its two declared dependencies.
