# Parent-supplied natural-language proof

- Parent DAG node: `root.varifold_tangents-a1.rescaled_divergence_bound-a1`
- Child DAG node: `root.varifold_tangents-a1.rescaled_divergence_bound-a1.rescaled_integral_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–3 of the parent proof (fact R2; Simon Ch. 8, §5, p. 215, rescalings η_{x,λ#}V of 5.1–5.2). Notation: ψ(z) := t⁻¹•(z − x); φ(z,S) := (ψ z, S); f(w,S) := div_S X(w) := Varifold.tangentialDivergence X w S = trace(S·jacobian X w), where jacobian X w is the coordinate matrix of fderiv ℝ X w; Y(z) := t•X(ψ z); δV(Y) := V.firstVariation Y = ∫ div_S Y(z) dV.measure(z,S).
1. (Derivative of the pulled-back field.) Fix w ∈ ℝ^N. The map z ↦ z − x has derivative Id at w, so ψ has derivative t⁻¹•Id at w (HasFDerivAt.sub_const, HasFDerivAt.const_smul). X is C¹, hence differentiable at ψ(w), with derivative D := fderiv ℝ X (ψ w). By the chain rule (HasFDerivAt.comp), X∘ψ has derivative D∘(t⁻¹•Id) at w, and Y = t•(X∘ψ) has derivative t•(D∘(t⁻¹•Id)) at w (HasFDerivAt.const_smul). For every v, (t•(D∘(t⁻¹•Id)))(v) = t•D(t⁻¹•v) = (t·t⁻¹)•D(v) = D(v), because t ≠ 0. Hence fderiv ℝ Y w = fderiv ℝ X (ψ w) (HasFDerivAt.fderiv).
2. (Pointwise divergence identity.) By step 1, jacobian Y w = jacobian X (ψ w) for every w, so for every (z,S): div_S Y(z) = trace(S·jacobian Y z) = trace(S·jacobian X (ψ z)) = div_S X(ψ z) = f(φ(z,S)).
3. (Scalar factor.) By definition, rescaledMeasure V x t = c • (V.measure.map φ) with c := ofReal((t⁻¹)^n). For every function g and every measure μ, ∫ g d(c•μ) = c.toReal • ∫ g dμ (integral_smul_measure; no integrability hypothesis is needed). Since t > 0, (t⁻¹)^n ≥ 0, so c.toReal = (t⁻¹)^n (ENNReal.toReal_ofReal). Thus ∫ f d(rescaledMeasure V x t) = (t⁻¹)^n · ∫ f d(V.measure.map φ).
4. (Pushforward.) φ is continuous (its components (z,S) ↦ t⁻¹•(z − x) and (z,S) ↦ S are continuous), hence measurable; f is continuous (Varifold.continuous_tangentialDivergence, as X is C¹), hence AE-strongly measurable with respect to V.measure.map φ. Therefore integral_map gives ∫ f d(V.measure.map φ) = ∫ f(φ(z,S)) dV.measure(z,S), again without any integrability hypothesis.
5. (Conclusion.) By step 2 the integrands f∘φ and (z,S) ↦ div_S Y(z) agree everywhere, so ∫ f∘φ dV.measure = ∫ div_S Y(z) dV.measure(z,S) = V.firstVariation Y (definition of Varifold.firstVariation). Combining steps 3–5: ∫ div_S X dV_{x,t} = (t⁻¹)^n · V.firstVariation Y, i.e. ∫ z, Varifold.tangentialDivergence X z.1 z.2 ∂(rescaledMeasure V x t) = t⁻¹ ^ n * V.firstVariation (fun z ↦ t • X (t⁻¹ • (z − x))). ∎

## Key steps

1. Chain rule: D(t·X∘ψ)(w) = t·DX(ψ w)∘(t⁻¹·Id) = DX(ψ w), so jacobian Y w = jacobian X (ψ w).
2. Pointwise identity div_S Y(z) = div_S X(ψ z) for all (z,S).
3. integral_smul_measure with toReal(ofReal((t⁻¹)^n)) = (t⁻¹)^n pulls out the scalar factor.
4. integral_map (φ continuous, integrand continuous) turns the pushforward integral into ∫ div_S X(ψ z) dV(z,S).
5. That integral equals ∫ div_S Y dV = δV(Y), giving ∫ div_S X dV_{x,t} = (t⁻¹)^n·δV(Y).

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (project 63436ae6, mathlib 25730c7c); lake-manifest + git rev-parse: .lake/packages/mathlib = 25730c7c, simongmt = 2b366308`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean vs workspace GMT/Ch08/Contract.lean and Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'def rescaledMeasure|def variationMeasure' project/GMT/Ch08/Contract.lean (lines 96, 63)`
- `rg -n '^theorem integral_map\b|^theorem integral_smul_measure\b' mathlib/Mathlib/MeasureTheory/Integral/Bochner/*.lean`
- `rg -n 'closure_ball_subset_closedBall|ofReal_inv_of_pos|protected theorem mul_inv|inv_mul_lt_iff₀|toReal_ofReal|ofReal_mul|pow_ne_top|HasFDerivAt.comp|HasFDerivAt.const_smul|sub_const' over snapshot mathlib/Mathlib`
- `rg -l firstVariation mathlib/Mathlib in snapshot (0 files: no varifold first variation in Mathlib); rg -l varifold_tangents_rdb_ over snapshot (0 files)`
- `grep -n 'def tangentialDivergence|structure TestVectorField|def firstVariationNormOn|UnitSupportedIn|firstVariation_const_smul|continuous_tangentialDivergence|tangentialDivergence_zero|firstVariationRieszMeasure_eq_norm' over pinned SimonGMT Chapter08`
- `grep -rn 'ofReal |V.firstVariation' and 'firstVariation_comp|blowUp.*firstVariation|rescale.*firstVariation' over SimonGMT (no existing variationMeasure-form bound or rescaling identity; only le_firstVariationNormOn, firstVariation_bound_of_unit_bound, VarifoldConvergence:86)`
- `read SimonGMT FirstVariationBounds.lean, FirstVariationRiesz.lean:200-313, BallVariationBound.lean, TangentRescaling.lean (blowUpMeasure equals rescaledMeasure but is outside Submission's import closure)`
- `python3 -I import verifier lean_contract.validate_lean_statement and gmt-compare.contract_scope/child_modules on both child statements (scope: open Set Filter MeasureTheory Metric; open scoped Topology ENNReal CompactlySupported Pointwise; namespace GMT.Ch08; open Poincare.SimonGMT; open Poincare.SimonGMT.Chapter08; section/end Definitions)`
- `lake env lean /tmp/rdb-decomp/Final2.lean (children proved, parent frozen type from children, exact Submission.X replays, #print axioms) and /tmp/rdb-decomp/Stub2.lean (child proofs sorry'd, parent still compiles)`
- `grep -rhoE '"lean_name": *"[^"]*"' over run dir and grep for varifold_tangents_rdb_ over .humanize and cluster-state (no reservation)`
- `grep book/sources/chapter-08-source.txt for 2.5 (p. 209) and 5.1-5.2 (p. 215)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/BallVariationBound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-08-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-rescaled-divergence-bound-a1/parent-child-handoff.json`

Snapshot = project 63436ae6 + Mathlib 25730c7c, matching the workspace .lake Mathlib; SimonGMT is pinned at 2b366308. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Mathlib (snapshot) supplies the change-of-variables tools for child A: integral_smul_measure (Bochner/Basic.lean:1052), integral_map (:1081), ENNReal.toReal_ofReal (ENNReal/Basic.lean:252), and the chain rule (HasFDerivAt.comp, FDeriv/Comp.lean:107; HasFDerivAt.const_smul, FDeriv/Add.lean:67). It supplies the parent's ENNReal and ball arithmetic: ENNReal.mul_inv (ENNReal/Inv.lean:245), ofReal_inv_of_pos (:945), ofReal_mul (ENNReal/Real.lean:297), pow_ne_top (ENNReal/Operations.lean:241), closure_ball_subset_closedBall (Pseudo/Lemmas.lean:73) and inv_mul_lt_iff₀ (GroupWithZero/Basic.lean:919). Mathlib has no varifold first variation (0 files match).

Pinned SimonGMT, all inside Submission's import closure, supplies child B's ingredients: firstVariationRieszMeasure_eq_norm (FirstVariationRiesz.lean:218), le_firstVariationNormOn, TestVectorField.scale and tsupport_scale_subset (FirstVariationBounds.lean), firstVariation_const_smul, firstVariation_zero and continuous_tangentialDivergence (Varifold.lean). SimonGMT has no lemma for the variationMeasure-form bound or for the rescaling identity. Its blowUpMeasure (TangentRescaling.lean) equals rescaledMeasure but is outside the import closure and has no first-variation identity. Hence both children are new, needed obligations.

Lean checks, in a scratch copy using the comparator's replayed scope:
- Both child statements pass validate_lean_statement and the `exact Submission.X` replay, and are fully proved.
- The parent's exact frozen type is proved from the two child statements alone.
- Axioms are only propext, Classical.choice and Quot.sound.

No varifold_tangents_rdb_ name is reserved anywhere in the run, cluster-state or sources.
