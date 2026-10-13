# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.cone_measure_homogeneous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 3, first half: "IsConeCurrent C gives η_{0,λ#}C = C for λ > 0; the mass measure of η_{0,λ#}C is λ^{−n}(η_{0,λ})_#μ (area formula for the homothety), so μ(λA) = λ^nμ(A) for Borel A" — Simon 7.4.5, proof line 698 ("by virtue of the fact that C is a cone", chapter-07.txt lines 697–699), push-forward Ch. 6, 2.23 (chapter-06.txt line 408) and the push-forward of integer multiplicity currents by the area formula Ch. 6, 3.3–3.6 (chapter-06.txt lines 770–830), and the representation independence of the mass measure, which is the sibling imrep_measure_unique (Simon 6.3.2(3)).

Notation. M = R.carrier, θ = R.mult, ξ = R.orient, H^n = μHE[n], μ = R.measure. Fix λ > 0 and put S(y) := λ^{-1}y; for a set A, λA := {λa : a ∈ A} = (x ↦ λx) '' A.
1. Scaling of H^n. For every set B and c > 0, H^n(cB) = c^n H^n(B) (Mathlib euclideanHausdorffMeasure_smul₀). Consequently the push-forward of H^n⌞M under the homeomorphism S is λ^n·H^n⌞S(M): for Borel B, H^n(M ∩ S^{-1}(B)) = H^n(λ(S(M) ∩ B)) = λ^n H^n(S(M) ∩ B). Hence for every function F on ℝ^P (Bochner integral, or lower integral of F ≥ 0):
 (1.1) ∫_{S(M)} F dH^n = λ^{-n} ∫_M F(S(y)) dH^n(y),
 using the change of variables formula for the measurable embedding S (Mathlib integral_map_equiv / lintegral_map_equiv) and linearity in the measure.
2. The cone identity in terms of forms. For an n-covector α and c ∈ ℝ, α∘(c·id) = c^n α (multilinearity: α(cv_1,…,cv_n) = c^nα(v)). By the contract, blowUp C 0 λ is the push-forward of C by the proper affine map η(y) = −λ^{-1}·0 + λ^{-1}y = S(y), acting by (blowUp C 0 λ)(ω) = C(η^#ω) with (η^#ω)(y) = ω(S(y))∘(λ^{-1}id) = λ^{-n}ω(λ^{-1}y) (affinePullbackForm with L = λ^{-1}id, b = 0); η^#ω is again a test form because η is a proper affine isomorphism. The domain of blowUp C 0 λ is dilation 0 λ '' univ = univ, so every test form ω on ℝ^P satisfies the test-form condition in currentEval, and IsConeCurrent C gives
 (2.1) C(ω) = C(η^#ω) for every ω ∈ 𝒟^n(ℝ^P).
3. The rescaled triple R_λ := (M', θ', ξ') with M' := S(M) = λ^{-1}M, θ'(z) := θ(λz), ξ'(z) := ξ(λz) is an IMRep univ n:
 - M' is Borel (image of a Borel set under the homeomorphism S) and M' ⊆ univ.
 - M' is countably n-rectifiable: if M ⊆ M_0 ∪ ⋃_j F_j(ℝ^n) with H^n(M_0) = 0 and F_j Lipschitz, then M' ⊆ S(M_0) ∪ ⋃_j (S∘F_j)(ℝ^n), H^n(S(M_0)) = λ^{-n}H^n(M_0) = 0, and S∘F_j is Lipschitz.
 - θ' is measurable and θ'(z) = θ(λz) > 0 for z ∈ M' (since λz ∈ M).
 - For compact K: ∫_{M'∩K} θ' dH^n = λ^{-n} ∫_{M∩λK} θ dH^n < ∞ by (1.1) (M' ∩ K = S(M ∩ λK)) and the local integrability of θ on the compact set λK.
 - ξ' is a.e.-strongly measurable for H^n⌞M': the map z ↦ λz carries H^n⌞M' to λ^{-n}·H^n⌞M (by step 1), so composing the H^n⌞M-a.e.-strongly measurable ξ with it gives an H^n⌞M'-a.e.-strongly measurable function.
 - Orientation: let E ⊆ M be the H^n-null set off which R.orients holds. S(E) is H^n-null by step 1. For z ∈ M' ∖ S(E), y := λz ∈ M ∖ E, so there is an n-plane Q with HasApproximateTangentSpaceAt n M y Q and IsUnitOrientationOf (ξ y) Q. For r > 0, blowUpMap z r '' M' = {r^{-1}(λ^{-1}m − z) : m ∈ M} = {(λr)^{-1}(m − λz) : m ∈ M} = blowUpMap y (λr) '' M, and λr → 0⁺ as r → 0⁺; hence HasApproximateTangentSpaceAt n M' z Q, and ξ'(z) = ξ(y) is a unit orientation of Q.
4. R_λ represents C. For ω ∈ 𝒟^n(ℝ^P), by (1.1) with F(z) = θ(λz)ξ(λz)(ω(z)) and linearity of ξ(y):
 R_λ.action(ω) = ∫_{M'} θ(λz) ξ(λz)(ω(z)) dH^n(z) = λ^{-n} ∫_M θ(y) ξ(y)(ω(λ^{-1}y)) dH^n(y) = ∫_M θ(y) ξ(y)(λ^{-n}ω(λ^{-1}y)) dH^n(y) = R.action(η^#ω) = C(η^#ω) = C(ω),
 the last two equalities by R.Represents C (η^#ω is a test form on ℝ^P) and (2.1).
5. By the sibling imrep_measure_unique (applied with U = ℝ^P, which is open, to the two representations R_λ and R of C): R_λ.measure = R.measure.
6. For measurable A, M' ∩ A = S(M ∩ λA), so by (1.1) R_λ.measure(A) = ∫_{M'∩A} θ' dH^n = λ^{-n}∫_{M∩λA} θ dH^n = λ^{-n}·R.measure(λA). With step 5, R.measure(λA) = λ^n·R.measure(A), i.e. R.measure((x ↦ λx) '' A) = ENNReal.ofReal(λ^n)·R.measure(A).

## Key steps

1. Pull-back by the dilation scales n-covectors by λ^{-n}; the cone property gives C(ω) = C(λ^{-n}ω(λ^{-1}·)) for all test forms.
2. The rescaled triple (λ^{-1}M, θ(λ·), ξ(λ·)) is an IMRep (rectifiability, integrability and approximate tangent planes rescale).
3. Change of variables (H^n(cB) = c^nH^n(B)) shows the rescaled triple represents C.
4. Uniqueness of the weight (sibling) gives λ^{-n}μ(λA) = μ(A).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 680,745p book/chapter-07.txt (7.4.5 and proof); sed -n 560,640p and 290,335p book/chapter-04.txt (5.1, 3.6); sed -n 290,305p, 400,415p, 730,830p book/chapter-06.txt (2.11-2.12, 2.23, 3.1-3.6); sed -n 75,100p book/chapter-03.txt (1.4-1.5)`
- `grep -n '^theorem \|^def ' simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean; sed -n 60,620p and 1130,1331p FirstVariation.lean`
- `sed -n 1,227p simongmt/Poincare/SimonGMT/Chapter04/Basic.lean; cat simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `sed -n 1,365p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 1,160p and 460,560p simongmt/Poincare/SimonGMT/Chapter06/Currents.lean; cat Chapter06/Mass.lean Chapter06/CurrentLocalEquality.lean Chapter06/AffineCurrentPushforward.lean`
- `grep -rn 'ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib; sed -n 1,60p and 150,240p mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `grep -n 'lemma\|theorem' mathlib/Mathlib/MeasureTheory/Measure/Support.lean; sed -n 186,205p Support.lean`
- `grep -rln 'Hadamard\|Binet' mathlib/Mathlib; grep -rn 'abs_det_le\|det_le_prod' mathlib/Mathlib/LinearAlgebra mathlib/Mathlib/Analysis`
- `grep -rn 'hausdorffMeasure_smul₀\|euclideanHausdorffMeasure_homothety_image\|det_to_matrix_orthonormalBasis_real\|aemeasurable_of_tendsto_metrizable_ae\|integral_withDensity_eq_integral_smul\|euclideanHausdorffMeasure_eq_volume\|eq_smul_basis_det' mathlib/Mathlib; sed -n 60,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rhoE '"lean_name": *"[^"]+"' nodes dag.json problem.json (reserved DAG names)`
- `lake env lean /tmp/hs-decomp/Stmts.lean and /tmp/hs-decomp/Final.lean (six child types, #synth MeasurableSpace/BorelSpace on Euclid P →L[ℝ] Euclid P, conditional parent assembly, #print axioms)`
- `lake env lean /tmp/hs-decomp-review/Child4Check.lean, Child5Check.lean, Child2StepCheck.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Hadamard.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/tmp/hs-decomp/Stmts.lean`
- `/tmp/hs-decomp/Final.lean`
- `/tmp/hs-decomp-review/Child4Check.lean`
- `/tmp/hs-decomp-review/Child5Check.lean`
- `/tmp/hs-decomp-review/Child2StepCheck.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. All six child Lean types elaborate in namespace GMT.Ch07 with the contract's opens; the measurable space on Euclid P →L[ℝ] Euclid P is the Borel instance (ContinuousLinearMap.instMeasurableSpace / instBorelSpace) that SimonGMT also uses; the conditional parent assembly from the six children and the sibling MinimizingImpliesStationary compiles with axioms propext, sorryAx, Classical.choice, Quot.sound. Library support: SimonGMT Chapter04/FirstVariation.lean proves Simon 4.3.6 (IsStationaryIn.satisfiesStationaryMonotonicity, monotonicityDefect_eq_zero, closed balls, all n) for Chapter04.RectifiableVarifold, whose fields (Basic.lean) include an a.e.-measurable tangent projection — hence the separate measurability child; Chapter03/Rectifiable.lean gives HasApproximateTangentSpaceAt (Simon 3.1.4 blow-up definition) and HasApproximateTangentSpaceAt.unique; Chapter06 gives support = U \ zeroRegion, massOn with the Euclidean coefficient norm and the proper affine push-forward used by blowUp. Mathlib (snapshot) supplies IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (Banach-valued, no local finiteness needed), Measure.support with measure_compl_support and mem_support_iff_forall, euclideanHausdorffMeasure_smul₀ / euclideanHausdorffMeasure_homothety_image / Isometry.euclideanHausdorffMeasure_image / EuclideanSpace.euclideanHausdorffMeasure_eq_volume, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, aemeasurable_of_tendsto_metrizable_ae', integral_withDensity_eq_integral_smul. There is no Hadamard determinant inequality or Cauchy–Binet formula (Matrix/Hadamard.lean is the Hadamard product), so Simon 6.3.2(3) (M_W(T) = μ(W)) is bypassed by fundamental-lemma arguments in the support and uniqueness children. Reviewer scratch proofs of radial_tangency_of_ball_ratio and radial_moment_vanishes (exact frozen types) and of the cone pull-back step compile with only propext, Classical.choice, Quot.sound. No other DAG branch has reserved names below depth 1; the six proposed names are new.
