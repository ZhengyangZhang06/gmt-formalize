# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.radial_tangency_of_ball_ratio-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 3, second half: "The monotonicity identity (Ch. 4, 3.6, H = 0) ρ^{−n}μ(B_ρ(0)) − σ^{−n}μ(B_σ(0)) = ∫_{B_ρ(0)∖B_σ(0)}|D^⊥r|²r^{−n}dμ (r = |x|, D^⊥r the projection of Dr = x/r onto (T_xM)^⊥) therefore gives D^⊥r = 0 μ-a.e., i.e. x^T := p_{T_xM}(x) = x for μ-a.e. x" — Simon Ch. 4, 3.6 (chapter-04.txt lines 290–312; B_ρ denotes a closed ball in Simon's notation), formalized in SimonGMT as Chapter04.RectifiableVarifold.IsStationaryIn.satisfiesStationaryMonotonicity with Chapter04.RectifiableVarifold.monotonicityDefect_eq_zero. The identity holds for every n ≥ 0 (for n = 0 it reads μ(B̄_ρ) = μ(B̄_σ) + μ(B̄_ρ ∖ B̄_σ)), so no case distinction is needed.

Notation. M = R.carrier, θ = R.mult, μ = R.measure = θH^n⌞M (H^n = μHE[n]), T_x := approxTangentPlane n M x, p_x its orthogonal projection, B̄_ρ := closedBall(0, ρ).
1. Local finiteness. μ(K) = ∫_{M∩K} θ dH^n < ∞ for compact K (R.locallyIntegrable_mult with U = ℝ^P). Since θ ≥ 1 on M, a statement holds μ-a.e. iff it holds H^n-a.e. on M.
2. Tangent planes. By R.orients, for H^n-a.e. x ∈ M some n-plane Q satisfies HasApproximateTangentSpaceAt n M x Q; at such x the defining "if" of approxTangentPlane holds, so HasApproximateTangentSpaceAt n M x T_x and dim T_x = n.
3. The varifold V = v(M, θ). The data — M (Borel, countably n-rectifiable: R.measurableSet_carrier, R.rectifiable), the real multiplicity x ↦ θ(x) (positive on M, measurable, integrable on M ∩ K for compact K by step 1), the tangent field x ↦ T_x (an approximate tangent plane H^n-a.e. on M by step 2), whose projection x ↦ p_x is measurable for the weight by hypothesis (ii), and the weight μHE[n].withDensity(1_M θ) = (H^n⌞M).withDensity θ = μ, locally finite by step 1 — form a rectifiable n-varifold in the sense of Simon Ch. 4 §1 (precisely the fields of SimonGMT Chapter04.RectifiableVarifold, with weight equal to R.measure).
4. V is stationary in ℝ^P (Simon Ch. 4, 2.4). For X ∈ C¹ with compact support, the first variation of V is ∫ div_M X dμ with div_M X(x) = trace(DX(x) ∘ p_x) (SimonGMT convention), which equals trace(p_x ∘ DX(x)) = tangentialDivergence n M X x because trace(AB) = trace(BA). By ∫ f dμ = ∫_M θ f dH^n (Mathlib integral_withDensity_eq_integral_smul, θ a measurable ℕ-valued density), ∫ div_M X dμ = ∫_M θ·tangentialDivergence n M X dH^n = R.firstVariation X = 0 by hypothesis (i).
Implementation note: the SimonGMT monotonicity results live in Poincare.SimonGMT.Chapter04.FirstVariation, which the contract does not import; the implementation file imports it. The weight identity of step 3 is μHE[n].withDensity(1_M·ofReal θ) = (μHE[n]⌞M).withDensity θ = R.measure (Mathlib withDensity_indicator, ENNReal.ofReal_natCast).
5. Monotonicity identity (Simon Ch. 4, 3.6 with centre 0; the condition B̄_{R_0}(0) ⊆ U holds for every R_0 since U = ℝ^P). For 0 < σ ≤ ρ:
 ρ^{-n}μ(B̄_ρ) = σ^{-n}μ(B̄_σ) + ∫_{B̄_ρ∖B̄_σ} |D^⊥r|²(x) |x|^{-n} dμ(x), where |D^⊥r|²(x) := |(id − p_x)(x/|x|)|² for x ≠ 0;
 all terms are finite and nonnegative, and the integrand is μ-measurable by hypothesis (ii).
6. Constant ratio. By hypothesis (iii), ρ^{-n}μ(B̄_ρ) = μ(B̄_1) = σ^{-n}μ(B̄_σ) < ∞ for all ρ, σ > 0. Hence ∫_{B̄_ρ∖B̄_σ} |D^⊥r|² |x|^{-n} dμ = 0 (SimonGMT monotonicityDefect_eq_zero). The integrand is ≥ 0 and |x|^{-n} > 0 on the annulus, so |D^⊥r|²(x) = 0 for μ-a.e. x with σ < |x| ≤ ρ.
7. Conclusion. Apply step 6 with σ = 1/j, ρ = j for j = 1, 2, …; the union of these annuli is ℝ^P ∖ {0}, so (id − p_x)(x/|x|) = 0, i.e. (multiplying by |x|) p_x(x) = x, for μ-a.e. x ≠ 0. For x = 0, p_0(0) = 0 = x. Hence (approxTangentPlane n R.carrier x).starProjection x = x for μ-a.e. x.

## Key steps

1. V = v(M,θ) with tangent field approxTangentPlane, measurable projection (hypothesis) and weight R.measure is a rectifiable n-varifold.
2. trace(DX∘p) = trace(p∘DX), so hypothesis (i) makes V stationary in ℝ^P.
3. Monotonicity identity (Ch. 4, 3.6; SimonGMT satisfiesStationaryMonotonicity) with constant ratio ρ^{-n}μ(B̄_ρ) forces ∫_{annulus}|D^⊥r|²r^{-n}dμ = 0.
4. Hence (id − p_x)(x) = 0 μ-a.e. on every annulus, so p_x x = x μ-a.e.

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
