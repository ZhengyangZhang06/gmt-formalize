# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.radial_moment_vanishes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 4–6, along the direct route recorded in the parent's step 5 ("Since x^T = x a.e., the same computation shows directly ∫hφ(r/ρ)dμ = ∫div_M Y_ρ dμ = 0"), i.e. Simon 7.4.5, proof lines 708–719 (chapter-07.txt): with h(x) = ⟨e, x⟩ (the book takes e = e_1), x·∇^V h = e·x^T, the right side of (1) equals ∫ e·∇^V Ψ dμ = ∫ div_V(Ψe) dμ, and this vanishes because V is stationary. Here we use the profile φ(s) := 4ρ²·max(1 − s², 0), for which the parent's primitive is Ψ_ρ(s) = −∫_s^∞ tφ(t/ρ)dt = −max(ρ² − s², 0)², so Y_ρ(x) = Ψ_ρ(|x|)e = −max(ρ² − |x|², 0)² e; we work with Y := −Y_ρ. The parent's requirements "φ ∈ C¹, constant near 0" only served the field X_ρ of its step 4, which is not used on this route; that Y is C¹ is checked directly.

Notation. M = R.carrier, θ = R.mult, μ = R.measure, H^n = μHE[n], p_x := orthogonal projection onto approxTangentPlane n M x, m(x) := max(ρ² − |x|², 0). Fix e ∈ ℝ^P and ρ ∈ ℝ.
1. The profile g(t) := (max(t, 0))² is C¹ on ℝ with g'(t) = 2max(t, 0): for t < 0, g ≡ 0 near t; for t > 0, g(s) = s² near t; at t = 0, |g(h) − g(0)| ≤ h², so g'(0) = 0; and t ↦ 2max(t,0) is continuous.
2. The field Y(x) := g(ρ² − |x|²)·e is C¹ (composition of g with the smooth map x ↦ ρ² − |x|², times the constant vector e) with
 DY(x)w = g'(ρ² − |x|²)·(−2⟨x, w⟩)·e = −4m(x)⟨x, w⟩e.
 If |x| ≥ |ρ| then ρ² − |x|² ≤ 0 and Y(x) = 0, so spt Y ⊆ closedBall(0, |ρ|) and Y has compact support.
3. Tangential divergence. tangentialDivergence n M Y x = trace(p_x ∘ DY(x)). The map p_x ∘ DY(x) is w ↦ −4m(x)⟨x, w⟩ p_x(e), and the trace of w ↦ ⟨a, w⟩b equals ⟨a, b⟩ (rank-one map); hence
 tangentialDivergence n M Y x = −4m(x)⟨x, p_x e⟩ = −4m(x)⟨p_x x, e⟩ (p_x is self-adjoint).
 By hypothesis (ii), p_x x = x for μ-a.e. x, so tangentialDivergence n M Y x = −4m(x)⟨e, x⟩ for μ-a.e. x. (This is the identity div_V Y_ρ = φ(r/ρ)e·x^T of the parent's step 5, with x^T = x.)
4. Stationarity. By hypothesis (i), 0 = R.firstVariation Y = ∫_M θ·tangentialDivergence n M Y dH^n = ∫ tangentialDivergence n M Y dμ (Mathlib integral_withDensity_eq_integral_smul; μ = (H^n⌞M).withDensity θ with θ a measurable ℕ-valued density). Since the integrand agrees μ-a.e. with x ↦ −4m(x)⟨e, x⟩ (step 3), the Bochner integrals agree (integral_congr_ae; no integrability needs to be checked for this), so 0 = ∫ −4m(x)⟨e, x⟩ dμ = −4∫ m(x)⟨e, x⟩ dμ.
5. Therefore ∫ max(ρ² − |x|², 0)·⟨e, x⟩ dμ(x) = 0.

## Key steps

1. Y(x) = max(ρ² − |x|², 0)² e is a C¹ compactly supported field with DY(x)w = −4max(ρ² − |x|², 0)⟨x,w⟩e.
2. div_M Y = trace(p_x∘DY) = −4max(ρ² − |x|², 0)⟨p_x x, e⟩ = −4max(ρ² − |x|², 0)⟨e, x⟩ μ-a.e. by radial tangency.
3. Stationarity: 0 = R.firstVariation Y = ∫ div_M Y dμ = −4∫max(ρ² − |x|², 0)⟨e,x⟩dμ.

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
