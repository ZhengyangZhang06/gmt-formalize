# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent's step 3 speaks of "the mass measure" μ of C; that it does not depend on the chosen representation is Simon Ch. 6, 3.2(3) (chapter-06.txt lines 763–768: M_W(T) = ∫_{M∩W} θ dH^n for open W ⊆ U, the right side therefore being determined by T). Simon states 3.2(3) without proof. We prove the needed consequence (representation independence of θH^n⌞M) directly by the fundamental lemma of the calculus of variations; this avoids comparing the contract's Euclidean coefficient norm with unit simple n-vectors (which would need Cauchy–Binet, absent from Mathlib).

Notation. R_i = (M_i, θ_i, ξ_i) (carrier, mult, orient), H^n = μHE[n], μ_i := R_i.measure = (H^n⌞M_i).withDensity θ_i, ν := H^n⌞(M_1 ∪ M_2).
1. Preliminaries.
 (a) θ_i ≥ 1 on M_i, so H^n(M_i ∩ K) ≤ μ_i(K) < ∞ for compact K ⊆ U (R_i.locallyIntegrable_mult); hence ν(K) < ∞ for compact K ⊆ U.
 (b) For an orthonormal family τ = (τ_1,…,τ_n) let δ_τ(w_1,…,w_n) := det(⟨τ_i, w_j⟩)_{i,j}: a continuous alternating n-linear form (row-determinant of the vectors (⟨τ_i,w_j⟩)_i ∈ ℝ^n) with δ_τ(τ) = 1 (δ_τ ≡ 1 if n = 0). If τ' is another orthonormal family with span τ' = span τ, put O := (⟨τ_i, τ'_j⟩)_{i,j}. Since τ is an orthonormal basis of the common span, τ'_j = Σ_i O_{ij} τ_i, so δ_{jk} = ⟨τ'_j, τ'_k⟩ = Σ_i O_{ij}O_{ik}, i.e. OᵀO = I; hence δ_τ(τ') = det O ∈ {−1, +1}.
 (c) For orthonormal τ and any n-covector α, |α(τ)| ≤ ‖α‖ (operator norm, ‖τ_i‖ = 1). Hence every unit orientation ξ_0 of an n-plane satisfies ‖ξ_0‖ ≤ 1.
 (d) By R_i.orients, for H^n-a.e. x ∈ M_i there are an n-plane Q_i(x) with HasApproximateTangentSpaceAt n M_i x Q_i(x), an orthonormal family τ^i(x) spanning Q_i(x) and ε_i(x) ∈ {−1, +1} with ξ_i(x)(α) = ε_i(x)·α(τ^i(x)) for all covectors α. In particular ‖ξ_i(x)‖ ≤ 1 and ξ_i(x)(δ_{τ^i(x)}) = ε_i(x) ≠ 0 there.
2. Equality of the vector densities. Put f(x) := 1_{M_1}(x)θ_1(x)ξ_1(x) − 1_{M_2}(x)θ_2(x)ξ_2(x), a function with values in the Banach space Λ_n = MultiVector P n. f is a.e.-strongly measurable for ν (indicators of measurable sets times functions that are a.e.-strongly measurable for H^n⌞M_i), ‖f‖ ≤ 1_{M_1}θ_1 + 1_{M_2}θ_2 ν-a.e. by 1(d), and ∫_K (1_{M_1}θ_1 + 1_{M_2}θ_2) dν = μ_1(K) + μ_2(K) < ∞ for compact K ⊆ U; so f is locally integrable on U with respect to ν. Let g ∈ C^∞(ℝ^P) have compact support with spt g ⊆ U and put I_g := ∫ g f dν ∈ Λ_n. For every n-covector α the form ω := gα lies in 𝒟^n(U); evaluation at α commutes with the Bochner integral (Mathlib ContinuousLinearMap.integral_apply), and by linearity of ξ_i(x),
 I_g(α) = ∫_{M_1} θ_1 ξ_1(ω) dH^n − ∫_{M_2} θ_2 ξ_2(ω) dH^n = R_1.action(ω) − R_2.action(ω) = T(ω) − T(ω) = 0
 (both integrands are integrable, being bounded by sup|g|·‖α‖·θ_i on the compact set spt g ⊆ U). Hence I_g = 0 for all such g, and by the fundamental lemma on the open set U for Banach-valued functions (Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, which needs no local finiteness of ν), f = 0 ν-a.e. on U, hence ν-a.e. (ν is carried by M_1 ∪ M_2 ⊆ U). That is, for ν-a.e. x,
 (★) 1_{M_1}(x)θ_1(x)ξ_1(x) = 1_{M_2}(x)θ_2(x)ξ_2(x) as n-vectors (linear functionals on n-covectors).
 Since ν = H^n⌞(M_1 ∪ M_2), (★) holds for H^n-a.e. x ∈ M_1 ∪ M_2.
3. The carriers agree up to null sets. For H^n-a.e. x ∈ M_1 ∖ M_2, (★) reads θ_1(x)ξ_1(x) = 0, so ξ_1(x) = 0 (θ_1 ≥ 1); by 1(d) this fails for H^n-a.e. x ∈ M_1. Hence H^n(M_1 ∖ M_2) = 0, and symmetrically H^n(M_2 ∖ M_1) = 0.
4. The approximate tangent planes agree. For x ∈ ℝ^P and r > 0 the map b_{x,r}(y) = r^{-1}(y − x) (blowUpMap x r) is injective and is a translation followed by the dilation by r^{-1}, so H^n(b_{x,r}(B)) = r^{-n}H^n(B) for every set B (translation invariance of μHE[n], Mathlib Isometry.euclideanHausdorffMeasure_image, and Mathlib euclideanHausdorffMeasure_smul₀ / euclideanHausdorffMeasure_homothety_image). Hence b_{x,r}(M_1) Δ b_{x,r}(M_2) = b_{x,r}(M_1 Δ M_2) has H^n-measure r^{-n}H^n(M_1 Δ M_2) = 0. Hence ∫_{b_{x,r}(M_1)} f dH^n = ∫_{b_{x,r}(M_2)} f dH^n for all f ∈ C_c(ℝ^P) and r > 0, and therefore, for every x and every subspace Q, HasApproximateTangentSpaceAt n M_1 x Q ⟺ HasApproximateTangentSpaceAt n M_2 x Q. For H^n-a.e. x ∈ M_1 ∩ M_2 both statements 1(d) hold; at such x, HasApproximateTangentSpaceAt n M_2 x Q_1(x) and HasApproximateTangentSpaceAt n M_2 x Q_2(x), so Q_1(x) = Q_2(x) by uniqueness (Simon Ch. 3, 1.5(1); SimonGMT HasApproximateTangentSpaceAt.unique).
5. The multiplicities agree. Let x ∈ M_1 ∩ M_2 be such that (★) and steps 1(d), 4 hold (H^n-a.e. point of M_1 ∩ M_2). Then τ^1(x) and τ^2(x) are orthonormal families spanning the same plane, so s := δ_{τ^1(x)}(τ^2(x)) ∈ {±1} by 1(b). Evaluating (★) at the covector δ := δ_{τ^1(x)} gives θ_1(x)ε_1(x) = θ_2(x)ε_2(x)s; taking absolute values, θ_1(x) = θ_2(x). Thus θ_1 = θ_2 H^n-a.e. on M_1 ∩ M_2.
6. Conclusion. For every measurable A, using steps 3 and 5:
 μ_1(A) = ∫_{M_1∩A} θ_1 dH^n = ∫_{M_1∩M_2∩A} θ_1 dH^n = ∫_{M_1∩M_2∩A} θ_2 dH^n = ∫_{M_2∩A} θ_2 dH^n = μ_2(A).
 Measures that agree on all measurable sets are equal, so R_1.measure = R_2.measure.

## Key steps

1. Testing T on ω = gα for all covectors α and the Banach-valued fundamental lemma give 1_{M_1}θ_1ξ_1 = 1_{M_2}θ_2ξ_2 H^n-a.e. on M_1 ∪ M_2.
2. ξ_i ≠ 0 a.e. (ξ_i(δ_τ) = ±1), so H^n(M_1 Δ M_2) = 0.
3. Blow-ups of a.e.-equal sets coincide, so the approximate tangent planes agree a.e. on M_1 ∩ M_2.
4. Two orthonormal frames of one plane have det(⟨τ^1_i,τ^2_j⟩) = ±1; evaluating at δ_{τ^1} gives θ_1 = θ_2 a.e.; hence θ_1H^n⌞M_1 = θ_2H^n⌞M_2.

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
