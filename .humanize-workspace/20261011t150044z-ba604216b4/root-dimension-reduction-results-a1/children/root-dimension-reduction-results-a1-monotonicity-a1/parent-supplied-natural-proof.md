# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1`
- Child DAG node: `root.dimension_reduction_results-a1.monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step T1, i.e. Simon Ch. 4, 3.1–3.17 and 3.11 (chapter-04.txt lines 215–430) applied to the varifold of T through the sibling minimizing_implies_stationary; the computations are written out. Write ω_n := unitBallVolume n ∈ (0, ∞).
0. (Setting.) Put k := P − n and ℓ := d − n; then P = n + k, d = n + ℓ and ℓ ≤ k. Transporting along the equality Euclid P = Euclid (n + k) (nothing else changes), the hypotheses are exactly those of the sibling minimizing_implies_stationary (DAG node root.minimizing_implies_stationary-a1, frozen type MinimizingImpliesStationary). T is integer multiplicity (first conjunct of IsMinimizingIn); fix a representation R = (M, θ, ξ) and put μ := R.measure = θ·H^n⌞M and V := v(M, θ). By the sibling, R.HasLocallyBoundedMeanCurvature: there is a μ-measurable H : ℝ^P → ℝ^P such that δV(X) := ∫ div_M X dμ = −∫ X·H dμ for every C¹ vector field X with compact support in U (div_M X(x) = trace(p_{T_xM} ∘ DX(x)), T_xM the approximate tangent plane, which exists μ-a.e.), and for every compact K ⊆ U there is Λ_K with |H| ≤ Λ_K μ-a.e. on K; and R.IsStationaryAlong N. By the sibling child im_mass_measure (a), M_W(T) = μ(W) for every open W ⊆ U; these values are finite when closure W is a compact subset of U.
1. (Differential identity; Simon 3.2–3.4 and 3.16.) Fix a compact K ⊆ U, Λ := max(Λ_K, 0), y ∈ ℝ^P and R > 0 with closedBall y R ⊆ K, ε ∈ (0, 1), and φ ∈ C¹(ℝ; [0, 1]) with φ' ≤ 0, φ = 1 on (−∞, 1] and φ = 0 on [1 + ε, ∞). For ρ ∈ (0, R/(1 + ε)) let X_ρ(x) := φ(|x − y|/ρ)(x − y), a C¹ vector field with support in closedBall y ((1 + ε)ρ) ⊆ K. With r := |x − y| and D^⊥r the component of (x − y)/r orthogonal to T_xM, at μ-a.e. x we have div_M X_ρ = n·φ(r/ρ) + (r/ρ)φ'(r/ρ)(1 − |D^⊥r|²) (Simon 3.2: ∇^M φ(r/ρ) = ρ^{−1}φ'(r/ρ) p_{T_xM}((x − y)/r) and div_M(x − y) = n). Put I(ρ) := ∫ φ(r/ρ) dμ and J(ρ) := ∫ φ(r/ρ)|D^⊥r|² dμ; both are differentiable in ρ with derivatives obtained by differentiating under the integral sign (φ' is bounded and all integrands vanish outside K). Since (r/ρ)φ'(r/ρ) = −ρ·∂_ρ[φ(r/ρ)], the identity δV(X_ρ) = −∫ X_ρ·H dμ reads n·I(ρ) − ρI'(ρ) = −ρJ'(ρ) − ∫ φ(r/ρ)(x − y)·H dμ, i.e. d/dρ(ρ^{−n}I(ρ)) = ρ^{−n}J'(ρ) + ρ^{−n−1}∫ φ(r/ρ)(x − y)·H dμ.
2. (Monotonicity on closed balls; Simon 3.17.) J is nondecreasing in ρ (φ(r/ρ) is nondecreasing in ρ because φ' ≤ 0), so J' ≥ 0. On the support of φ(r/ρ) we have |x − y| ≤ (1 + ε)ρ and |H| ≤ Λ μ-a.e., so the last term is ≥ −(1 + ε)Λρ^{−n}I(ρ). Hence d/dρ(e^{(1+ε)Λρ}ρ^{−n}I(ρ)) ≥ 0, and e^{(1+ε)Λρ}ρ^{−n}I(ρ) is nondecreasing on (0, R/(1 + ε)). Let ε ↓ 0 along a sequence of such φ = φ_ε decreasing pointwise to the indicator of (−∞, 1]; by dominated convergence I_ε(ρ) → μ(closedBall y ρ). Hence e^{Λσ}σ^{−n}μ(closedBall y σ) ≤ e^{Λρ}ρ^{−n}μ(closedBall y ρ) for 0 < σ < ρ < R. (This is the statement of SimonGMT HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn for the library's varifold structure.)
3. ((i).) Let 0 < σ < ρ < R and σ ≤ s < ρ. Then e^{Λσ}σ^{−n}μ(B_σ(y)) ≤ e^{Λσ}σ^{−n}μ(closedBall y σ) ≤ e^{Λs}s^{−n}μ(closedBall y s) ≤ e^{Λs}s^{−n}μ(B_ρ(y)), and letting s ↑ ρ gives e^{Λσ}σ^{−n}μ(B_σ(y)) ≤ e^{Λρ}ρ^{−n}μ(B_ρ(y)). As B_ρ(y) ⊆ K ⊆ U is open, μ(B_ρ(y)) = M_{B_ρ(y)}(T) (step 0), so ρ ↦ ofReal(e^{Λρ}/ρ^n)·M_{B_ρ(y)}(T) is nondecreasing on (0, R). Λ depends only on K, as required.
4. ((ii).) If N = ℝ^P, every vector v is tangent to N at every point (take γ(t) := x + tv in the definition of tangentSpace), so R.IsStationaryAlong N says δV(X) = 0 for every C¹ field X with compact support in U. Then steps 1–3 hold with the H-term replaced by 0, i.e. with Λ = 0, on every closed ball closedBall y R' ⊆ U. If B_R(y) ⊆ U and 0 < σ < ρ < R, choose R' ∈ (ρ, R); closedBall y R' ⊆ B_R(y) ⊆ U, and the Λ = 0 version of step 3 on (0, R') compares σ and ρ.
5. ((iii).) Let y ∈ U; choose R > 0 with K := closedBall y R ⊆ U and Λ as in (i). g(ρ) := e^{Λρ}ρ^{−n}μ(B_ρ(y)) is nondecreasing, nonnegative and finite on (0, R), so g(ρ) → L := inf g ∈ [0, ∞) as ρ ↓ 0, and ρ^{−n}μ(B_ρ(y)) = e^{−Λρ}g(ρ) → L. With θ := L/ω_n ≥ 0 we get M_{B_ρ(y)}(T)/(ω_n·ofReal(ρ^n)) → ofReal θ as ρ ↓ 0, i.e. HasMassDensity T y θ. Limits in [0, ∞] are unique, so this θ is unique; call it Θ(y), and put Θ(y) := 0 for y ∉ U.
6. ((iii), upper semicontinuity; Simon 3.11.) Θ of step 5 satisfies HasMassDensity T y (Θ(y)) for y ∈ U. To see that Θ is upper semicontinuous on U, let y_j → y with y_j, y ∈ U, choose R > 0 with closedBall y (2R) ⊆ U and Λ for K := closedBall y (2R), and let ρ, η > 0 with ρ + η < R. For large j, |y_j − y| < η, so closedBall y_j R ⊆ K and, by step 5 and monotonicity at y_j, Θ(y_j) ≤ e^{Λρ}μ(B_ρ(y_j))/(ω_nρ^n) ≤ e^{Λρ}μ(B_{ρ+η}(y))/(ω_nρ^n). Hence limsup_j Θ(y_j) ≤ e^{Λρ}μ(closedBall y (ρ + η))/(ω_nρ^n); letting η ↓ 0 replaces closedBall y (ρ + η) by closedBall y ρ, and letting ρ ↓ 0 gives limsup_j Θ(y_j) ≤ Θ(y), because (ω_nρ^n)^{−1}μ(closedBall y ρ) → Θ(y) as well (for s < ρ < s', μ(B_ρ(y)) ≤ μ(closedBall y ρ) ≤ μ(B_{s'}(y))).
7. ((iv).) For H^n-a.e. x ∈ M, Θ^n(μ, x) = θ(x) (Simon Ch. 3, Theorem 1.9 together with Ch. 4, Remark 1.8(2), as used at chapter-04.txt line 350: H^n⌞M has density 1 at H^n-a.e. point of the countably n-rectifiable set M, and H^n⌞M-a.e. point of M is a Lebesgue point of the locally integrable θ); since θ ≥ 1 on M, Θ ≥ 1 μ-a.e. Let y ∈ spt T and HasMassDensity T y θ_y; by uniqueness θ_y = Θ(y). By im_mass_measure (b), μ(B_ε(y)) > 0 for every ε > 0, so every small ball B_ε(y) ⊆ U contains a point z_ε with Θ(z_ε) ≥ 1. By step 6, θ_y = Θ(y) ≥ limsup_{ε↓0} Θ(z_ε) ≥ 1.

## Key steps

1. The sibling minimizing_implies_stationary gives a representation whose varifold has generalized mean curvature bounded on compacts (and zero when N = ℝ^P); im_mass_measure identifies masses with the varifold weight.
2. First-variation identity with radial fields X = φ(r/ρ)(x − y) gives d/dρ(ρ^{−n}I) ≥ −Λρ^{−n}I, hence e^{Λρ}ρ^{−n}μ(B̄_ρ) is nondecreasing; pass to open balls.
3. Monotone limits give existence of Θ^n at every point of U; the 3.11 argument gives upper semicontinuity of Θ on U.
4. Θ = θ ≥ 1 μ-a.e. plus upper semicontinuity give Θ ≥ 1 on spt T.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n 'μHE\|euclideanHausdorffMeasure' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (same file)`
- `grep -rn 'theorem massOn_le_liminf\|theorem boundary_affinePushforward\|exp_normalizedBallMass_monotoneOn\|theorem bvVariationOn_le_liminf_of_locallyL1\|theorem cone_simonsDefect_lower_bound' simongmt/Poincare`
- `grep -n 'def support\|zeroRegion\|def massOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn dimred --include=*.lean GMT .lake/packages/simongmt/Poincare; grep -c dimred dag.json; grep -rln dimred_ .swarm-worktrees/*/gmt-ch07/GMT (no match anywhere)`
- `python3 inspection of dag.json: sibling lean_statements (abstract_dimension_reduction, density_and_tangent_cones, density_one_implies_regular, compactness_of_minimizing_currents, minimizing_implies_stationary) and similar lemma nodes in other branches (dtc_mass_eq_measure, dor_imrep_massOn_eq_measure_and_support, dtc_dim_zero_eq_zero, imrep_measure_eq_of_represents_same_current, rsd_massOn_eq_measure)`
- `lean -R /tmp/dr-v2-check/src /tmp/dr-v2-check/src/CheckV2Types.lean (private olean of GMT.Ch07.Submission; 12 child types declared as Submission.X in namespace GMT.Ch07 with the contract opens; assembly ⟨A, B, C⟩; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-review-receipt-v1.json`
- `/tmp/dr-v2-check/src/CheckV2Types.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD), mathlib 25730c7c and simongmt 2b36630. The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean; its only sorry is the frozen main_theorem.

Normalization (decides correction R1). Mathlib defines μHE[d] = addHaarScalarFactor(volume, μH[d]) • μH[d] (Measure.lean, lines 68–101). The scalar is in ℝ≥0 and nonzero (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero), so μ_A = ϑ_A·μHE[n] gives ∫_K ϑ_A dμH[n] = c_n⁻¹·μ_A(K).

SimonGMT definitions used:
- massOn is the sSup over admissible forms with Euclidean coefficient norm ≤ 1 (Mass.lean).
- support = U \ zeroRegion (CurrentLocalEquality.lean, lines 108–117).
- WeaklyConvergesOn.massOn_le_liminf (Mass.lean:100) gives the lower semicontinuity used for the new mass bounds.

Other cited library facts exist:
- GeometricCurrentOn.boundary_affinePushforward (AffineCurrentPushforward.lean:188);
- HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn (Chapter04/MeanCurvature.lean:361);
- bvVariationOn_le_liminf_of_locallyL1 (Chapter02/BV.lean:225);
- cone_simonsDefect_lower_bound (AppendixB/ConeDefect.lean:228).

The library provides none of the following for the contract's IMRep currents: the mass–measure identity, product currents, Federer–Fleming compactness, or Appendix A.4. These are children or sibling prerequisites.

Lean check. All twelve child types elaborate after import GMT.Ch07.Submission, in namespace GMT.Ch07 with the contract opens, with only the stub sorry warnings. The assembly ⟨A, B, C⟩ proves IntegerDensityAndTangentPlanes ∧ SingularSetSmallWhereDensityBelowTwo ∧ CodimensionOneRegularity, and the conditional assembly depends only on propext, Classical.choice and Quot.sound.

Names. No dimred_ identifier occurs in the workspace, SimonGMT, any speculative worktree or dag.json. Similar lemmas in other branches have different types and names, so there is neither reuse nor collision.
