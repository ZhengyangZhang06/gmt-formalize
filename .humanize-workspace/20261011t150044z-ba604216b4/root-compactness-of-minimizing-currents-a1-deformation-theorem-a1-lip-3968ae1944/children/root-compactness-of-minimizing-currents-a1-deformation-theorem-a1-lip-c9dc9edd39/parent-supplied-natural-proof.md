# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.cylinder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof A2 (product [[0,1]] × X via the slice operator, its support, boundary formula and mass, A2(a)–(f)) and the verification of conjuncts (7)–(9). Notation: ι, J, e₀ as in the statement; |α| := covectorEuclideanNorm α; NC as in the parent. Siblings used: Submission.cmcdt_lpo_slice_forms ((a) slices, (b) affine slices, (c), (d) homotopy identities, (e) Minkowski bound) and Submission.cmcdt_lpo_current_toolkit applied to (VO), (REP) ((MSB), (BC), (SB), (LOC)). (L1), (L2) are the first two conjuncts of (LB). Φ(γ) := (γ.curryLeft e₀).compContinuousLinearMap J for a (m+1)-covector γ on ℝ^{N+1}; Φ(γ)(v) = γ(Fin.cons e₀ (J ∘ v)), Φ is continuous linear, and ‖J‖ ≤ 1 (‖Jv‖ = ‖v‖), ‖e₀‖ = 1.
1. Pointwise bounds. For a (m+1)-covector γ: |Φ(γ)| ≤ ‖J‖^m·|γ.curryLeft e₀| ≤ ‖e₀‖·|γ| = |γ| by (L1), (L2). For an m-covector γ: |γ.compContinuousLinearMap J| ≤ ‖J‖^m·|γ| ≤ |γ| by (L1).
2. Slice operator. For ω ∈ 𝒟^{k+1}(ℝ^{N+1}) let S_ω ∈ 𝒟^k(ℝ^N) be the test form of slice (a) (by choice). Any test form with the slice formula equals S_ω (test forms are determined by their values; ContinuousAlternatingMap.ext). Hence ω ↦ S_ω is linear: S_{ω₁} + S_{ω₂} and c·S_ω satisfy the slice formulas of ω₁ + ω₂ and c·ω (interval integrals of continuous integrands are additive and homogeneous). Bound: if |ω(y)| ≤ c for all y then |S_ω(x)| ≤ c for all x, by slice (e) with f(t) := Φ(ω(ι(t, x))) (continuous; S_ω(x)(v) = ∫_0^1 f(t)(v) dt; |f(t)| ≤ |ω(ι(t, x))| ≤ c by step 1). The same holds in every degree.
3. Definition. If M(X) < ∞, T₀^X(ω) := X(S_ω) is linear in ω (step 2) and |T₀^X(ω)| ≤ c·M(X).toReal whenever |ω| ≤ c (step 2 and (MSB) with the bound c on all of ℝ^N). By (BC) there is a current cyl(X) ∈ 𝒟_{k+1}(ℝ^{N+1}) with cyl(X)(ω) = X(S_ω) for all ω and M(cyl X) ≤ ofReal(M(X).toReal) = M(X). If M(X) = ∞ put cyl(X) := 0.
4. Conjunct (9). For NC X and ω, η := S_ω satisfies the formula and cyl(X)(ω) = X(S_ω) = X(η).
5. Conjunct (8). For NC X, Y, M(X − Y) ≤ M(X) + M(Y) < ∞ (for admissible ω, (X − Y)(ω) = X(ω) + Y(−ω) and −ω is admissible), so cyl(X − Y)(ω) = (X − Y)(S_ω) = X(S_ω) − Y(S_ω) = cyl(X)(ω) − cyl(Y)(ω) for every ω; GeometricCurrentOn.ext.
6. Conjunct (7), mass: M(cyl X) ≤ M(X) < ∞ by step 3.
7. Conjunct (7), support and compactness. C := {ι(t, x) : t ∈ [0, 1], x ∈ spt X} is compact (continuous image of [0, 1] × spt X). Let y ∉ C, r := infDist y C > 0 (r := 1 if C = ∅) and B := ball(y, r/2) (open, compact closure). Let ω ∈ 𝒟^{k+1}(ℝ^{N+1}) with tsupport ω ⊆ B. By slice (a), tsupport S_ω ⊆ K_ω := {x : ∃ t ∈ [0, 1], ι(t, x) ∈ tsupport ω}, and K_ω ∩ spt X = ∅ (if x ∈ spt X and ι(t, x) ∈ tsupport ω ⊆ B with t ∈ [0, 1], then ι(t, x) ∈ C and dist(ι(t, x), y) < r/2 < r, impossible). So S_ω = 0 on the open set (tsupport S_ω)ᶜ ⊇ spt X, and X(S_ω) = X(0) = 0 by (LOC). Hence cyl(X) vanishes on B, y ∈ zeroRegion(cyl X), y ∉ spt cyl(X). Therefore spt cyl(X) ⊆ C, which is the set in (7); spt cyl(X) is closed (complement of the open zero region), hence compact as a closed subset of C.
8. Conjunct (7), boundary mass. Let ω ∈ 𝒟^k(ℝ^{N+1}) with |ω(y)| ≤ c for all y. ∂cyl(X)(ω) = cyl(X)(dω) = X(S_{dω}). Let ρ₁, ρ₀ be the test forms of slice (b) for ω and s = 1, 0; ρ_s(x) = (ω(ι(s, x))).compContinuousLinearMap J, so |ρ_s(x)| ≤ c by step 1. Case k = 0: by slice (d), S_{dω}(x)(v) = ω(ι(1, x))(J ∘ v) − ω(ι(0, x))(J ∘ v), so S_{dω} = ρ₁ − ρ₀ and |∂cyl(X)(ω)| ≤ |X(ρ₁)| + |X(ρ₀)| ≤ 2c·M(X).toReal by (MSB). Case k = k' + 1: θ := S_ω ∈ 𝒟^{k'}(ℝ^N) satisfies the hypothesis of slice (c) for β := ω, so S_{dω} = ρ₁ − ρ₀ − dθ, and ∂cyl(X)(ω) = X(ρ₁) − X(ρ₀) − ∂X(θ). |θ(x)| ≤ c by step 2 and M(∂X) = boundaryMassOn X univ < ∞, so (MSB) for X and ∂X gives |∂cyl(X)(ω)| ≤ c·(2·M(X).toReal + (boundaryMassOn X univ).toReal). For admissible ω (c = 1) this gives ofReal(∂cyl(X)(ω)) ≤ ofReal(2·M(X).toReal + (boundaryMassOn X univ).toReal); taking the supremum, M(∂ cyl X) < ∞. □

## Key steps

1. Pointwise: |Φ(γ)| ≤ |γ| and |γ ∘ J| ≤ |γ| by (L1), (L2) with ‖J‖ ≤ 1, ‖e₀‖ = 1.
2. Slice operator ω ↦ S_ω (slice (a)) is linear and |S_ω| ≤ sup|ω| (Minkowski bound, slice (e)).
3. cyl(X)(ω) := X(S_ω) is a current with M(cyl X) ≤ M(X) by (MSB) and (BC); this gives (9) and (8).
4. Support: S_ω vanishes near spt X when tsupport ω avoids ι([0,1] × spt X), so (LOC) gives spt cyl(X) ⊆ ι([0,1] × spt X), compact.
5. Boundary mass: S_{dω} = ρ₁ − ρ₀ − dS_ω (slice (c), (d)), so |∂cyl(X)(ω)| ≤ (2M(X) + M(∂X))·sup|ω|.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical)`
- `git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, as recorded in manifest.json)`
- `rg -n cmcdt_lpo local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'IsLipschitzPushforward|LipschitzPushforwardIntegerMultiplicity' local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `rg -n 'theorem extDeriv_pullback|theorem extDeriv_apply' mathlib/Mathlib (Analysis/Calculus/DifferentialForm/Basic.lean:198, :259)`
- `rg -n 'theorem exists_contDiff_tsupport_subset|theorem IsOpen.exists_contDiff_support_eq|theorem HasCompactSupport.contDiff_convolution_left|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le|theorem norm_integral_le_of_norm_le_const|theorem norm_fderiv_le_of_lipschitz|def curryLeftLI|theorem curryLeft_apply_apply|theorem integral_eq_sub_of_hasDerivAt|theorem integral_pos_iff_support_of_nonneg|def smoothTransition' mathlib/Mathlib -g '*.lean'`
- `rg -n compContinuousLinearMap mathlib/Mathlib/Analysis/Calculus/ContDiff mathlib/Mathlib/Analysis/Normed/Module/Alternating mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean -g '*.lean'`
- `sed -n 200,260p mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean (interval version hasFDerivAt_integral_of_dominated_of_fderiv_le'')`
- `sed -n 1,140p mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,AffineCurrentPushforward}.lean`
- `lake env lean /tmp/ops-decomp-k7q2/Avail.lean, Avail2.lean, Avail3.lean, Avail4.lean (#check availability of every cited lemma in the frozen import closure of GMT.Ch07.Submission)`
- `lake env lean /tmp/ops-decomp-k7q2/Children.lean (all eight child types elaborate; sorry-free assembly Submission.lpo_assembly_check of the exact selected frozen type; #print axioms)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name fields and of the selected node's depth and dependencies`
- `grep of /runtime/flows/*/_recursive_lean/inherited.py and runtime.py _overlay_accepted_children (ancestor dependency names cited in a child proof become inherited prerequisites)`
- `sed -n 350,530p book/chapter-06.txt (Simon 6.2.17-2.29: product with [[0,1]], push-forward 2.23-2.24, homotopy formula 2.25-2.27, Lemmas 2.28-2.29)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-3968ae1944/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ops-decomp-k7q2/Children.lean`
- `/tmp/ops-decomp-k7q2/Avail.lean`
- `/tmp/ops-decomp-k7q2/Avail2.lean`
- `/tmp/ops-decomp-k7q2/Avail3.lean`
- `/tmp/ops-decomp-k7q2/Avail4.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Submission.lean. Its only Lipschitz push-forward material is the unsolved Ch06 specification (IsLipschitzPushforward, LipschitzPushforwardIntegerMultiplicity; main_theorem := by sorry). That specification is written over another Euclidean type and cannot be imported into Ch07, so no proof can be reused. Every Mathlib tool the child proofs cite is in the frozen import closure: extDeriv_apply, extDeriv_pullback, Filter.EventuallyEq.extDeriv_eq, curryLeftLI, curryLeft_apply_apply, exists_contDiff_tsupport_subset, IsOpen.exists_contDiff_support_eq, Real.smoothTransition, ContDiffBump with hasContDiffBump_of_innerProductSpace, HasCompactSupport.contDiff_convolution_left, hasFDerivAt_integral_of_dominated_of_fderiv_le'', intervalIntegral.integral_eq_sub_of_hasDerivAt, norm_integral_le_of_norm_le_const (Bochner and interval), norm_fderiv_le_of_lipschitz, integral_pos_iff_support_of_nonneg and LinearMap.exists_leftInverse_of_injective. ContDiffBump.normed, ContDiffBump.dist_normed_convolution_le, intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le, contDiff_parametric_integral_of_contDiff and exists_smooth_zero_one_of_isClosed are not in the closure, and the child proofs do not use them. SimonGMT Chapter 6 provides GeometricCurrentOn, TestFormOn, TestFormOnConverges, massOn and mass, support via zeroRegion, boundary and boundary_boundary, tsupport_exteriorDerivative_subset, exteriorDerivative_apply and affinePullbackForm_isTestForm. No DAG node or snapshot declaration uses the prefix cmcdt_lpo_. All eight child types elaborate after import GMT.Ch07.Submission. The assembly of the exact selected frozen type from the pushforward, cylinder and homotopy child types and the covector-bounds type compiles without sorry, with axioms propext, Classical.choice and Quot.sound. Simon 6.2.25-2.29 in book/chapter-06.txt matches the decomposition: the homotopy formula, the mass estimate 2.27, the smooth estimate in the proof of 2.28, and the mollifier limit of 2.29.
