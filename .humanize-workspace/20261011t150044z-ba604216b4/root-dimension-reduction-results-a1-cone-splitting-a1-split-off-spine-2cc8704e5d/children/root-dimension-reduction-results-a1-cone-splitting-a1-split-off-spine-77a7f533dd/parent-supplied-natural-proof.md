# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- k := q + 1 ≥ 1 is the degree of X.
- M := R.carrier, θ := R.mult, ξ := R.orient, H^k := μHE[k].
- 𝒟^j := TestFormOn univ j, the C^∞ compactly supported j-forms.
- ‖·‖ is the operator norm on Λ^j := Covector (Euclid P) j and on k-vectors.
- For a (k+1)-form ω, (Kω)(x) := ∫_0^1 t^k • (ω(t•x)).curryLeft x dt, a k-form.
- For a k-form γ, (K₀γ)(x) := ∫_0^1 t^q • (γ(t•x)).curryLeft x dt, a q-form.
- d is exteriorDerivative. For a test form γ, dγ is the test form exteriorDerivativeTestOn univ _ γ, whose underlying form is exteriorDerivative γ.

0. Two properties of X (step 0 of the parent proof).
 (0a) Vanishing. If γ ∈ 𝒟^k and γ(x) = 0 for every x ∈ spt X, then X(γ) = 0. Indeed, since R represents X, X(γ) = R.action γ = ∫_M θ(x)·ξ(x)(γ(x)) dH^k(x). For x ∈ M ⊆ spt X the integrand is θ(x)·ξ(x)(0) = 0 (setIntegral_eq_zero_of_forall_eq_zero).
 (0b) C⁰ bound. Put C_X := (R.measure univ).toReal. By definition R.measure univ = ((H^k⌞M).withDensity θ)(ℝ^P) = ∫⁻_M θ dH^k, which is finite by hypothesis. Claim: if γ ∈ 𝒟^k and b ≥ 0 satisfy ‖γ(x)‖ ≤ b for all x, then |X(γ)| ≤ C_X·b.
  - By R.orients, for H^k-a.e. x ∈ M there are a plane Q and an orthonormal τ = (τ_1, …, τ_k) with ξ(x)(α) = α(τ) for all α, or ξ(x)(α) = −α(τ) for all α (IsUnitOrientationOf).
  - Hence |ξ(x)(α)| = |α(τ)| ≤ ‖α‖·∏_i ‖τ_i‖ = ‖α‖ (ContinuousAlternatingMap.le_opNorm).
  - So |θ(x)·ξ(x)(γ(x))| ≤ θ(x)·b for H^k-a.e. x ∈ M.
  - θ is measurable with ∫⁻_M θ < ∞, so x ↦ θ(x)·b is integrable on M with integral C_X·b. By norm_integral_le_of_norm_le, |X(γ)| ≤ C_X·b.
1. Cutoff. spt X is compact, hence bounded; choose ρ > 0 with ‖x‖ < ρ for all x ∈ spt X. Let ζ be the ContDiffBump centered at 0 with rIn = ρ and rOut = ρ + 1. Then:
 - ζ is C^∞ with compact support and 0 ≤ ζ ≤ 1;
 - ζ(x) = 1 for ‖x‖ ≤ ρ, and ζ(x) = 0 for ‖x‖ > ρ + 1 (tsupport ζ = closedBall 0 (ρ+1));
 - in particular ζ ≡ 1 on the open set N := ball(0, ρ) ⊇ spt X.
 (This construction was compiled in Lean during decomposition.)
2. The test forms η_ω. Let ω ∈ 𝒟^{k+1}.
 - By the sibling radial_homotopy (with q := k and β := ω, which is C^∞), Kω is C^∞.
 - Hence η_ω(x) := ζ(x) • Kω(x) defines a C^∞ k-form (ContDiff.smul) with tsupport η_ω ⊆ tsupport ζ, which is compact. So η_ω ∈ 𝒟^k.
 - ω ↦ η_ω is ℝ-linear. For fixed x, the integrand t ↦ t^k • (ω(t•x)).curryLeft x is continuous, hence interval integrable on [0, 1], and it is linear in ω (curryLeft_add, curryLeft_smul). So K(ω + ω′) = Kω + Kω′ and K(cω) = c·Kω by linearity of the interval integral, and multiplication by ζ keeps linearity.
 - For x ∈ spt X, ζ(x) = 1, so η_ω(x) = Kω(x).
3. The current Y. Define Y(ω) := X(η_ω) for ω ∈ 𝒟^{k+1}. This is a linear functional: the linear map ω ↦ η_ω of step 2 followed by X.
 Continuity (step 4 of the parent proof; its a = 0 estimate suffices together with (0b)):
 - Let ω_j ∈ 𝒟^{k+1} with TestFormOnConverges ω_j 0. Then there is a compact K₁ with tsupport ω_j ⊆ K₁ for all j, and iteratedFDeriv ℝ a ω_j → 0 uniformly on K₁ for every a.
 - Take a = 0. Since ‖iteratedFDeriv ℝ 0 f y‖ = ‖f y‖ (norm_iteratedFDeriv_zero), for every ε > 0 there is J with ‖ω_j(y)‖ ≤ ε for all j ≥ J and y ∈ K₁. For y ∉ K₁, ω_j(y) = 0. So ‖ω_j(y)‖ ≤ ε for all y and all j ≥ J.
 - Let j ≥ J and x ∈ ℝ^P. Then ‖(ω_j(t•x)).curryLeft x‖ ≤ ‖ω_j(t•x)‖·‖x‖ ≤ ε‖x‖ (norm_curryLeft), and 0 ≤ t^k ≤ 1 on [0, 1]. So ‖Kω_j(x)‖ ≤ ε‖x‖ (intervalIntegral.norm_integral_le_of_norm_le_const).
 - Since |ζ| ≤ 1 and ζ(x) = 0 for ‖x‖ > ρ + 1, ‖η_{ω_j}(x)‖ ≤ (ρ + 1)ε for all x.
 - By (0b), |Y(ω_j)| = |X(η_{ω_j})| ≤ C_X(ρ + 1)ε for j ≥ J. Hence Y(ω_j) → 0.
 So (toCurrent := X ∘ (ω ↦ η_ω), continuous′ as above) is a GeometricCurrentOn univ (k+1) = GeometricCurrentOn univ (q+1+1). Call it Y.
4. Action formula. For ω ∈ 𝒟^{k+1}, the test form η := η_ω satisfies η(x) = Kω(x) = ∫_0^1 t^{q+1} • (ω(t•x)).curryLeft x dt for x ∈ spt X (step 2), and Y(ω) = X(η) by definition. This is the last conclusion.
5. ∂Y = X (step 5 of the parent proof). Let γ ∈ 𝒟^k = TestFormOn univ (q+1).
 - By GeometricCurrentOn.boundary_apply, ∂Y(γ) = Y(dγ) = X(η_{dγ}), where η_{dγ} = ζ • K(dγ) and K(dγ)(x) = ∫_0^1 t^{q+1} • ((dγ)(t•x)).curryLeft x dt.
 - By radial_homotopy (with q and β := γ), K₀γ is C^∞ and d(K₀γ)(x) + K(dγ)(x) = γ(x) for all x. Hence η_{dγ} = ζ•γ − ζ•d(K₀γ) pointwise. (The definitional alignment of K(dγ) with the homotopy formula was compiled in Lean during decomposition.)
 - ζ•γ and ζ•d(K₀γ) are test k-forms: they are C^∞ (d(K₀γ) = alt ∘ D(K₀γ) is C^∞ because K₀γ is) and have tsupport ⊆ tsupport ζ. Likewise ψ := ζ•K₀γ ∈ 𝒟^q.
 - By linearity of X, X(η_{dγ}) = X(ζ•γ) − X(ζ•d(K₀γ)).
 - First term. (ζ•γ − γ)(x) = (ζ(x) − 1)•γ(x) = 0 for x ∈ spt X. By (0a) and linearity, X(ζ•γ) = X(γ).
 - Second term. On the open set N, ψ = K₀γ because ζ ≡ 1 there. So for x ∈ N, ψ =ᶠ[𝓝 x] K₀γ, hence Dψ(x) = D(K₀γ)(x) (Filter.EventuallyEq.fderiv_eq) and dψ(x) = d(K₀γ)(x) = ζ(x)•d(K₀γ)(x). Thus the test form ζ•d(K₀γ) − dψ vanishes on N ⊇ spt X, and (0a) gives X(ζ•d(K₀γ)) = X(dψ).
 - X(dψ) = (∂X)(ψ) = 0 because ∂X = 0.
 Hence ∂Y(γ) = X(γ) for every γ, and Y.boundary = X by extensionality (GeometricCurrentOn.ext).
6. Support (step 6 of the parent proof). Let C₀ := {s•x : s ∈ [0,1], x ∈ spt X}. It is the image of the compact set [0,1] × spt X under the continuous map (s, x) ↦ s•x, so it is compact and closed.
 (6a) Let ω ∈ 𝒟^{k+1} with tsupport ω ∩ C₀ = ∅. For x ∈ spt X and t ∈ [0,1], t•x ∈ C₀, so ω(t•x) = 0. So the integrand t ↦ t^k • (ω(t•x)).curryLeft x vanishes for every t ∈ [0,1], and the interval integral over [0,1] is 0 (intervalIntegral.integral_congr on uIcc 0 1 with the zero function). Hence Kω(x) = 0 and η_ω(x) = 0 for every x ∈ spt X, and (0a) gives Y(ω) = X(η_ω) = 0.
 (6b) Let y ∉ C₀. Since C₀ is closed, there is r > 0 with ball(y, r) ∩ C₀ = ∅. Put W := ball(y, r).
  - W is open, and closure W ⊆ closedBall(y, r) is compact (ℝ^P is proper) and ⊆ univ.
  - Y vanishes on W: if tsupport ω ⊆ W, then tsupport ω ∩ C₀ = ∅, so Y(ω) = 0 by (6a).
  - Hence W ⊆ Y.zeroRegion, and y ∈ W, so y ∉ Y.support = univ ∖ Y.zeroRegion.
 Thus Y.support ⊆ C₀ = {y | ∃ s ∈ Icc 0 1, ∃ x ∈ X.support, y = s•x}. Y.support is closed (the complement of the open zero region), so as a closed subset of the compact C₀ it is compact.
7. Steps 3–6 give Y with Y.boundary = X, IsCompact Y.support, Y.support ⊆ C₀, and the action formula. ∎

## Key steps

1. From R (carrier ⊆ spt X, finite mass): X(γ) = 0 when γ vanishes on spt X, and |X(γ)| ≤ μ_R(ℝ^P)·sup‖γ‖ since unit orientations have norm ≤ 1.
2. With a bump ζ ≡ 1 on ball(0,ρ) ⊇ spt X and K smooth (sibling radial_homotopy), η_ω := ζ·Kω is a test form linear in ω. Y(ω) := X(η_ω) is a current, since ‖η_{ω_j}‖ ≤ (ρ+1) sup‖ω_j‖ → 0.
3. ∂Y(γ) = X(ζ K(dγ)) = X(ζγ) − X(ζ d(K₀γ)) by the homotopy formula. Since ζ ≡ 1 near spt X, d is local, and ∂X = 0, this equals X(γ) − X(d(ζK₀γ)) = X(γ).
4. If tsupport ω misses the compact cone C₀, then Kω = 0 on spt X, so Y(ω) = 0. Hence spt Y ⊆ C₀, and spt Y is compact.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (b4d606d, 25730c7c, 2b36630: pins match)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 over dag.json: siblings of split_off_spine-a1; regex search of statements and lean_statements for homotop|cone|parametriz|push-?forward|curryLeft|Matrix.det with covectorEuclideanNorm; statuses and candidate commits of the reuse candidates`
- `python3 over dag.json: the subtrees …moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_pushforward-a1 (lpip_*) and …flat_convergence-a1.deformation-a1.im_pushforward-a1 (dor_lmb_fcd_imp_*); parallel node idtp_fons_cs_sos_cone_filling_in_subspace (same type, rlcr-lean, not accepted); dor_lmb_fcd_imp_parametric_rep (comparing, not accepted); dor_lmb_fc_im_series (decomposing, not accepted)`
- `git show <candidate commit>:GMT/Ch07/Submission.lean | grep import, for 551eaab, 3d04d72, 918eb38, 9b823b5, 44ef61f, 27de75e, 2af75d6, a2ba78f, 2fd8f6f, 0ea228e, 77ba671 (the lpip commits add import Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `grep SimonGMT Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean for TestFormOnConverges, GeometricCurrentOn, boundary_apply, zeroRegion, support, massOn, massAdmissibleOn, covectorEuclideanNorm, IsSmoothForm, exteriorDerivative`
- `grep the Mathlib snapshot for ParametricIntegral and ParametricIntervalIntegral (no ContDiff lemma for parametric integrals, so the accepted cmcdt_lpo_slice_param_integral is reused), Alternating/Curry.lean (norm_curryLeft, curryLeftLI), BumpFunction/Basic.lean, Constructions/Pi.lean (volume_preserving_piFinSuccAbove), Haar/InnerProductSpace.lean (PiLp.volume_preserving_ofLp/toLp), ContDiff/RCLike.lean (ContDiff.lipschitzWith_of_hasCompactSupport)`
- `lake env lean /tmp/cfs-decomp/Check1.lean, Check2.lean, Check3.lean, Check4.lean after import GMT.Ch07.Submission with the contract opens`
- `python3 -I /tmp/cfs-scripts/homotopy_num.py (numeric check of the radial homotopy formula with Mathlib extDeriv/curryLeft conventions)`
- `grep -c dimred_cs_sos_cfs dag.json (0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9310c84433/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-14afd577b6/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-equals-rep-measure-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/tmp/cfs-decomp/Check1.lean`
- `/tmp/cfs-decomp/Check2.lean`
- `/tmp/cfs-decomp/Check3.lean`
- `/tmp/cfs-decomp/Check4.lean`

Pins and contract. The pins match: project b4d606d, mathlib 25730c7c, SimonGMT 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and the selected node's proof base 480b1bd contains only the contract.

Library gaps. Mathlib has no lemma for smoothness of parametric integrals; this is covered by the accepted cmcdt_lpo_slice_param_integral. SimonGMT has no cone, homotopy or Lipschitz-pushforward constructions. Every other API cited by the child proofs exists and was probed with #check, including:
- norm_curryLeft, curryLeftLI, alternatizeUncurryFinCLM, ContinuousAlternatingMap.apply;
- ContDiffBump, ContDiff.lipschitzWith_of_hasCompactSupport, Filter.EventuallyEq.fderiv_eq;
- intervalIntegral_comp_comm, integral_eq_sub_of_hasDerivAt, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp;
- measurable_fderiv, norm_fderiv_le_of_lipschitz, enorm_integral_le_lintegral_enorm, HasSum.unique.

Reuse. Comparator-accepted DAG declarations with byte-identical frozen types are reused:
- 6 as siblings: cmcdt_lpo_slice_param_integral, dtc_cone_euler_cartan, cmcdt_lp_covector_curryLeft_norm_le, dtc_vanish_off_support, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub;
- 6 cited for the depth-6 wiring of two children: dimred_mbl_dt_lpip_normalized_rep, dimred_mbl_dt_lpip_piece_representation, dpf_rectifiable_bilipschitz_pieces, covectorEuclideanNorm_gram_bounds, dimred_mbl_dt_lpip_lipschitz_piece_current, cmcdt_im_series.
The three lpip commits add import Poincare.SimonGMT.Chapter02.AreaLipschitz, which is inherited through the merge. The other commits add no imports.

Not reused (not accepted): the parallel same-type node idtp_fons_cs_sos_cone_filling_in_subspace (rlcr-lean), dor_lmb_fcd_imp_parametric_rep (comparing), dor_lmb_fc_im_series and emf_exists_cone_filling (decomposing).

Lean checks:
- Check1: all child types (and the 6 wiring types) elaborate as Submission stubs, and the frozen parent type is proved from the 5 new child types. Axioms: propext, sorryAx (stubs only), Classical.choice, Quot.sound.
- Check2: compact_im_param and param_series_im are fully proved from the frozen types of the accepted lemmas they cite.
- Check3: the homotopy formula aligns by rfl with cone_current's boundary step, Kω is smooth for test forms, and the ContDiffBump cutoff works.
- Check4: covector evaluation commutes with interval integrals.
- The radial homotopy formula was also checked numerically.

Names: the 5 new dimred_cs_sos_cfs_* names occur nowhere in dag.json.
