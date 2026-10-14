# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the closing step of B3 in the parent proof, together with the elementary fact that mass-summable series of currents define currents. That step combines countably many integer multiplicity pieces whose multiplicities have finite total integral into one integer multiplicity current, using the locality of approximate tangent spaces and the sign rule (L3). This replaces Simon's completeness theorem 3.13 in the parent proof (departure (i)).

Notation. All currents are in 𝒟_{n'}(ℝ^P) with domain univ, n' := k + 1. ‖ω‖ := sup_x |ω(x)| (Euclidean coefficient norm). Hypotheses (VO), (MR), (IMC) are the three displayed hypotheses of the statement (frozen types of Submission.dtc_vanish_off_support, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub).

1. Evaluation bound. For every current X and test form ω, |X(ω)| ≤ M(X)‖ω‖ (in [0, ∞]). Indeed, if ‖ω‖ = 0 then ω = 0; otherwise ±ω/‖ω‖ are admissible for M(X) (support in univ, |·| ≤ 1), so ±X(ω)/‖ω‖ ≤ M(X).

2. Definition of S. Let Σ_i M(W_i) =: A < ∞. For each ω, Σ_i |W_i(ω)| ≤ A‖ω‖ < ∞, so S(ω) := Σ_i W_i(ω) converges absolutely; in particular HasSum (i ↦ W_i(ω)) (S(ω)). S is linear. Continuity: if ω_j → 0 in the test-form topology (supports in one compact set, all derivatives → 0 uniformly), then sup_x of the operator norm of ω_j(x) tends to 0. The Euclidean coefficient norm is bounded by a constant C(P, n') times the operator norm (each coefficient ω(x)(e_{i_1},…,e_{i_{n'}}) is bounded by the operator norm). Hence ‖ω_j‖ → 0 and |S(ω_j)| ≤ A‖ω_j‖ → 0. So S ∈ 𝒟_{n'}(ℝ^P).

3. Mass. For admissible ω, S(ω) = Σ_i W_i(ω) ≤ Σ_i M(W_i), so M(S) ≤ Σ_i M(W_i).

4. Support. Let E := closure ⋃_i spt W_i and x ∉ E. Choose r > 0 with closedBall(x, r) ∩ E = ∅. The open ball B := ball(x, r) has compact closure. Every test form ω with tsupport ω ⊆ B satisfies tsupport ω ∩ spt W_i = ∅ for all i, hence W_i(ω) = 0 by (VO) and S(ω) = 0. So x lies in the zero region of S, i.e. spt S ⊆ E.

5. Integer multiplicity. Assume every W_i is integer multiplicity, with IMRep R_i = (M_i, θ_i, ξ_i). By (MR) (U = W = univ, open), ∫_{M_i} θ_i dH^{n'} = R_i.measure(ℝ^P) = M(W_i). Modifying ξ_i on an H^{n'}⌞M_i-null set, we may take ξ_i Borel (this changes neither the action nor the a.e. orientation property).
 (5a) N := ⋃_i M_i is Borel and countably n'-rectifiable (SimonGMT countablyRectifiable_iUnion), and H^{n'}(N) ≤ Σ_i H^{n'}(M_i) ≤ Σ_i ∫_{M_i}θ_i dH^{n'} = A < ∞ because θ_i ≥ 1 on M_i.
 (5b) Θ := Σ_i θ_i 1_{M_i} : ℝ^P → [0, ∞] has ∫ Θ dH^{n'} = A, so Θ < ∞ off an H^{n'}-null set. At such points only finitely many i have x ∈ M_i (θ_i ≥ 1 there).
 (5c) Tangent planes. For each i, apply (IMC)(a) with U = univ, M = M_i ⊆ M' = N (H^{n'}(N ∩ K) ≤ A < ∞): for H^{n'}-a.e. x ∈ M_i and every subspace Q, HasApproximateTangentSpaceAt n' M_i x Q ⟺ HasApproximateTangentSpaceAt n' N x Q. By the orientation field of R_i, for H^{n'}-a.e. x ∈ M_i there is Q_i(x) with HasApproximateTangentSpaceAt n' M_i x Q_i(x) and IsUnitOrientationOf (ξ_i(x)) (Q_i(x)). Removing a countable union of null sets, for H^{n'}-a.e. x ∈ N each i with x ∈ M_i gives an approximate tangent space Q_i(x) of N at x. By uniqueness (SimonGMT HasApproximateTangentSpaceAt.unique) these coincide; call the common value Q(x).
 (5d) Signs. Let ι(x) := min{i : x ∈ M_i} for x ∈ N (Borel) and η(x) := ξ_{ι(x)}(x) (Borel). (L3) Two unit orientations of the same n'-dimensional subspace differ by a sign: if ξ = ±(α ↦ α(τ)) and ξ' = ±(α ↦ α(τ')) with orthonormal bases τ, τ' of Q, then τ' = Oτ for an orthogonal O, and α(τ') = det(O)α(τ) = ±α(τ) for every alternating α. Put s_i(x) := 1 if ‖ξ_i(x) − η(x)‖ ≤ ‖ξ_i(x) + η(x)‖ and s_i(x) := −1 otherwise (Borel). A unit orientation is nonzero (it takes the value ±1 on a covector dual to its orthonormal frame). So for H^{n'}-a.e. x ∈ N and every i with x ∈ M_i, ξ_i(x) = s_i(x)η(x).
 (5e) Multiplicity. m(x) := Σ_i s_i(x)θ_i(x)1_{M_i}(x) (set m := 0 where Θ(x) = ∞) is Borel, as a pointwise limit of finite sums of Borel integer-valued functions. H^{n'}-a.e. on N it is a finite sum of integers, and |m| ≤ Θ, so m is integer-valued a.e. with ∫|m| dH^{n'} ≤ A.
 (5f) Action. For a test form ω, |ξ_i(x)(ω(x))| ≤ |ω(x)| ≤ ‖ω‖ for a.e. x ∈ M_i ((IMC)(d)), so Σ_i ∫ θ_i 1_{M_i}|ξ_i(ω)| ≤ ‖ω‖A. Dominated convergence for series gives
 S(ω) = Σ_i ∫_{M_i} θ_i ξ_i(x)(ω(x)) dH^{n'} = ∫_N Σ_i θ_i 1_{M_i} s_i η(x)(ω(x)) dH^{n'} = ∫_N m(x) η(x)(ω(x)) dH^{n'}.
 (5g) The IMRep. Let Z ⊆ N be a Borel H^{n'}-null set outside of which (5b)–(5e) hold. Put N' := {x ∈ N ∖ Z : m(x) ≠ 0} (Borel), mult := |m| on N' and 0 elsewhere (Borel, ℕ-valued, positive on N'), and orient := sign(m)η. Check the IMRep fields:
 - N' ⊆ univ;
 - N' ⊆ N is countably n'-rectifiable (SimonGMT CountablyRectifiable.mono);
 - local integrability: ∫_{N'∩K}|m| ≤ A < ∞;
 - orient is Borel;
 - for H^{n'}-a.e. x ∈ N', (IMC)(a) with M = N' ⊆ M' = N gives that Q(x), an approximate tangent space of N at x, is also one of N' at x, and sign(m(x))η(x) is a unit orientation of Q(x) (the definition IsUnitOrientationOf allows either sign).
 Its action is ∫_{N'} |m| sign(m) η(ω) dH^{n'} = ∫_N m η(ω) dH^{n'} = S(ω) (m = 0 on N ∖ (N' ∪ Z)). Hence S is integer multiplicity.

6. The current S of 2 satisfies the four conclusions by 2, 3, 4 and 5. ∎

## Key steps

1. |X(ω)| ≤ M(X)‖ω‖, so S(ω) := Σ_i W_i(ω) converges absolutely and defines a sequentially continuous linear functional.
2. M(S) ≤ Σ M(W_i) by evaluating on admissible forms; spt S ⊆ closure ⋃ spt W_i by (VO).
3. For integer multiplicity W_i with IMReps (M_i, θ_i, ξ_i): N := ⋃M_i has finite Hausdorff measure by (MR), and a.e. point lies in finitely many M_i.
4. By (IMC)(a) and uniqueness all M_i containing x share the approximate tangent space of N at x; the orientations differ from a Borel reference orientation η by signs (sign rule).
5. The integer multiplicity m := Σ s_iθ_i1_{M_i} and dominated convergence give S(ω) = ∫_N mη(ω)dH, and (N', |m|, sign(m)η) is an IMRep of S.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n -i 'deformation theorem|federer|polyhedral|cubical|skeleton' project/GMT -g '*.lean'`
- `rg -n -i 'homotopy|lipschitz.*push|pushforward' project/GMT -g '*.lean'`
- `rg -n 'cmcdt_' project mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm|polyhedral chain' mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'theorem (cthickening_smul|smul_cthickening|thickening_smul|infEDist_smul₀|infDist_smul₀)' mathlib/Mathlib`
- `rg -n 'theorem (exists_disjoint_subfamily_covering_enlargement|ae_differentiableAt|integral_divergence_of_hasFDerivAt_off_countable)' mathlib/Mathlib`
- `grep in lake-packages-25730c7c for the declarations cited by the child proofs: countablyRectifiable_iUnion, HasApproximateTangentSpaceAt.unique, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, area_image_criticalSet_eq_zero, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, exteriorDerivativeOn_pullbackFormWithin, GeometricCurrentOn.boundary_affinePushforward, exteriorDerivative_affinePullbackForm, WeaklyConvergesOn.massOn_le_liminf, WeaklyConvergesOn.boundary, exteriorDerivative_apply, GeometricCurrentOn.boundary_boundary, euclideanHausdorffMeasure_smul₀, LipschitzOnWith.extend_real, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LinearMap.exists_antilipschitzWith, MeasurableSet.image_of_continuousOn_injOn, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, Monotone.ae_differentiableAt, LipschitzWith.ae_differentiableAt, LipschitzOnWith.hausdorffMeasure_image_le, LipschitzWith.integral_lineDeriv_mul_eq, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, cthickening_cthickening_subset, cthickening_subset_thickening', IsCompact.cthickening, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, measurable_deriv (all found)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json (681 nodes): lean_name collisions for the eight proposed names (none), frozen types of the five resolved dependencies, statuses; verbatim antecedent check of the child types`
- `lake env lean /tmp/cmcdt2/lean/V1Types.lean (eight child types elaborate); lake env lean /tmp/cmcdt2/lean/AssemblySkeleton.lean; lake env lean /tmp/cmcdt2/lean/Assembly.lean (assembly proof, #print axioms: propext, Classical.choice, Quot.sound); lake env lean /tmp/cmcdt2/lean/InstCheck.lean (ContDiff ℝ (⊤ : ℕ∞) = C^∞ ≠ ω; pointwise Sub by rfl; trace coercion)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v1.json`
- `/tmp/cmcdt2/lean/V1Types.lean`
- `/tmp/cmcdt2/lean/Assembly.lean`
- `/tmp/cmcdt2/lean/InstCheck.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Contract.lean and Submission.lean. The project holds only a separate, unsolved Ch06 specification of the deformation theorem and Lipschitz push-forward (project/GMT/Ch06/Contract.lean: DeformationTheorem, LipschitzPushforwardIntegerMultiplicity, IsLatticeChain; main_theorem := by sorry). It uses incompatible types (Eucl, IsLatticeChain) and cannot be imported into Ch07, so it is not reusable. Mathlib has no deformation, flat-norm or polyhedral-chain results (no match). It does provide every tool cited by the child proofs: Vitali covering, Rademacher, the divergence theorem, integrability of monotone derivatives, infEDist_smul₀, cthickening lemmas, and Hausdorff measure scaling and isometry. Every cited SimonGMT declaration exists. No declaration or DAG node uses the cmcdt_ prefix. All eight child types elaborate. The assembly from the five dependency types and three child types to the selected frozen type compiles with only propext, Classical.choice and Quot.sound.
