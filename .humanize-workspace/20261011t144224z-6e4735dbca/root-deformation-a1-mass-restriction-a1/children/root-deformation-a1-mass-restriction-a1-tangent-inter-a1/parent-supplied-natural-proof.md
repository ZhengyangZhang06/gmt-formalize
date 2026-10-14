# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.mass_restriction-a1`
- Child DAG node: `root.deformation-a1.mass_restriction-a1.tangent_inter-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the orientation argument of Step 9(b) of the selected parent's supplied proof. That argument has two parts. First, the Upper Density Theorem (Simon Ch. 1, 3.6 with Remark 3.7(2)) shows that ν := θHᵏ⌞(M ∖ A) has zero k-dimensional density at Hᵏ-a.e. x ∈ M ∩ A. Second, the blow-up change of variables shows that the blow-up integrals of (M, θ) and (M ∩ A, θ) at such x have the same limit. Here the first part is the sibling zero_density (accepted theorem lpf_wtc_ae_zero_density_off_set) and the second is the sibling tangent_locality (accepted theorem iwl_weighted_tangent_locality).

Conventions. ℝ^N := Eucl N, Hᵏ := μHE[k], B̄_s(x) := closedBall x s. ∫⁻ is the [0, ∞]-valued lower Lebesgue integral and ‖·‖ₑ the extended norm (‖t‖ₑ = ofReal|t| for real t). 1_E f := E.indicator f. Limits "r → 0+" are along 𝓝[>] 0.

Siblings used.
 - zero_density (lpf_wtc_ae_zero_density_off_set). Let W ⊆ ℝ^Q be open, S Hⁿ-null-measurable and g : ℝ^Q → [0, ∞] with ∫⁻_{S∩K} g dHⁿ < ∞ for every compact K ⊆ W. Then for Hⁿ-a.e. y with y ∈ W and y ∉ S, (∫⁻_{S ∩ B̄_ρ(y)} g dHⁿ)/ofReal(ρⁿ) → 0 as ρ → 0+.
 - tangent_locality (iwl_weighted_tangent_locality). Let M, M′ be Hⁿ-null-measurable, θ, θ′ real functions and x a point with θ(x) = θ′(x). Assume that for some ρ > 0, θ is Hⁿ-integrable on M ∩ B̄_ρ(x) and θ′ on M′ ∩ B̄_ρ(x). Assume also that for every R > 0, ofReal((rⁿ)⁻¹)·∫⁻_{B̄_{Rr}(x)} ‖1_Mθ − 1_{M′}θ′‖ₑ dHⁿ → 0 as r → 0+. Then for every subspace Q, HasWeightedApproximateTangentSpaceAt n M θ x Q ↔ HasWeightedApproximateTangentSpaceAt n M′ θ′ x Q.

Fix N, k, M, θ and A as in the statement, and put S := M ∖ A and g(z) := ofReal(θ(z)) ∈ [0, ∞).

1. (Measurability.) A is Borel, so M ∩ A and S = M ∖ A are Hᵏ-null-measurable (NullMeasurableSet.inter, NullMeasurableSet.diff).

2. (Local finiteness.) Let K be compact. θ is Hᵏ-integrable on M ∩ K and S ∩ K ⊆ M ∩ K, so θ is integrable on S ∩ K. Since ofReal(θ(z)) ≤ ‖θ(z)‖ₑ, we get ∫⁻_{S∩K} g dHᵏ ≤ ∫⁻_{S∩K} ‖θ‖ₑ dHᵏ < ∞ (lintegral_ofReal_le_lintegral_enorm and finiteness of the integral of an integrable function).

3. (Zero density.) Apply zero_density with Q := N, n := k, W := ℝ^N (open), S and g; the hypothesis is step 2. Writing F_y(ρ) := ∫⁻_{S ∩ B̄_ρ(y)} g dHᵏ, we get: for Hᵏ-a.e. y, if y ∉ S then F_y(ρ)/ofReal(ρᵏ) → 0 as ρ → 0+.

4. (Passing to Hᵏ⌞(M ∩ A).) An Hᵏ-a.e. property holds Hᵏ⌞(M ∩ A)-a.e. (ae_restrict_of_ae). Since M ∩ A is null-measurable, Hᵏ⌞(M ∩ A)-a.e. x lies in M ∩ A (ae_restrict_mem₀). Hence for Hᵏ⌞(M ∩ A)-a.e. x we have both x ∈ M ∩ A and the conclusion of step 3. Fix such an x. As x ∈ A, x ∉ S, and therefore
 (Z) F_x(ρ)/ofReal(ρᵏ) → 0 as ρ → 0+.

5. (The integrand.) For every z, 1_Mθ(z) − 1_{M∩A}θ(z) = 1_Sθ(z): both sides are 0 if z ∉ M or z ∈ M ∩ A, and both equal θ(z) if z ∈ M ∖ A. Since θ > 0 on M ⊇ S, ‖1_Sθ(z)‖ₑ = 1_S g(z). Since S is null-measurable also for Hᵏ⌞B̄_s(x) (a measure below Hᵏ), lintegral_indicator₀ and Measure.restrict_restrict₀ give, for every s,
 ∫⁻_{B̄_s(x)} ‖1_Mθ − 1_{M∩A}θ‖ₑ dHᵏ = ∫⁻_{B̄_s(x)} 1_S g dHᵏ = F_x(s).

6. (Rescaling.) Let R > 0 and r > 0. Then Rr > 0 and ofReal((Rr)ᵏ) = ofReal(Rᵏ)·ofReal(rᵏ), where 0 < ofReal(Rᵏ) < ∞ and 0 < ofReal(rᵏ) < ∞; also ofReal((rᵏ)⁻¹) = ofReal(rᵏ)⁻¹. Hence
 ofReal((rᵏ)⁻¹)·F_x(Rr) = ofReal(Rᵏ)·[F_x(Rr)/ofReal((Rr)ᵏ)].
 As r → 0+, Rr → 0+ (Rr is continuous in r, vanishes at 0, and is positive for r > 0). By (Z) the bracket tends to 0, and multiplying by the finite constant ofReal(Rᵏ) gives a limit of ofReal(Rᵏ)·0 = 0 (ENNReal.Tendsto.const_mul). With step 5:
 ofReal((rᵏ)⁻¹)·∫⁻_{B̄_{Rr}(x)} ‖1_Mθ − 1_{M∩A}θ‖ₑ dHᵏ → 0 as r → 0+, for every R > 0.

7. (Local integrability.) The closed ball B̄_1(x) is compact, so θ is Hᵏ-integrable on M ∩ B̄_1(x), and hence on its subset (M ∩ A) ∩ B̄_1(x).

8. (Tangent locality.) Apply tangent_locality with P := N, n := k, M, M′ := M ∩ A, θ′ := θ, the point x and ρ := 1. Its hypotheses are: null-measurability (step 1); θ(x) = θ(x); integrability (step 7); and the decay condition (step 6). It yields, for every subspace L, HasWeightedApproximateTangentSpaceAt k M θ x L ↔ HasWeightedApproximateTangentSpaceAt k (M ∩ A) θ x L. The forward implication is the claim at x.

9. (Conclusion.) Steps 4–8 apply at Hᵏ⌞(M ∩ A)-a.e. x. The exceptional null set does not depend on L, so for Hᵏ⌞(M ∩ A)-a.e. x every weighted approximate tangent space of (M, θ) at x is one of (M ∩ A, θ) at x. ∎

## Key steps

1. S := M ∖ A and M ∩ A are Hᵏ-null-measurable; g := ofReal∘θ has ∫⁻_{S∩K} g < ∞ for compact K.
2. zero_density gives F_x(ρ)/ofReal(ρᵏ) → 0 for Hᵏ-a.e. x ∉ S, hence for Hᵏ⌞(M∩A)-a.e. x (which lies in M ∩ A).
3. ‖1_Mθ − 1_{M∩A}θ‖ₑ = 1_S·ofReal θ (θ > 0 on M), so the blow-up defect integral over B̄_{Rr}(x) equals F_x(Rr).
4. ofReal((rᵏ)⁻¹)F_x(Rr) = ofReal(Rᵏ)·F_x(Rr)/ofReal((Rr)ᵏ) → 0 as r → 0+.
5. tangent_locality with M′ = M ∩ A, θ′ = θ, ρ = 1 transfers every weighted tangent space of (M, θ) at x to (M ∩ A, θ).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both identical); git -C .lake/packages/{mathlib,simongmt} rev-parse HEAD (25730c7c…, 2b366308…)`
- `python3 -I over dag.json: nodes with status accepted/integrating/merged and a candidate_commit whose lean_statement matches IsMassMeasure|IsRestriction|IsMeasureRepresentation|HasWeightedApproximateTangentSpaceAt|∃ … : TestFormOn|supportᶜ|IsBounded`
- `git show <candidate_commit>:GMT/Ch06/Submission.lean | grep 'theorem Submission.<name>' for iwl_restriction_theory, rectifiability_mass_measure_representation, slicing_representation_unique, polyhedral_approx_restriction_tau, lpf_wtc_ae_zero_density_off_set, iwl_weighted_tangent_locality (types byte-identical)`
- `cat nodes/<node>/isolated-comparator-result.json for the six reused nodes (passed = true, same candidate commits)`
- `rg -n 'def GeometricCurrentOn.massOn|theorem GeometricCurrentOn.massOn_mono|def massAdmissibleOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; rg -n 'def GeometricCurrentOn.(VanishesOn|zeroRegion|support)' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean; rg -n 'def IsSmoothForm|def IsTestForm' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `rg -n 'theorem CountablyRectifiable.mono|def HasWeightedApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'theorem isOpen_sUnion_countable|theorem measure_sUnion_null_iff|theorem iUnion_ball_nat|Monotone.measure_iUnion|theorem exists_contDiff_support_eq_eq_one_iff|theorem lintegral_indicator₀|theorem restrict_restrict₀|theorem ofReal_inv_of_pos' local-references/197bdd4b88278494/mathlib/Mathlib`
- `git for-each-ref (931 ref tips) | xargs git grep -l -E 'dmr_|deformation_mass_restriction' -- 'GMT/*.lean' (no match); dag.json lean_name and node-id scan for the four new names (free)`
- `grep github_selected_issue 1104 .humanize/swarm-configs/*.json (1d5c18b4… max_nodes 1000); cat .humanize/issue-claims/22ac3a995036b376/1104.json (pid 31860); len(dag.json nodes) = 528`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py child_modules(contract mode) for all ten children; lean /tmp/dmr3/nc/NC_<key>.lean (exit 0, only the sorry warning)`
- `lean /tmp/dmr3/lean/Full.lean: six reused types as axioms, four new children proved, frozen parent type proved; #print axioms Submission.deformation_mass_restriction`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-mass-restriction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-mass-restriction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-mass-restriction-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-theory-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-theory-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-representation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-representation-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-restriction-tau-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-restriction-tau-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-tangent-locality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-tangent-locality-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/1d5c18b476c6436d8f2d8d63aa0120ff.json`
- `/tmp/dmr3/nc/NC_restriction_theory.lean`
- `/tmp/dmr3/lean/Full.lean`

Pinned revisions are confirmed, and Contract = Submission = snapshot Contract. Six accepted theorems in other branches cover the heavy parts of the supplied proof: Riesz representation and mass measure, restriction existence, uniqueness and mass identity, local π–λ uniqueness, τ-restriction, the upper-density zero set, and weighted-tangent locality. Each is status accepted with a candidate commit and a passing isolated comparator, and each candidate Submission.lean declares Submission.<name> with exactly the type reused here. The remaining obligations are four new nodes with free names: mass-measure support and finiteness, bounded covector uniqueness, a.e. tangent transfer, and the restricted triple. All ten types pass validate_lean_statement and elaborate in the exact comparator NodeChallenge scope. A scratch file proves the four new children from exactly their declared dependencies and the exact frozen parent type from the ten children. Its axioms are only propext, Classical.choice and Quot.sound plus the six reused accepted declarations; there is no sorryAx and no parent helper declaration. The SimonGMT definitions used (massOn, massOn_mono, zeroRegion, support, IsSmoothForm order ∞, CountablyRectifiable.mono) and the Mathlib lemmas cited in the child proofs are present in the pinned sources.
