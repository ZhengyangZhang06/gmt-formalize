# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.lower_density-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.lower_density-a1.local_filling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–4 of the parent proof (Simon Ch. 6, 8.2(2)–(4), with the parent's corrections: the lower density replaces Θ^{*n}, and the support of the filling is controlled by the support bound of the isoperimetric filling). The argument is the accepted proof of cbrld_exists_small_filling_of_low_density (node root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.local_filling-a1, candidate commit 348cc6f616fa56dce61ca9cf76278330359db2c3) with exactly one change: the filling is taken from the in-range hypothesis (Isor) instead of the unrestricted (ISO), and (Isor) is applied only at (P, m) with d = m + 1, where m + 1 = d < d + 1 < P. Siblings used: small_scale (steps 1–2), slice and radius (step 3), mass_gap (step 5), constants (step 6).

Notation: n := d + 1 ≥ 1; ω_n := unitBallVolume n ∈ [0, ∞] and w := ω_n read as a real number; for a current Z, M(Z) := Z.mass = M_{ℝ^P}(Z) ∈ [0, ∞]; powers with real exponents are Real.rpow, with (n − 1)/n computed in ℝ from the cast of n.

1. (Reduction to a filling constant.) Fix P, d with d + 1 < P. It suffices to find a real a > 0, depending only on P and d, with the property
(H) for all x₁ ∈ ℝ^P, reals δ, s, ρ, F and A ∈ 𝒟_n(ℝ^P) with 0 < s, ρ < s, s < δ, 0 ≤ F ≤ (as)^n, ∂A integer multiplicity, spt ∂A ⊆ ∂B_ρ(x₁) and M(∂A) ≤ ENNReal.ofReal(2na·F^{(n−1)/n}), there is S ∈ 𝒟_n(ℝ^P) with ∂S = ∂A, M(S) ≤ ENNReal.ofReal(F/2) and spt S ⊆ B̄_{(1+3√P)δ}(x₁).
Indeed, suppose a > 0 has (H). Sibling small_scale, part (a) for n, gives w > 0. Put η₀ := a^n/w > 0. Fix C, μ, ξ satisfying the hypotheses of the statement (∂C = 0, μ finite on compacts, ξ μ-a.e. strongly measurable with |ξ(x)(α)| ≤ |α| a.e., C(ω) = ∫ξ(ω)dμ, ISP), a point x₁ with liminf_{r↓0} μ(B_r(x₁))/(ω_n r^n) < ENNReal.ofReal η₀, and δ > 0. Steps 2–4 produce ρ, A, S as required.

2. (Small scale.) Sibling small_scale, part (b) with P, μ, x₁, η₀ and δ, gives s with 0 < s < δ and μ(B_s(x₁)) < ENNReal.ofReal(η₀·w·s^n). Since η₀·w = a^n (w ≠ 0) and a^n·s^n = (as)^n, μ(B_s(x₁)) < ENNReal.ofReal((as)^n).

3. (Good radius and slice.) Sibling slice (with (SL), P, d, C, μ, ξ, x₁, ∂C = 0, the representation hypotheses and ISP) gives a Lebesgue-null set N ⊆ ℝ. Sibling radius (with P, n, μ, x₁, a, s and N; μ finite on compacts, 1 ≤ n, a > 0, s > 0, the bound of step 2 and volume N = 0) gives ρ with 0 < ρ < s, ρ ∉ N, μ(∂B_ρ(x₁)) = 0 and ℓ := liminf_{h↓0} h⁻¹·μ({x : ρ − h < |x − x₁| < ρ}) ≤ ENNReal.ofReal(2na·F^{(n−1)/n}), where F := μ(B_ρ(x₁)) read as a real number. The conclusion of slice at ρ (ρ > 0, ρ ∉ N) gives A ∈ 𝒟_n(ℝ^P) with A(ω) = ∫_{B_ρ(x₁)} ξ(ω)dμ for every test form ω, ∂A integer multiplicity, spt ∂A ⊆ ∂B_ρ(x₁) and M(∂A) ≤ ℓ, hence M(∂A) ≤ ENNReal.ofReal(2na·F^{(n−1)/n}). Since B_ρ(x₁) ⊆ B_s(x₁), μ(B_ρ(x₁)) ≤ μ(B_s(x₁)) < ENNReal.ofReal((as)^n) < ∞; so μ(B_ρ(x₁)) is finite, F ≥ 0, and F ≤ (as)^n (ENNReal.toReal_le_of_le_ofReal, using (as)^n ≥ 0).

4. (Conclusion from (H).) Apply (H) to x₁, δ, s, ρ, F and A (0 < s, ρ < s < δ, 0 ≤ F ≤ (as)^n and the properties of ∂A from step 3). It gives S with ∂S = ∂A, M(S) ≤ ENNReal.ofReal(F/2) and spt S ⊆ B̄_{(1+3√P)δ}(x₁). Since μ(B_ρ(x₁)) < ∞, ENNReal.ofReal(F/2) = ENNReal.ofReal((1/2)·F) = ENNReal.ofReal(1/2)·ENNReal.ofReal(F) = ENNReal.ofReal(1/2)·μ(B_ρ(x₁)) (ENNReal.ofReal_mul with 1/2 ≥ 0, then ENNReal.ofReal_toReal). Together with 0 < ρ < s < δ and μ(∂B_ρ(x₁)) = 0, the radius ρ and the currents A, S satisfy every requirement of the conclusion. It remains to produce a with (H); we distinguish d = 0 and d = m + 1.

5. (Case d = 0, n = 1.) Take a := 1/4 > 0. In (H), (n − 1)/n = 0, so F^{(n−1)/n} = F^0 = 1 and 2na·F^{(n−1)/n} = 2·1·(1/4)·1 = 1/2; hence M(∂A) ≤ ENNReal.ofReal(1/2) < 1. As ∂A ∈ 𝒟_0(ℝ^P) is integer multiplicity, sibling mass_gap (with (MR)) gives ∂A = 0. Take S := 0 ∈ 𝒟_1(ℝ^P). Then ∂S = 0 = ∂A (extensionality: (∂0)(η) = 0(dη) = 0 for every η). M(S) = 0 ≤ ENNReal.ofReal(F/2), because every value of the zero current is 0, so the supremum defining M(0) is 0. And spt S = ∅ ⊆ B̄_{(1+3√P)δ}(x₁): every y ∈ ℝ^P lies in the open ball B_1(y), an open set with compact closure on which the zero current vanishes, so y lies in the zero region of 0.

6. (Case d = m + 1, n = m + 2.) From d + 1 < P we get m + 1 < P, so (Isor) at (P, m) gives a real c ≥ 1 such that every integer multiplicity Z ∈ 𝒟_{m+1}(ℝ^P) with compact support, ∂Z = 0 and M(Z) < ∞ equals ∂Y for some integer multiplicity Y ∈ 𝒟_{m+2}(ℝ^P) with M(Y) ≤ ENNReal.ofReal(c(2cM)^{1/(m+1)}M) and spt Y ⊆ thickening(3√P(2cM)^{1/(m+1)}, spt Z), where M := M(Z) read as a real number. Sibling constants, with m and c ≥ 1, gives a > 0 such that for all reals s, F, M with s ≥ 0, F ≥ 0, F ≤ (as)^{m+2} and 0 ≤ M ≤ 2n·a·F^{(n−1)/n}: (A) c(2cM)^{1/(m+1)}M ≤ F/2 and (B) (2cM)^{1/(m+1)} ≤ s. We verify (H) for this a. Let x₁, δ, s, ρ, F and A be as in (H), and Z := ∂A ∈ 𝒟_{m+1}(ℝ^P).
(a) ∂Z = ∂∂A = 0 (GeometricCurrentOn.boundary_boundary); Z is integer multiplicity by assumption; spt Z is closed, being the complement of the open zero region of Z, and is contained in the compact sphere ∂B_ρ(x₁), hence compact; and M(Z) ≤ ENNReal.ofReal(2na·F^{(n−1)/n}) < ∞.
(b) (Isor) gives Y as above. Put M := M(Z) read as a real number. Since 2na·F^{(n−1)/n} ≥ 0, M(Z) ≤ ENNReal.ofReal(2na·F^{(n−1)/n}) gives 0 ≤ M ≤ 2na·F^{(n−1)/n} (ENNReal.toReal_le_of_le_ofReal). Sibling constants, applied with s (s ≥ 0 because s > 0), F (0 ≤ F ≤ (as)^{m+2}) and M, gives (A) and (B).
(c) Take S := Y. Then ∂S = Z = ∂A, and M(S) ≤ ENNReal.ofReal(c(2cM)^{1/(m+1)}M) ≤ ENNReal.ofReal(F/2) by (A) and monotonicity of ENNReal.ofReal.
(d) Let y ∈ spt S. By the support bound of (Isor) and Metric.mem_thickening_iff there is z ∈ spt Z with |y − z| < 3√P(2cM)^{1/(m+1)}. By (B) and s < δ, (2cM)^{1/(m+1)} ≤ s ≤ δ, so 3√P(2cM)^{1/(m+1)} ≤ 3√P·δ (√P ≥ 0). Since spt Z ⊆ ∂B_ρ(x₁), |z − x₁| = ρ < s < δ. By the triangle inequality |y − x₁| ≤ |y − z| + |z − x₁| < 3√P·δ + δ = (1 + 3√P)δ, so y ∈ B̄_{(1+3√P)δ}(x₁). Hence spt S ⊆ B̄_{(1+3√P)δ}(x₁).

7. (Conclusion.) In both cases a > 0 has (H), so by steps 1–4 the number η₀ = a^n/w > 0, which depends only on P and d (through c of (Isor) at (P, d − 1) when d ≥ 1), has the asserted property. ∎

## Key steps

1. Reduce to a constant a > 0 with the slice-filling property (H) and put η₀ := a^n/ω_n (small_scale gives ω_n > 0).
2. small_scale gives s ∈ (0, δ) with μ(B_s(x₁)) < (as)^n.
3. slice gives a null set N; radius gives ρ ∈ (0, s) ∖ N with μ(∂B_ρ(x₁)) = 0 and slice liminf ≤ 2naF^{(n−1)/n}; slice at ρ gives A = C⌞B_ρ(x₁) with ∂A integer multiplicity on the sphere and M(∂A) ≤ 2naF^{(n−1)/n}.
4. n = 1: a = 1/4, so M(∂A) ≤ 1/2 < 1, ∂A = 0 by mass_gap, and S = 0.
5. n = m + 2: (Isor) at (P, m), m + 1 = d < P, fills Z = ∂A by S; constants gives M(S) ≤ F/2 and filling radius ≤ s, so spt S ⊆ B̄_{(1+3√P)δ}(x₁).
6. Convert M(S) ≤ ofReal(F/2) into M(S) ≤ ½·μ(B_ρ(x₁)) using μ(B_ρ(x₁)) < ∞.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD (b4d606db1da5da8fa2c0292ad4924d97de8b3c4b)`
- `cmp GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn 'dtc_bc_tc_cl\|cbrld' local-references/123e8435b4a2469b/project (no match)`
- `grep -rn 'theorem ae_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean (line 134); 'theorem exists_disjoint_closedBall_covering_ae ' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean (line 833); 'theorem mem_thickening_iff' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean (line 143); 'theorem isCompact_sphere' mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean (line 46) in the snapshot`
- `grep -rn 'isOpen_zeroRegion' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (line 119)`
- `python3 -I over dag.json: status, candidate_commit, lean_statement and natural_proof of the cbrld_* / cbrldlf_* nodes under root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1 (all accepted); scan for lean statements containing '(∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 1 ≤ c' and for lean names with prefix dtc_bc_tc_cl_ld (none)`
- `git show <candidate>:GMT/Ch07/Submission.lean for c226ea8f, 215074ec, d57ff8da, 8dc7218d, 1751929c, b6539fa1, a1c12d76: the line 'theorem Submission.<name> : <type> := by' is string-equal to the DAG lean_statement (all True); git show 348cc6f6:GMT/Ch07/Submission.lean lines 1006–1092 (accepted local-filling proof; (ISO) used only as hISO P m in the d = m + 1 case)`
- `lake env lean /tmp/ld_split_check/lean/Check.lean (all 8 types elaborate after import GMT.Ch07.Submission; LDCheck.local_filling and LDCheck.parent compile; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean on each extracted candidate Submission.lean with #print axioms of the reused declaration and of cmc_slice_mass_bounds (all exit 0; propext, Classical.choice, Quot.sound)`
- `verifier/lean_contract.py validate_lean_statement on the 7 child types and the parent type (all pass)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-6a2d7e6c22/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5b8e55fd95/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3d838668ea/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8ea6d63a05/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-77789fb32b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ld_split_check/lean/Check.lean`

The snapshot (local-project; project b4d606db, Mathlib 25730c7c) has a Ch07 contract byte-identical to the workspace Contract.lean and Submission.lean. It contains no lower-density, slice-filling or null-set declaration (no match for dtc_bc_tc_cl or cbrld in the project tree), so the reusable material comes from the DAG. All lemmas the assembly and the new child rely on are present: ae_iff, Besicovitch.exists_disjoint_closedBall_covering_ae, Metric.mem_thickening_iff and isCompact_sphere in the snapshot Mathlib, and GeometricCurrentOn.isOpen_zeroRegion in the pinned simongmt. The six reused lower-density pieces of the parallel cbr branch (slice, radius, mass_gap, small_scale, constants, null_set) are all accepted. Their declaration lines at the candidate commits are string-equal to the proposed types, and each recompiles there with only propext, Classical.choice and Quot.sound. The accepted local filling cannot be reused because it assumes the unrestricted (ISO). The in-range variant is the only new child, and no DAG node has its type or name. All 7 child types and the parent type elaborate after import GMT.Ch07.Submission. The parent assembly from cmc_slice_mass_bounds, local_filling and null_set, and local_filling from its five siblings, compile with standard axioms.
