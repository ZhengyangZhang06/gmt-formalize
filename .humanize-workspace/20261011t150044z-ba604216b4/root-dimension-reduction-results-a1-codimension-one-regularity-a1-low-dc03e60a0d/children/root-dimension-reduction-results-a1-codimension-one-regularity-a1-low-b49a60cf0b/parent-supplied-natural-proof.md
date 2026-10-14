# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.allard_graph-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.allard_graph-a1.tilt_excess_decay-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Role in the parent proof: 7B and Parts 8.2–8.3 (Simon Ch. 5, Remark 4.6 and the proof of Theorem 5.2, (1)–(8)) of the proof of the selected Allard theorem Submission.codim1_ldr_allard_bounded_curvature_graph; the parent applies it at (y, σ := δ₀ρ/2, T₀) for every y ∈ spt μ ∩ B_{δ₀ρ/2}(z). Provenance: statement, frozen Lean type and proof are identical to those of the independently audited child tilt_excess_decay (Submission.dorag_tilt_excess_decay) of DAG node root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1, whose supplied parent proof equals Parts 0–9 of the selected proof; the only change is that the sibling tilt_excess_step is the declaration Submission.codim1_ldr_ag_tilt_excess_one_step_decay.

Sibling map (dependency key — frozen Lean declaration — labels used below): tangent_projection_measurable — Submission.dorag_approxTangent_starProjection_aesm (x ↦ p_x is AE-strongly measurable for μ = R.measure); density_bounds — Submission.dorag_standing_density_bounds (constants δ₁, C₂; (a), (b), (c), (d) are its four conclusions in order); tilt_excess_step — Submission.codim1_ldr_ag_tilt_excess_one_step_decay (constants θ₀ ∈ (0, 1/4] and δ_s ∈ (0, 1/8], named θ₀ and δ₂ in its Lean type; its conclusion is the one-step decay E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T) for every ξ ∈ spt μ ∩ B_{δρ}(z), σ ∈ (0, δρ] and n-plane T, with an n-plane S).
Source: parent proof Part 7, 7B (Simon Ch. 5, Remark 4.6) and Parts 8.2–8.3 (Simon Ch. 5, proof of Theorem 5.2, (1)–(8), with the correction recorded there: Simon's η^jσ₀ is η^jσ₀/2), here at a general scale σ ∈ (0, δρ] and for a general initial n-plane T. Conventions: E := ℝ^{n+k}; B_t(y) closed ball; M := R.carrier, θ := R.mult, μ := R.measure = θHⁿ⌞M; ω_n := unitBallVolume n ∈ (0, ∞); p_x := projection onto approxTangentPlane n M x; for a subspace S, p_S := S.starProjection; for linear A : E → E, |A|² := Σ_i |Ae_i|² (Hilbert–Schmidt; the Lean sums over EuclideanSpace.single i 1), a Euclidean norm on the finite-dimensional space of linear maps E → E, with ‖A‖ ≤ |A|. For the fixed centre ξ below, E(r, S) := r^{−n}∫_{B_r(ξ)}|p_x − p_S|²dμ and E_*(r, S) := max{E(r, S), δ^{−1}κ²r²} (the Lean max of ofReal(1/rⁿ)·∫⁻ and ofReal(κ²r²/δ)). All integrals of nonnegative functions are lower Lebesgue integrals in [0, ∞].

Preliminaries. (P1) κ ≥ 0 since κ ≥ ‖H(x)‖. (P2) For compact K ⊆ W, μ(K) = ∫_{M∩K}θ dHⁿ < ∞ (IMRep.locallyIntegrable_mult, K ⊆ W ⊆ U). (P3) For a subspace S, p_S is a self-adjoint idempotent and |p_S|² = trace p_S = dim S; since approxTangentPlane n M x is either an n-dimensional subspace or ⊥, |p_x|² ≤ n, so |p_x − p_S|² ≤ (|p_x| + |p_S|)² ≤ 4n for every x and every n-plane S. (P4) For every fixed n-plane S, x ↦ |p_x − p_S|² is μ-AE-measurable (tangent_projection_measurable composed with the continuous map A ↦ |A − p_S|²); hence the integral of a sum of such functions and of nonnegative constants over a Borel set is the sum of the integrals.
0. Constants. Take θ₀ ∈ (0, 1/4] and δ_s ∈ (0, 1/8] from tilt_excess_step and δ₁ ∈ (0, 1/8] from density_bounds. Put δ₂ := min{δ_s, δ₁} ∈ (0, 1/8], C₁₀ := 8/ω_n and C := max{4C₁₀θ₀^{−n}, (2 + 16ω_nC₁₀)θ₀^{−n−1}} > 0. These depend only on n and k.
1. Setting. Let 0 < δ ≤ δ₂ and assume the hypotheses; put r₁ := δρ, and fix ξ ∈ spt μ ∩ B_{r₁}(z), σ ∈ (0, r₁] and an n-plane T. For 0 < t ≤ r₁: |ξ − z| + t ≤ 2r₁ ≤ ρ, so B_t(ξ) ⊆ B_ρ(z) ⊆ W; moreover ξ ∈ spt μ ∩ B_{4r₁}(z) and t ≤ r₁ ≤ (1 − 4δ)ρ (as 5δ ≤ 1), so density_bounds (a), (b) (δ ≤ δ₁) give
 (D±) ½ω_ntⁿ ≤ μ(B_t(ξ)) ≤ 2ω_ntⁿ for 0 < t ≤ r₁.
 By (P3) and (D±), E(t, S) ≤ 8nω_n < ∞ and E_*(t, S) < ∞ for every n-plane S and 0 < t ≤ r₁. Put E_* := E_*(σ, T) ∈ [0, ∞).
2. One-step tilt bound (parent 7B; Simon 4.6). Claim: if 0 < r ≤ r₁ and S, S' are n-planes with E_*(θ₀r, S') ≤ θ₀E_*(r, S), then |p_{S'} − p_S|² ≤ C₁₀θ₀^{−n}E_*(r, S). Indeed, for every x, |p_{S'} − p_S|² ≤ 2|p_x − p_{S'}|² + 2|p_x − p_S|² (triangle inequality for the Hilbert–Schmidt norm and (a + b)² ≤ 2a² + 2b²). Integrating over B_{θ₀r}(ξ) (P4) and using B_{θ₀r}(ξ) ⊆ B_r(ξ): |p_{S'} − p_S|²μ(B_{θ₀r}(ξ)) ≤ 2(θ₀r)ⁿE(θ₀r, S') + 2rⁿE(r, S) ≤ 2(θ₀r)ⁿθ₀E_*(r, S) + 2rⁿE_*(r, S). By (D±), μ(B_{θ₀r}(ξ)) ≥ ½ω_n(θ₀r)ⁿ > 0, so |p_{S'} − p_S|² ≤ (4/ω_n)(θ₀ + θ₀^{−n})E_*(r, S) ≤ (8/ω_n)θ₀^{−n}E_*(r, S) (θ₀ ≤ 1 ≤ θ₀^{−n}).
3. Iteration (parent 8.2). Let σ_j := θ₀^jσ ∈ (0, r₁] for j ≥ 0. Define n-planes S_j recursively: S₀ := T; given the n-plane S_j, apply tilt_excess_step (δ ≤ δ_s, the same data, ξ ∈ spt μ ∩ B_{δρ}(z), the scale σ_j ∈ (0, δρ] and the plane S_j) to obtain an n-plane S_{j+1} with E_*(σ_{j+1}, S_{j+1}) = E_*(θ₀σ_j, S_{j+1}) ≤ θ₀E_*(σ_j, S_j). By induction E_*(σ_j, S_j) ≤ θ₀^jE_* for all j ≥ 0, and by Step 2 (with r := σ_j, S := S_j, S' := S_{j+1}): |p_{S_{j+1}} − p_{S_j}| ≤ (C₁₀θ₀^{−n}θ₀^jE_*)^{1/2} = (C₁₀θ₀^{−n}E_*)^{1/2}θ₀^{j/2}.
4. The limit plane (parent 8.2). Since θ₀^{1/2} ≤ 1/2, for i ≥ j: |p_{S_i} − p_{S_j}| ≤ Σ_{l≥j}(C₁₀θ₀^{−n}E_*)^{1/2}θ₀^{l/2} ≤ 2(C₁₀θ₀^{−n}E_*)^{1/2}θ₀^{j/2}. Hence (p_{S_j}) is a Cauchy sequence in the finite-dimensional normed space of linear maps E → E and converges to a linear map P. Each p_{S_j} satisfies p² = p, p* = p and trace p = n; these conditions are closed (composition, adjoint and trace are continuous), so P² = P, P* = P and trace P = n. A self-adjoint idempotent is the orthogonal projection onto its range, and the trace of an idempotent equals its rank; so S := P(E) is a subspace with dim S = n and p_S = P (in Lean: Module.finrank ℝ S = n and S.starProjection = P). Letting i → ∞: |p_S − p_{S_j}|² ≤ 4C₁₀θ₀^{−n}θ₀^jE_* for every j ≥ 0. With j = 0 (S₀ = T): |p_S − p_T|² ≤ 4C₁₀θ₀^{−n}E_* ≤ C·E_*. This is the second conclusion.
5. Decay at all scales (parent 8.3; Simon (7)). Let 0 < s ≤ σ. Since σ_j = θ₀^jσ equals σ for j = 0 and decreases to 0 (θ₀ < 1), there is j ≥ 0 with σ_{j+1} < s ≤ σ_j. For every x, |p_x − p_S|² ≤ 2|p_x − p_{S_j}|² + 2|p_{S_j} − p_S|²; integrating over B_s(ξ) ⊆ B_{σ_j}(ξ) (P4) and using Steps 3–4 and (D±):
 ∫_{B_s(ξ)}|p_x − p_S|²dμ ≤ 2σ_jⁿE(σ_j, S_j) + 2|p_{S_j} − p_S|²μ(B_s(ξ)) ≤ 2σ_jⁿθ₀^jE_* + 2·4C₁₀θ₀^{−n}θ₀^jE_*·2ω_nsⁿ.
 Since σ_j = σ_{j+1}/θ₀ < s/θ₀, σ_jⁿ ≤ θ₀^{−n}sⁿ; and θ₀^j = σ_j/σ < s/(θ₀σ). Therefore ∫_{B_s(ξ)}|p_x − p_S|²dμ ≤ (2 + 16ω_nC₁₀)θ₀^{−n}θ₀^jsⁿE_* ≤ (2 + 16ω_nC₁₀)θ₀^{−n−1}(s/σ)sⁿE_* ≤ C(s/σ)sⁿE_*. This is the first conclusion.
6. Lean form. By Step 1, E_* is the finite value of max(ofReal(1/σⁿ)·∫⁻_{B_σ(ξ)} ofReal(|p_x − p_T|²)dμ, ofReal(κ²σ²/δ)), and all integrals above are the lower Lebesgue integrals ∫⁻ ofReal(…) dμ of the statement, which are finite. So Step 5 gives ∫⁻_{B_s(ξ)} ofReal(|p_x − p_S|²)dμ ≤ ofReal(C(s/σ)sⁿ)·max(…) for every s ∈ (0, σ], and Step 4 gives ofReal(|p_S − p_T|²) ≤ ofReal(C)·max(…) (ofReal is monotone and multiplicative on [0, ∞)). Together with Module.finrank ℝ S = n this is the assertion, for every δ ∈ (0, δ₂], with δ₂ ∈ (0, 1/8] and C > 0 depending only on n and k. ∎

## Key steps

1. Take θ₀, δ_s from tilt_excess_step and δ₁ from density_bounds; δ₂ := min{δ_s, δ₁}, C₁₀ := 8/ω_n.
2. One-step tilt bound (7B): E_*(θ₀r, S') ≤ θ₀E_*(r, S) implies |p_{S'} − p_S|² ≤ C₁₀θ₀^{−n}E_*(r, S), by density_bounds (b) and measurability of x ↦ p_x.
3. Iterate tilt_excess_step at the scales σ_j = θ₀^jσ, giving n-planes S_j with E_*(σ_j, S_j) ≤ θ₀^jE_*.
4. (p_{S_j}) is Cauchy; its limit is the orthogonal projection onto an n-plane S with |p_S − p_{S_j}|² ≤ 4C₁₀θ₀^{−n}θ₀^jE_*, hence |p_S − p_T|² ≤ CE_*.
5. Interpolate between consecutive scales using density_bounds (a): ∫_{B_s(ξ)}|p_x − p_S|² ≤ C(s/σ)sⁿE_* for s ∈ (0, σ]; translate to the ENNReal form.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A6 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n -i 'allard|tilt.?excess|harmonic.?approx|lipschitz.?approx' local-references/123e8435b4a2469b/project/GMT`
- `grep -n 'sorry|^theorem|^lemma|structure RectifiableVarifold|^import' local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `rg -l -i 'rellich|kondrachov|weyl.s lemma' local-references/123e8435b4a2469b/mathlib/Mathlib (exit 1, no match)`
- `rg -n 'theorem ae_tendsto_average_norm_sub|theorem exists_disjoint_subfamily_covering_enlargement_closedBall|theorem ae_differentiableAt|theorem extend_real|theorem norm_fderiv_le_of_lipschitz' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn 'dorag_|codim1_ldr' local-references/123e8435b4a2469b/project/GMT (no match)`
- `rg -l -i allard simongmt/Poincare/SimonGMT; sed -n 1,40p simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `python3 -I scans of dag.json (08:30Z–09:01Z): the selected node; dor_allard_bounded_curvature_graph and its 12 children (status, candidate_commit, frozen lean_statement, depends_on) and their subtrees; DAG owners of all 12 proposed lean_names; children of the parent low_density_regular`
- `diff nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/parent-supplied-natural-proof.md nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dc03e60a0d/parent-supplied-natural-proof.md`
- `python3 -I: compare decomposition-v3.json subproblems with each child's parent-child-handoff.json and the dag.json frozen types; read decomposition-audit-v1..v3.json and the parent's decomposition-v2.json and decomposition-audit-v2.json`
- `git show fa8a43ae (speculative assembly of dor_allard_bounded_curvature_graph); git show 67cb4097 ea6fb1e8 0794dd28 (speculative drafts of the 3 originals); git show <candidate>:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name> ' for the 9 reused candidates; isolated-comparator-result.json and comparator-v1.log of each reused node`
- `lean -DautoImplicit=false /tmp/ag-ldr-check/Types.lean; lean -DautoImplicit=false /tmp/ag-ldr-check/Assembly.lean (LEAN_PATH from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `grep -c codim1_ldr_ag in the dag.json of all 8 chapter runs; grep -rl codim1_ldr_ag GMT simongmt/Poincare local-references/123e8435b4a2469b/project nodes; git for-each-ref refs/heads refs/remotes (1434 distinct commits) | xargs git grep -l codim1_ldr_ag -- 'GMT/*.lean' (no match)`
- `runtime.py: _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _reference_use_problem, speculative promotion; store.py ensure; swarm config 9c96ace3 (max_children, max_depth, max_nodes)`
- `python3 -I /tmp/ag-ldr-check/cmp.py on the transcribed subproblems (byte-identical to final_subproblems.json)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dc03e60a0d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dc03e60a0d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-b06ad0f914/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-b06ad0f914/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-34fbedec8b/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-5e610a0036/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-bca0eeb76e/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-8c018a8a8b/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b5982cc9c1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-498c875e36/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9e10fe2792/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db45a55178/isolated-comparator-result.json`
- `/runtime/flows/gmt-claude-ebe9113f52d5/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-ebe9113f52d5/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/9c96ace382df405680ef2a8c9a521a87.json`
- `/tmp/ag-ldr-check/Types.lean`
- `/tmp/ag-ldr-check/Types.log`
- `/tmp/ag-ldr-check/Assembly.lean`
- `/tmp/ag-ldr-check/Assembly.log`
- `/tmp/ag-ldr-check/reuse-evidence.json`
- `/tmp/ag-ldr-check/final_subproblems.json`
- `/tmp/ag-ldr-check/cmp.py`

Pins match. The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. simongmt 2b366308 equals the snapshot lake-manifest pin. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library.
- SimonGMT Chapter05/Basic.lean leaves Lipschitz approximation, excess decay and Allard regularity unformalized.
- The snapshot GMT/Ch05/Submission.lean only states analogues, for its own RectifiableVarifold, behind a sorry-backed main_theorem.
- The snapshot Mathlib has no Rellich, Kondrachov or Weyl lemma (rg exit 1). It does have the tools the children cite: ae_tendsto_average_norm_sub, Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall, norm_fderiv_le_of_lipschitz and Rademacher.
- No dorag_ or codim1_ldr declaration exists in the snapshot project.
So the analytic lemmas remain genuine children.
DAG. The selected type equals that of dor_allard_bounded_curvature_graph, whose audited 12-child v3 decomposition is reused.
- 9 children are accepted, with candidate commits, identical frozen types and passing isolated comparators; they are reused by name.
- 3 children are not accepted; they are mirrored under fresh codim1_ldr_ag_ names with no collisions.
Lean. All 12 child types and the selected type elaborate after import GMT.Ch07.Submission. The assembly proves the selected type from the 5 directly used child types, with axioms propext, Classical.choice and Quot.sound only.
