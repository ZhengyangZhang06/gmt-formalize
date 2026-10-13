# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.allard_graph-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.allard_graph-a1.harmonic_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Role in the parent proof: Part 6 (Simon Ch. 5, 3.1–3.4) of the proof of the selected Allard theorem Submission.codim1_ldr_allard_bounded_curvature_graph, in the affine-output form used in Part 7, Steps 7–8, by the sibling tilt_excess_step (Submission.codim1_ldr_ag_tilt_excess_one_step_decay). Provenance: statement, frozen Lean type and proof are identical to those of the independently audited child harmonic_approximation (Submission.dorag_harmonic_affine_approximation) of DAG node root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1, whose supplied parent proof equals Parts 0–9 of the selected proof.

Source: parent proof Part 6 (Simon Ch. 5, Lemma 3.1 and its proof; estimates 3.2–3.4) and the use made of them in Part 7, Steps 7–8 ((17'), (18'), (19')). Conventions: Lⁿ := volume on ℝⁿ (Lean Euclid n); B̆_ρ, B_ρ open/closed balls of ℝⁿ centred at 0 unless indicated; ω_n := Lⁿ(B̆₁) ∈ (0, ∞); for a Lipschitz function w, ∇w := the a.e. derivative (Lean fderiv ℝ w, a linear functional whose operator norm |∇w| is the Euclidean norm of the gradient), ∇w·∇ζ := Σ_i ∂_iw ∂_iζ (the Lean sum over EuclideanSpace.single i 1). A Lipschitz function on B̆_ρ belongs to W^{1,2}(B̆_ρ) and its weak gradient equals its a.e. gradient. "Harmonic on B̆_ρ" means C² (hence C^∞) with Δh = 0 there.

Part A (Harmonic approximation, Simon 3.1, normalized). Claim: for every ε' > 0 there is δ_A(n, ε') > 0 such that if B := B̆₁ and w ∈ W^{1,2}(B) satisfies ∫_B|∇w|² ≤ 1 and |∫_B ∇w·∇ζ| ≤ δ_A sup|∇ζ| for every ζ ∈ C¹_c(B), then there is a harmonic h on B with ∫_B|∇h|² ≤ 1 and ∫_B(h − w)² ≤ ε'.
A1. Suppose not. Then there are ε' > 0 and w_j ∈ W^{1,2}(B) (j = 1, 2, …) with ∫_B|∇w_j|² ≤ 1, |∫_B ∇w_j·∇ζ| ≤ j^{−1}sup|∇ζ| for all ζ ∈ C¹_c(B), and ∫_B(w_j − h)² > ε' for every harmonic h on B with ∫_B|∇h|² ≤ 1.
A2. Let λ_j := ω_n^{−1}∫_B w_j. By the Poincaré inequality on the ball (e.g. [GT01, (7.45)]), ∫_B|w_j − λ_j|² ≤ C(n)∫_B|∇w_j|² ≤ C(n). Thus (w_j − λ_j) is bounded in W^{1,2}(B), and by Rellich's compactness theorem and weak compactness of bounded sets in L²(B) a subsequence (not relabelled) satisfies w_j − λ_j → w in L²(B) and ∇w_j ⇀ ∇w weakly in L²(B; ℝⁿ), with w ∈ W^{1,2}(B) and ∫_B|∇w|² ≤ liminf ∫_B|∇w_j|² ≤ 1 (weak lower semicontinuity of the norm).
A3. For ζ ∈ C¹_c(B), ∇ζ ∈ L²(B), so ∫_B ∇w·∇ζ = lim_j ∫_B ∇w_j·∇ζ = 0 by A1. By Weyl's lemma, w (after modification on a null set) is harmonic on B.
A4. h_j := w + λ_j is harmonic with ∫_B|∇h_j|² = ∫_B|∇w|² ≤ 1, and ∫_B(w_j − h_j)² = ∫_B(w_j − λ_j − w)² → 0 < ε', contradicting A1 for large j.
Part B (Scaling). Let R₀ > 0 and w ∈ W^{1,2}(B̆_{R₀}) with R₀^{−n}∫_{B̆_{R₀}}|∇w|² ≤ 1 and |∫_{B̆_{R₀}}∇w·∇ζ| ≤ δ_A R₀ⁿ sup|∇ζ| for all ζ ∈ C¹_c(B̆_{R₀}). Put w₁(y) := R₀^{−1}w(R₀y). Then ∇w₁(y) = ∇w(R₀y), ∫_B|∇w₁|² = R₀^{−n}∫_{B̆_{R₀}}|∇w|² ≤ 1; for ζ₁ ∈ C¹_c(B) let ζ(x) := R₀ζ₁(x/R₀) ∈ C¹_c(B̆_{R₀}), so ∇ζ(x) = ∇ζ₁(x/R₀), sup|∇ζ| = sup|∇ζ₁| and ∫_{B̆_{R₀}}∇w·∇ζ = R₀ⁿ∫_B∇w₁·∇ζ₁; hence |∫_B∇w₁·∇ζ₁| ≤ δ_A sup|∇ζ₁|. Part A gives a harmonic h₁ on B; then h(x) := R₀h₁(x/R₀) is harmonic on B̆_{R₀} with R₀^{−n}∫_{B̆_{R₀}}|∇h|² ≤ 1 and ∫_{B̆_{R₀}}(h − w)² = R₀^{n+2}∫_B(h₁ − w₁)² ≤ ε'R₀^{n+2}.
Part C (Estimates for harmonic functions, Simon 3.2–3.4). Let h be harmonic on B̆_{R₀} with ∫_{B̆_{R₀}}|∇h|² ≤ R₀ⁿ and h ∈ L²(B̆_{R₀}).
C1. Mean value property: h(0) = (ω_nρⁿ)^{−1}∫_{B̆_ρ}h for 0 < ρ < R₀; letting ρ ↑ R₀ (h ∈ L¹(B̆_{R₀})), h(0) = (ω_nR₀ⁿ)^{−1}∫_{B̆_{R₀}}h, so by Cauchy–Schwarz |h(0)| ≤ ω_n^{−1/2}R₀^{−n/2}‖h‖_{L²(B̆_{R₀})}.
C2. Each ∂_ih is harmonic, so likewise ∇h(0) = (ω_nR₀ⁿ)^{−1}∫_{B̆_{R₀}}∇h and |∇h(0)| ≤ ω_n^{−1/2}R₀^{−n/2}‖∇h‖_{L²(B̆_{R₀})} ≤ ω_n^{−1/2}.
C3. For |y| ≤ 3R₀/4, B̆_{R₀/4}(y) ⊆ B̆_{R₀}, so by the mean value property |∂_ih(y)| ≤ (ω_n(R₀/4)ⁿ)^{−1/2}‖∇h‖_{L²(B̆_{R₀})} ≤ 2ⁿω_n^{−1/2}. For a harmonic u on B̆_ρ(x), |∇u(x)| ≤ (n/ρ)sup_{B̆_ρ(x)}|u| (apply the mean value property to ∂_ju and the divergence theorem). With u = ∂_ih, ρ = R₀/4 and |x| ≤ R₀/2: |D²h(x)| ≤ C₁/R₀ for |x| ≤ R₀/2, C₁ := n^{3/2}·4·2ⁿω_n^{−1/2} (|D²h| the Hilbert–Schmidt norm).
C4. Let ℓ(v) := h(0) + ∇h(0)·v and θ' ∈ (0, 1/4]. For |v| ≤ θ'R₀ ≤ R₀/4, Taylor's formula with the segment [0, v] ⊆ B_{R₀/2} gives |h(v) − ℓ(v)| ≤ ½|v|² sup_{B_{R₀/2}}|D²h| ≤ ½C₁θ'²R₀.
Part D (Conclusion; Simon 3.4 and the computation (17')–(19') of the parent proof). Put C := max{ω_n^{−1/2}, 2, ½ω_nC₁²} (depends only on n) and, given ε' > 0, δ_h := δ_A(n, ε'). Let R₀ > 0 and w : ℝⁿ → ℝ be Lipschitz with ∫_{B̆_{R₀}}|∇w|² ≤ R₀ⁿ and |∫_{B̆_{R₀}}∇w·∇ζ| ≤ δ_h R₀ⁿ G whenever ζ is C¹ with compact support, tsupport ζ ⊆ B̆_{R₀}, and |∇ζ| ≤ G everywhere (in particular with G = sup|∇ζ|). (Integrability: fderiv ℝ w is Borel measurable (Mathlib measurable_fderiv, valid for every function), and since w is Lipschitz with constant Lw, ‖fderiv ℝ w v‖ ≤ Lw for every v (norm_fderiv_le_of_lipschitz; fderiv is 0 where w is not differentiable); by Rademacher's theorem w is differentiable a.e., and, as recalled in the conventions, its a.e. derivative fderiv ℝ w is the weak gradient ∇w. For ζ as above, fderiv ℝ ζ is continuous with compact support, hence bounded. So the integrands ‖fderiv ℝ w v‖² and Σ_i ∂_iw(v)∂_iζ(v) of the two Lean hypotheses are bounded Borel functions on the ball B̆_{R₀}, which has finite measure, and their Bochner integrals are the Lebesgue integrals written here; likewise w² and (w − a − b)² are continuous, hence bounded on bounded balls, so the Bochner integrals in the conclusions are genuine Lebesgue integrals.) Then w|_{B̆_{R₀}} ∈ W^{1,2}(B̆_{R₀}) and Part B provides a harmonic h on B̆_{R₀} with ∫_{B̆_{R₀}}|∇h|² ≤ R₀ⁿ and ∫_{B̆_{R₀}}(h − w)² ≤ ε'R₀^{n+2}; in particular h ∈ L²(B̆_{R₀}) (w is bounded on B̆_{R₀}). Let a := h(0) and b := Dh(0) (the linear functional v ↦ ∇h(0)·v; ‖b‖ = |∇h(0)|).
D1. ‖b‖ ≤ ω_n^{−1/2} ≤ C by C2.
D2. By C1 and Minkowski, |a| ≤ ω_n^{−1/2}R₀^{−n/2}(‖w‖_{L²(B̆_{R₀})} + ‖h − w‖_{L²(B̆_{R₀})}) ≤ ω_n^{−1/2}(R₀^{−n}∫_{B̆_{R₀}}w²)^{1/2} + ω_n^{−1/2}R₀^{−n/2}(ε'R₀^{n+2})^{1/2} ≤ C·√(∫_{B̆_{R₀}}w²/R₀ⁿ) + C√ε' R₀.
D3. For θ' ∈ (0, 1/4], by (u + u')² ≤ 2u² + 2u'², Part B and C4: ∫_{B̆_{θ'R₀}}(w − a − b(v))²dv ≤ 2∫_{B̆_{R₀}}(w − h)² + 2∫_{B̆_{θ'R₀}}(h − ℓ)² ≤ 2ε'R₀^{n+2} + 2ω_n(θ'R₀)ⁿ(½C₁θ'²R₀)² = (θ'R₀)^{n+2}(2ε'/θ'^{n+2} + ½ω_nC₁²θ'²) ≤ C(ε'/θ'^{n+2} + θ'²)(θ'R₀)^{n+2}.
D1–D3 are the three asserted conclusions; C does not depend on ε', and δ_h depends only on n and ε'. ∎

## Key steps

1. Harmonic approximation (Simon 3.1) by contradiction, using the Poincaré inequality, Rellich compactness, weak limits and Weyl's lemma.
2. Scale to radius R₀.
3. Mean-value and derivative estimates for harmonic h (Simon 3.2–3.4), and Taylor expansion on B_{θ'R₀}.
4. Set a := h(0) and b := Dh(0), and derive the bounds on ‖b‖, |a| and ∫(w − a − b)².

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
