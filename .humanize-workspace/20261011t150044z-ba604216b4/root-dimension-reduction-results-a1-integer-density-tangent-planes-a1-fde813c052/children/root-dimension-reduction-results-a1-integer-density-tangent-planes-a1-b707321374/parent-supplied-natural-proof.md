# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.cycle_tangent_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.cycle_tangent_cone-a1.tangent_cones-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Registration note (context, not part of the numbered proof). This child is a new obligation with a fresh Lean name. Its frozen type is byte-identical to that of DAG node root.density_and_tangent_cones-a1 (Submission.density_and_tangent_cones, status speculative-ready). Step 4 of the selected node's supplied proof invokes that node, and its part (1) also supplies the density function used in step 5. That node is not comparator-accepted and is owned by another parent, so the runtime forbids reusing its name here, and ancestor dependencies are not inherited by the selected node. The numbered proof below is that node's parent-supplied natural proof, accepted in the decomposition audit of root. It is reproduced unchanged except that its two references to 'the sibling minimizing_implies_stationary' (steps 3 and 6) are re-targeted to the registered sibling stationarity (Submission.idtp_cttp_ctc_minimizing_stationary, same frozen type MinimizingImpliesStationary). That sibling is its only DAG prerequisite, mirroring the original's single dependency on root.minimizing_implies_stationary-a1; all other citations are to Simon's book, as in the original. Every child of root.density_and_tangent_cones-a1 except dtc_blowUp_compactness (Lemma BC of step 4) is comparator-accepted, and each can be reused at its identical frozen type in this node's own split; dtc_blowUp_compactness, whose subtree is still being decomposed, should be reused once it is comparator-accepted rather than re-proved as a depth-6 leaf. Once density_and_tangent_cones itself is comparator-accepted it can likewise be reused at its identical type.

Source: Simon 7.3.1 and its proof (chapter-07.txt lines 302–364, footnote 2), Remark 2.5(2) (lines 166–174, proof "left to the reader", supplied in step 4), README erratum 3 ((1) on U ∖ spt ∂T, (2) for x ∈ spt T ∖ spt ∂T). For integer multiplicity S, every representation has measure μ_S (Ch. 6, 3.2(3)) and M_W(S) = μ_S(W) for open W.
1. Case n = 0: T is minimizing in U ∩ N with spt T ⊆ N, so deleting any point of a representation would give a competitor of smaller mass; hence T = 0, Θ :≡ 0 works and (2) is vacuous. Assume n ≥ 1.
2. Localization. U' := U ∖ spt ∂T is open and T' := T restricted to U' satisfies ∂T' = 0, spt T' ⊆ N, (N̄∖N) ∩ U' = ∅, and T' is minimizing in U' ∩ N: a competitor S' for T' in W ⊂⊂ U' differs from T' by a compactly supported current, so S := T + (S' − T') (extension by zero) is an integer multiplicity competitor for T with the same boundary and the same masses difference on W.
3. Part (1) (book lines 326–328). By the sibling stationarity (Submission.idtp_cttp_ctc_minimizing_stationary, frozen type MinimizingImpliesStationary) applied to T' in U', V = v(M, θ) is stationary in N ∩ U', hence (Ch. 4, 2.7) has generalized mean curvature H with |H| ≤ Λ_K := √n·sup_{N∩K}|B_N| on each compact K ⊂ U'. By the monotonicity formula with bounded mean curvature (Ch. 4, 3.17; the book cites 4.7–4.9), for ξ ∈ U' and B_{R}(ξ) ⊂ K: F(ρ)ρ^{−n}μ_T(B_ρ(ξ)) is nondecreasing on (0, R) with F(ρ) ∈ [e^{−Λρ}, e^{Λρ}]. Hence Θ(ξ) := lim_{ρ↓0} μ_T(B_ρ(ξ))/(ω_nρ^n) exists in [0, ∞) for every ξ ∈ U', is upper semicontinuous on U' (Ch. 4, 3.11 argument), and Θ ≥ 1 on spt T ∩ U' (θ ≥ 1 a.e. and Ch. 4, 4.10(1)). Set Θ := 0 off U'. Since M_{B_ρ(ξ)}(T) = μ_T(B_ρ(ξ)) for B_ρ(ξ) ⊂ U, HasMassDensity T ξ (Θ ξ) holds on U' = U ∖ boundarySupport T.
4. Lemma BC (blow-up compactness; Remark 2.5(2) for N_j = η_{x_j,λ_j}(N), "left to the reader", proof supplied). Let x ∈ U', x_j → x, λ_j → 0⁺, S_j := η_{x_j,λ_j#}T. A subsequence satisfies S_j ⇀ C in ℝ^{n+k}, C integer multiplicity, ∂C = 0, C minimizing in ℝ^{n+k}, μ_{S_j} → μ_C. Proof: (i) step 3 gives μ_T(B_ρ(z)) ≤ cρ^n near x, so M_{B_R(0)}(S_j) ≤ cR^n and ∂S_j = 0 on B_{r/λ_j}(0) for large j; (ii) Ch. 6, 2.15 (diagonal in R) and 3.11 give a weak limit C (every test form is eventually supported in η_{x_j,λ_j}(U), where currentEval equals S_j) with ∂C = 0, integer multiplicity; (iii) if dist(x_j,N)/λ_j is unbounded, then along a subsequence it tends to ∞, every ball B_R(0) eventually misses η_{x_j,λ_j}(N) ⊇ spt S_j, so C = 0 and μ_{S_j} → 0; otherwise dist(x_j, N) ≤ C₀λ_j for all j and some C₀ < ∞, x ∈ N and, with π the nearest point projection onto N (C¹ near x, π = id on N, Lip(π|B_s(z)) ≤ 1 + cs), the retractions π_j := η_{x_j,λ_j}∘π∘η_{x_j,λ_j}^{−1} onto η_{x_j,λ_j}(N) have Lipschitz constants L_j → 1 on each ball; (iv) run the proof of 2.4: for compact K, a cut-off ψ and W_s := {ψ > s}, Ch. 6, 7.2 gives C − S_j = ∂R_j + S'_j with masses in W_0 → 0, slicing (Ch. 6, 4.5) at a good α gives C⌞W_α = S_j⌞W_α + ∂R̃_j + S̃_j with M(R̃_j) + M(S̃_j) → 0 and boundary error P_j on {ψ = α}, M(P_j) → 0; fix G > 0 with spt ψ ∪ π_j(spt ψ) ⊆ B_G(0) for all large j (|π_j(z) − z| = dist(z, η_{x_j,λ_j}(N)) ≤ |z| + C₀, C₀ as in (iii)); for an integer multiplicity cycle X with spt X ⊆ K put Y_j := X + ∂R̃_j and Z_j := S_j + π_{j#}Y_j (π_{j#} is applied only to the compactly supported Y_j; Ch. 6, 2.24(2), 3.9): ∂Z_j = ∂S_j (as ∂π_{j#}Y_j = π_{j#}∂Y_j = 0) and spt(Z_j − S_j) ⊆ π_j(spt Y_j) ⊆ η_{x_j,λ_j}(N) ∩ B_G(0), so Z_j is a competitor for S_j in η_{x_j,λ_j}(U ∩ N) (dilations preserve minimality); since π_j is C¹ and equals the identity on spt S_j, the push-forward formula (Ch. 6, 2.24(2), 3.3–3.9) gives π_{j#}(S_j⌞B_G(0)) = S_j⌞B_G(0), so Z_j⌞B_G(0) = π_{j#}((S_j + Y_j)⌞B_G(0)) and μ_{S_j}(B_G) ≤ μ_{Z_j}(B_G) ≤ L_j^nμ_{S_j+Y_j}(B_G); comparing off {ψ ≥ α} as in 2.4 (book (9)–(11)), M_{W_α}(S_j) ≤ M_{W_α}(C+X) + M(S̃_j) + M(P_j) + (L_j^n − 1)Λ_G with Λ_G := sup_j μ_{S_j+Y_j}(B_G(0)) ≤ cG^n + M(X) + sup_j M(∂R̃_j) < ∞ (∂R̃_j = (C − S_j)⌞W_α − S̃_j); (v) lower semicontinuity gives M_{W_α}(C) ≤ M_{W_α}(C+X), hence C is minimizing in ℝ^{n+k} (localize to an arbitrary W ⊂⊂ ℝ^{n+k} as in 2.4), and with X = 0, limsup μ_{S_j}(K) ≤ μ_C(K); with lower semicontinuity on open sets and the layer-cake formula, μ_{S_j} → μ_C (for every sub-subsequence, hence for the subsequence). [This replaces footnote 2: competitors are arbitrary in ℝ^{n+k}, so no projection onto T_xN is needed.]
5. Part (2) (book (1)–(4)). Let x ∈ spt T ∖ spt ∂T and apply Lemma BC with x_j = x: S_{j'} ⇀ C, C minimizing, μ_{S_{j'}} → μ_C. For each ρ > 0, (ω_nρ^n)^{−1}μ_{S_j}(B_ρ(0)) = (ω_n(λ_jρ)^n)^{−1}μ_T(B_{λ_jρ}(x)) → Θ(x) (book (1)). For all but countably many ρ, μ_C(∂B_ρ(0)) = 0, so μ_{S_{j'}}(B_ρ(0)) → μ_C(B_ρ(0)) (book (4)); by monotonicity in ρ and left-continuity, μ_C(B_ρ(0)) = ω_nρ^nΘ(x) for all ρ > 0. Hence HasMassDensity C 0 Θ(x) and HasMassDensity T x Θ(x).
6. Cone property (book lines 342–360). By the sibling stationarity (Submission.idtp_cttp_ctc_minimizing_stationary; ℓ = k, U = N = ℝ^{n+k}), V_C is stationary in ℝ^{n+k}. Since ρ^{−n}μ_C(B_ρ(0)) is constant, the monotonicity identity (Ch. 4, 3.6) gives D^⊥r = 0 μ_C-a.e., i.e. x ∈ T_xV_C, so x ∧ C⃗(x) = 0 μ_C-a.e.; Lemma 2.33 of Ch. 6 (homotopy formula, ∂C = 0, locally finite mass) gives η_{0,λ#}C = C for all λ > 0. As dilation 0 λ '' ℝ^{n+k} = ℝ^{n+k}, currentEval(blowUp C 0 λ, ω) = C(η_{0,λ}^#ω) = C(ω): IsConeCurrent C.
7. Output: the subsequence (strictly increasing), C, ConvergesWeakly and MassMeasuresConverge from step 5 and Lemma BC (all representations have the measures μ_{S_j}, μ_C), IsMinimizingIn C univ, IsConeCurrent C, and θ = Θ(x).

## Key steps

1. Localize to U∖spt ∂T; stationarity and bounded mean curvature give monotonicity, existence and upper semicontinuity of Θ.
2. Blow-up compactness with retractions onto η(N): limits are minimizing with mass convergence.
3. Constant density ratios of the limit give x ∈ T_xV_C a.e., so C is a cone with Θ(C,0) = Θ(T,x).

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fde813c052/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json}`
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git show 00832a8f:GMT/Ch07/Submission.lean | diff - GMT/Ch07/Contract.lean`
- `python3 dag.json scans: status/depends_on/children/candidate_commit of density_and_tangent_cones, minimizing_implies_stationary, dimred_minimizing_monotonicity and their children; lean_statement regex 'IsConeCurrent|ConvergesWeakly|MassMeasuresConverge|1 ≤ θ|IsTangentConeAt'; lean_name lookups for the 7 children; prefix 'idtp_cttp_ctc'`
- `python3 subtree dump (depth 3) of root.density_and_tangent_cones-a1.blowup_compactness-a1, root.minimizing_implies_stationary-a1, root.compactness_of_minimizing_currents-a1`
- `grep -n '_existing_lean_name_problem|_dependency_problem|_accepted_checkpoint|resolved_dependencies|def _solve_children|def _decompose|def _wait_for_accepted_dependencies' /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py; sed -n 1840,1990p; 6640,6728p; grep -n 'def ensure' store.py; DECOMPOSE/DECOMPOSITION_AUDIT/RLCR_LEAN_TASK in prompts.py`
- `cat /runtime/flows/gmt-claude-9a0895c8c5e1/scripts/gmt-campaign-ops/remove_dependency.py; cat operator-dependency-edits/*/receipt.json; ls decomposition-reopenings`
- `read nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/{decomposition-v2.json,decomposition-audit-v1.json,decomposition-audit-v2.json} (flat_off_null_set precedent)`
- `read parent-child-handoff.json of root.density_and_tangent_cones-a1, root.minimizing_implies_stationary-a1, root.dimension_reduction_results-a1.monotonicity-a1 (+ its decomposition-v2.json keys), im_mass_measure-a1, ae_density_lower_bound-a1, support_density_lower_bound-a1, unweighted_density_one-a1, closed_to_open_ball_density-a1`
- `git show {02c6122c94d0,f498a8efc56f,01ae2c59e8d7,b59dbf93abba,61b1b7b2cd0e}:GMT/Ch07/Submission.lean; diff each against Contract.lean (single hunk after line 453; no duplicate declaration names)`
- `grep -rl 'idtp_cttp_ctc_density_tangent_cones|idtp_cttp_ctc_minimizing_stationary' nodes dag.json GMT; grep -rl --include=*.lean 'idtp_cttp_ctc_' .swarm-worktrees/*/gmt-ch07/GMT (1194 worktrees)`
- `sed -n 300,312p book/chapter-07.txt; sed -n 26,34p book/chapter-07.txt; sed -n 348,366p book/chapter-04.txt`
- `lake env lean /tmp/ctc_dec2/check2/{Assembly,Context}.lean and /tmp/ctc_dec2/check/{Stmts,TypeEq}.lean, one at a time (container cgroup limit 3.67 GB), with #print axioms`
- `python3 read of nodes/root-dimension-reduction-results-a1-monotonicity-a1/decomposition-v2.json rationale item 3 (assembly of (iv)); independent reviewer subagent: /tmp/ctc_dec2/review/Indep.lean, validate.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fde813c052/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fde813c052/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-fde813c052/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1-ae-density-lower-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1-support-density-l-69839965cf/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/operator-dependency-edits/20261013T091722Z-revert/receipt.json`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/scripts/gmt-campaign-ops/remove_dependency.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/ctc_dec2/check2/Assembly.lean`
- `/tmp/ctc_dec2/check2/Assembly.out`
- `/tmp/ctc_dec2/check2/Context.lean`
- `/tmp/ctc_dec2/check2/Context.out`
- `/tmp/ctc_dec2/check/Stmts.lean`
- `/tmp/ctc_dec2/check/Stmts.out`
- `/tmp/ctc_dec2/check/TypeEq.lean`
- `/tmp/ctc_dec2/check/TypeEq.out`
- `/tmp/ctc_dec2/review/Indep.lean`

Pins match the manifest: workspace HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and to the Submission.lean of this node's proof base 00832a8f (the bare contract).

Prerequisite gap (the attempt-1 audit finding):
- This node has depends_on [] and its handoff has resolved_dependencies [].
- density_and_tangent_cones is speculative-ready. Its children are all accepted except dtc_blowUp_compactness, whose subtree is still decomposing. It depends on minimizing_implies_stationary, also speculative-ready.
- dimred_minimizing_monotonicity is rlcr-lean. All its children are accepted, and its proof invokes minimizing_implies_stationary without registering it.
- runtime.py _existing_lean_name_problem rejects reuse of an unaccepted node under another parent.
- remove_dependency.py forbids adding edges to handed-off children, and the edge added to monotonicity-a1 on 2026-10-13 was reverted.
- The flat_off_null_set decomposition-audit-v2 accepted fresh-name registered obligations with byte-identical types and verbatim reviewed proofs.

Reused declarations, all status accepted with byte-identical types in dag.json:
- rsd_cmr_support_subset_of_vanish (02c6122c)
- idtp_tpf_blowUp_limit_boundaryVanishes (f498a8ef)
- dimred_im_mass_measure (01ae2c59)
- dimred_mono_ae_ball_density_ge_one (b59dbf93, whose history includes rsd_tendsto_closedBall_density_of_approxTangent and rsd_tendsto_ball_density_of_closedBall)
- dimred_mono_support_density_ge_one_of_usc (61b1b7b2)

Each candidate inserts a single hunk after contract line 453, and no declaration name is duplicated across the hunks. The handoff titles, statements and types equal the dag.json records.

New names: idtp_cttp_ctc_density_tangent_cones and idtp_cttp_ctc_minimizing_stationary occur nowhere in dag.json, nodes/, the workspace GMT/ or 1194 swarm worktrees.

Book: Theorem 3.1 is chapter-07.txt lines 302–309, Lemma 1.2 is lines 29–34, and Ch. 4, 3.11–3.13 (Θ ≥ α on spt V from a.e. bounds and upper semicontinuity) is chapter-04.txt lines 348–364.

Mathlib: AlternatingMap.map_linearDependent is in Mathlib/LinearAlgebra/Alternating/Basic.lean.

Lean, run sequentially because the container's cgroup limit is 3.67 GB:
- Assembly.lean (all seven children as axioms) proves the exact frozen parent type, exit 0. Its axioms are propext, Classical.choice and Quot.sound plus the six children it uses directly; stationarity enters only through tangent_cones.
- Context.lean (the five accepted hunks verbatim plus the two new obligations as axioms) compiles, exit 0. Each reused declaration has only propext, Classical.choice and Quot.sound. The parent has those three plus Submission.idtp_cttp_ctc_density_tangent_cones, and no other stub.
- Both of these are the final check2 versions, which compile without warnings.
- Stmts.lean (all seven types and the parent type) compiles, exit 0.
- TypeEq.lean (each accepted declaration closes its proposed type) compiles, exit 0.
- An independent reviewer subagent re-ran an assembly built from the proposal's own type strings (Indep.lean, exit 0, same axiom list) and returned ACCEPT.

Precedent for the step-5 replacement: MON's accepted decomposition-v2 (item 3) assembles (iv) from support_density_lower_bound, im_mass_measure, ae_density_lower_bound and (iii).
