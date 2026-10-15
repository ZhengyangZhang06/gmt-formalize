# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 2.15, 3.11, 4.6, 4.10, truncating at good slicing radii instead of gluing over balls.
Siblings: mass_and_support, first conjunct (MR); foundations (IMC)(b),(d); slicing (SL); closure_and_boundary_rectifiability (CL).
Notation: n := m + 1, B_r := ball(0, r), IM := integer multiplicity, |ω|_∞ := sup_x |ω(x)| (Euclidean coefficient norm). (E1) For a current X in open V, open W ⊆ V and a test form ω in V with tsupport ω ⊆ W, |X(ω)| ≤ |ω|_∞·M_W(X) (ω = 0 if |ω|_∞ = 0; else ±ω/|ω|_∞ are admissible).

1. (Radii) For integers R ≥ 1 choose J(R) ∈ ℕ, c_R ∈ [0, ∞) with closedBall(0, R) ⊆ U_j and M_{B_R}(S_j) ≤ c_R for j ≥ J(R) ((i), (ii)); replacing J(R) by max_{R′≤R} J(R′), J is nondecreasing. Let j₀ := J(8) and, for j ≥ j₀, R_j := max{R ∈ ℕ : 8 ≤ R ≤ max(8, j), J(R) ≤ j}. Then R_j ≥ 8, J(R_j) ≤ j, so closedBall(0, R_j) ⊆ U_j; R_j → ∞ (R_j ≥ R if R ≥ 8, j ≥ max(R, J(R))). Only j ≥ j₀ are used.
2. (Good slicing radius) Fix j ≥ j₀, an IMRep (M_j, θ_j, ξ_j) of S_j and its measure μ_j = θ_jHⁿ⌞M_j, finite on compact subsets of U_j (locallyIntegrable_mult). (μ_j, ξ_j) represents S_j as in (SL): ξ_j is a.e. strongly measurable for μ_j (as for Hⁿ⌞M_j), |ξ_j(x)(α)| ≤ |α| μ_j-a.e. ((IMC)(d)), S_j(ω) = ∫ ξ_j(ω) dμ_j; as S_j.boundary = 0, (μ′, ξ′) := (0, 0) represents the boundary. (SL) in U_j with f := |·| (1-Lipschitz) gives A_t ∈ 𝒟_n(U_j), A_t(ω) = ∫_{B_t} ξ_j(ω) dμ_j = ∫_{M_j∩B_t} θ_jξ_j(ω) dHⁿ; its currents in 𝒟_m(U_j) vanish (μ′ = 0), so the slices are ∂A_t and, for W := B_{3R_j/4}, (a, b) := (R_j/4, R_j/2), ∫⁻_{(a,b)} M_W(∂A_t) dt ≤ μ_j(W ∩ {a < |y| < b}) ≤ μ_j(closedBall(0, R_j/2)) < ∞ (compact in U_j). The integrand is finite somewhere in the interval: otherwise it is ≡ ∞ there and lintegral_mono (no measurability needed) gives ∫⁻ ≥ ∞·(R_j/4) = ∞. Choose ρ′_j ∈ (R_j/4, R_j/2) with σ_j := M_{B_{3R_j/4}}(∂A_{ρ′_j}) < ∞.
3. (Truncation) R̂_j := (M_j ∩ B_{ρ′_j}, θ_j, ξ_j) is an IMRep in ℝ^P: by (IMC)(b) (in U_j, E := B_{ρ′_j}) it is one in U_j; its carrier lies in ℝ^P, ∫_{carrier∩K} θ_j dHⁿ ≤ μ_j(closedBall(0, ρ′_j)) < ∞ for compact K, other fields unchanged. By (IMC)(b) in ℝ^P (E := ℝ^P) it represents some IM Ŝ_j ∈ 𝒟_n(ℝ^P): Ŝ_j(ω) = ∫_{M_j∩B_{ρ′_j}} θ_jξ_j(ω) dHⁿ.
 (a) If ω ∈ 𝒟ⁿ(ℝ^P), tsupport ω ⊆ B_{ρ′_j}, then ω is a test form in U_j (B_{ρ′_j} ⊆ U_j), ω = 0 off B_{ρ′_j}, and Ŝ_j(ω) = ∫_{M_j} θ_jξ_j(ω) dHⁿ = S_j(ω) = currentEval(S_j, ω).
 (b) Take χ ∈ C_c^∞(B_{3R_j/4}; [0, 1]), χ = 1 near closedBall(0, ρ′_j). For β ∈ 𝒟^m(ℝ^P), χβ is a test form in U_j with tsupport in B_{3R_j/4}, and d(χβ) = dβ near closedBall(0, ρ′_j) (χβ = β there; d is local: forms agreeing on an open set have equal d there). So ∂Ŝ_j(β) = Ŝ_j(dβ) = ∫_{M_j∩B_{ρ′_j}} θ_jξ_j(d(χβ)) dHⁿ = A_{ρ′_j}(d(χβ)) = ∂A_{ρ′_j}(χβ), and (E1) gives |∂Ŝ_j(β)| ≤ σ_j|χβ|_∞ ≤ σ_j|β|_∞. Hence M_O(∂Ŝ_j) ≤ σ_j for every open O.
 (c) If tsupport β ⊆ B_{ρ′_j}, then tsupport dβ ⊆ tsupport β (tsupport_exteriorDerivative_subset), so by (a) ∂Ŝ_j(β) = Ŝ_j(dβ) = S_j(dβ) = S_j.boundary(β) = 0. So M_O(∂Ŝ_j) = 0 for open O ⊆ B_{ρ′_j} (admissible forms are supported in B_{ρ′_j}).
 (d) For open O: M_O(Ŝ_j) = R̂_j.measure(O) = μ_j(O ∩ B_{ρ′_j}) ≤ μ_j(O) = M_O(S_j) ((MR) in ℝ^P and U_j).
4. (Uniform bounds) Let O be bounded open, O ⊆ B_R, R ≥ 1 an integer, j₂ ≥ max(j₀, J(R)) with ρ′_j > R for j ≥ j₂ (ρ′_j > R_j/4 → ∞). For j ≥ j₂: M_O(Ŝ_j) ≤ M_O(S_j) ≤ M_{B_R}(S_j) ≤ c_R (3(d), massOn monotone), M_O(∂Ŝ_j) = 0 (3(c)). For j₀ ≤ j < j₂: M_O(Ŝ_j) ≤ μ_j(closedBall(0, ρ′_j)) < ∞, M_O(∂Ŝ_j) ≤ σ_j < ∞. So sup_{j≥j₀}(M_O(Ŝ_j) + M_O(∂Ŝ_j)) < ∞; in particular c′_R := sup_{j≥j₀} M_{B_R}(Ŝ_j) < ∞.
5. (Weak compactness) Claim: there are strictly increasing φ, φ(i) ≥ j₀, and C ∈ 𝒟_n(ℝ^P) with Ŝ_{φ(i)}(ω) → C(ω) for all ω ∈ 𝒟ⁿ(ℝ^P).
 (a) If tsupport ω ⊆ B_R, |Ŝ_j(ω)| ≤ c′_R|ω|_∞ for j ≥ j₀ (E1).
 (b) For R ∈ ℕ let 𝒯_R := {test forms ω on ℝ^P : tsupport ω ⊆ B_R}, d(ω, ω′) := |ω − ω′|_∞. Restriction to closedBall(0, R) embeds 𝒯_R into C(closedBall(0, R), Λⁿ) (Λⁿ: n-covectors, Mathlib's norm), whose sup metric is equivalent to d (covectorEuclideanNorm and Mathlib's operator norm are norms on the finite-dimensional Λⁿ). C(closedBall(0, R), Λⁿ) is second countable (ContinuousMap.instSecondCountableTopology; on a compact domain the compact-open topology is the sup-metric one, ContinuousMap.instPseudoMetricSpace), hence separable, and so is its subset 𝒯_R: it has a countable d-dense D_R.
 (c) D := ⋃_R D_R is countable and each (Ŝ_j(ω))_{j≥j₀}, ω ∈ D, is bounded by (a); a Cantor diagonal argument gives strictly increasing φ, φ(i) ≥ j₀, with lim_i Ŝ_{φ(i)}(ω) existing for all ω ∈ D.
 (d) Each ω ∈ 𝒟ⁿ(ℝ^P) has compact support, so ω ∈ 𝒯_R for some R. Given ε > 0 pick ω′ ∈ D_R with |ω − ω′|_∞ < ε; (a) for ω − ω′ gives |Ŝ_{φ(i)}(ω) − Ŝ_{φ(i′)}(ω)| ≤ 2c′_Rε + |Ŝ_{φ(i)}(ω′) − Ŝ_{φ(i′)}(ω′)|, so (Ŝ_{φ(i)}(ω))_i is Cauchy; C(ω) := its limit.
 (e) C is linear, |C(ω)| ≤ c′_R|ω|_∞ on 𝒯_R. If ω_q → 0 in 𝒟ⁿ(ℝ^P) (TestFormOnConverges: supports in a fixed compact set ⊆ some B_R, uniform convergence; norms on Λⁿ are equivalent, so |ω_q|_∞ → 0), then C(ω_q) → 0. So C is a GeometricCurrentOn univ n and Ŝ_{φ(i)} ⇀ C (WeaklyConvergesOn).
6. (C is IM) T_i := Ŝ_{φ(i)} is IM; for open W with compact closure (CompactlyContained W univ; W bounded), sup_i(M_W(T_i) + boundaryMassOn T_i W) = sup_i(M_W(T_i) + M_W(∂T_i)) < ∞ by step 4 (n = m + 1); T_i ⇀ C in U := ℝ^P. By (CL), C is IM.
7. (Output) Ŝ_i := Ŝ_{φ(i)}, ρ_i := ρ′_{φ(i)}. φ is strictly increasing; C and the Ŝ_i are IM; sup_i(M_W(Ŝ_i) + M_W(∂Ŝ_i)) < ∞ for bounded open W (step 4, fewer indices); Ŝ_i ⇀ C (step 5); ρ_i → ∞ (ρ′_j > R_j/4 → ∞); closedBall(0, ρ_i) ⊆ closedBall(0, R_{φ(i)}) ⊆ U_{φ(i)} (ρ_i < R_{φ(i)}/2); agreement is 3(a). C.boundary = 0: β ∈ 𝒟^m(ℝ^P) has tsupport β ⊆ B_r for some r, and ρ_i > r for large i, so ∂Ŝ_i(β) = 0 (3(c)) and C.boundary(β) = C(dβ) = lim_i Ŝ_i(dβ) = lim_i ∂Ŝ_i(β) = 0. S_{φ(i)} ⇀ C (ConvergesWeakly): if tsupport ω ⊆ B_r, then for large i, ρ_i > r and currentEval(S_{φ(i)}, ω) = Ŝ_i(ω) (3(a)) → C(ω). ∎

## Key steps

1. 1. Radii R_j → ∞, closedBall(0, R_j) ⊆ U_j, eventual mass bounds c_R.
2. 2. (SL) with f = |·|, μ′ = 0 and the lower integral give ρ′_j ∈ (R_j/4, R_j/2) with σ_j < ∞.
3. 3–4. Truncation Ŝ_j: IM in ℝ^P, = S_j on B_{ρ′_j}, ∂-mass ≤ σ_j (locality of d), 0 inside; uniform bounds.
4. 5. Separability of C(closedBall, Λⁿ) and a diagonal argument: Ŝ_{φ(i)} ⇀ C.
5. 6–7. (CL): C is IM; agreement on growing balls: ∂C = 0, S_{φ(i)} ⇀ C.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node, prerequisite types, accepted reusable declarations and their lean_statement, status of the children of root.compactness_of_minimizing_currents-a1, lean_name collisions (dimred_mbl_: no match)`
- `grep -n _existing_lean_name_problem _accepted_checkpoint contract in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and speculation.py`
- `grep -rn of every cited Mathlib/SimonGMT lemma name in the pinned lake packages`
- `lean (v4.35.0-rc3) on AllTypes.lean, AssemblyCond.lean (#print axioms) and 12 Challenge_<key>.lean modules; lean_contract.validate_lean_statement on all child types`
- `sed -n on book/chapter-06.txt (2.15, 2.23–2.33, 3.3–3.10, 4.6–4.11) and book/chapter-07.txt (7.2.4–7.2.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/mb2/lean/src/AssemblyCond.lean`

Pins match (HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308) and Submission.lean is byte-identical to the frozen contract. The pinned libraries lack Federer–Fleming compactness, the deformation theorem, flat convergence, Lipschitz slicing and integral push-forward by nonlinear maps; SimonGMT supplies currents, mass, support, weak convergence, affine push-forward, the Lipschitz area formula and approximate tangent spaces, and every cited library name exists. Accepted declarations with exact types: dtc_vanish_off_support and dor_imrep_massOn_eq_measure_and_support (reused). The children of root.compactness_of_minimizing_currents-a1 are decomposing, not accepted, so they cannot be shared; identical types with unique dimred_mbl_* names are used. A child's prerequisites are its children plus depends_on, so monotonicity enters as a hypothesis. All 12 child types elaborate and the conditional assembly proves the parent type (axioms propext, Classical.choice, Quot.sound).
