# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.null_set-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 7–10 of the supplied proof (Simon Ch. 6, 8.2 (4)–(6): disjoint balls, comparison currents X_i = S_i − C⌞B_i, the cone inequality and lower semicontinuity of M_W), carried out for each admissible test form separately: for a W-admissible ω, C(ω) is bounded by μ(W ∖ ⋃B_i) + ΣM(S_i) + Σ|X_i(ω)|, which is exactly the estimate behind M_W(C_δ) ≤ μ(W ∖ ⋃B_i) + κΣμ(B_i) and C_δ ⇀ C in Steps 8–9; taking the supremum over ω replaces lower semicontinuity. Steps 1–2 of the supplied proof (Borel measurability of the density, inner regularity) are not needed because E is an arbitrary set. Siblings used: cone = cbrld_cycle_eval_le_radius_mul_mass and covering = cbrld_vitali_setIntegral_le. (λ denotes the Lean variable lam.)

Notation: n := d + 1; |·| is the Euclidean coefficient norm of covectors; a test form ω ∈ 𝒟^n(ℝ^P) is G-admissible if tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x, and M_G(T) = sup{max(T(ω), 0) : ω G-admissible} (GeometricCurrentOn.massOn); M := M_{ℝ^P}; masses and measures are read as real numbers when finite.

1. (Elementary facts.) For S, A ∈ 𝒟_n(ℝ^P):
(a) (S − A)(ω) = S(ω) − A(ω), and ∂(S − A) = ∂S − ∂A, since ∂(S − A)(η) = (S − A)(dη) = S(dη) − A(dη) (extensionality of currents).
(b) If M(T) < ∞ and ω is ℝ^P-admissible, then |T(ω)| ≤ M(T): T(ω) ≤ M(T) by the definition of M (GeometricCurrentOn.le_massOn), and −T(ω) = T(−ω) ≤ M(T) because −ω is admissible (|−β| = |β|).
(c) M(S − A) ≤ M(S) + M(A): for an ℝ^P-admissible ω, (S − A)(ω) = S(ω) + A(−ω) and max(S(ω) + A(−ω), 0) ≤ max(S(ω), 0) + max(A(−ω), 0) ≤ M(S) + M(A); take the supremum over ω.
(d) spt(S − A) ⊆ spt S ∪ spt A: if y ∉ spt S ∪ spt A, there are open sets W₁, W₂ ∋ y with compact closures such that S vanishes on every test form supported in W₁ and A on every test form supported in W₂; then W₁ ∩ W₂ is an open neighbourhood of y with compact closure on which S − A vanishes, so y lies in the zero region of S − A.
(e) If A(ω) = ∫_{B_ρ(x)} ξ(ω)dμ for all ω, then M(A) ≤ μ(B_ρ(x)) and spt A ⊆ B̄_ρ(x). For ℝ^P-admissible ω, |ξ(y)(ω(y))| ≤ |ω(y)| ≤ 1 for μ-a.e. y, so A(ω) ≤ μ(B_ρ(x)) (finite: B̄_ρ(x) is compact); take the supremum. If y ∉ B̄_ρ(x), put r := (|y − x| − ρ)/2 > 0; the ball W' := B_r(y) is open with compact closure and disjoint from B_ρ(x), so every test form ω with tsupport ω ⊆ W' vanishes on B_ρ(x) and A(ω) = ∫_{B_ρ(x)} ξ(y)(0) dμ = 0; hence y ∉ spt A.

2. (Reduction to bounded pieces.) E = ⋃_{k∈ℕ} E_k with E_k := E ∩ B_k(0), so by countable subadditivity (measure_iUnion_null) it suffices to show μ(E_k) = 0 for every k; each E_k satisfies the hypothesis of the statement because E_k ⊆ E. Fix k and put E' := E_k and W := B_{k+1}(0): W is open, E' ⊆ W, and μ(W) ≤ μ(B̄_{k+1}(0)) < ∞.

3. (Estimate for one admissible form.) Claim: every W-admissible ω satisfies C(ω) ≤ μ(W) − (1 − κ)·μ(E').
Let g(y) := ξ(y)(ω(y)). g is μ-a.e. strongly measurable (ContinuousLinearMap.aestronglyMeasurable_comp₂ applied to the identity map of Λ_{d+1}(ℝ^P) = (Λ^{d+1}(ℝ^P) →L ℝ), with ξ μ-a.e. strongly measurable and ω continuous) and |g(y)| ≤ |ω(y)| ≤ 1 for μ-a.e. y. Since ω = 0 outside W, g = 0 outside W, so C(ω) = ∫ g dμ = ∫_W g dμ. Let c ≥ 0 be the constant given by the sibling cone (with (VO)) for the test form ω of degree d + 1. Fix ε ∈ (0, 1 − κ] and put δ₀ := ε/((c + 1)·λ·(1 + κ)) > 0.
(i) For every x ∈ E' and δ' > 0 there is ρ ∈ (0, δ') with ∫_{B̄_ρ(x)} g dμ ≤ (κ + ε)·μ(B̄_ρ(x)). Indeed, apply the hypothesis at x with δ := min(δ', δ₀) > 0: it gives ρ ∈ (0, δ), μ(∂B_ρ(x)) = 0 and A, S as in the statement. Put X := S − A. By 1(a), ∂X = ∂S − ∂A = 0. By 1(c), 1(e) and the hypothesis, M(X) ≤ M(S) + M(A) ≤ κμ(B_ρ(x)) + μ(B_ρ(x)) = (1 + κ)μ(B_ρ(x)) < ∞. By 1(d), 1(e) and the hypothesis, spt X ⊆ B̄_{λδ}(x) ∪ B̄_ρ(x) = B̄_{λδ}(x), since ρ < δ ≤ λδ. The sibling cone with x₀ := x and ϱ := λδ > 0 gives |X(ω)| ≤ c·λδ·M(X) ≤ cλδ(1 + κ)μ(B_ρ(x)) ≤ ε·μ(B_ρ(x)), because cλδ(1 + κ) ≤ cλδ₀(1 + κ) = cε/(c + 1) ≤ ε. Since ω is also ℝ^P-admissible and M(S) ≤ κμ(B_ρ(x)) < ∞, 1(b) gives S(ω) ≤ κμ(B_ρ(x)). Hence ∫_{B_ρ(x)} g dμ = A(ω) = S(ω) − X(ω) ≤ (κ + ε)μ(B_ρ(x)). Finally B̄_ρ(x) ∖ B_ρ(x) = ∂B_ρ(x) is μ-null, so ∫_{B̄_ρ(x)} g dμ = ∫_{B_ρ(x)} g dμ and μ(B̄_ρ(x)) = μ(B_ρ(x)).
(ii) The sibling covering, applied with μ, g, θ := κ + ε ≤ 1, the set E' and the open set W ⊇ E' with μ(W) < ∞, using (i), gives ∫_W g dμ ≤ μ(W) − (1 − κ − ε)·μ(E').
(iii) Hence C(ω) ≤ μ(W) − (1 − κ − ε)·μ(E') for every ε ∈ (0, 1 − κ]; letting ε ↓ 0 proves the claim.

4. (Conclusion.) Put β := μ(W) − (1 − κ)·μ(E') ∈ ℝ. By step 3, max(C(ω), 0) ≤ max(β, 0) for every W-admissible ω, so by the hypothesis on μ and the definition of M_W as a supremum, μ(W) = M_W(C) ≤ max(β, 0) (ENNReal.ofReal β). If μ(E') > 0, then μ(W) ≥ μ(E') > 0 and β < μ(W) because 1 − κ > 0, so max(β, 0) < μ(W), a contradiction. Hence μ(E') = 0, i.e. μ(E_k) = 0 for every k, and μ(E) = 0 by step 2. ∎

## Key steps

1. Current calculus for X = S − A: ∂X = ∂S − ∂A = 0, M(X) ≤ M(S) + M(A) ≤ (1 + κ)μ(B_ρ(x)), spt X ⊆ spt S ∪ spt A ⊆ B̄_{λδ}(x).
2. Reduce to E ∩ B_k(0) and the open set W = B_{k+1}(0) of finite measure.
3. For a W-admissible ω, cone gives |X(ω)| ≤ εμ(B_ρ(x)) at scales δ ≤ δ₀(ω, ε), so ∫_{B̄_ρ(x)} ξ(ω)dμ = A(ω) = S(ω) − X(ω) ≤ (κ + ε)μ(B̄_ρ(x)).
4. covering gives C(ω) = ∫_W ξ(ω)dμ ≤ μ(W) − (1 − κ − ε)μ(E'); let ε ↓ 0.
5. Supremum over ω: μ(W) = M_W(C) ≤ μ(W) − (1 − κ)μ(E'), hence μ(E') = 0 and μ(E) = 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD; cmp snapshot project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `rg -c 'dmcbrld|cbrld_' over the snapshot (no match, exit 1); grep -rl dmcbrld_ over GMT/, .lake/packages/simongmt and RUN/nodes (no match)`
- `rg -n 'theorem exists_disjoint_closedBall_covering_ae|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem MonotoneOn.intervalIntegrable_deriv|theorem Monotone.ae_differentiableAt|theorem measurable_deriv|theorem countable_meas_pos_of_disjoint_iUnion|theorem hausdorffMeasure_zero_singleton|theorem ae_iff|theorem measure_iUnion_null' over snapshot mathlib/Mathlib (all found: Besicovitch.lean:833, DerivIntegrable.lean:86/100, Monotone.lean:209, FDeriv/Measurable.lean:398, SFinite.lean:305, Hausdorff.lean:628, OuterMeasure/AE.lean:134)`
- `python3 -I scans of RUN/dag.json: twin node root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1 has a byte-identical frozen type; statuses, candidate commits and frozen types of its 7 children and grandchildren; cbr_isoperimetric_filling and dmcbr_isoperimetric_filling types identical; (VO), (SL), (DT) types occur verbatim in the selected type; fresh-name collision check over 1598 nodes`
- `sed of RUN/nodes/…b16b774435/decomposition-v1.json and decomposition-audit-v1.json (twin split and its passing audit); difflib comparison of the two supplied natural proofs`
- `git show b82dc736 (twin parent assembly draft), 909d2bdf (local_filling draft), 6bf34ee2 (null_set draft); git log of the twin radius worktree (215074ec7 proves cbrld_exists_good_slice_radius)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py: _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _reference_use_problem`
- `sed of .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (massAdmissibleOn, massOn, mass, le_massOn, WeaklyConvergesOn.massOn_le_liminf) and Currents.lean (zeroRegion, support)`
- `lake env lean /tmp/dmcbrld_work/lean/Types.lean, Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound), WiringLF.lean, WiringNS.lean, Names.lean; verifier/lean_contract.py validate_lean_statement on the 7 child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-f72d9d736e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/tmp/dmcbrld_work/lean/Types.lean`
- `/tmp/dmcbrld_work/lean/Assembly.lean`
- `/tmp/dmcbrld_work/lean/WiringLF.lean`
- `/tmp/dmcbrld_work/lean/WiringNS.lean`

The pins match: HEAD b4d606d equals the snapshot project commit, Mathlib is 25730c7c, and Submission.lean is byte-identical to the frozen contract and its snapshot copy. The snapshot has no dmcbrld_ or cbrld_ declaration and no lower-density, covering or slicing theorem, so the split is needed. Every cited Mathlib lemma exists in the snapshot. MonotoneOn.intervalIntegral_deriv_mem_uIcc and intervalIntegrable_deriv live in a module that GMT.Ch07.Submission does not import; the radius proof says so and gives the lintegral alternative. The twin lower_density node has the same frozen type and a passing audit. Its four accepted children are reused by exact name with identical types; its three unaccepted children get fresh dmcbrld_ names, which collide with nothing. All 7 types elaborate. The assembly proves the exact parent type using only propext, Classical.choice and Quot.sound. The wiring drafts of local_filling and null_set typecheck against their declared siblings.
