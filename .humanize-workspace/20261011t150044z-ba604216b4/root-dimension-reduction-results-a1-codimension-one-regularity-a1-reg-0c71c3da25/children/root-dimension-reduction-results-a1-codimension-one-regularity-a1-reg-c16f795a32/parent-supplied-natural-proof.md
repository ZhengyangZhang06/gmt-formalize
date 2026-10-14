# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.volume_density_lower-a1.discrete_growth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 4. This is the rigorous discrete replacement of the printed 'Integration (using the fact that L^{n+1}(E ∩ B_ρ(0)) is non-decreasing) then implies (10)' (Simon Ch. 3, 4.3, chapter-03.txt l. 690-733), together with the monotonicity remark of parent step 2. Notation: q := m/(m+1) ∈ [0, 1) and s := 1/(m+1) ∈ (0, 1]. For x ≥ 0 the real powers satisfy x^s ≥ 0, (x^s)^{m+1} = x and (x^s)^m = x^q (natural powers on the left, since s(m+1) = 1 and sm = q).
1. V is strictly increasing on (0, ρ₁). Let 0 < r < r′ < ρ₁ and apply (ii) with ρ := r, δ := r′ − r > 0 (so ρ + δ = r′ < ρ₁): V(r)^q ≤ (K/δ)(V(r′) − V(r)). By (i), V(r)^q > 0, and K/δ > 0, so V(r′) > V(r).
2. For 0 < r < ρ₁ let W(r) := V(r)^s. Then W(r) > 0, W(r)^{m+1} = V(r) and W(r)^m = V(r)^q. Also W(r) < W(r′) whenever 0 < r < r′ < ρ₁, by step 1 and because x ↦ x^s is strictly increasing on [0, ∞).
3. One step. Let r > 0, δ > 0 with r + δ < ρ₁. Put b := W(r) and a := W(r+δ), so 0 < b < a, and put c_δ := δ/(K(m+1)) > 0. Since a^{m+1} − b^{m+1} = (a − b)·Σ_{k=0}^{m} a^k b^{m−k} and each a^k b^{m−k} ≤ a^m, we get V(r+δ) − V(r) = a^{m+1} − b^{m+1} ≤ (m+1)a^m(a − b). Combined with (ii): b^m = V(r)^q ≤ (K/δ)(a^{m+1} − b^{m+1}) ≤ (K/δ)(m+1)a^m(a − b). That is,
 (3.1) c_δ·b^m ≤ a^m(a − b), equivalently W(r+δ) − W(r) ≥ c_δ·(W(r)/W(r+δ))^m.
4. Fix 0 < ρ < ρ₁ and N ∈ ℕ with N ≥ 1. Put δ := ρ/(2N) and ρ_j := ρ/2 + jδ for 0 ≤ j ≤ N. Then ρ_0 = ρ/2 > 0, ρ_N = ρ, and ρ_j + δ = ρ_{j+1} ≤ ρ < ρ₁, so (3.1) holds with r := ρ_j for every j < N. Put x_j := (W(ρ_j)/W(ρ_{j+1}))^m ∈ (0, 1]. Telescoping,
 W(ρ) − W(ρ/2) = Σ_{j<N} (W(ρ_{j+1}) − W(ρ_j)) ≥ c_δ Σ_{j<N} x_j.
 By weighted AM-GM with weights 1/N (Real.geom_mean_le_arith_mean_weighted), (Π_j x_j)^{1/N} = Π_j x_j^{1/N} ≤ (1/N)Σ_j x_j. The product telescopes: Π_{j<N} W(ρ_j)/W(ρ_{j+1}) = W(ρ/2)/W(ρ) =: θ ∈ (0, 1], so Π_j x_j = θ^m. Since N·c_δ = ρ/(2K(m+1)),
 (4.1) W(ρ) − W(ρ/2) ≥ (ρ/(2K(m+1)))·θ^{m/N} for every N ≥ 1.
5. Since θ > 0, t ↦ θ^t is continuous at 0, so θ^{m/N} → 1 as N → ∞. Letting N → ∞ in (4.1) gives W(ρ) − W(ρ/2) ≥ ρ/(2K(m+1)).
6. Since W(ρ/2) > 0, W(ρ) ≥ ρ/(2K(m+1)) ≥ 0. As t ↦ t^{m+1} is nondecreasing on [0, ∞), V(ρ) = W(ρ)^{m+1} ≥ (ρ/(2K(m+1)))^{m+1}. ∎
Alternative to steps 4-5 (finite; either route proves the statement).
4′(a) For 0 < b ≤ a: a^m(a − m(a − b)) ≤ a·b^m. First, a^{n+1} − b^{n+1} ≤ (n+1)a^n(a − b) for all n, by induction: a^{n+2} − b^{n+2} = a(a^{n+1} − b^{n+1}) + b^{n+1}(a − b) ≤ (n+1)a^{n+1}(a − b) + a^{n+1}(a − b). For m = 0 the claim reads a ≤ a. For m = n + 1, multiplying the case n by a gives a^{m+1} − a·b^m ≤ m·a^m(a − b), which is the claim.
4′(b) In the situation of step 3, for every w with 0 < w ≤ b: a − b ≥ c_δ·w/(w + m·c_δ). Proof: by 4′(a) and (3.1), c_δ·a^m(a − m(a − b)) ≤ c_δ·a·b^m ≤ a·a^m(a − b). Dividing by a^m > 0 gives c_δ(a − m(a − b)) ≤ a(a − b). If c_δ ≤ a − b, then c_δ·w ≤ (a − b)w ≤ (a − b)(w + m·c_δ). Otherwise c_δ − (a − b) > 0, and since w ≤ a, w(c_δ − (a − b)) ≤ a(c_δ − (a − b)) = a·c_δ − a(a − b) ≤ m·c_δ(a − b). In both cases c_δ·w ≤ (a − b)(w + m·c_δ).
4′(c) Fix 0 < ρ < ρ₁ and let A := ρ/(2K(m+1)) > 0 and w₀ := W(ρ/2) > 0. Choose N ∈ ℕ with N > mA²/w₀² (so N ≥ 1). Put δ := ρ/(2N), ρ_j := ρ/2 + jδ, c := c_δ = A/N and e := c·w₀/(w₀ + m·c) ≥ 0. By induction on j ≤ N, W(ρ_j) ≥ w₀ + j·e: for j < N we have ρ_j > 0, ρ_j + δ ≤ ρ < ρ₁ and W(ρ_j) ≥ w₀ + j·e ≥ w₀, so 4′(b) with w := w₀ gives W(ρ_{j+1}) ≥ W(ρ_j) + e. At j = N, W(ρ) ≥ w₀ + N·e = w₀ + A·w₀/(w₀ + m·c). Clearing the positive denominator, A ≤ w₀ + A·w₀/(w₀ + m·c) is equivalent to A·m·c ≤ w₀² + m·c·w₀. This holds because A·m·c = mA²/N < w₀². Hence W(ρ) ≥ A, and step 6 concludes.
Validation note (not part of the proof): a Lean proof of exactly this frozen statement, following 4′, compiled against the frozen import closure with axioms propext, Classical.choice, Quot.sound (scratch file /tmp/vdl-split-check/A/Proof.lean, outside the repository).

## Key steps

1. V is strictly increasing on (0, ρ₁): the hypothesis with δ = r′ − r and V(r)^{m/(m+1)} > 0.
2. W := V^{1/(m+1)} is positive, with W^{m+1} = V and W^m = V^{m/(m+1)}.
3. One step: (δ/(K(m+1)))·W(r)^m ≤ W(r+δ)^m·(W(r+δ) − W(r)), from a^{m+1} − b^{m+1} ≤ (m+1)a^m(a − b).
4. Partition [ρ/2, ρ] into N steps. Telescoping plus AM-GM (or the finite Bernoulli variant 4′) gives W(ρ) − W(ρ/2) ≥ (ρ/(2K(m+1)))·θ^{m/N}.
5. Let N → ∞ with θ > 0: W(ρ) ≥ ρ/(2K(m+1)), hence V(ρ) ≥ (ρ/(2K(m+1)))^{m+1}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); git status / git log in the workspace (clean, HEAD b4d606db = snapshot project commit)`
- `python3 scans of dag.json: frozen types of de_giorgi-a1 children (cutoff_estimates-a1, sobolev_perimeter-a1, selected volume_density_lower-a1); regex scan for trace/fderiv/cutoff/bump/rpow statements; collision check of the 7 proposed codim1_rdo_dg_vdl_* names and 5 scratch helper names (0 hits among 974 nodes)`
- `git show bc0bc2b9 -- GMT/Ch07/Submission.lean (accepted Submission.dorag_th_radial_cutoff technique and type)`
- `rg in snapshot mathlib: integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable, integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable, tendsto_integral_filter_of_dominated_convergence, integral_add_compl, trace_eq_sum_inner, geom_mean_le_arith_mean_weighted, norm_fderiv_le_of_lipschitz, HasCompactSupport.fderiv, hasDerivAt_iff_tendsto_slope_zero, contDiff_one_iff_deriv, Continuous.integral_hasStrictDerivAt`
- `lake env lean -DautoImplicit=false /tmp/vdl-split-check/Avail.lean (#check of the above inside the frozen import closure of GMT.Ch07.Submission)`
- `sed -n 640,760p book/chapter-03.txt (Simon Ch. 3, 4.3, (10)-(11))`
- `sed of runtime.py (_decompose, _solve_children, _existing_lean_name_problem), prompts.py (DECOMPOSITION_AUDIT, RLCR_LEAN_TASK), verifier/gmt-compare.py header; cat swarm-project.json (max_depth 6, max_children 12)`
- `lake env lean -DautoImplicit=false on /tmp/vdl-split-check/Assembly.lean, /tmp/vdl-split-check/EndToEnd.lean and /tmp/vdl-split-check/{A,B,C,D,E,F,G}/Proof.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-0c71c3da25/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/vdl-split-check/Assembly.lean`
- `/tmp/vdl-split-check/EndToEnd.lean`
- `/tmp/vdl-split-check/A/Proof.lean`
- `/tmp/vdl-split-check/B/Proof.lean`
- `/tmp/vdl-split-check/C/Proof.lean`
- `/tmp/vdl-split-check/D/Proof.lean`
- `/tmp/vdl-split-check/E/Proof.lean`
- `/tmp/vdl-split-check/F/Proof.lean`
- `/tmp/vdl-split-check/G/Proof.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) matches the clean workspace HEAD. Library: Mathlib's integration-by-parts lemmas exist in the snapshot (IntegrationByParts.lean:179-226) but are NOT in the frozen import closure of GMT.Ch07.Submission (Lean reports Unknown identifier). divergence_integral_zero therefore uses integral_add_right_eq_self, tendsto_integral_filter_of_dominated_convergence (DominatedConvergence.lean:67) and LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25). All of the following are available: AM-GM (MeanInequalities.lean:129), integral_add_compl (Bochner/Set.lean:158), norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947), HasCompactSupport.fderiv (FDeriv/Const.lean:389), hasDerivAt_iff_tendsto_slope_zero (Deriv/Slope.lean:82), contDiff_one_iff_deriv (ContDiff/Deriv.lean:98), Continuous.integral_hasStrictDerivAt (FundThmCalculus.lean:656) and Real.smoothTransition. No local or accepted DAG declaration states any of the following: the thin-annulus C1 cut-off with O(1/delta) gradient, the discrete integration lemma, the finite-difference inequality, int div phi = 0, or the complement Gauss-Green identity. The accepted dorag_th_radial_cutoff (commit bc0bc2b9) has a fixed r/2-to-r ratio, and doragm_sab_cutoff_profile has no gradient bound, so no identical-type reuse is possible. DAG: the 7 proposed codim1_rdo_dg_vdl_* names and the 5 scratch helper names occur in none of the 974 nodes. Lean: all 7 child types elaborate in the contract scope. Assembly.lean proves the parent's exact frozen type from the 7 children plus stubs of the 2 resolved sibling dependencies. EndToEnd.lean compiles real proofs of all 7 children (#print axioms: propext, Classical.choice, Quot.sound for each) together with the assembly (parent axioms: propext, sorryAx, Classical.choice, Quot.sound, where sorryAx comes only from the two sibling stubs). Runtime: depth 5 < max_depth 6, so the children are leaves. The child comparator elaborates the frozen type in the contract scope and checks it with exact Submission.<lean_name>.
