# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, i.e. Simon Ch. 6, proof of 7.2 (chapter-06.txt lines 2092–2100: "by 4.5(1),(2) and an argument as in 6.7(2) of Ch. 2 we can find a subsequence {T_j'} … with sup_j' M(∂(T_j'⌞W_i)) < ∞ … thus we can assume … spt T_j ⊆ W̄"), with the slice estimate 4.9 obtained as in Simon's proof of 4.9 through the identity 4.11 (lines 1355–1400). The parent writes ∂(T_j⌞B_t) = (∂T_j)⌞B_t + ⟨T_j, f, t−⟩ and bounds the two terms separately; the first term needs the Radon measure representation 2.7 of ∂T_j. Here the computation 4.11 is applied directly to ∂(T_j⌞B_t). It gives the same kind of bound, M(∂(T_j⌞B_t)) ≤ M_V(∂T_j) + c·liminf_{h↓0} h⁻¹μ_{T_j}({t − h < |x| < t}), without restricting ∂T_j. This is the only difference from the parent's step 3.

Notation. B_r := ball(0, r); |x| is the Euclidean norm; Hⁿ := μHE[n]. For a covector α, |α| is the Euclidean coefficient norm (covectorEuclideanNorm). For a current X and a set G, M_G(X) = X.massOn G is the supremum of ofReal X(ω) over test forms ω with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x ("admissible" forms), and M := M_{ℝ^P}. Applying the definition to ω and −ω (|−α| = |α|) gives |X(ω)| ≤ M_G(X) for admissible ω.
Siblings used: (IC) cmc_imRep_locality_restrict_sub, parts (b) (the restriction of an IMRep to a Borel set represents an integer multiplicity current) and (d) (|⟨α, ξ(x)⟩| ≤ |α| for Hⁿ-a.e. x of the carrier); (MM) dtc_mass_eq_measure (M_G(T) = μ_R(G) for open G, R an IMRep of T, here U = ℝ^P); (SI) cmcs_slice_mass_integral (Simon 4.10); (SV) rsd_cmr_support_subset_of_vanish.

1. (Setup.) W is bounded, so W ⊆ B_{r₀} for some r₀ > 0. Put V := B_{r₀+2}, which is open and bounded, and Λ₀ := sup_j (M_V(T_j) + M_V(∂T_j)) < ∞. In particular M_V(T_j) ≤ Λ₀ and M_V(∂T_j) ≤ Λ₀ for every j.
2. (Weights.) For each j fix an IMRep ℛ_j = (M_j, θ_j, ξ_j) representing T_j and put μ_j := ℛ_j.measure = θ_jHⁿ⌞M_j. By (MM), μ_j(G) = M_G(T_j) for every open G; so μ_j(V) ≤ Λ₀ and μ_j is finite on compact sets. By (IC)(d), |⟨α, ξ_j(x)⟩| ≤ |α| for μ_j-a.e. x and every n-covector α.
3. (Dini derivatives.) For t ∈ ℝ and h > 0 put A_j(t, h) := μ_j({x : t − h < |x| < t}) and D_j(t) := liminf_{h↓0} ofReal(h⁻¹)·A_j(t, h) ∈ [0, ∞] (liminf along 𝓝[>]0).
 (a) For t ∈ (r₀, r₀ + 1) and 0 < h < 1 the set {t − h < |x| < t} lies in V, so A_j(t, h) ≤ Λ₀ < ∞, and A_j(t, h) = F_j(t) − G_j(t − h) with F_j(s) := μ_j(B_s ∩ V) and G_j(s) := μ_j(closedBall(0, s) ∩ V), both finite and nondecreasing in s. Monotone functions are Borel, so t ↦ A_j(t, h) is Borel on (r₀, r₀ + 1) for each fixed h.
 (b) For fixed t, h ↦ A_j(t, h) is nondecreasing. Hence, for δ > 0 and every real h ∈ (0, ε), a rational h' ∈ [h/(1 + δ), h] satisfies h'⁻¹A_j(t, h') ≤ (1 + δ)h⁻¹A_j(t, h). So the liminf over rational h ↓ 0 is at most (1 + δ)D_j(t) for every δ > 0, and it is at least D_j(t) trivially. Thus D_j(t) = sup_k inf{h⁻¹A_j(t, h) : h ∈ ℚ ∩ (0, 1/k)} is Borel on (r₀, r₀ + 1).
 (c) By (SI) with μ := μ_j, f := |·| (continuous, hence measurable), W := ℝ^P, L := 1, m := D_j and (a, b) := (r₀, r₀ + 1) (the pointwise hypothesis holds with equality): ∫⁻_{(r₀, r₀+1)} D_j dt ≤ μ_j({r₀ < |x| < r₀ + 1}) ≤ μ_j(V) ≤ Λ₀.
4. (Good radius.) By (b) and Fatou's lemma, ∫⁻_{(r₀, r₀+1)} liminf_j D_j dt ≤ liminf_j ∫⁻_{(r₀, r₀+1)} D_j dt ≤ Λ₀ < ∞. Hence liminf_j D_j(t) < ∞ for a.e. t ∈ (r₀, r₀ + 1). This interval has positive measure, so we may fix such a t₀ ∈ (r₀, r₀ + 1); put C := liminf_j D_j(t₀) + 1 < ∞. Since D_j(t₀) < C for infinitely many j, there is a strictly increasing φ : ℕ → ℕ with D_{φ(j)}(t₀) ≤ C for every j.
5. (Restriction.) Put B := B_{t₀}, a Borel set. For each j apply (IC)(b) to ℛ_{φ(j)} and E := B. This gives an integer multiplicity current T'_j ∈ 𝒟_n(ℝ^P) represented by ℛ'_j := (M_{φ(j)} ∩ B, θ_{φ(j)}, ξ_{φ(j)}), i.e. T'_j(ω) = ∫_{M_{φ(j)} ∩ B} θ_{φ(j)}⟨ω, ξ_{φ(j)}⟩ dHⁿ. Its weight is ℛ'_j.measure = μ_{φ(j)}⌞B (restriction commutes with withDensity).
6. (Agreement on W.) If tsupport ω ⊆ W ⊆ B_{r₀} ⊆ B, then ω = 0 on M_{φ(j)} ∖ B, so T'_j(ω) = ∫_{M_{φ(j)}} θ_{φ(j)}⟨ω, ξ_{φ(j)}⟩ dHⁿ = T_{φ(j)}(ω).
7. (Support.) K := closedBall(0, r₀ + 1) is compact (ℝ^P is proper) and contains B. If tsupport ω is disjoint from K, then ω = 0 on B, so T'_j(ω) = 0. By (SV) (U = ℝ^P open, K compact), spt T'_j ⊆ K.
8. (Mass.) By (MM) applied to T'_j and ℛ'_j with G := ℝ^P: M(T'_j) = μ_{φ(j)}(B) ≤ μ_{φ(j)}(V) ≤ Λ₀.
9. (Boundary mass: computation 4.11.) Fix j and write T := T_{φ(j)}, μ := μ_{φ(j)}, ξ := ξ_{φ(j)}. Let η ∈ 𝒟^m(ℝ^P) with |η(x)| ≤ 1 for all x. We bound ∂T'_j(η) = T'_j(dη).
 (a) Fix a C^∞ nondecreasing ψ : ℝ → [0, 1] with ψ = 0 on (−∞, 0] and ψ = 1 on [1, ∞) (e.g. Mathlib's Real.smoothTransition), and put c₁ := sup|ψ'| < ∞. For 0 < h < min(1, t₀/2) let γ_h(s) := 1 − ψ((s − t₀ + h)/h) and g_h(x) := γ_h(|x|). Then γ_h = 1 on (−∞, t₀ − h], γ_h = 0 on [t₀, ∞) and |γ_h'| ≤ c₁/h. Since γ_h is constant near 0 (t₀ − h > 0) and |·| is C^∞ on ℝ^P ∖ {0}, g_h is C^∞ on ℝ^P. Also 0 ≤ g_h ≤ 1, g_h = 1 on closedBall(0, t₀ − h), g_h = 0 off B, and Dg_h(x) = γ_h'(|x|)·x/|x| vanishes unless t₀ − h < |x| < t₀, with |Dg_h| ≤ c₁/h.
 (b) g_hη and g_h dη are test forms. The Leibniz rule for the exterior derivative of a function times a form gives d(g_hη) = dg_h ∧ η + g_h dη, where (dg ∧ η)(v₀, …, v_m) := Σ_{i=0}^{m} (−1)^i Dg(v_i)·η(v₀, …, v̂_i, …, v_m). Hence T(g_h dη) = T(d(g_hη)) − T(dg_h ∧ η) = ∂T(g_hη) − T(dg_h ∧ η). This is Simon's identity 4.11.
 (c) g_hη is admissible for M_V: tsupport(g_hη) ⊆ closedBall(0, t₀) ⊆ V and |g_hη| ≤ |η| ≤ 1. So |∂T(g_hη)| ≤ M_V(∂T) ≤ Λ₀.
 (d) For increasing I = (i₀ < ⋯ < i_m), (dg ∧ η)(e_I) = Σ_k (−1)^k ∂_{i_k}g·η(e_{I∖i_k}). By Cauchy–Schwarz, |(dg ∧ η)(e_I)|² ≤ (m + 1)Σ_k (∂_{i_k}g)²η(e_{I∖i_k})². Summing over I (each pair (i, J) with i ∉ J occurs at most once) gives |dg ∧ η| ≤ √(m+1)·|Dg|·|η| pointwise. With step 2: |T(dg_h ∧ η)| = |∫⟨dg_h ∧ η, ξ⟩ dμ| ≤ ∫|dg_h ∧ η| dμ ≤ √(m+1)·(c₁/h)·A_{φ(j)}(t₀, h).
 (e) T'_j(dη) = ∫_B ⟨dη, ξ⟩ dμ (step 5 and the weight formula), and T(g_h dη) = ∫ g_h⟨dη, ξ⟩ dμ. As h ↓ 0, g_h → 1_B pointwise: for |x| < t₀, g_h(x) = 1 once h ≤ t₀ − |x|; for |x| ≥ t₀, g_h(x) = 0. Also |g_h⟨dη, ξ⟩| ≤ |dη| μ-a.e., which is μ-integrable (bounded with compact support; μ is finite on compact sets). By dominated convergence (𝓝[>]0 is countably generated), T(g_h dη) → T'_j(dη).
 (f) By (b)–(d), |T(g_h dη)| ≤ Λ₀ + c₁√(m+1)·h⁻¹A_{φ(j)}(t₀, h) for all small h > 0. Take the liminf as h ↓ 0 and use (e): |∂T'_j(η)| ≤ Λ₀ + c₁√(m+1)·D_{φ(j)}(t₀) ≤ Λ₀ + c₁√(m+1)·C. Hence M(∂T'_j) ≤ Λ₁ := Λ₀ + c₁√(m+1)·C.
10. (Conclusion.) Put Λ := max(Λ₀, Λ₁) ∈ [0, ∞). Then K, φ, Λ and T'_j satisfy everything: T'_j is integer multiplicity (step 5), spt T'_j ⊆ K (step 7), M(T'_j) ≤ Λ (step 8), M(∂T'_j) ≤ Λ (step 9), and T'_j = T_{φ(j)} on forms supported in W (step 6). ∎

## Key steps

1. Choose r₀ with W ⊆ B_{r₀}, put V := B_{r₀+2} and Λ₀ := sup_j (M_V(T_j) + M_V(∂T_j)); the weights μ_j of integer multiplicity representations satisfy μ_j(V) ≤ Λ₀ (mass = weight).
2. D_j(t) := liminf_{h↓0} h⁻¹μ_j({t−h<|x|<t}) is Borel on (r₀, r₀+1) and ∫_{r₀}^{r₀+1} D_j ≤ Λ₀ (Simon 4.10, cmcs_slice_mass_integral).
3. Fatou gives t₀ ∈ (r₀, r₀+1) with liminf_j D_j(t₀) < ∞, and a subsequence φ with D_{φ(j)}(t₀) ≤ C.
4. T'_j := T_{φ(j)}⌞B_{t₀}, by restricting the representation: integer multiplicity, equal to T_{φ(j)} on forms supported in W, spt ⊆ closedBall(0, r₀+1), M(T'_j) ≤ Λ₀.
5. Computation 4.11 with a radial cut-off g_h gives |T'_j(dη)| ≤ Λ₀ + c₁√(m+1)·D_{φ(j)}(t₀) for |η| ≤ 1, a uniform bound on M(∂T'_j).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `rg -l 'DeformationTheorem|FlatConvergenceIffWeakConvergence|BoundaryRectifiability|SlicingTheorem|flatDistance' local-references/123e8435b4a2469b/project -g '*.lean' (only GMT/Ch06/Contract.lean and Submission.lean: sorry-based statements in namespace GMT.Ch06, not importable from GMT.Ch07); rg 'deform|flatDistance|IsSlice|BoundaryRectifiability' local-references/123e8435b4a2469b/project/GMT/Ch07 (no match)`
- `sed -n 95,362p local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean (formulations IsSlice, latticeFace, IsLatticeChain, DeformationTheorem, BoundaryRectifiability, FlatConvergenceIffWeakConvergence; used only as formulation reference)`
- `grep declarations in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,WedgeForms,AffineCurrentPushforward}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn, Zero instance, boundary_apply, massAdmissibleOn, massOn, mass, le_massOn, massOn_mono, WeaklyConvergesOn.massOn_le_liminf, covectorEuclideanNorm_neg, zeroRegion/support, isOpen_zeroRegion, affinePushforward, countablyRectifiable_of_measure_zero (no deformation theorem, slicing, flat norm, completeness or boundary rectifiability)`
- `python3 -I scans of the run dag.json (995 nodes): non-accepted related nodes cmc_flat_convergence, cmc_deformation_theorem, cmc_closure_and_boundary_rectifiability, cmcdt_im_series, cmc_fc_series_current, cmc_fc_localize, cmc_fc_total_bounded, dimred_mbl_flat_convergence, dimred_mbl_deformation_theorem, dor_lmb_flat_convergence_cycles and children; accepted helpers cmc_imRep_locality_restrict_sub, dtc_mass_eq_measure, cmc_fc_cs_diagonal_subseq, dtc_vanish_off_support, rsd_cmr_support_subset_of_vanish, cmcs_slice_mass_integral (also seen, not needed: cmc_fc_cauchy_subseq, cmcs_cutoff_defect_bound, lcmp_massOn_le_of_vanish_off_compact, cmc_fc_tb_massOn_sub_le); collision check of the six dtc_bc_lc_fd_ names (none)`
- `git show <candidate commit>:GMT/Ch07/Submission.lean for the six reused declarations (2af75d6, bff81d3, b046f22, 44ef61f, 02c6122, 9dfa657); whitespace-normalised type comparison with my strings and the DAG (all identical); grep sorry/axiom (only the frozen root theorem, no axiom declarations)`
- `rg in local-references/123e8435b4a2469b/mathlib: tendsto_of_subseq_tendsto (Order/Filter/AtTopBot/CountablyGenerated.lean:125), ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (Analysis/SpecificLimits/Basic.lean:273), IsCompact.cthickening (Topology/MetricSpace/Thickening.lean:283), tendsto_add_atTop_iff_nat (Order/Filter/AtTopBot/Basic.lean:337), Real.smoothTransition (Analysis/SpecialFunctions/SmoothTransition.lean)`
- `lake env lean /tmp/fdsplit_check/Types.lean; /tmp/fdsplit_check/Challenges.lean (12 children in comparator challenge form); /tmp/fdsplit_check/Print.lean (pp.coercions); /tmp/fdsplit_check/AllChecks.lean (fd_assembly, fd_cauchy_from, fd_series_limit_from with #print axioms)`
- `sed book/chapter-06.txt lines 875-1150 (3.11-3.16), 1335-1500 (4.6-5.4), 1925-2160 (6.1-7.2), 2296-2335 (8.2-8.3); book/chapter-03.txt lines 551-606 (4.1-4.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-21d9fb1dcd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-cauchy-81bbc80940/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-integral-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/fdsplit_check/stmts.json`
- `/tmp/fdsplit_check/Types.lean`
- `/tmp/fdsplit_check/Challenges.lean`
- `/tmp/fdsplit_check/AllChecks.lean`

The pinned snapshot has no deformation theorem, slicing, flat norm, completeness lemma or boundary rectifiability usable from GMT.Ch07. The snapshot's Ch06 contract only states them (sorry-based, namespace GMT.Ch06) and served as a formulation reference. SimonGMT provides currents, boundary, massOn/mass, support/zero region, weak convergence with lower semicontinuity of mass, affine push-forward and countablyRectifiable_of_measure_zero. Six accepted DAG declarations are reused with identical types and the six new names are unique. The flat-convergence, deformation and closure nodes of the cmc, dimred_mbl and dor_lmb branches are not accepted, so they are not reused. deformation, boundary_im and series are stated so that they follow from cmc_deformation_theorem, from the BR conjunct of cmc_closure_and_boundary_rectifiability and from cmcdt_im_series. All Mathlib names used in the Lean checks exist at the pin. The checks prove this node's frozen type from the children, and cauchy_subseq and series_limit from their declared siblings, using only propext, Classical.choice and Quot.sound.
