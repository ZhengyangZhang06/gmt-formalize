# Parent-supplied natural-language proof

- Parent DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1`
- Child DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.im_parametrization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part E of the selected parent's supplied proof (E1: the carrier of S lies in spt S up to a null set; E2–E4: Lipschitz pieces, integer weights and the representation (REP), with F_j(A_j) ⊆ spt S and F_j differentiable on A_j), i.e. Simon Ch. 6, 3.1 and 3.3–3.6 (integer multiplicity currents computed on Lipschitz parametrizations by the area formula) and 2.11–2.12 (spt T = spt μ_T). Steps E2–E4 of the supplied proof, for a representation of finite total measure, are exactly the comparator-accepted sibling imrep_parametric_rep (whose kernel-checked proof runs through the same bi-Lipschitz pieces, tangent-plane orientation signs and Lipschitz area formula); E1 follows from the comparator-accepted sibling imrep_mass_support. Finite total measure is where the hypothesis "spt S compact" enters.

Notation: H^k := μHE[k] on ℝ^P; L^k := volume on ℝ^k; ∂F and JF as in the statement.

1. Representation. By IsIntegerMultiplicity S there is an IMRep R0 = (M, θ, ξ) in univ with R0.Represents S: S(ω) = R0.action ω = ∫_M θ ξ(ω) dH^k for every ω ∈ 𝒟^k (TestFormOn univ k). Let μ := R0.measure = (H^k.restrict M).withDensity θ.
2. Support and mass. The sibling imrep_mass_support (Submission.dor_imrep_massOn_eq_measure_and_support) with U := univ (open) gives (i) S.massOn W = μ(W) for every open W and (ii) spt S = univ ∩ supp μ = supp μ (Measure.support).
3. μ((spt S)ᶜ) = μ((supp μ)ᶜ) = 0 by Mathlib Measure.measure_compl_support (ℝ^P is second countable, hence hereditarily Lindelöf).
4. Finite mass. spt S is compact, hence closed and Borel. So μ(ℝ^P) = μ(spt S) + μ((spt S)ᶜ) = μ(spt S) = ∫⁻_{spt S} θ d(H^k.restrict M) = ∫⁻_{M ∩ spt S} θ dH^k (withDensity_apply, Measure.restrict_restrict), which is ≠ ∞ by the IMRep field locallyIntegrable_mult with K := spt S (compact, ⊆ univ). By 2(i) with W := univ, S.mass = S.massOn univ = μ(ℝ^P) ≠ ∞: this is the first conclusion.
5. E1: the carrier lies in spt S up to a null set. By 3 and withDensity_apply, ∫⁻_{(spt S)ᶜ} θ d(H^k.restrict M) = 0. For (H^k.restrict M)-a.e. x we have x ∈ M, hence θ(x) ≥ 1 (mult_pos, θ ∈ ℕ). Therefore (H^k.restrict M)((spt S)ᶜ) = ∫⁻_{(spt S)ᶜ} 1 d(H^k.restrict M) ≤ ∫⁻_{(spt S)ᶜ} θ d(H^k.restrict M) = 0, i.e. x ∈ spt S for (H^k.restrict M)-a.e. x.
6. E2–E4 (pieces and weights). Apply the sibling imrep_parametric_rep (Submission.dor_lmb_fcd_imp_parametric_rep) with N := P to R0, which is allowed since μ(univ) ≠ ∞ (step 4). It gives maps G_j : ℝ^k → ℝ^P, sets B_j ⊆ ℝ^k and functions w_j : ℝ^k → ℝ (j ∈ ℕ) such that: each G_j is Lipschitz; each B_j is Borel; G_j is differentiable at every point of B_j; each w_j is measurable and integer-valued at every point; w_j is integrable on B_j; Σ_j ∫⁻_{B_j} |w_j|·JG_j ≤ μ(ℝ^P); for every continuous k-form γ with sup_x ‖γ(x)‖ < ∞, HasSum (j ↦ ∫_{B_j} w_j(u)·γ(G_j u)(∂G_j(u)) du) (R0.action γ); and for every predicate p on ℝ^P holding (H^k.restrict M)-a.e., p(G_j(u)) holds for L^k-a.e. u ∈ B_j, for every j.
7. Definitions (re-indexing as in E4). F_j := G_j; A_j := B_j ∩ G_j⁻¹(spt S), Borel since B_j is Borel, G_j is continuous (Lipschitz) and spt S is closed; g_j(u) := ⌊w_j(u)⌋ ∈ ℤ. Because w_j(u) is an integer, (g_j(u) : ℝ) = w_j(u) for every u. g_j is measurable: ℤ is countable with the discrete σ-algebra, and g_j⁻¹{z} = w_j⁻¹([z, z + 1)) is Borel for every z (measurable_to_countable').
8. Elementary properties. F_j is Lipschitz; A_j is Borel; g_j is measurable; (g_j : ℝ) = w_j is integrable on A_j ⊆ B_j (IntegrableOn.mono_set); F_j = G_j is differentiable at every point of A_j ⊆ B_j; F_j(A_j) ⊆ spt S by the definition of A_j.
9. Total weight. Σ_j ∫⁻_{A_j} |g_j|·JF_j ≤ Σ_j ∫⁻_{B_j} |w_j|·JG_j ≤ μ(ℝ^P) < ∞ (A_j ⊆ B_j, g_j = w_j, step 6, step 4).
10. A_j and B_j differ by a null set. Apply the last property of step 6 to p(x) :≡ (x ∈ spt S), which holds (H^k.restrict M)-a.e. by step 5: G_j(u) ∈ spt S for L^k-a.e. u ∈ B_j, i.e. L^k(B_j ∖ A_j) = 0; as A_j ⊆ B_j, A_j =ᵐ B_j.
11. Representation (REP). Let ω ∈ 𝒟^k. It is C^∞, hence continuous, with compact support, so sup_x ‖ω(x)‖ < ∞ (HasCompactSupport.exists_bound_of_continuous). Step 6 with γ := ω gives HasSum (j ↦ ∫_{B_j} w_j ω(G_j)(∂G_j)) (R0.action ω), and R0.action ω = S(ω) by step 1. By step 10 (setIntegral_congr_set) and (g_j : ℝ) = w_j, ∫_{A_j} g_j(u) ω(F_j u)(∂F_j u) du = ∫_{B_j} w_j(u) ω(G_j u)(∂G_j u) du for every j. Hence HasSum (j ↦ ∫_{A_j} g_j(u)·ω(F_j u)(∂F_j u) du) (S(ω)).
Steps 4, 8, 9 and 11 are the conclusions. ∎

## Key steps

1. Take an IMRep (M, θ, ξ) of S; the sibling imrep_mass_support gives S.massOn W = μ(W) for open W and spt S = supp μ, μ := θH^k⌞M.
2. μ((spt S)ᶜ) = 0 (measure_compl_support), so μ(ℝ^P) = ∫_{M∩spt S}θ < ∞ by local integrability on the compact spt S; hence S.mass = μ(ℝ^P) ≠ ∞.
3. θ ≥ 1 on M turns μ((spt S)ᶜ) = 0 into H^k(M ∖ spt S) = 0 (E1).
4. The sibling imrep_parametric_rep (E2–E4 for a finite-measure representation) gives Lipschitz G_j, Borel B_j, integer-valued integrable w_j with Σ∫|w_j|JG_j ≤ μ(ℝ^P), the series representation and pull-back of a.e. statements.
5. Shrink B_j to A_j := B_j ∩ G_j⁻¹(spt S) (a null change by E1) and set g_j := ⌊w_j⌋ = w_j; all conclusions transfer.

## Reference use

### local-project

Queries:
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem exists_contDiff_support_eq_eq_one_iff|lemma measure_compl_support|theorem volume_preserving_piFinSuccAbove|theorem EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp|theorem norm_fderiv_le_of_lipschitz|theorem measurable_to_countable.|theorem enorm_integral_le_lintegral_enorm|theorem setIntegral_congr_set|theorem measurable_fderiv |def curryLeft|theorem extDeriv_apply|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le..' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `grep -rln 'contDiff_parametric|ContDiff.*intervalIntegral|contDiff_integral' mathlib/Mathlib (no match)`
- `python3 -I over dag.json (2375 nodes): keyword search homotop|cone|parametri|Lipschitz|Gram|orientation|approximate tangent|density|area formula|pushforward; status, candidate_commit and child/dependency closure of the reuse targets; byte equality of lean_statement with each handoff; replay of Runtime._existing_lean_name_problem for all 12 names`
- `git show <candidate>:GMT/Ch07/Submission.lean | grep -n 'theorem Submission.<name>|sorry' for the 8 reused candidates; cross-candidate comparison of 77 shared theorem headers`
- `lake env lean /tmp/cone-split-check/Final.lean (12 exact child types; parent assembly; Lean proofs of ecf_im_lipschitz_parametrization and ecf_isIntegerMultiplicity_of_parametrization from the reused types; Fin.cons, enorm and inner meaning checks; #print axioms)`
- `sed -n 441,551p and 850,866p book/chapter-06.txt`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|def ensure|_overlay_accepted_children|cited_inherited|_reference_use_problem' /runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/{runtime,store,inherited}.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9310c84433/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-1df3e47686/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-53b6b2be95/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-covector-gram-bounds-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cone-split-check/Final.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 contract is byte-identical (sha256 e4148e7f…) to the workspace Contract.lean and Submission.lean.

Availability of the cited Mathlib facts:
- The pinned Mathlib contains every Mathlib fact the new children cite: exists_contDiff_support_eq_eq_one_iff, Measure.measure_compl_support, volume_preserving_piFinSuccAbove, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, ContinuousAlternatingMap.curryLeft, extDeriv_apply, measurable_to_countable', enorm_integral_le_lintegral_enorm, setIntegral_congr_set, measurable_fderiv, norm_fderiv_le_of_lipschitz and hasFDerivAt_integral_of_dominated_of_fderiv_le''.
- It has no C^∞ parametric-integral lemma (no match). B1 therefore reuses the accepted cmcdt_lpo_slice_param_integral.
- No cone construction, homotopy operator or general integrality-of-parametrization theorem exists in the snapshot project or in SimonGMT.

Reuse of DAG checkpoints:
- The DAG holds comparator-accepted checkpoints that are exactly E2–E4, E1/(MR), G2–G6 for one piece, the G4–G6 summation, (IMC), A2a and (VO). These are dor_lmb_fcd_imp_parametric_rep, dor_imrep_massOn_eq_measure_and_support, dimred_mbl_dt_lpip_lipschitz_piece_current, cmcdt_im_series, cmc_imRep_locality_restrict_sub, covectorEuclideanNorm_gram_bounds and dtc_vanish_off_support.
- Their frozen types match byte for byte. Their candidate commits contain the declared theorems, with the only sorry in main_theorem. Their closures are fully accepted, and the shared theorem headers are identical across candidates.
- The runtime permits identical-type reuse of accepted checkpoints across branches. The four new ecf_ names are unreserved.

Lean checks:
- All 12 child types elaborate.
- The parent assembly compiles.
- Both glue children are proved in Lean from the exact reused types, with 0 errors and only stub sorries.
