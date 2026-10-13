# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6 and 7 of the parent proof, stated for one index: the competitor Z_i = S_i + π_{i#}Y_i, minimality of S_i in A_i, π_{i#}Q_i = Q_i and the estimate (I). The parent applies it with S = S_i, A = A_i, U = U_i, π = π_i, L = 1 + η and Y = Y_i, where spt Y_i ⊆ B_{G/3}(0).

Siblings used: pushforward (PF), orientation_fixed (OF), measure_subadditive (F4), mass_eq_measure (M), vanish_off_support (V), im_calculus (b) restriction and (c) differences, restrict_domain_im (RD), support_of_vanishing (SV).

Notation. n := m + 1 and B_r := ball(0, r). ι is the inclusion of 𝒟ⁿ(U) into 𝒟ⁿ(ℝ^P) (same form). For currents A, B in one domain, A + B := A − (0 − B), so (A + B)(ω) = A(ω) + B(ω). The zero current is integer multiplicity, since it equals A − A for any integer multiplicity A (im_calculus (c)).

1. (Derivative bound.) π is C¹ and L-Lipschitz on the open ball B_{2G}, with L ≥ 0. So ‖Dπ(y)‖ ≤ L for y ∈ B_{2G} (Mathlib norm_fderiv_le_of_lipschitzOn).

2. (Q := S⌞B_G as a current in ℝ^P.) Let (M, θ, ξ) represent S; S is integer multiplicity by the first part of IsMinimizingIn.
 (a) By im_calculus (b) (with U and E = B_G), (M ∩ B_G, θ, ξ) is an integer multiplicity triple in U. Since M ∩ B_G ⊆ closedBall(0, G), a compact subset of U, its multiplicity is integrable over every compact K ⊆ ℝ^P: ∫_{M∩B_G∩K} θ ≤ ∫_{M∩closedBall(0,G)} θ < ∞.
 (b) So the same data form an integer multiplicity triple in ℝ^P. By im_calculus (b) (with ℝ^P and E = ℝ^P) it represents a current Q ∈ 𝒟_n(ℝ^P), with carrier M ∩ B_G and weight μ_Q = μ_S⌞B_G.
 (Q1) If ω ∈ 𝒟ⁿ(U) and tsupport ω ⊆ B_G, then S(ω) = Q(ιω). Both are ∫θ⟨ω, ξ⟩ dHⁿ, over M and over M ∩ B_G respectively, and ω = 0 on M ∖ B_G.
 (Q2) spt Q ⊆ K_Q := closedBall(0, G) ∩ spt S. This set is compact (it equals closedBall(0, G) ∖ Z_S, as closedBall(0, G) ⊆ U) and contained in A ∩ B_{2G} (as spt S ⊆ A). Indeed Hⁿ(M ∖ spt S) = 0, because μ_S(U ∖ spt S) = 0 by V and M and θ ≥ 1. If tsupport ω ∩ K_Q = ∅, then ω(x) = 0 for every x ∈ (M ∩ B_G) ∩ spt S. So the integrand of Q(ω) vanishes Hⁿ-a.e. on M ∩ B_G, and Q(ω) = 0. SV gives spt Q ⊆ K_Q, and spt Q is compact.

3. (Push-forward.) Apply PF with O := B_{2G} and f := π, which is C¹ on O. This gives push with properties (i)–(v) and (B). Q and Y are in its domain: both are integer multiplicity with compact supports contained in B_{2G}, since spt Q ⊆ closedBall(0, G) and spt Y ⊆ B_{G/2}.
 (Q3) push Q = Q.
 (a) Apply OF to Q with its representation (M ∩ B_G, θ, ξ), U := ℝ^P, O := B_{2G} and f := π, which is differentiable on O. Its hypothesis holds: for y ∈ spt Q ∩ B_{2G} we have y ∈ spt S ⊆ A, so π(y) = y.
 (b) Hence for Hⁿ-a.e. x ∈ M ∩ B_G (⊆ B_{2G}): π(x) = x and ⟨α ∘ ΛⁿDπ(x), ξ(x)⟩ = ⟨α, ξ(x)⟩ for all α.
 (c) By PF (i), push Q(ω) = ∫_{M∩B_G} θ⟨ω(π(x)) ∘ ΛⁿDπ(x), ξ(x)⟩ dHⁿ = ∫_{M∩B_G} θ⟨ω(x), ξ(x)⟩ dHⁿ = Q(ω).

4. (Additivity.) 0 − Y is integer multiplicity with spt(0 − Y) = spt Y, since (0 − Y)(ω) = −Y(ω) and so the zero regions coincide; and spt 0 = ∅.
 (a) PF (B) with (0, 0) gives push 0 = push 0 − push 0, hence push 0 = 0.
 (b) PF (B) with (0, Y) gives push(0 − Y) = 0 − push Y.
 (c) PF (B) with (Q, 0 − Y) gives push(Q + Y) = push Q − push(0 − Y).
 (d) Using (Q3), push(Q + Y)(ω) = Q(ω) + push Y(ω) for every ω.

5. (The competitor; parent step 6.) Let Z := S + (push Y)|_U ∈ 𝒟_n(U), where (push Y)|_U is the restriction to the domain U (restrictDomain).
 (a) (push Y)|_U is integer multiplicity by RD and PF (ii), so Z is integer multiplicity by im_calculus (c).
 (b) ∂Z = ∂S, because ∂((push Y)|_U)(ω) = push Y(ι dω) = ∂(push Y)(ιω) = 0, by PF (v) and ∂Y = 0.
 (c) Let K_π := π(spt Y). It is compact, since π is continuous on B_{2G} ⊇ spt Y. It is contained in A ∩ B_G, since π maps B_{2G} into A and |π(y)| ≤ 2|y| < G for y ∈ spt Y ⊆ B_{G/2}. In particular K_π ⊆ U.
 (d) For ω ∈ 𝒟ⁿ(U) with tsupport ω ∩ K_π = ∅: (Z − S)(ω) = push Y(ιω) = 0, by V and spt push Y ⊆ K_π (PF (iii)). By SV, spt(Z − S) ⊆ K_π and spt(Z − S) is compact. So spt(Z − S) is a compact subset of A ∩ B_G.
 (e) B_G is open with closure closedBall(0, G) compact and contained in U. Minimality of S in A (IsMinimizingIn, with W := B_G and the competitor Z) gives M_{B_G}(S) ≤ M_{B_G}(Z).

6. (Estimate of M_{B_G}(Z); parent (I).)
 (a) For ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ B_G: Z(ω) = S(ω) + push Y(ιω) = Q(ιω) + push Y(ιω) = push(Q + Y)(ιω), by (Q1) and step 4. Since ιω is admissible for M_{B_G} in ℝ^P whenever ω is, M_{B_G}(Z) ≤ M_{B_G}(push(Q + Y)) ≤ M(push(Q + Y)).
 (b) Q + Y is integer multiplicity, with compact support in K_Q ∪ spt Y ⊆ B_{2G}: it vanishes on forms supported off this compact set, and SV applies. By PF (iv) and step 1, M(push(Q + Y)) ≤ Lⁿ·M(Q + Y).
 (c) M(Q + Y) = M_{B_G}(Q + Y). By F4 (with c = 1), μ_{Q+Y} ≤ μ_Q + μ_Y. Also μ_Q(ℝ^P ∖ B_G) = 0, since its carrier M ∩ B_G lies in B_G, and μ_Y(ℝ^P ∖ B_G) ≤ μ_Y(ℝ^P ∖ spt Y) = 0 by V and M. So μ_{Q+Y}(ℝ^P ∖ B_G) = 0, and by M, M(Q + Y) = μ_{Q+Y}(ℝ^P) = μ_{Q+Y}(B_G) = M_{B_G}(Q + Y).
 (d) M_{B_G}(Q + Y) ≤ M_{B_G}(S + Y|_U). Every ω' ∈ 𝒟ⁿ(ℝ^P) admissible for M_{B_G} lies in 𝒟ⁿ(U), as tsupport ω' ⊆ B_G ⊆ U, and (Q + Y)(ω') = S(ω') + Y(ω') = (S + Y|_U)(ω') by (Q1).

7. (Conclusion.) M_{B_G}(S) ≤ M_{B_G}(Z) ≤ M(push(Q + Y)) ≤ Lⁿ·M(Q + Y) = Lⁿ·M_{B_G}(Q + Y) ≤ Lⁿ·M_{B_G}(S + Y|_U), with Lⁿ read as ENNReal.ofReal (L^n). ∎

## Key steps

1. ‖Dπ‖ ≤ L on B_{2G}. Q := S⌞B_G is an integer multiplicity current in ℝ^P that agrees with S on forms supported in B_G, with compact support in B̄_G ∩ spt S ⊆ A.
2. By orientation_fixed and the push-forward formula, π_#Q = Q; by additivity, π_#(Q + Y) = Q + π_#Y.
3. Z := S + π_#Y is an integer multiplicity competitor with ∂Z = ∂S and spt(Z − S) ⊆ π(spt Y), a compact subset of A ∩ B_G. Minimality gives M_{B_G}(S) ≤ M_{B_G}(Z).
4. M_{B_G}(Z) ≤ M(π_#(Q + Y)) ≤ Lⁿ·M(Q + Y), and M(Q + Y) = M_{B_G}(Q + Y) = M_{B_G}(S + Y) by measure subadditivity off B_G.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; read workspace GMT/Ch07/Contract.lean, GMT/Ch07/README.md (contract unchanged; Submission.lean byte copy)`
- `rg/grep 'def GeometricCurrentOn.massOn|massAdmissibleOn|covectorEuclideanNorm_neg|le_massOn|massOn_mono|massOn_le_liminf' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep 'structure GeometricCurrentOn|instance .*Zero|def GeometricCurrentOn.boundary|boundary_boundary|exteriorDerivativeTestOn|tsupport_exteriorDerivative_subset|WeaklyConvergesOn' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean; grep 'abbrev Covector|abbrev DifferentialForm|abbrev exteriorDerivative' Chapter06/Forms.lean`
- `grep 'restrictDomain|testFormOnInclusion|VanishesOn|zeroRegion|def GeometricCurrentOn.support|isOpen_zeroRegion' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `grep 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|blowUpMap|HasApproximateTangentSpaceAt.unique|support_euclideanHausdorffMeasure_restrict_submodule' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (no slicing, flat-norm, deformation theorem or non-affine push-forward in Chapter06)`
- `python3 -I scans of dag.json (673 nodes at the first scan, 783 at the final re-check): related nodes cmc_flat_convergence, cmc_slice_mass_bounds, dimred_mbl_pushforward, dimred_mbl_local_comparison, imrep_c1_diffeo_pushforward_im (not accepted, not reusable); accepted candidates dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, dtc_restrictDomain_isIntegerMultiplicity, rsd_cmr_support_subset_of_vanish, dtc_approxTangent_of_null_diff, lcmp_massOn_le_add_of_eval_eq, dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes; collision check of the seven new dtc_bc_lc_ names (none)`
- `git grep 'theorem Submission.<name> ' <accepted commit> -- GMT for the five reused declarations; whitespace-normalised type comparison (all IDENTICAL); git show e34a71c (dispatch commit contains only the contract)`
- `#check of Mathlib names at the pin: Filter.extraction_forall_of_eventually, ENNReal.tendsto_atTop_zero_of_tsum_ne_top, Metric.mem_thickening_iff_infDist_lt, IsCompact.cthickening, Measure.countable_meas_level_set_pos, norm_fderiv_le_of_lipschitzOn, ENNReal.tsum_geometric, restrict_withDensity, Measure.le_iff, image_eq_zero_of_notMem_tsupport`
- `lake env lean /tmp/dtcbclc/check/Types.lean; challenge modules /tmp/dtcbclc/check/challenges/Challenge_<key>.lean (12, generated by verifier gmt-compare.py child_modules, contract mode); lake env lean /tmp/dtcbclc/out/Assembly.lean with #print axioms for assembly and ret_assembly`
- `sed book/chapter-07.txt lines 150-300 (Simon 7.2.4 proof (1)-(14), Remark 7.2.5); book/chapter-06.txt lines 395-540, 700-1000, 1140-1500, 1990-2120 (2.23-2.29, 3.1-3.14, 4.1-4.11, 5.1-5.4, 6.3, 7.1-7.2); book/chapter-03.txt lines 100-160, 327-445 (1.6, 2.1-2.10)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dtcbclc/out/Assembly.lean`
- `/tmp/dtcbclc/check/Types.lean`
- `/tmp/dtcbclc/stmts/children.py`

The pinned SimonGMT library provides currents, boundary, massOn with the Euclidean coefficient norm, support/zeroRegion, restrictDomain, testFormOnInclusion, lower semicontinuity of mass, CountablyRectifiable and HasApproximateTangentSpaceAt. It has no flat-norm theorem, deformation theorem, slicing, C¹ push-forward of currents or area/coarea formula on rectifiable sets. These are the three Simon Ch. 6 results (C1)–(C3) cited by the supplied proof, so they become the children flat_decomposition, slicing and pushforward. Related DAG nodes in other branches (cmc_flat_convergence, cmc_slice_mass_bounds, dimred_mbl_pushforward) are not accepted, so they cannot be reused and the new names are unique. Five accepted declarations are reused with identical types: dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, dtc_restrictDomain_isIntegerMultiplicity and rsd_cmr_support_subset_of_vanish. All Mathlib lemmas used in the Lean assembly exist at the pin. All 12 child types elaborate in the comparator scope. The Lean assembly proves the exact frozen type of dtc_bc_local_comparison from the 12 child types and the sibling measure_locality type, and proves retraction_comparison from its declared siblings, using only propext, Classical.choice and Quot.sound.
