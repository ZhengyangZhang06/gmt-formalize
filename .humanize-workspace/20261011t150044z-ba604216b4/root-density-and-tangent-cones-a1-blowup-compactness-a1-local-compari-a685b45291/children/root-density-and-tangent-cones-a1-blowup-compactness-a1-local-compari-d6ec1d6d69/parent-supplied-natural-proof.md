# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2(c) and 3(b) of the parent proof (Simon Ch. 6, 2.23–2.24(2), chapter-06.txt lines 404–425: f_#T(ω) = T(ζ·f^#ω) with ζ = 1 near spt T, and its integral form for currents of locally finite mass). The parent approximates the continuous, compactly supported form β = χ·(ω(f(·))∘ΛⁿDf(·)) uniformly by mollified smooth forms β_k with supports in a fixed compact set, and identifies ∫_M θ⟨β, ξ⟩ dHⁿ with lim_k Y(β_k). Here the sequence is fixed before Y and R are chosen; this yields both the independence of the representation (2(c)) and the additivity (3(b)) in the parent. The frozen type is byte-identical to that of dimred_mbl_pf_pullback_integral_extension in another branch.
Notation: Hⁿ := μHE[n]; ‖·‖ is the operator norm on n-covectors (a finite-dimensional normed space); for x ∈ ℝ^P, γ(x) := ω(f(x))∘Df(x) = (ω (f x)).compContinuousLinearMap (fderiv ℝ f x).
1. γ is continuous on O. f is C¹ on the open set O, so f and Df are continuous on O (ContDiffOn.continuousOn and ContDiffOn.continuousOn_fderiv_of_isOpen with 1 ≤ 1). ω is continuous (it is smooth). The map (β, A) ↦ β∘A from n-covectors × linear maps to n-covectors is continuous: it is β ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM A β, which is jointly continuous in (β, A) (equivalently, in coordinates it is a polynomial in the entries of β and A). Hence γ is continuous on O.
2. Cut-off. K is compact, O open and K ⊆ O, so there is δ > 0 with cthickening(2δ, K) ⊆ O (IsCompact.exists_cthickening_subset_open). By the smooth Urysohn lemma (exists_contDiff_support_eq_eq_one_iff with the open set thickening(2δ, K) and the closed set cthickening(δ, K) contained in it) there is χ : ℝ^P → [0, 1] of class C^∞ with χ = 1 on cthickening(δ, K) ⊇ W₀ := thickening(δ, K) ⊇ K and tsupport χ ⊆ cthickening(2δ, K), a compact subset of O. (This is the cut-off of the parent's step 2(c); the same construction appears in the sibling c1_perturbation, which is not needed here.) Define h(x) := χ(x)·γ(x) for x ∈ ℝ^P. Then:
 (a) h is continuous on ℝ^P: on the open set O it is the product of the continuous functions χ and γ (step 1); on the open set ℝ^P ∖ tsupport χ it vanishes identically; and these two open sets cover ℝ^P because tsupport χ ⊆ O.
 (b) h(x) = 0 for x ∉ tsupport χ, so h has compact support; put B := sup_x ‖h(x)‖ < ∞.
 (c) h = γ on W₀, in particular on K.
3. The test forms. For j ∈ ℕ let ρ_j : ℝ^P → ℝ be C^∞ with ρ_j ≥ 0, ∫ρ_j = 1 and support in the open ball of radius r_j := 1/(j + 1) about 0 (the normalized ContDiffBump with outer radius r_j), and let ω_j := ρ_j ∗ h, i.e. ω_j(x) = ∫ ρ_j(t)·h(x − t) dt (convolution of a scalar kernel with a covector-valued function; ℝ^P carries Lebesgue measure).
 (a) ω_j is C^∞ (HasCompactSupport.contDiff_convolution_left: ρ_j is C^∞ with compact support and h is continuous, hence locally integrable) and has compact support (contained in tsupport h + closedBall(0, 1)); so ω_j ∈ 𝒟ⁿ(ℝ^P) (IsTestForm, and tsupport ω_j ⊆ ℝ^P trivially).
 (b) Since ρ_j ≥ 0 and ∫ρ_j = 1, ‖ω_j(x)‖ ≤ B and ‖ω_j(x) − h(x)‖ ≤ sup_{|t| < r_j} ‖h(x − t) − h(x)‖ for every x (ContDiffBump.dist_normed_convolution_le). h is uniformly continuous (continuous with compact support), so δ_j := sup_x ‖ω_j(x) − h(x)‖ → 0 as j → ∞.
 (c) The sequence (ω_j) depends only on f, ω, O and K (through δ and χ), not on any current or representation.
4. Let Y ∈ 𝒟_n(ℝ^P) and R = (M, θ, ξ) (IMRep univ n) with R.Represents Y and spt Y ⊆ K.
 (a) By the sibling carrier_facts (part (1)), Hⁿ(M ∖ spt Y) = 0; as M ∖ K ⊆ M ∖ spt Y, Hⁿ(M ∖ K) = 0.
 (b) By R.locallyIntegrable_mult for the compact set K, c := ∫⁻_{M∩K} θ dHⁿ < ∞.
 (c) By R.orients, for Hⁿ-a.e. x ∈ M there are an orthonormal family τ and s ∈ {1, −1} with ξ(x)(β) = s·β(τ) for every n-covector β; at such x, |ξ(x)(β)| = |β(τ)| ≤ ‖β‖·Π_i|τ_i| = ‖β‖ (ContinuousAlternatingMap.le_opNorm).
5. Rewriting both sides. Since R represents Y and ω_j ∈ 𝒟ⁿ(ℝ^P), Y(ω_j) = R.action ω_j = ∫_M θ(x)·ξ(x)(ω_j(x)) dHⁿ(x). Since h = γ on K and Hⁿ(M ∖ K) = 0, the functions x ↦ θ(x)ξ(x)(γ(x)) and x ↦ θ(x)ξ(x)(h(x)) agree Hⁿ⌞M-a.e., so their integrals over M coincide (integral_congr_ae; this needs no integrability). The functions θ·ξ(ω_j) and θ·ξ(h) are a.e. strongly measurable for Hⁿ⌞M (θ is measurable, ξ is a.e. strongly measurable, ω_j and h are continuous, and evaluation (ζ, β) ↦ ζ(β) is continuous bilinear), and by step 4 they are bounded Hⁿ⌞M-a.e. by B·θ·1_K, whose integral is B·c < ∞; so they are integrable.
6. Convergence. By linearity of ξ(x) and of the integral, |Y(ω_j) − ∫_M θ(x)ξ(x)(γ(x)) dHⁿ(x)| = |∫_M θ(x)·ξ(x)(ω_j(x) − h(x)) dHⁿ(x)| ≤ ∫_M θ(x)·‖ω_j(x) − h(x)‖·1_K(x) dHⁿ(x) ≤ δ_j·c → 0, using step 4(c) and Hⁿ(M ∖ K) = 0. Hence Y(ω_j) → ∫_M θ(x)·ξ(x)(ω(f(x))∘Df(x)) dHⁿ(x) as j → ∞, for every such Y and R and with the same sequence (ω_j). ∎

## Key steps

1. γ = ω(f(·))∘Df(·) is continuous on O; a smooth cut-off χ (χ = 1 near K, compact tsupport χ ⊆ O) makes h = χγ a continuous compactly supported form equal to γ on K.
2. Mollifications ω_j = ρ_j ∗ h are test forms converging uniformly to h; they depend only on f, ω, O, K.
3. For every R representing Y with spt Y ⊆ K: Hⁿ(M ∖ K) = 0 (carrier_facts), ∫_{M∩K} θ < ∞, and |ξ(x)(β)| ≤ ‖β‖ a.e.
4. Y(ω_j) = ∫_M θξ(ω_j), ∫_M θξ(γ) = ∫_M θξ(h), and the difference is at most ∫_{M∩K}θ·sup‖ω_j − h‖ → 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; read GMT/Ch07/Contract.lean, GMT/Ch07/README.md, PROBLEM.md and this node's parent-child-handoff.json, parent-supplied-plan.md, parent-supplied-natural-proof.md (proof identical to the handoff)`
- `grep '^theorem|^def|^structure|^abbrev|^instance' simongmt Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean and Chapter03/{Rectifiable,Differential}.lean`
- `grep '^theorem' simongmt Poincare/SimonGMT/Chapter02/{AreaLipschitz,AreaNoninjective,AreaCritical,AreaDomain,Area}.lean (weighted_area_formula_lipschitz_injOn, area_image_criticalSet_eq_zero, linear_area_formula)`
- `python3 -I scans of dag.json (995 nodes): lean_name/statement matching push|area|pullback|compContinuousLinearMap|mollif|fderiv|ContDiffOn; status and candidate_commit of dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes, dpf_smooth_approx_compact_perturbation, dpf_rectifiable_bilipschitz_pieces, covectorEuclideanNorm_gram_bounds, ptd_ae_approxTangent_iff_of_subset, ptd_piece_image_approxTangent_ae; parallel nodes dimred_mbl_pf_* and dor_lmb_pc_* (all decomposing); byte-identity comparisons; collision check of dtc_bc_lc_pf_* (none)`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name>' for the six reused declarations (types identical); git log --all --oneline -S'dtc_bc_lc_pf_' (no match)`
- `read nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/decomposition-v1.json, nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json, and the parent-child-handoff.json of the reused nodes (audited proofs)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|_overlay_accepted_children' /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `grep Mathlib at the pin: exists_contDiff_support_eq_eq_one_iff, IsCompact.exists_cthickening_subset_open, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, MeasurableSet.image_of_continuousOn_injOn, LipschitzWith.ae_differentiableAt, ContDiffOn.continuousOn_fderiv_of_isOpen, norm_compContinuousLinearMap_le, ae_tendsto_average_norm_sub, ae_tendsto_measure_inter_div, norm_integral_le_of_norm_le, LipschitzOnWith.hausdorffMeasure_image_le, Filter.EventuallyEq.fderiv_eq, ContDiffBump.convolution_tendsto_right_of_continuous, Isometry.hausdorffMeasure_image, euclideanHausdorffMeasure_smul₀, LinearMap.euclideanHausdorffMeasure_image`
- `sed -n book/chapter-06.txt lines 395-540 and 760-870 (2.23-2.29, 3.1-3.10); book/chapter-03.txt lines 330-412 (2.1-2.6)`
- `lake env lean /tmp/pfdecomp/check/Types2.lean (12 child types in the scope from gmt-compare.py contract_scope); lake env lean /tmp/pfdecomp/check/Assembly2.lean with #print axioms; verifier lean_contract.validate_lean_statement on all 12 strings; topological sort of depends_on`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/pfdecomp/check/Types2.lean`
- `/tmp/pfdecomp/check/Assembly2.lean`

The pinned SimonGMT library has currents, boundary, mass with the Euclidean coefficient norm, support and zero region, countable rectifiability, approximate tangent spaces and the Lipschitz area formula on ℝⁿ. It has only the affine push-forward, and no push-forward of integer multiplicity currents by C¹ maps. Comparator-accepted DAG declarations already prove, for compactly supported C¹ perturbations of the identity, that the push-forward formula defines a current and maps cycles to cycles (dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes). They are reused together with the node's four inherited dependencies (dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, rsd_cmr_support_subset_of_vanish), all with types identical to their accepted candidate commits. Five new types are byte-identical to the unaccepted dimred_mbl_pf_*/dor_lmb_pc_* nodes and get new unique names dtc_bc_lc_pf_*; c1_perturbation is new. All 12 types elaborate in the comparator scope, and a Lean assembly proves the exact frozen parent type from them using only propext, Classical.choice and Quot.sound.
