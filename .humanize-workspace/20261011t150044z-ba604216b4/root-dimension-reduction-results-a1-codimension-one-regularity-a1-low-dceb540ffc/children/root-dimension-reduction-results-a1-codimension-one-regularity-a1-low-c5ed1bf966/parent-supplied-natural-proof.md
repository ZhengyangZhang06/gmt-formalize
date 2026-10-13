# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.diffeo_pushforward-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.diffeo_pushforward-a1.image_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 of the parent proof; Simon 6.3.6–3.9 for injective f (chapter-06.txt lines 815–862: f_#T = τ(f(M), θ∘f^{-1}, η) with the induced orientation η of 3.5/3.7) and 6.2.24(3) (lines 426–440: for 1:1 f, f_#T(ω) = ∫_{f(M_+)} ⟨ω(y), η(y)⟩ dH^n by the area formula), with the details filled in. Notation: E := ℝ^P, H^n := μHE[n], μ := H^n⌞M, Q(x) := approxTangentPlane n M x, ψ := φ^{-1}; J(x) := sqrt(det(⟨Dφ(x)e_a, Dφ(x)e_b⟩)) with e = stdOrthonormalBasis ℝ Q(x) (the Jacobian of the siblings); ζ(x) := (R.orient x).comp (compContinuousLinearMapCLM (Dφ x)), i.e. ζ(x)(β) = ξ(x)(β∘Dφ(x)). Replacing Λ by max(Λ, 1) we assume Λ ≥ 1. Provenance: this statement and its frozen Lean type are byte-identical to Submission.dpf_imrep_bilipschitz_image_rep (node root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1, not yet accepted, owned by another parent); the proof below is that node's parent-supplied proof with the siblings renamed to codim1_ldr_dpf_approxTangent_bilipschitz_image_ae and codim1_ldr_dpf_area_formula_bilipschitz_rectifiable, and it does not use that node.
1. Facts on φ and ψ. ψ is Λ-Lipschitz (for y = φ(x), y' = φ(x'): |ψy − ψy'| = |x − x'| ≤ Λ|y − y'|), hence continuous and Borel measurable. φ(U) = U (φ^{-1}(U) = U and φ is surjective); for compact C ⊆ U, ψ(C) = φ^{-1}(C) is compact and ⊆ U. For every A ⊆ E, H^n(φ(A)) ≤ Λ^n H^n(A) and H^n(ψ(A)) ≤ Λ^n H^n(A) (LipschitzWith.hausdorffMeasure_image_le; μHE[n] is a fixed multiple of μH[n]). ‖Dφ(x)‖ ≤ Λ (norm_fderiv_le_of_lipschitz).
2. Local finiteness of M. θ ≥ 1 on M (R.mult_pos), so H^n(M ∩ C) ≤ ∫⁻_{M∩C} θ dH^n < ∞ for compact C ⊆ U (R.locallyIntegrable_mult).
3. Inputs. (G) By the sibling codim1_ldr_dpf_approxTangent_bilipschitz_image_ae (U open, M = R.carrier Borel ⊆ U, R.rectifiable, step 2, φ C¹ with injective derivatives, Λ-Lipschitz, Λ-antilipschitz, φ^{-1}(U) = U): for μ-a.e. x, HasApproximateTangentSpaceAt n M x Q(x) and HasApproximateTangentSpaceAt n φ(M) φ(x) (Dφ(x)Q(x)). (H) By the sibling codim1_ldr_dpf_area_formula_bilipschitz_rectifiable (φ injective): ∫⁻_{φ(M)} g dH^n = ∫⁻_M J(x) g(φ(x)) dH^n(x) for every g : E → [0, ∞]. (I) By the sibling dpf_aestronglyMeasurable_gramJacobian with μ, Q, L := Dφ (continuous, hence a.e. strongly measurable) and the projection hypothesis: J is μ-a.e. strongly measurable. (O) By R.orients: for μ-a.e. x there is Q' with HasApproximateTangentSpaceAt n M x Q' and IsUnitOrientationOf ξ(x) Q'.
 Let G ⊆ M be the set of x where (G) and (O) hold; H^n(M ∖ G) = 0. For x ∈ G, Q' = Q(x) by uniqueness (HasApproximateTangentSpaceAt.unique), so ξ(x) orients Q(x), and the sibling dpf_unitOrientation_map_gramNormalized (with ξ(x), Q(x), Dφ(x) injective, J = J(x)) gives 0 < J(x) ≤ ‖Dφ(x)‖^n ≤ Λ^n and IsUnitOrientationOf (J(x)^{-1} ζ(x)) (Dφ(x)Q(x)).
4. Definition of R'. Carrier M' := φ(M); multiplicity θ'(y) := θ(ψ(y)); orientation ξ'(y) := J(ψ(y))^{-1} • ζ(ψ(y)) (equal to 0 where J(ψ(y)) = 0, as 0^{-1} = 0).
5. The fields of IMRep. (a) M' = ψ^{-1}(M) (φ bijective) is Borel since ψ is continuous. (b) M' = φ(M) ⊆ φ(U) = U. (c) M' is countably n-rectifiable: if M ⊆ M₀ ∪ ⋃_j F_j(ℝ^n) as in CountablyRectifiable, then M' ⊆ φ(M₀) ∪ ⋃_j (φ∘F_j)(ℝ^n), H^n(φ(M₀)) ≤ Λ^n · 0 = 0 and φ∘F_j is Lipschitz. (d) θ' = θ∘ψ is measurable. (e) For y ∈ M', ψ(y) ∈ M, so θ'(y) = θ(ψ(y)) > 0. (f) Local integrability: for compact C ⊆ U, apply (H) to g := 1_C θ' (note θ'(φ(x)) = θ(x) and 1_C(φ(x)) = 1_{ψ(C)}(x)): ∫⁻_{M'∩C} θ' dH^n = ∫⁻_M J(x) 1_{ψ(C)}(x) θ(x) dH^n(x) ≤ Λ^n ∫⁻_{M∩ψ(C)} θ dH^n < ∞, using J ≤ Λ^n μ-a.e. (step 3) and R.locallyIntegrable_mult for the compact ψ(C) ⊆ U. (g) ξ' is a.e. strongly measurable for μ' := H^n⌞M': the map f(x) := J(x)^{-1} • ζ(x) is μ-a.e. strongly measurable (J by (I) and inversion on ℝ is measurable; ζ because ξ is μ-a.e. strongly measurable (R.aestronglyMeasurable_orient), Dφ is continuous and (ξ, L) ↦ ξ.comp (compContinuousLinearMapCLM L) is continuous, by ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM and continuity of composition). ψ is quasi-measure-preserving from μ' to μ: it is measurable, and for Borel A, μ'(ψ^{-1}(A)) = H^n(φ(M) ∩ φ(A)) = H^n(φ(M ∩ A)) ≤ Λ^n μ(A), so the image measure of μ' under ψ is absolutely continuous with respect to μ (it suffices to test measurable sets, Measure.AbsolutelyContinuous.mk). Hence ξ' = f∘ψ is μ'-a.e. strongly measurable (AEStronglyMeasurable.comp_quasiMeasurePreserving). (h) Orientation: for y ∈ φ(G), x := ψ(y) ∈ G, and by step 3 ξ'(y) = J(x)^{-1} ζ(x) is a unit orientation of Dφ(x)Q(x), which is an approximate tangent plane of M' at y = φ(x) by (G). M' ∖ φ(G) = φ(M ∖ G) has H^n-measure ≤ Λ^n · 0 = 0, so this holds for μ'-a.e. y. Thus R' := (M', θ', ξ') is an IMRep U n.
6. The action. Fix ω ∈ 𝒟^n(U); let h(y) := θ'(y) ξ'(y)(ω(y)) and g_ω(x) := θ(x) ξ(x)(ω(φ(x))∘Dφ(x)) = θ(x) ζ(x)(ω(φ(x))).
 (a) For x ∈ G: J(x) h(φ(x)) = J(x) θ(x) J(x)^{-1} ζ(x)(ω(φ(x))) = g_ω(x) since J(x) > 0 and ψ(φ(x)) = x. Since J ≥ 0, J·(h∘φ)⁺ = (g_ω)⁺, J·(h∘φ)⁻ = (g_ω)⁻ and J·|h∘φ| = |g_ω| μ-a.e. (positive and negative parts).
 (b) g_ω is μ-integrable: it is μ-a.e. strongly measurable (θ measurable, ξ μ-a.e. strongly measurable, x ↦ ω(φ(x))∘Dφ(x) continuous, evaluation continuous), and for μ-a.e. x, |g_ω(x)| ≤ θ(x)‖ω‖_∞ Λ^n 1_{ψ(tsupport ω)}(x) (|ξ(x)(β)| ≤ ‖β‖ because ξ(x) = ±evaluation at an orthonormal frame, by (O); ‖β∘L‖ ≤ ‖β‖‖L‖^n; ω(φ(x)) = 0 unless x ∈ ψ(tsupport ω), a compact subset of U), which is integrable by R.locallyIntegrable_mult.
 (c) h is μ'-integrable: it is μ'-a.e. strongly measurable (θ' measurable, ξ' a.e. strongly measurable by 5(g), ω continuous, evaluation continuous), and by (H) with g := ‖h‖₊ and (a), ∫⁻_{M'} |h| dH^n = ∫⁻_M J |h∘φ| dH^n = ∫⁻_M |g_ω| dH^n < ∞ by (b).
 (d) By (H) applied to g := ofReal(h⁺) and to g := ofReal(h⁻), and (a): ∫⁻_{M'} h^± dH^n = ∫⁻_M J (h∘φ)^± dH^n = ∫⁻_M (g_ω)^± dH^n. For integrable real functions ∫ f = ∫⁻ f⁺ − ∫⁻ f⁻ (integral_eq_lintegral_pos_part_sub_lintegral_neg_part), so R'.action(ω) = ∫_{M'} h dH^n = ∫_M g_ω dH^n = ∫_M θ(x) ξ(x)(ω(φ(x))∘Dφ(x)) dH^n(x).
7. Dimension zero needs no change: for n = 0, Q(x) = {0}, J = 1, β∘Dφ(x) = β for 0-covectors, so ζ = ξ and ξ' = ξ∘ψ.

## Key steps

1. ψ = φ^{-1} is Lipschitz, φ(U) = U, φ and ψ change H^n by at most Λ^n; θ ≥ 1 makes M locally H^n-finite.
2. Siblings give, a.e. on M: T_{φx}φ(M) = Dφ(x)T_xM, the area formula with J, a.e. measurability of J, and (with R.orients and uniqueness) 0 < J ≤ Λ^n and J^{-1}ζ orients Dφ(x)T_xM.
3. Define R' := (φ(M), θ∘ψ, (J^{-1}ζ)∘ψ) and verify every IMRep field (Borel, rectifiable, local integrability via the area formula, measurability via quasi-measure-preservation of ψ, a.e. orientation).
4. J·(h∘φ) = g_ω a.e. on M; the area formula on positive and negative parts gives R'.action ω = ∫_M g_ω.

## Reference use

### local-project

Queries:
- `python3 -I read of local-references/123e8435b4a2469b/manifest.json and local-references/123e8435b4a2469b/project/lake-manifest.json package revs; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -rn -E 'theorem (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|ae_tendsto_measure_inter_div|normDet_sq_eq_det_gram|normDet_comp|normDet_of_subsingleton|lintegral_iUnion|contDiff_symm|hasFDerivAt_convolution_right|contDiff_convolution_left|image_of_continuousOn_injOn)\b' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn -E 'theorem [A-Za-z.]*(image_of_continuousOn_injOn|contDiff_symm|hausdorffMeasure_image_le|euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_homothety_image|ae_tendsto_average_norm_sub|integral_eq_lintegral_pos_part_sub_lintegral_neg_part)\b' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn -E 'theorem (weighted_area_formula_lipschitz_injOn|HasApproximateTangentSpaceAt.unique|area_image_compl_regularSet_eq_zero|measurableSet_areaRegularSet|measurable_areaJacobianAt|exteriorDerivativeOn_pullbackFormWithin)\b|def (CountablyRectifiable|HasApproximateTangentSpaceAt|areaJacobianAt|areaRegularSet|blowUpMap)\b' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn -i -E '^(theorem|noncomputable def|def) .*pushforward' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06`
- `sed -n 60,140p GMT/Ch07/Submission.lean (IMRep fields, IMRep.action, IMRep.Represents, IsIntegerMultiplicity, BoundaryVanishes); grep -n 'def contract_scope' -A70 verifier/gmt-compare.py`
- `python3 -I scans of dag.json at 11:41:46Z and 11:55:52Z: status, candidate_commit, depends_on and frozen lean_statement of the 7 reused and 4 mirrored declarations and the subtree of root.minimizing_implies_stationary-a1.diffeo_pushforward-a1; lean_name hits for the 4 fresh names`
- `python3 -I diff of nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-v2.json subproblems against the 11 original parent-child-handoff.json files; equality check of /tmp/dpf-v3-check/final.json against decomposition-v2.json (all 11 children identical in every field)`
- `git show <candidate>:GMT/Ch07/Submission.lean for b44fe315b2 3de784c0d8 6b000c3693 74a1c6be70 a2ba78fca3 ee75447541 863f6d9cf6 36b2d37204: exact 'theorem Submission.<name> : <frozen type> :=' text found, one declaration each`
- `grep -rlE 'codim1_ldr_dpf_(approxTangent_ae_bilipschitz_piece|approxTangent_bilipschitz_image_ae|area_formula_bilipschitz_rectifiable|imrep_bilipschitz_image_rep)' over dag.json, nodes/*/decomposition-v*.json, GMT, .lake/packages/simongmt/Poincare, local-references/123e8435b4a2469b/project and local-references/123e8435b4a2469b/mathlib/Mathlib; /tmp/dpf-v3-scripts/refgrep.sh (git grep -l -E with the refs before the 'GMT/*.lean' pathspec) over all 4166 refs/heads and refs/remotes: 0 hits; positive control dpf_rectifiable_bilipschitz_pieces: 8 hits`
- `grep -n 'subproblem decomposition attempt|def _decompose|def _solve_children|def _existing_lean_name_problem|def _accepted_checkpoint|def _install_parent_supplied_child_handoff' /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py; sed -n 1,200p /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/decomposition_scope.py`
- `tail cluster-state/logs/gmt-ch07/30a94ba245764a7ba1e5ac06b265b8e7.log 2ee9f278722846438e9834336e81985e.log 9afc789922184ff18c490ae355f8dbcb.log; python3 -I issue-workers.json entries for issue 4957; python3 -I read of swarm-configs/9afc789922184ff18c490ae355f8dbcb.json (max_depth 6, max_children 12, max_nodes 5000)`
- `lake env lean -DautoImplicit=false /tmp/dpf-v3-check/Check.lean (exit 0); /tmp/dpf-v3-check/Cond.lean (exit 0; #print axioms: propext, Classical.choice, Quot.sound); /tmp/dpf-v3-check/Wiring.lean (exit 0; same axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dceb540ffc/decomposition-scope-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-686bf23105/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-db3aef81cd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-smooth-ap-e30aa8106d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-b3d596d026/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-4eba0cda06/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-rectifiab-d698709751/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-jacobian-d0fc2e675e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-f9454fcfd5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-89b1ce4202/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/9afc789922184ff18c490ae355f8dbcb.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/30a94ba245764a7ba1e5ac06b265b8e7.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/2ee9f278722846438e9834336e81985e.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/9afc789922184ff18c490ae355f8dbcb.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/decomposition_scope.py`
- `/tmp/dpf-v3-check/Check.lean`
- `/tmp/dpf-v3-check/Cond.lean`
- `/tmp/dpf-v3-check/Wiring.lean`
- `/tmp/dpf-v3-check/final.json`

Pins match.
- The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib.
- The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt.
- The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library. Every Mathlib and SimonGMT lemma the child proofs cite exists at the pinned revisions:
- Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255); the Besicovitch, DensityTheorem and Differentiation density theorems; normDet_sq_eq_det_gram, normDet_comp, normDet_of_subsingleton and euclideanHausdorffMeasure_image; lintegral_iUnion; MeasurableSet.image_of_continuousOn_injOn; LipschitzWith.hausdorffMeasure_image_le; Homeomorph.contDiff_symm.
- SimonGMT: weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet, measurable_areaJacobianAt, HasApproximateTangentSpaceAt.unique, exteriorDerivativeOn_pullbackFormWithin.
- SimonGMT Chapter06 has only nVectorPushforward and the affine current push-forward, and no C¹ integer-multiplicity push-forward theorem, so the split is needed.
DAG (11:55:52Z, 1031 nodes).
- The 7 reused declarations are accepted with candidate commits. Each has a byte-identical frozen type, declared exactly once in its candidate, and matching depends_on.
- The 4 originals are still speculative-ready, so their mirrors get the fresh codim1_ldr_ names.
- The fresh names have 0 hits in the DAG, other proposals, sources, the snapshot and all 4166 refs (positive control: 8 hits).
Runtime. v1 and v2 were returned by _decompose (scope files written), but their workers stopped before activation. _install_parent_supplied_child_handoff returns early for accepted checkpoints.
Lean.
- All 11 child types, the dependency type and the parent type elaborate.
- The assembly proves the exact parent type from four child types plus the dependency, using only propext, Classical.choice and Quot.sound.
- All sibling applications used by the child proofs typecheck.
- The submitted children equal decomposition-v2.json in every field.
