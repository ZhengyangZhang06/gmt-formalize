# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1.image_imrep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 2, 5, 6 and the measure computation of step 7 of the parent-supplied proof. These are Simon Ch. 6, 2.23–2.24 and 3.3–3.9 (book/chapter-06.txt lines 403–436 and 765–870) for the injective map L with Jacobian J_L ≡ 1. In that case 3.8 reduces to the multiplicity θ(L⁻¹y) and the orientation L_#ξ(L⁻¹y). The accepted dtc_blowUp_imrep (for similarities of ℝ^P) has the same structure.
1. Facts about L.
(a) Apply the sibling change_of_variables (Submission.dor_lmb_fc_dtop_ip_isometry_change_of_variables) to the isometry f := ⇑L. It gives:
 - L is a measurable embedding;
 - (Hᵈ⌞A).map L = Hᵈ⌞L(A) for every A ⊆ ℝ^P;
 - ∫_{L(A)} g dHᵈ = ∫_A g∘L dHᵈ for every g : ℝ^Q → ℝ;
 - ∫⁻_{L(A)} g dHᵈ = ∫⁻_A g∘L dHᵈ for every g : ℝ^Q → [0, ∞].
(b) L0 = 0, so |Lx| = |x| (Isometry.norm_map_of_map_zero). Thus L is a linear isometry and ⟨Lx, Ly⟩ = ⟨x, y⟩ for all x, y (LinearIsometry.inner_map_map).
(c) A continuous linear left inverse. Let L⁺ := L* : ℝ^Q → ℝ^P be the adjoint (ContinuousLinearMap.adjoint; both spaces are complete). For x, y ∈ ℝ^P, ⟨L*(Lx), y⟩ = ⟨Lx, Ly⟩ = ⟨x, y⟩ (ContinuousLinearMap.adjoint_inner_left and (b)). Hence L⁺(Lx) = x (ext_inner_right).
(d) L is a closed embedding (Isometry.isClosedEmbedding), hence a proper map (Topology.IsClosedEmbedding.isProperMap). So L⁻¹(K) is compact for every compact K ⊆ ℝ^Q (IsProperMap.isCompact_preimage).
(e) Let C := L^* = ContinuousAlternatingMap.compContinuousLinearMapCLM L. This is the continuous linear map β ↦ β(L·, …, L·) from d-covectors of ℝ^Q to d-covectors of ℝ^P. The map Φ : MultiVector P d → MultiVector Q d, ζ ↦ ζ∘C, is continuous (Continuous.clm_comp applied to continuous_id and the constant C).
2. Definition of R'. Write R = (M, θ, ξ). Let R' have carrier L(M), multiplicity θ'(y) := θ(L⁺y) and orientation ξ'(y) := ξ(L⁺y)∘C. By 1(c), for every x ∈ ℝ^P, θ'(Lx) = θ(x) and ξ'(Lx) = ξ(x)∘C = Φ(ξ(x)).
3. R' is an IMRep in univ ⊆ ℝ^Q. We check the fields of the contract structure IMRep univ d.
(a) measurableSet_carrier: M is Borel and L is a measurable embedding (1(a)), so L(M) is Borel (MeasurableEmbedding.measurableSet_image). carrier_subset: L(M) ⊆ univ.
(b) rectifiable: CountablyRectifiable d M gives M₀ with Hᵈ(M₀) = 0 and Lipschitz maps F_j : ℝ^d → ℝ^P (j ∈ ℕ) with M ⊆ M₀ ∪ ⋃_j range F_j. Use L(M₀) and the maps L∘F_j. First, Hᵈ(L(M₀)) = Hᵈ(M₀) = 0 (Isometry.euclideanHausdorffMeasure_image). Second, each L∘F_j is Lipschitz, since L is 1-Lipschitz (Isometry.lipschitzWith). Third, L(M) ⊆ L(M₀) ∪ ⋃_j range(L∘F_j): if x ∈ M then x ∈ M₀ or x = F_j(v), so Lx ∈ L(M₀) or Lx = (L∘F_j)(v).
(c) measurable_mult: θ' = θ∘L⁺ is measurable, since θ is measurable and L⁺ is continuous.
(d) mult_pos: if y ∈ L(M), say y = Lx with x ∈ M, then θ'(y) = θ(L⁺(Lx)) = θ(x) > 0.
(e) locallyIntegrable_mult: let K ⊆ ℝ^Q be compact (K ⊆ univ). Since L(M) ∩ K = L(M ∩ L⁻¹(K)) (Set.image_inter_preimage), 1(a) gives ∫⁻_{L(M)∩K} θ' dHᵈ = ∫⁻_{M∩L⁻¹(K)} θ'(Lx) dHᵈ(x) = ∫⁻_{M∩L⁻¹(K)} θ dHᵈ. This is finite by locallyIntegrable_mult of R, because L⁻¹(K) is compact (1(d)) and contained in univ.
(f) aestronglyMeasurable_orient: by 1(a), Hᵈ⌞L(M) = (Hᵈ⌞M).map L. Since L is a measurable embedding, h is a.e.-strongly measurable for (Hᵈ⌞M).map L iff h∘L is a.e.-strongly measurable for Hᵈ⌞M (MeasurableEmbedding.aestronglyMeasurable_map_iff). Here ξ'∘L = Φ∘ξ (step 2). This composes the continuous Φ (1(e)) with ξ, which is Hᵈ⌞M-a.e.-strongly measurable (aestronglyMeasurable_orient of R). Hence it is a.e.-strongly measurable (Continuous.comp_aestronglyMeasurable).
(g) orients: by orients of R, for Hᵈ⌞M-a.e. x there is a subspace S of ℝ^P with HasApproximateTangentSpaceAt d M x S and IsUnitOrientationOf (ξ(x)) S. For such x:
 - the sibling tangent_transport (Submission.dor_lmb_fc_dtop_ip_approxTangent_isometry) gives HasApproximateTangentSpaceAt d (L(M)) (Lx) (S.map L);
 - the sibling orientation_transport (Submission.dor_lmb_fc_dtop_ip_unitOrientation_isometry) gives IsUnitOrientationOf (ξ(x)∘C) (S.map L), and ξ(x)∘C = ξ'(Lx) by step 2.
 Let p(y) be the property ∃ S', HasApproximateTangentSpaceAt d (L(M)) y S' ∧ IsUnitOrientationOf (ξ'(y)) S'. Then p(Lx) holds for Hᵈ⌞M-a.e. x. Since Hᵈ⌞L(M) = (Hᵈ⌞M).map L and L is a measurable embedding, MeasurableEmbedding.ae_map_iff (no measurability of p required) gives p(y) for Hᵈ⌞L(M)-a.e. y.
4. R' represents L#T. Let ω ∈ 𝒟^d(ℝ^Q) = TestFormOn univ d.
 By definition of the push-forward (GeometricCurrentOn.affinePushforward_apply, which holds by rfl), L#T(ω) = T(L^#ω), where L^#ω = affinePullbackTestOn L 0 hL univ d ω. This is a test form on (x ↦ 0 + Lx)⁻¹(univ), which is definitionally univ. So L^#ω is an element of TestFormOn univ d, and the representation hypothesis of R applies to it: L#T(ω) = R.action(L^#ω).
 In Lean, state this identity as `have h1 : (GeometricCurrentOn.affinePushforward (V := (univ : Set (Euclid Q))) L 0 hL T) ω = R.action (affinePullbackForm L 0 (ω : DifferentialForm (Euclid Q) d)) := hR (affinePullbackTestOn L 0 hL univ d ω)`, which typechecks by definitional unfolding. Do not use `rw [GeometricCurrentOn.affinePushforward_apply]`: it fails because the domain change is only definitional.
 As a form, L^#ω(x) = affinePullbackForm L 0 ω x = (ω(0 + Lx)).compContinuousLinearMap L = C(ω(Lx)), using 0 + Lx = Lx. Define g(y) := θ'(y)·ξ'(y)(ω(y)). By step 2, for every x ∈ ℝ^P the integrand of R.action(L^#ω) is θ(x)·ξ(x)(C(ω(Lx))) = θ'(Lx)·ξ'(Lx)(ω(Lx)) = g(Lx).
 Hence R.action(L^#ω) = ∫_M g∘L dHᵈ = ∫_{L(M)} g dHᵈ by 1(a) with A = M, and the right side is R'.action(ω) by definition. So L#T(ω) = R'.action(ω) for every ω, i.e. R' represents L#T.
5. The measure. Let s ⊆ ℝ^Q be Borel. Then L⁻¹(s) is Borel because L is continuous. By definition μ_{R'} = (Hᵈ⌞L(M)).withDensity θ' and μ_R = (Hᵈ⌞M).withDensity θ. Then:
 μ_{R'}(s) = ∫⁻_s θ' d(Hᵈ⌞L(M)) (withDensity_apply)
 = ∫⁻_s θ' d((Hᵈ⌞M).map L) (1(a))
 = ∫⁻ θ' d(((Hᵈ⌞M)⌞L⁻¹(s)).map L) (MeasurableEmbedding.restrict_map)
 = ∫⁻ θ'∘L d((Hᵈ⌞M)⌞L⁻¹(s)) (MeasurableEmbedding.lintegral_map)
 = ∫⁻_{L⁻¹(s)} θ d(Hᵈ⌞M) (θ'∘L = θ by step 2)
 = μ_R(L⁻¹(s)) (withDensity_apply).
6. Steps 3–5 show that R' is an IMRep in univ ⊆ ℝ^Q that represents L#T and satisfies μ_{R'}(s) = μ_R(L⁻¹(s)) for every Borel s ⊆ ℝ^Q. ∎

## Key steps

1. Facts about L: change of variables (sibling change_of_variables), ⟨Lx, Ly⟩ = ⟨x, y⟩, the adjoint L* as a continuous linear left inverse, properness of L, and continuity of ζ ↦ ζ∘L^*.
2. R' := (L(M), θ∘L*, (ξ∘L*)∘L^*), so θ'(Lx) = θ(x) and ξ'(Lx) = ξ(x)∘L^*.
3. IMRep fields of R': Borel image; rectifiable cover by L(M₀) and L∘F_j; measurable, positive and locally integrable multiplicity via the change of variables and compact L⁻¹(K); a.e.-measurable orientation via aestronglyMeasurable_map_iff; a.e. orientation of L(S) via ae_map_iff with the siblings tangent_transport and orientation_transport.
4. Representation: L#T(ω) = R.action(L^#ω) by definitional unfolding; the integrand is g∘L with g = θ'·ξ'(ω), so the change of variables gives R'.action ω.
5. Measure: withDensity_apply, restrict_map and lintegral_map give μ_{R'}(s) = μ_R(L⁻¹(s)) for Borel s.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean <workspace>/GMT/Ch07/Submission.lean (identical)`
- `rg -n "dtop_ip_|isometry_change_of_variables|approxTangent_isometry|unitOrientation_isometry|image_imrep" <snapshot>/project .lake/packages/simongmt --glob '*.lean' (no match)`
- `rg -n -i "isometr" and rg -n "affinePushforward" <snapshot>/project/GMT --glob '*.lean' (only Ch05 rotated-plane docstrings and the Ch07 contract's blowUp)`
- `read SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt), Chapter06/AffineCurrentPushforward.lean (affinePullbackForm, affinePullbackTestOn, affinePushforward_apply rfl), Chapter06/Mass.lean (massOn, mass = massOn U), Chapter06/Forms.lean and Currents.lean`
- `rg Isometry.map_euclideanHausdorffMeasure / Isometry.euclideanHausdorffMeasure_image in <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (lines 131, 141)`
- `rg MeasurableEmbedding.restrict_map, ae_map_iff, restrict_restrict_of_subset, integral_map, lintegral_map, aestronglyMeasurable_map_iff, IsClosedEmbedding.measurableEmbedding, Isometry.isClosedEmbedding, Isometry.lipschitzWith, IsClosedEmbedding.isProperMap, HasCompactSupport.comp_isClosedEmbedding, Orthonormal.comp_linearIsometry, adjoint_inner_left, span_image, equivMapOfInjective, Continuous.clm_comp, withDensity_apply, setIntegral_congr_fun, image_inter_preimage in <snapshot>/mathlib/Mathlib`
- `python3 -I scans of the run's dag.json (1552 nodes): HasApproximateTangentSpaceAt / IsUnitOrientationOf / Isometry / affinePushforward statements and the types of dtc_blowUp_imrep, dtc_hausdorff_dilation, dtc_approxTangent_dilation, dpfir_bilipschitz_image_imrep_exists, dpf_approxTangent_bilipschitz_image_ae, dpf_unitOrientation_map_gramNormalized, codim1_rdo_gc_unitOrientation_isometry, dor_imrep_massOn_eq_measure_and_support; collision check of the four new lean_names`
- `git show 047b3402ecebcae7b968f8ca435cbbb0b9ed036f:GMT/Ch07/Submission.lean (lines 455-740, accepted dtc_blowUp_imrep template)`
- `sed -n 395,440p and 765,880p book/chapter-06.txt (Simon 6.2.23-2.24, 6.3.3-3.9)`
- `python3 -I gen.py: gmt-compare.py child_modules (contract scope) + lean_contract.validate_lean_statement on the four types; lake env lean /tmp/isopf-decomp/challenges/Challenge_*.lean and /tmp/isopf-decomp/lean/{Stmts,Assembly,Full,SolutionCheck,Names}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-382dee4359/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-b4c8dbc0a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/isopf-decomp/lean/Full.lean`
- `/tmp/isopf-decomp/lean/SolutionCheck.lean`

Snapshot: project b4d606db and Mathlib 25730c7c. Its Ch07 Contract.lean is byte-identical to the workspace Submission.lean.

No-match results:
- No snapshot or SimonGMT declaration transports Hausdorff measure, approximate tangent spaces, unit orientations or IMReps along a linear isometric embedding ℝ^P → ℝ^Q.
- Accepted DAG lemmas only treat self-maps of ℝ^P (dilations, bi-Lipschitz/C¹ diffeomorphisms) or plane parametrisations, so none can be reused for P ≠ Q.
- None of the four new names occurs in dag.json, the snapshot or SimonGMT.

The children use only snapshot Mathlib:
- Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, Isometry.isClosedEmbedding;
- the MeasurableEmbedding API (restrict_map, integral_map, lintegral_map, ae_map_iff, aestronglyMeasurable_map_iff);
- HasCompactSupport.comp_isClosedEmbedding, Orthonormal.comp_linearIsometry, Submodule.span_image, ContinuousLinearMap.adjoint.

From SimonGMT they use affinePullbackForm, affinePullbackTestOn and affinePushforward_apply.

The accepted dtc_blowUp_imrep is the structural template.

Lean results:
- All four child types compile as the exact comparator challenges.
- Full proofs of all four children check with only propext, Classical.choice and Quot.sound.
- The exact selected type follows in 7 lines from image_imrep and the accepted dor_imrep_massOn_eq_measure_and_support.
