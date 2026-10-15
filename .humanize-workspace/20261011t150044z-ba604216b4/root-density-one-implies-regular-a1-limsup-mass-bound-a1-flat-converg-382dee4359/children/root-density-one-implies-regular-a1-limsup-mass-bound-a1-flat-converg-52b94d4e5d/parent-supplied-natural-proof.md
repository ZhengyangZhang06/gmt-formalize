# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.isometric_pushforward-a1.tangent_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent-supplied proof (approximate tangent spaces are transported). It combines Simon Ch. 3, 1.4 (the definition of the approximate tangent space, here SimonGMT HasApproximateTangentSpaceAt) with the Jacobian-one change of variables. Cf. T_y(f(M)) in Simon Ch. 6, 3.7 (book/chapter-06.txt lines 823–835).
1. Dimension. L is injective: Lw = Lw' gives |w − w'| = |Lw − Lw'| = 0. So L restricted to S is a linear isomorphism of S onto S.map L (Submodule.equivMapOfInjective). Hence dim(S.map L) = dim S (LinearEquiv.finrank_eq), and dim S = d by the first clause of the hypothesis.
2. Blow-ups commute with L. Let r ∈ ℝ and w ∈ ℝ^P. By linearity (map_sub, map_smul), blowUpMap (Lx) r (Lw) = r⁻¹ • (Lw − Lx) = L(r⁻¹ • (w − x)) = L(blowUpMap x r w). This holds for every real r, including r ≤ 0, because it is an identity between linear expressions. Taking images (Set.image_image), blowUpMap (Lx) r '' (L '' M) = L '' (blowUpMap x r '' M) for every r.
3. Pulling back the test function. Fix f ∈ C_c(ℝ^Q) and set g := f∘L. Then g is continuous. It also has compact support: L is a closed embedding (Isometry.isClosedEmbedding, ℝ^P complete), and a compactly supported function composed with a closed embedding is compactly supported (HasCompactSupport.comp_isClosedEmbedding). Concretely, tsupport g ⊆ L⁻¹(tsupport f), and this set is compact because closed embeddings are proper. So g ∈ C_c(ℝ^P).
4. Change of variables. Apply part (iii) of the sibling change_of_variables (Submission.dor_lmb_fc_dtop_ip_isometry_change_of_variables) to the isometry ⇑L. For every A ⊆ ℝ^P it gives ∫_{L(A)} f dHᵈ = ∫_A f(Lw) dHᵈ(w) = ∫_A g dHᵈ.
 With A = blowUpMap x r '' M and step 2, for every r ∈ ℝ: ∫_{blowUpMap (Lx) r '' L(M)} f dHᵈ = ∫_{blowUpMap x r '' M} g dHᵈ.
 With A = S, using that the underlying set of S.map L is L(S) (Submodule.map_coe): ∫_{S.map L} f dHᵈ = ∫_S g dHᵈ.
5. Conclusion. The second clause of HasApproximateTangentSpaceAt d M x S, applied to g ∈ C_c(ℝ^P), gives ∫_{blowUpMap x r '' M} g dHᵈ → ∫_S g dHᵈ as r → 0⁺ (along 𝓝[>] 0). By step 4 the function r ↦ ∫_{blowUpMap (Lx) r '' L(M)} f dHᵈ equals r ↦ ∫_{blowUpMap x r '' M} g dHᵈ for all r, and ∫_{S.map L} f dHᵈ = ∫_S g dHᵈ. Hence ∫_{blowUpMap (Lx) r '' L(M)} f dHᵈ → ∫_{S.map L} f dHᵈ as r → 0⁺. Since f ∈ C_c(ℝ^Q) was arbitrary, this and step 1 prove HasApproximateTangentSpaceAt d (L '' M) (Lx) (S.map L). ∎

## Key steps

1. dim L(S) = dim S = d because L is injective.
2. blowUpMap (Lx) r ∘ L = L ∘ blowUpMap x r for every r, so the blow-up of L(M) at Lx is L applied to the blow-up of M at x.
3. For f ∈ C_c(ℝ^Q), f∘L ∈ C_c(ℝ^P) because L is a closed embedding.
4. The sibling change_of_variables turns the blow-up integrals and the limit ∫_{L(S)} f into the corresponding integrals of f∘L, so the hypothesis applied to f∘L gives the claim.

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
