# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.high_degree_case-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0 of the parent proof ("If n > P, every n-covector on ℝ^P vanishes, so S = 0; then S₀ := 0 satisfies (c) (both supports are empty, both densities are 0 everywhere) and (a), (b) are trivial"), with the details written out. Write d := dim L and m := n − d.
1. (Covectors of degree > P vanish.) Let k > P and α ∈ Covector(ℝ^P, k), a continuous alternating k-linear form on ℝ^P. For any v_1, …, v_k ∈ ℝ^P the family (v_i) is linearly dependent because k > P = dim ℝ^P, and an alternating multilinear map vanishes on every linearly dependent family (Mathlib AlternatingMap.map_linearDependent, applied to α.toAlternatingMap). Hence α = 0.
2. (Currents of degree > P vanish.) Let U ⊆ ℝ^P and T ∈ 𝒟_k(U) with k > P. Every ω ∈ 𝒟^k(U) = TestFormOn U k is a function with values in Covector(ℝ^P, k), so ω(x) = 0 for every x by step 1; hence ω is the zero element of the submodule TestFormOn U k and T ω = T 0 = 0 because T.toCurrent is linear. By extensionality (GeometricCurrentOn.ext), T = 0. In particular S = 0.
3. (Proof of (a) and (b).) For x ∈ ℝ^P and λ ≠ 0, blowUp S x λ is a current of degree n > P in dilation x λ '' univ, hence the zero current by step 2. By definition currentEval T ω equals either T⟨ω, h⟩ or 0; for T = blowUp S x λ both are 0. Since S ω = 0 as well, currentEval (blowUp S x λ h) ω = S ω for all x, λ ≠ 0, ω. Taking x = 0 and λ > 0 gives IsConeCurrent S; taking x = −v (v ∈ L) and λ = 1 gives (b).
4. (Zero currents.) Fix a degree j and let 0 ∈ GeometricCurrentOn univ j.
(i) Mass: for every W, (0).massOn W = sSup {ofReal((0)(ω)) : ω ∈ massAdmissibleOn univ j W} = sSup {0} = 0; the set is exactly {0} because it is nonempty (the zero form is admissible: tsupport 0 = ∅ ⊆ W and its Euclidean norm is 0 ≤ 1).
(ii) Integer multiplicity: the triple R₀ with carrier ∅, mult ≡ 0 and orient ≡ 0 is an IMRep univ j: ∅ is Borel and contained in univ; it is countably j-rectifiable because H^j(∅) = 0 (countablyRectifiable_of_measure_zero); the constant multiplicity is measurable; mult_pos is vacuous; ∫⁻_{∅ ∩ K} mult dH^j = 0 ≠ ∞; the constant orientation is a.e. strongly measurable; the remaining a.e. condition refers to H^j⌞∅ = 0 and is vacuous. Its action is ∫_∅ (…) dH^j = 0 = (0)(ω) for every ω, so R₀ represents 0 and 0 is integer multiplicity.
(iii) Minimality: IsMinimizingIn 0 univ holds by (ii) and because (0).massOn W = 0 ≤ S'.massOn W for every competitor S' (by (i)).
(iv) Boundary: BoundaryVanishes 0 is True if j = 0; if j = j' + 1 then (0).boundary ω = (0)(dω) = 0 for every ω ∈ 𝒟^{j'}(ℝ^P), so (0).boundary = 0 by extensionality.
(v) Cone: for λ > 0, unfolding blowUp (restrictDomain followed by affinePushforward), every value of blowUp 0 0 λ is the zero current applied to a pulled-back test form, hence 0; so currentEval (blowUp 0 0 λ) ω = 0 = (0)(ω).
(vi) Support: (0).support = univ ∖ zeroRegion(0) = ∅. Indeed every x lies in the open ball B_1(x), whose closure B̄_1(x) is compact (ℝ^P is proper) and contained in univ, and 0 vanishes on B_1(x); so x ∈ zeroRegion(0).
(vii) Densities: by (i) the quotient in HasMassDensity is 0 / (ω_j ρ^j) = 0 for every ρ (ENNReal.zero_div). As 𝓝[>] 0 is a nontrivial filter on ℝ and ℝ≥0∞ is Hausdorff, Tendsto (fun _ => 0) (𝓝[>] 0) (𝓝 (ofReal θ)) holds iff ofReal θ = 0, i.e. iff θ ≤ 0. Hence HasMassDensity 0 x θ ⟺ (0 ≤ θ ∧ θ ≤ 0) ⟺ θ = 0, for every x and every degree j.
5. (Proof of (c).) Put S₀ := 0 ∈ GeometricCurrentOn univ m. By step 4 (iii)–(v), S₀ is minimizing in ℝ^P, BoundaryVanishes S₀ and S₀ is a cone. By (vi), spt S₀ = ∅ ⊆ L^⊥, and, since S = 0 (step 2), spt S = ∅ as well, so for t ∈ L, y ∈ L^⊥ both t + y ∈ spt S and y ∈ spt S₀ are false and hence equivalent. By (vii) applied in degrees n (to S = 0) and m (to S₀): HasMassDensity S (t + y) θ ⟺ θ = 0 ⟺ HasMassDensity S₀ y θ. Together with step 3 this proves (a), (b) and (c).

## Key steps

1. An alternating form of degree k > P on ℝ^P vanishes, so every test k-form is zero and every current of degree k > P is 0; hence S = 0 and all blow-ups of S are 0, giving (a) and (b).
2. The zero current of any degree has zero mass, is integer multiplicity via the empty IMRep, is minimizing, is a cycle and a cone, and has empty support.
3. For zero currents HasMassDensity x θ ⟺ θ = 0, so with S₀ := 0 both support and density equivalences of (c) hold.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n '^theorem\|^def\|^structure\|^abbrev' simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward,WedgeForms,Product,GeometricPointProduct,Representation}.lean; sed -n 25,140p simongmt Chapter03/Rectifiable.lean`
- `sed -n 40,160p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] definition, euclideanHausdorffMeasure_zero, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_smul₀)`
- `grep -n 'ae_tendsto_average_norm_sub\|exists_disjoint_subfamily_covering_enlargement_closedBall\|map_linearDependent\|starProjection_eq_self_iff\|hausdorffMeasure_smul₀' in the snapshot mathlib`
- `sed -n 340,430p book/chapter-07.txt (Simon 7.3.1 with footnote 2, Remark 7.3.4, Lemma 7.3.5 'left to the reader')`
- `python3 inspection of dag.json: sibling frozen types (dimred_im_mass_measure, dimred_minimizing_monotonicity), accepted lemmas in other branches (imrep_univ_tangent_starProjection_aemeasurable, dtc_cone_wedge_vanishes, dtc_cone_euler_cartan, unit_orientation_norm_le_one, stationary_imrep_radial_tangency_of_ball_ratio), duplicate lean_name scan, reuse precedent in cone_lemma-a1/decomposition-v1.json`
- `grep -c dimred_cs_ dag.json; grep -rl dimred_cs_ GMT .lake/packages/simongmt/Poincare; grep -rl dimred_cs_ --include=*.lean .swarm-worktrees (no match anywhere)`
- `git cat-file -t 74a7d91… 9203aee… 77ba671… 0325970… (all commits present)`
- `lake env lean /tmp/cs-decomp/CheckV2.lean (12 child types as Submission.X in namespace GMT.Ch07 with the contract opens, stubs of minimizing_implies_stationary, dimred_im_mass_measure, dimred_minimizing_monotonicity, assembly of dimred_invariant_cone_splitting, #print axioms, pp.coercions #check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-tangent-projection-aemeasurable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-wedge-vanishes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-child-handoff.json`
- `/tmp/cs-decomp/CheckV2.lean`

The pins match: the snapshot is at project b4d606d (= workspace HEAD) and mathlib 25730c7c, and SimonGMT is at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

What the library lacks. SimonGMT provides geometric currents, boundary, massOn, support and the proper affine push-forward. It provides no slicing, no Cartesian products of currents, no IMRep push-forward, no homotopy formula, and no mass–measure identity for the contract's IMRep. WedgeForms is not imported by the contract. Therefore no child type may mention products or wedges; the product structure is passed as a measure identity, and the heavy constructions stay inside the proofs of split_off_spine and subspace_projection.

Mathlib facts used, all present in the snapshot:
- μHE[0] = μH[0] (counting measure);
- μHE[d] is invariant under isometries and satisfies the scaling law euclideanHausdorffMeasure_smul₀;
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall;
- VitaliFamily.ae_tendsto_average_norm_sub;
- AlternatingMap.map_linearDependent;
- Submodule.starProjection_eq_self_iff.

Reuse. Four comparator-accepted declarations from other branches are reused, with types byte-identical to dag.json: imrep_univ_tangent_starProjection_aemeasurable, dtc_cone_wedge_vanishes, dtc_cone_euler_cartan and unit_orientation_norm_le_one.

No reuse. stationary_imrep_radial_tangency_of_ball_ratio is accepted but covers only centre 0. The centre-z identity dtc_cone_monotonicity_identity and the cone criterion dtc_cone_of_wedge_vanishing are not accepted. So spine_tangency and cone_of_radial_tangency are new children under unique dimred_cs_ names.

Lean check. All 12 child types elaborate, and the assembly of the frozen dimred_invariant_cone_splitting type from them typechecks with only the stub sorries.
