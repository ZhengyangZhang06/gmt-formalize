# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.spine_tangency-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (T6: the monotonicity identity of Simon Ch. 4, 3.6 for the stationary V forces x − z ∈ T_xM a.e. for z ∈ L, then a countable dense subset of L), with the monotonicity identity derived from the first variation as in Simon Ch. 4, 3.2–3.4. Notation: μ = R.measure = θ·H^n⌞M, T_x = approxTangentPlane n M x, p_x its orthogonal projection.
1. (Constant ratios at points of L.) Let z ∈ L and ρ > 0. B̄_ρ(z) = (fun x => (−z) + x)⁻¹' B̄_ρ(0) with −z ∈ L, so μ(B̄_ρ(z)) = μ(B̄_ρ(0)) by the translation hypothesis; and B̄_ρ(0) = (fun x => ρ • x) '' B̄_1(0), so μ(B̄_ρ(0)) = ρ^n μ(B̄_1(0)) by homogeneity. Put c := μ(B̄_1(0)) < ∞ (μ is finite on compact sets by the field locallyIntegrable_mult). Then μ(B̄_ρ(z)) = c ρ^n for all ρ > 0 and all z ∈ L.
2. (Tangent planes.) For H^n-a.e. x ∈ M, hence for μ-a.e. x (μ ≪ H^n⌞M), M has an approximate tangent space Q at x (field orients); approximate tangent spaces are unique (Simon Ch. 3, 1.4: H^n⌞Q is the weak limit of the blow-ups H^n⌞η_{x,r}(M), and Q = spt(H^n⌞Q)), so T_x = Q has dimension n and trace p_x = n. By the sibling child tangent_projection_measurable (the accepted declaration imrep_univ_tangent_starProjection_aemeasurable, reused) the map x ↦ p_x is AEMeasurable with respect to μ. This is load-bearing: R.firstVariation X is a Bochner integral of θ·trace(p_x ∘ DX(x)) over M, and the measurability of x ↦ p_x makes this integrand a.e. strongly measurable and bounded by θ·|DX| (|trace(p_x ∘ A)| ≤ P‖A‖), hence integrable for compactly supported C¹ X; so the hypothesis R.firstVariation X_ρ = 0 below is the vanishing of a genuine absolutely convergent integral, which may be split into the two terms used in step 3. Fix z ∈ ℝ^P, write r(x) := |x − z| and g_z(x) := |(x − z) − p_x(x − z)|², and let h_z(x) := g_z(x)/r(x)² for x ≠ z, h_z(z) := 0; h_z is μ-measurable with 0 ≤ h_z ≤ 1, and |p_x(x − z)|² = r² − g_z(x) = r²(1 − h_z(x)) for x ≠ z.
3. (First variation identity.) Fix ε ∈ (0, 1) and φ ∈ C¹(ℝ; [0, 1]) with φ' ≤ 0, φ = 1 on (−∞, 1] and φ = 0 on [1 + ε, ∞). For ρ > 0 let X_ρ(x) := φ(r(x)/ρ)(x − z). X_ρ is C¹ (it equals x − z on B_ρ(z), and r is smooth away from z) with compact support in B̄_{(1+ε)ρ}(z). For x ≠ z, DX_ρ(x) = φ(r/ρ) I + ρ^{−1} φ'(r/ρ) r^{−1} (x − z) ⊗ (x − z), so at μ-a.e. x: div_M X_ρ(x) = trace(p_x ∘ DX_ρ(x)) = n φ(r/ρ) + ρ^{−1} φ'(r/ρ) r^{−1} |p_x(x − z)|² = n φ(r/ρ) + (r/ρ) φ'(r/ρ)(1 − h_z(x)) (near z the second term is 0 since φ' = 0 on (−∞, 1)). Put I(ρ) := ∫ φ(r/ρ) dμ and J(ρ) := ∫ φ(r/ρ) h_z dμ. For ρ in a compact subinterval of (0, ∞) the integrands are C¹ in ρ with ρ-derivatives −(r/ρ²) φ'(r/ρ) and −(r/ρ²) φ'(r/ρ) h_z, bounded by a constant times the indicator of a fixed closed ball (μ-integrable); so I and J are differentiable with I'(ρ) = −∫ (r/ρ²) φ'(r/ρ) dμ and J'(ρ) = −∫ (r/ρ²) φ'(r/ρ) h_z dμ. The hypothesis R.firstVariation X_ρ = ∫ div_M X_ρ dμ = 0 reads 0 = n I(ρ) − ρ I'(ρ) + ρ J'(ρ), i.e. d/dρ (ρ^{−n} I(ρ)) = ρ^{−n} J'(ρ) for all ρ > 0.
4. (x − z ∈ T_x for z ∈ L.) Let z ∈ L. For every x, φ(r(x)/ρ) = ∫_{r(x)}^∞ (−φ'(s/ρ)/ρ) ds (φ(∞) = 0 and −φ' ≥ 0), so by Tonelli and step 1, I(ρ) = ∫_0^∞ (−φ'(s/ρ)/ρ) μ(B̄_s(z)) ds = c ∫_0^∞ (−φ'(s/ρ)/ρ) s^n ds = c ρ^n ∫_0^∞ (−φ'(u)) u^n du. Hence ρ^{−n} I(ρ) is constant and step 3 gives J'(ρ) = 0 for all ρ > 0, so J is constant on (0, ∞). As ρ ↓ 0, φ(r/ρ) h_z → 0 pointwise (for x ≠ z it vanishes once (1 + ε)ρ < r(x); h_z(z) = 0) and it is dominated by the μ-integrable indicator of B̄_2(z) for ρ ≤ 1; so J(ρ) → 0 and J ≡ 0. For ρ = k ∈ ℕ, φ(r/k) h_z = 0 μ-a.e. and φ(r/k) = 1 on B̄_k(z), so h_z = 0 μ-a.e. on B̄_k(z); taking the union over k, g_z = 0 μ-a.e., i.e. p_x(x − z) = x − z for μ-a.e. x.
5. (Conclusion.) L is a finite-dimensional subspace, hence separable; let D ⊆ L be countable and dense in L. Applying step 4 to z = 0 and to every z ∈ D and discarding countably many μ-null sets: for μ-a.e. x, p_x(x) = x and p_x(x − z) = x − z for all z ∈ D, so x ∈ T_x and z = x − (x − z) ∈ T_x for all z ∈ D. T_x is a finite-dimensional subspace, hence closed, so L = closure of D ⊆ T_x. For such x, p_x(x) = x and p_x(v) = v for every v ∈ L (Submodule.starProjection_eq_self_iff).

## Key steps

1. Translation invariance by L and n-homogeneity give μ(B̄_ρ(z)) = c ρ^n for z ∈ L and all ρ > 0.
2. Testing stationarity with X_ρ = φ(|x − z|/ρ)(x − z) gives d/dρ(ρ^{−n} I(ρ)) = ρ^{−n} J'(ρ), where J weights |(x − z)^⊥|²/|x − z|².
3. Constant ratios make ρ^{−n} I constant, so J is constant, tends to 0 as ρ ↓ 0, and vanishes: x − z ∈ T_x μ-a.e. for each z ∈ L.
4. A countable dense subset of L and closedness of T_x give x ∈ T_x and L ⊆ T_x for μ-a.e. x.

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
