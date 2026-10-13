# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.tangent_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2(a) of the parent proof: P̂(v) = D(v)G(v)⁻¹D(v)ᵀ with G = DᵀD is the orthogonal projection onto range D(v) and is C¹ on V. Notation: D(v) := Dψ(v) ∈ L(ℝ^d, ℝ^P). For A ∈ L(ℝ^d, ℝ^P), Aᵀ ∈ L(ℝ^P, ℝ^d) is the adjoint, ⟨Aᵀh, w⟩ = ⟨h, Aw⟩ (Mathlib ContinuousLinearMap.adjoint, adjoint_inner_left).
1. D is C¹ on V. V is open and ψ is C² on V, so v ↦ D(v) is C¹ on V (Mathlib ContDiffOn.fderiv_of_isOpen, with 1 + 1 ≤ 2).
2. A ↦ Aᵀ is a bounded ℝ-linear map L(ℝ^d, ℝ^P) → L(ℝ^P, ℝ^d): it is additive, (cA)ᵀ = c̄Aᵀ = cAᵀ for real c, and ‖Aᵀ‖ = ‖A‖. A bounded linear map is C^∞ (Mathlib IsBoundedLinearMap.contDiff). So v ↦ D(v)ᵀ is C¹ on V.
3. G(v) := D(v)ᵀ ∘ D(v) ∈ L(ℝ^d, ℝ^d) is C¹ on V, since composition of operators is a bounded bilinear operation (Mathlib ContDiffOn.clm_comp).
4. G(v) is invertible for v ∈ V. For w ∈ ℝ^d, ⟨G(v)w, w⟩ = ⟨D(v)w, D(v)w⟩ = |D(v)w|². If G(v)w₁ = G(v)w₂, then G(v)(w₁ − w₂) = 0. Hence |D(v)(w₁ − w₂)|² = 0, so D(v)(w₁ − w₂) = 0, and w₁ = w₂ because D(v) is injective. An injective linear endomorphism of the finite-dimensional space ℝ^d is bijective (Mathlib LinearEquiv.ofInjectiveEndo), with continuous inverse. So G(v) is a unit of the complete normed algebra L(ℝ^d, ℝ^d). (For d = 0 this algebra is the zero ring and all statements are trivial.)
5. Inversion is C^∞ at every unit of a complete normed algebra (Mathlib contDiffAt_ringInverse). G is C¹ and its values on V are units, so the composition v ↦ G(v)⁻¹ = Ring.inverse(G(v)) is C¹ on V.
6. R(v) := D(v) ∘ G(v)⁻¹ ∘ D(v)ᵀ is C¹ on V, again by ContDiffOn.clm_comp.
7. R(v) = P̂(v) for v ∈ V. Fix v ∈ V and h ∈ ℝ^P, and let u := R(v)h = D(v)(G(v)⁻¹D(v)ᵀh). Then u ∈ range D(v). Using G(v)G(v)⁻¹ = id, for every w ∈ ℝ^d:
⟨h − u, D(v)w⟩ = ⟨D(v)ᵀ(h − u), w⟩ = ⟨D(v)ᵀh − G(v)(G(v)⁻¹D(v)ᵀh), w⟩ = ⟨D(v)ᵀh − D(v)ᵀh, w⟩ = 0.
So h − u is orthogonal to range D(v). The orthogonal projection of h onto a subspace K is the unique u ∈ K with h − u ⊥ K (Mathlib Submodule.eq_starProjection_of_mem_of_inner_eq_zero). Hence P̂(v)h = u = R(v)h for all h, i.e. R(v) = P̂(v).
8. P̂ agrees on V with the C¹ map R, so P̂ is C¹ on V (Mathlib ContDiffOn.congr). ∎

## Key steps

1. D = Dψ is C¹ on the open set V because ψ is C²; transposition is a bounded linear map, so v ↦ D(v)ᵀ is C¹.
2. G = DᵀD is C¹ on V and, since each D(v) is injective, invertible there; inversion is smooth at units, so G⁻¹ is C¹ on V.
3. R = DG⁻¹Dᵀ is C¹ on V, with R(v)h ∈ range D(v) and h − R(v)h ⊥ range D(v).
4. By the characterization of orthogonal projections R(v) = P̂(v) on V, so P̂ is C¹ on V.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical; grep -c sorry = 1)`
- `python3 -I verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') (child scope replay: opens, namespace GMT.Ch07, noncomputable section/end)`
- `grep -rli 'nearest.point|tubular|nearestPoint|metric projection' simongmt/Poincare/SimonGMT local-references/123e8435b4a2469b/project --include=*.lean (no match)`
- `grep -rli 'tubular|nearest point retraction|nearestPoint' local-references/123e8435b4a2469b/mathlib/Mathlib --include=*.lean (no match)`
- `grep -rn 'starProjection|orthogonalProjection' simongmt/Poincare/SimonGMT | grep ContDiff (only constant projections in Chapter08/ConstancyProjection.lean)`
- `grep -n 'IsSimonLocalRepresentation|exists_open_image_eq_inter|isEmbedding_chartMap|exists_local_coordinate_leftInverse' simongmt Chapter02/Submanifold.lean, Chapter02/SubmanifoldTopology.lean, Chapter08/ConstancyNormalCharts.lean`
- `grep mathlib: def starProjection, starProjection_apply_eq_zero_iff, eq_starProjection_of_mem_of_inner_eq_zero, sub_starProjection_mem_orthogonal, starProjection_norm_le, starProjection_eq_self_iff, class HasOrthogonalProjection (Prop), finrank_add_finrank_orthogonal, LinearMap.range (takes a LinearMap; use (fderiv ℝ ψ v).range), LinearMap.finrank_range_of_inj, injective_iff_surjective_of_finrank_eq_finrank, ofInjectiveEndo, ContinuousLinearMap.adjoint, contDiffAt_ringInverse, NormedRing.inverse_continuousAt, ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, isOpen_image_of_subset_source, ContinuousLinearEquiv.isOpen, HasFDerivAt.clm_apply, IsLocalMin.hasFDerivAt_eq_zero, IsCompact.exists_isMinOn, ContDiffOn.fderiv_of_isOpen`
- `python3 -I dag.json scan (674 nodes): lean_name collisions for dor_lmb_ret_* (none); statements mentioning tangentSpace/starProjection/Injective (fderiv; the nodes dtc_bc_local_retraction and dor_lmb_c1_retraction`
- `git grep 'dor_lmb_ret_' over all 1325 branch tips in 200-commit chunks (no match; control query regcomp_norm_radial_retraction_sub_le: 17 hits); grep -rl 'dor_lmb_ret_' .humanize (no match)`
- `git show <tip>:GMT/Ch07/Submission.lean | grep '^import' over 1318 tips (accepted solutions add Mathlib/SimonGMT imports, e.g. Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the eight child statements (all OK, unchanged)`
- `lake env lean /tmp/dor-ret-decomp/Types.lean; Assembly.lean; ProofSmall.lean; ProofE.lean; ProofB.lean; ProofC2.lean; ProofD.lean; Full.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retraction-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyTangentGraph.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dor-ret-decomp/Types.lean`
- `/tmp/dor-ret-decomp/Assembly.lean`
- `/tmp/dor-ret-decomp/ProofSmall.lean`
- `/tmp/dor-ret-decomp/ProofE.lean`
- `/tmp/dor-ret-decomp/ProofB.lean`
- `/tmp/dor-ret-decomp/ProofC2.lean`
- `/tmp/dor-ret-decomp/ProofD.lean`
- `/tmp/dor-ret-decomp/Full.lean`
- `/tmp/dor-ret-decomp/stmts.py`

Snapshot revisions: project b4d606db and Mathlib 25730c7c; SimonGMT is pinned at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Its only sorry is main_theorem.

What the reference sources contain:
- No nearest-point, tubular-neighbourhood or C¹ projection-field result exists in the snapshot project, SimonGMT or Mathlib (keyword searches returned no match).
- SimonGMT has related tools:
  - Chapter02.IsSimonLocalRepresentation.exists_open_image_eq_inter: chart localization, under the full chart hypotheses.
  - Chapter08.exists_local_coordinate_leftInverse: an ambient C² left inverse built from a non-orthogonal left inverse, so it does not give ‖Dπ(y)‖ ≤ 1. Its file imports Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff, which the contract does not import.
- Mathlib at the pin supplies every API the child proofs cite: Submodule.starProjection (HasOrthogonalProjection is Prop-valued, so instance choice is irrelevant), adjoint, Ring.inverse smoothness, the inverse function theorem, openness of the set of continuous linear equivalences, the clm_apply product rule, and first-order conditions at local minima.
- Related accepted DAG declarations have different types and are not sibling prerequisites, so none is reused: chart_tangentSpace_eq_range_fderiv, dsmc_chart_tangentSpace_eq_range, dsmc_tangent_projection_field, submanifold_tangentProjection_c1_extension, atsm_chart_image_flat. The other-branch node dtc_bc_local_retraction is still decomposing and also has a different type.
- No dor_lmb_ret_* name occurs in dag.json (674 nodes), in any of the 1325 branch tips, or in the run artifacts.

Lean results (lake env lean):
- All eight child types elaborate in the exact comparator scope and pass validate_lean_statement.
- The frozen parent type compiles from the eight children stubbed with sorry.
- Every child was test-proved: chart_localization, tangent_projection, normal_space_transfer, tangent_identity, derivative_estimate and uniform_injectivity outright; normal_coordinates and nearest_point from their declared siblings.
- The combined Full.lean (571 lines) proves Submission.dor_lmb_c1_retraction with axioms [propext, Classical.choice, Quot.sound] only.
