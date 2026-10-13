# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.uniform_injectivity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2(b) of the parent proof, with D replaced by a general continuous family L on a compact set K. That step sets b := sup_{v∈V₀}‖G(v)⁻¹D(v)ᵀ‖ < ∞ and uses that G⁻¹Dᵀ is a left inverse of D, so |w| ≤ b|D(v)w|. Below, Aᵀ is the adjoint of A ∈ L(ℝ^d, ℝ^P).
1. For v ∈ K put G(v) := L(v)ᵀL(v) ∈ L(ℝ^d, ℝ^d). G(v) is invertible. Indeed, G(v)w = 0 implies |L(v)w|² = ⟨G(v)w, w⟩ = 0, hence L(v)w = 0 and w = 0. An injective endomorphism of ℝ^d is bijective with continuous inverse, i.e. a unit of the complete normed algebra L(ℝ^d, ℝ^d).
2. M(v) := G(v)⁻¹L(v)ᵀ ∈ L(ℝ^P, ℝ^d) satisfies M(v)L(v) = G(v)⁻¹G(v) = id.
3. v ↦ M(v) is continuous on K, because:
- L is continuous on K;
- the adjoint is a continuous (isometric) map;
- composition is continuous;
- inversion is continuous at every unit (Mathlib NormedRing.inverse_continuousAt).
4. A continuous function on a compact set is bounded: there is C with ‖M(v)‖ ≤ C for v ∈ K (Mathlib IsCompact.exists_bound_of_continuousOn). Put b := max(C, 0) ≥ 0.
5. For v ∈ K and w ∈ ℝ^d: |w| = |M(v)(L(v)w)| ≤ ‖M(v)‖|L(v)w| ≤ b|L(v)w|. ∎
An equivalent compactness argument, also complete and shorter in Lean:
- Let S := K × {w : |w| = 1}, which is compact.
- If S = ∅ (K = ∅ or d = 0), then b := 0 works: for v ∈ K every w is 0, since otherwise (v, w/|w|) ∈ S.
- Otherwise (v, w) ↦ |L(v)w| is continuous on S (Mathlib ContinuousOn.clm_apply) and attains its minimum m at some (v₁, w₁) ∈ S (IsCompact.exists_isMinOn). Here m > 0, because w₁ ≠ 0 and L(v₁) is injective.
- For v ∈ K and w ≠ 0, m ≤ |L(v)(w/|w|)| = |L(v)w|/|w|, so |w| ≤ m⁻¹|L(v)w|. This also holds for w = 0, so b := m⁻¹ works.

## Key steps

1. G(v) = L(v)ᵀL(v) is invertible for v ∈ K because L(v) is injective.
2. M(v) = G(v)⁻¹L(v)ᵀ is a left inverse of L(v) and depends continuously on v ∈ K.
3. b := max(sup_K ‖M‖, 0) is finite by compactness, and |w| = |M(v)L(v)w| ≤ b|L(v)w|.

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
