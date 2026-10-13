# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1.map_calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–4 of the parent proof, stated for general C¹ data ψ, Q and a subspace E on which Q(v₀) vanishes.
1. Linear pieces. The maps pr₁ : ℝ^d × E → ℝ^d, pr₂ : ℝ^d × E → E and ι : E → ℝ^P are continuous linear, hence C^∞, and each is its own derivative at every point. Also pr₁ maps V × E into V.
2. Φ is C¹ on V × E.
- (a) (v, k) ↦ ψ(v) is ψ ∘ pr₁. It is C¹ on V × E because ψ is C¹ on V and pr₁ is smooth and maps V × E into V (Mathlib ContDiffOn.comp with contDiffOn_fst).
- (b) (v, k) ↦ k ∈ ℝ^P is ι ∘ pr₂, which is continuous linear and hence C¹.
- (c) (v, k) ↦ Q(v) is Q ∘ pr₁, C¹ on V × E as in (a). So (v, k) ↦ Q(v)k, the application of a C¹ operator-valued map to a C¹ vector-valued map, is C¹ on V × E (Mathlib ContDiffOn.clm_apply).
Sums and differences of C¹ maps are C¹, so Φ = (a) + (b) − (c) is C¹ on V × E.
3. Derivatives of ψ and Q at v₀. V is open and v₀ ∈ V, so ψ and Q are C¹ at v₀ (ContDiffOn.contDiffAt) and therefore differentiable there. Thus ψ has derivative Dψ(v₀) at v₀, and Q has derivative DQ(v₀) : ℝ^d → L(ℝ^P, ℝ^P) at v₀.
4. Chain rule. At (v₀, 0):
- ψ ∘ pr₁ has derivative Dψ(v₀) ∘ pr₁;
- Q ∘ pr₁ has derivative DQ(v₀) ∘ pr₁;
- ι ∘ pr₂ has derivative ι ∘ pr₂.
5. Product rule for application (Mathlib HasFDerivAt.clm_apply). Since ι(pr₂(v₀, 0)) = 0, the map (v, k) ↦ Q(v)k has derivative at (v₀, 0) given by
(w, h) ↦ Q(v₀)(ι h) + (DQ(v₀)w)(0) = Q(v₀)h.
6. Assembly. By the sum and difference rules, Φ has derivative at (v₀, 0) given by (w, h) ↦ Dψ(v₀)w + h − Q(v₀)h. Since h ∈ E, Q(v₀)h = 0 by hypothesis. So this derivative sends (w, h) to Dψ(v₀)w + h = (Dψ(v₀) ∘ pr₁ + ι ∘ pr₂)(w, h). Two continuous linear maps that agree at every point are equal, which proves the claim. ∎
Implementation notes (test-proved in about 30 lines):
- Use `hψ.comp contDiffOn_fst (fun z hz => hz.1)` for (a) and (c).
- For (b), use `(E.subtypeL.comp (ContinuousLinearMap.snd ℝ (Euclid d) E)).contDiff` and `.hasFDerivAt`.
- Annotate the type of `hQd.comp (v₀, (0 : E)) hasFDerivAt_fst` before applying `.clm_apply`.
- Close with `convert (d1.add d2).sub d3 using 1`, then `ContinuousLinearMap.ext fun z => ?_` and `simp [hQ0 _ z.2.2]`. A plain `ext` would split the goal into product and coordinate cases.

## Key steps

1. ψ∘pr₁ and Q∘pr₁ are C¹ on V × E and ι∘pr₂ is continuous linear. ContDiffOn.clm_apply and the sum/difference rules show that Φ is C¹ on V × E.
2. ψ and Q are differentiable at v₀, because they are C¹ on the open set V.
3. By the chain rule and HasFDerivAt.clm_apply, DΦ(v₀, 0)(w, h) = Dψ(v₀)w + h − Q(v₀)h − (DQ(v₀)w)(0).
4. Q(v₀)h = 0 for h ∈ E, so DΦ(v₀, 0) = Dψ(v₀) ∘ pr₁ + ι ∘ pr₂, by extensionality of continuous linear maps.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean vs workspace GMT/Ch07/Contract.lean and Submission.lean (identical)`
- `python3 -I: verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') -> opens, namespace GMT.Ch07, noncomputable section/end; CHILD_TARGET = HumanizeNodeComparator.target`
- `python3 -I dag.json scan: retraction-a1 children, depths (selected node depth 4), lean_name collision check for dor_lmb_ret_*; regex search for inverse function/OpenPartialHomeomorph/localInverse nodes (found dtc_bc_lr_local_inverse, codim1_rdo_gc_local_inverse_c2 with different types); generic '(X : Type) [NormedAddCommGroup' precedents (regcomp_norm_radial_retraction_sub_le accepted)`
- `grep snapshot Mathlib: toOpenPartialHomeomorph, toOpenPartialHomeomorph_coe, mem_toOpenPartialHomeomorph_source, OpenPartialHomeomorph.contDiffAt_symm, isOpen_image_of_subset_source, ContinuousLinearEquiv.isOpen, ContDiffOn.continuousOn_fderiv_of_isOpen, ContDiffOn.clm_apply, HasFDerivAt.clm_apply, LinearMap.finrank_range_of_inj, Submodule.finrank_add_finrank_orthogonal, Submodule.inf_orthogonal_eq_bot, starProjection_apply_eq_zero_iff, injective_iff_surjective_of_finrank_eq_finrank, LinearEquiv.ofBijective, LinearEquiv.toContinuousLinearEquiv, Module.finrank_prod, finrank_euclideanSpace_fin; grep contDiffOn_symm (no match: no Mathlib lemma gives C^1 of the inverse on a whole image)`
- `grep -rln 'toOpenPartialHomeomorph|contDiffAt_symm|InverseFunctionTheorem' simongmt/Poincare (only Chapter08/ConstancyNormalCharts.lean: exists_local_coordinate_leftInverse, a pointwise ContDiffAt left inverse, not reusable for this type)`
- `lake env lean /tmp/nc-decomp-0513/lean/{Probe,Types,Assembly,ProofA,ProofBC,Full}.lean (#print axioms; comparator-shaped exact Submission.X checks)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the three child statements and the parent (all OK, unchanged)`
- `git grep -E 'dor_lmb_ret_nc_|nc_local_inverse|nc_linear_iso|nc_map_calculus' over 1662 branch tips in 200-commit chunks (no match; control regcomp_norm_radial_retraction_sub_le: 17 hits); grep -rl 'dor_lmb_ret_nc_' .humanize (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-0513f409ad/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-0513f409ad/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/nc-decomp-0513/lean/Types.lean`
- `/tmp/nc-decomp-0513/lean/Assembly.lean`
- `/tmp/nc-decomp-0513/lean/ProofA.lean`
- `/tmp/nc-decomp-0513/lean/ProofBC.lean`
- `/tmp/nc-decomp-0513/lean/Full.lean`

Snapshot revisions are project b4d606db and Mathlib 25730c7c (SimonGMT pin 2b36630). The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

What the sources provide:
- Mathlib has the inverse function theorem only pointwise: ContDiffAt.toOpenPartialHomeomorph and to_localInverse, which is ContDiffAt at a single point. It also has OpenPartialHomeomorph.contDiffAt_symm, which needs an invertible derivative at the preimage point, and ContinuousLinearEquiv.isOpen (BoundedLinearMaps.lean:543).
- No snapshot lemma gives a C¹ inverse on a whole open image; a search for contDiffOn_symm finds nothing. That gap is exactly the child local_inverse.
- SimonGMT's exists_local_coordinate_leftInverse (Chapter08/ConstancyNormalCharts.lean) gives only a pointwise C² left inverse of an immersion and has a different type, so it is not reused.
- The other-branch DAG nodes dtc_bc_lr_local_inverse and codim1_rdo_gc_local_inverse_c2 have different types (Euclid d → Euclid d) and are still decomposing, so nothing is reused.
- A generic `(X : Type) [NormedAddCommGroup X] ...` statement has an accepted precedent: regcomp_norm_radial_retraction_sub_le.

Lean results (exact comparator scope, lake env lean):
- The three child types elaborate with only `import GMT.Ch07.Submission`. `L.range` elaborates to `LinearMap.range ↑L`, matching the frozen `(fderiv ℝ ψ v).range`, and `CompleteSpace (Euclid d × ↥(L.range)ᗮ)` is inferred.
- Each child was test-proved with axioms [propext, Classical.choice, Quot.sound]. local_inverse needs `import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`.
- The exact frozen parent type was proved from the three children plus the stubbed siblings tangent_projection and normal_space_transfer (Full.lean, 207 lines). Its only sorryAx comes from the sibling stubs.
- The comparator-shaped `exact Submission.X` checks pass.
- Proposed names are unused in dag.json, on 1662 branch tips, and in run artifacts.
