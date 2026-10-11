# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.straightening_chart-a1`
- Child DAG node: `root.coarea_formula-a1.straightening_chart-a1.submersion_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3-5 of the parent proof, together with the identity Φ(Λ p) = p from its step 6(e). This is the local submersion (rectification) theorem (cf. Spivak, Calculus on Manifolds, Thm 2-13), proved with the inverse function theorem.

Notation.
- E := Rn (m + k) = ℝ^{m+k}; P := WithLp 2 (ℝᵐ × ℝᵏ); for p ∈ P, p₁ := WithLp.fst p.
- T : ℝᵐ × ℝᵏ → P, T(u, w) := WithLp.toLp 2 (u, w). T is a continuous linear equivalence, namely (WithLp.prodContinuousLinearEquiv 2 ℝ ℝᵐ ℝᵏ).symm, and WithLp.fst (T(u, w)) = u holds by definition.
- All spaces here are finite-dimensional, hence complete, and every linear map between them is continuous. dim E = m + k and dim P = dim(ℝᵐ × ℝᵏ) = m + k.
No case distinction is needed: the argument is also valid when m = 0 or k = 0, where ℝ⁰ is the zero space.

1. Regularity of G. V is open and G is C¹ on V. So for every x ∈ V, G is differentiable at x with Fréchet derivative DG(x) := fderiv ℝ G x.
2. Kernel dimension. L := DG(a) is surjective, so range L = ℝᵐ has dimension m. By rank-nullity, dim range L + dim ker L = dim E = m + k. Hence K₀ := ker L has dimension k.
3. A linear map that is injective on K₀.
   - Since dim K₀ = k = dim ℝᵏ, there is a linear isomorphism e : K₀ → ℝᵏ (LinearEquiv.ofFinrankEq).
   - The inclusion ι : K₀ → E is injective, so it has a linear left inverse r : E → K₀ with r(ι v) = v for all v ∈ K₀ (LinearMap.exists_leftInverse_of_injective; the orthogonal projection onto K₀ also works).
   - Put π := e ∘ r : E → ℝᵏ, a continuous linear map. Then π(v) = e(r(ι v)) = e(v) for every v ∈ K₀.
4. The completed map. Define Φ : E → P by Φ(x) := T(G(x), π(x − a)). Then WithLp.fst (Φ x) = G(x) for every x ∈ E.
   (a) Derivative. Let x ∈ V. The map y ↦ (G(y), π(y − a)) has derivative v ↦ (DG(x)v, πv) at x: the first component by step 1, the second because π is continuous linear and y ↦ y − a has derivative id. Composing with the continuous linear map T, Φ has derivative DΦ(x) := T ∘ (DG(x), π) at x, i.e. DΦ(x)v = T(DG(x)v, πv). In particular fderiv ℝ Φ x = DΦ(x).
   (b) Smoothness. The map y ↦ (G(y), π(y − a)) is C¹ on V, because G is C¹ on V and y ↦ π(y − a) is affine. T is continuous linear, so Φ is C¹ on V. Since V is open, x ↦ fderiv ℝ Φ x is continuous on V (ContDiffOn.continuousOn_fderiv_of_isOpen).
5. DΦ(a) is invertible.
   - Let v ∈ E with DΦ(a)v = 0. Since T is injective, Lv = 0 and πv = 0. So v ∈ K₀ and e(v) = π(v) = 0, hence v = 0 because e is injective.
   - So DΦ(a) : E → P is an injective linear map between spaces of the same finite dimension m + k, and therefore also surjective (LinearMap.injective_iff_surjective_of_finrank_eq_finrank).
   - Let Φ'ₐ : E ≃L[ℝ] P be the continuous linear equivalence whose underlying map is DΦ(a). By step 4, Φ has derivative Φ'ₐ at a. Φ is C¹ at a because V is an open neighbourhood of a.
6. The invertibility set.
   - Let 𝓘 be the set of continuous linear maps E → P that are underlying maps of continuous linear equivalences E ≃L[ℝ] P. 𝓘 is open in the space of continuous linear maps (ContinuousLinearEquiv.isOpen; E is complete).
   - Let V′ := {x ∈ V : fderiv ℝ Φ x ∈ 𝓘}. Since x ↦ fderiv ℝ Φ x is continuous on the open set V (step 4(b)), V′ is open (ContinuousOn.isOpen_inter_preimage).
   - Since fderiv ℝ Φ a = DΦ(a) = Φ'ₐ, we have a ∈ V′.
7. Inverse function theorem. Apply the C¹ inverse function theorem (Mathlib ContDiffAt.toOpenPartialHomeomorph) to Φ at a, with derivative Φ'ₐ and smoothness order 1 ≠ 0. It gives an open partial homeomorphism h from E to P whose underlying function is Φ and whose source S contains a. Its source S and target S′ are open. Its inverse Λ₀ := h.symm : P → E is a function on all of P and satisfies:
   - for p ∈ S′: Λ₀(p) ∈ S and Φ(Λ₀(p)) = p;
   - for x ∈ S: Φ(x) ∈ S′ and Λ₀(Φ(x)) = x;
   - Λ₀ is continuous on S′ and injective on S′.
8. Definitions.
   - V₁ := S ∩ V′. It is open, a ∈ V₁ (steps 6 and 7), and V₁ ⊆ V′ ⊆ V.
   - Ω := {p ∈ S′ : Λ₀(p) ∈ V₁}. It is open because Λ₀ is continuous on the open set S′ and V₁ is open (OpenPartialHomeomorph.isOpen_inter_preimage_symm).
   - Λ := Λ₀.
9. Λ(Ω) = V₁. If p ∈ Ω, then Λ(p) ∈ V₁ by definition. Conversely, let x ∈ V₁. Then x ∈ S, so p := Φ(x) ∈ S′ and Λ(p) = x ∈ V₁; hence p ∈ Ω and x = Λ(p). So Λ(Ω) = V₁, which is open, contains a and is contained in V.
10. Injectivity. Λ is injective on Ω, since Ω ⊆ S′ and Λ is injective on S′.
11. C¹ regularity and derivative of Λ.
   - Let p ∈ Ω and x := Λ(p) ∈ V₁. Since x ∈ V′, there is a continuous linear equivalence φₓ : E ≃L[ℝ] P whose underlying map is fderiv ℝ Φ x.
   - Since x ∈ V, Φ is differentiable at x (steps 1 and 4), so Φ has derivative φₓ at x = Λ(p). Φ is C¹ at x because V is an open neighbourhood of x.
   - Since p ∈ S′, the target of h, OpenPartialHomeomorph.contDiffAt_symm shows that Λ is C¹ at p, and OpenPartialHomeomorph.hasFDerivAt_symm shows that Λ has derivative φₓ⁻¹ at p.
   - Hence fderiv ℝ Λ p = φₓ⁻¹, the underlying map of a linear equivalence P ≃ E, which is bijective.
   - Λ is C¹ at every point of the open set Ω, so it is C¹ on Ω.
12. The first component. For p ∈ Ω ⊆ S′, Φ(Λ(p)) = p (step 7). Hence G(Λ(p)) = WithLp.fst (Φ(Λ(p))) = WithLp.fst p (step 4).
13. Conclusion. Ω is open (8). Λ is C¹ on Ω (11) and injective on Ω (10). Λ(Ω) is open, contains a and is contained in V (9). fderiv ℝ Λ p is bijective for every p ∈ Ω (11). G(Λ p) = WithLp.fst p for every p ∈ Ω (12). This is exactly the claimed statement.

## Key steps

1. Rank-nullity: K₀ := ker DG(a) has dimension k because DG(a) : ℝ^{m+k} → ℝᵐ is surjective.
2. Choose a linear isomorphism e : K₀ ≅ ℝᵏ and a linear left inverse r of the inclusion K₀ ↪ ℝ^{m+k}. Then π := e∘r is continuous linear and π = e on K₀.
3. Φ(x) := toLp(G x, π(x − a)) is C¹ on V, with DΦ(x)v = toLp(DG(x)v, πv) and WithLp.fst ∘ Φ = G.
4. DΦ(a) is injective (kernel argument via e), hence bijective since both spaces have dimension m + k.
5. V′ := {x ∈ V : fderiv Φ x is a continuous linear equivalence} is open (ContinuousLinearEquiv.isOpen and continuity of fderiv Φ on V) and contains a.
6. C¹ inverse function theorem at a gives a partial homeomorphism h with underlying map Φ. Set V₁ := source ∩ V′, Ω := target ∩ h.symm⁻¹(V₁) (open), Λ := h.symm.
7. Λ(Ω) = V₁ is open, contains a and lies in V. Λ is injective on Ω. At p ∈ Ω, Λ is C¹ with derivative DΦ(Λp)⁻¹, which is bijective (contDiffAt_symm, hasFDerivAt_symm).
8. G(Λ p) = WithLp.fst(Φ(Λ p)) = WithLp.fst p, because Φ(Λ p) = p on the target.

## Reference use

### local-project

Queries:
- `rg -n "theorem continuousOn_fderiv_of_isOpen|theorem ContDiffOn.continuousOn_fderiv_of_isOpen" mathlib/Mathlib/Analysis/Calculus/ContDiff/`
- `rg -n "isOpen_inter_preimage_symm" mathlib/Mathlib/Topology/OpenPartialHomeomorph/`
- `rg -n "theorem isOpen\b|protected theorem isOpen\b|theorem ContinuousLinearEquiv.isOpen" mathlib/Mathlib/Analysis`
- `rg -n "prodContinuousLinearEquiv" mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `rg -n "^def fst|^abbrev fst|def WithLp.fst|protected def fst|fst_toLp|toLp_fst" mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `rg -n "theorem range_comp_of_range_eq_top|theorem LinearMap.range_comp_of_range_eq_top" mathlib/Mathlib`
- `grep -n "theorem OpenPartialHomeomorph.contDiffAt_symm\|theorem OpenPartialHomeomorph.hasFDerivAt_symm\|theorem OpenPartialHomeomorph.contDiffOn_symm" -A 12 mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean mathlib/Mathlib/Analysis/Calculus/FDeriv/*.lean`
- `sed -n 1,140p mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `grep -n "^theorem\|^def\|^lemma" mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `rg -il "submersion" mathlib/Mathlib/Analysis/Calculus mathlib/Mathlib/Geometry/Manifold`
- `grep -n "^theorem\|^lemma\|^def" mathlib/Mathlib/Geometry/Manifold/Submersion.lean`
- `rg -n "Submission\." project`
- `sed -n 1,200p project/GMT/Ch02/Contract.lean (tangentSpace, coareaJacobian, Rn)`
- `read SimonGMT Chapter02/Submanifold.lean (IsSimonLocalRepresentation, IsSimonSubmanifold) and Chapter02/SubmanifoldTopology.lean (exists_open_image_eq_inter)`
- `python3 -I scripts/gen_checks.py gen scripts/children.json (verifier gmt-compare.py layout/child_modules contract scope + lean_contract.validate_lean_statement)`
- `lean NodeChallenge_0.lean; lean NodeChallenge_1.lean; lean Sol0.lean; lean Sol1.lean (against a scratch olean of GMT.Ch02.Submission)`
- `lean ChildA.lean; lean ChildB.lean; lean Assembly.lean; lean Assembly2.lean; #print axioms`
- `python3 -I: list lean_name of every dag.json node and compare stand-in types with dag.json lean_statement; grep -rl for both proposed names in the run directory`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Manifold/Submersion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-straightening-chart-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-jacobian-linear-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1/decomposition-v1.json`
- `/tmp/straight-decomp-cThsEp/check/ChildA.lean`
- `/tmp/straight-decomp-cThsEp/check/ChildB.lean`
- `/tmp/straight-decomp-cThsEp/check/Assembly.lean`
- `/tmp/straight-decomp-cThsEp/check/Assembly2.lean`
- `/tmp/straight-decomp-cThsEp/gen/NodeChallenge_0.lean`
- `/tmp/straight-decomp-cThsEp/gen/NodeChallenge_1.lean`
- `/tmp/straight-decomp-cThsEp/gen/Sol0.lean`
- `/tmp/straight-decomp-cThsEp/gen/Sol1.lean`
- `/tmp/straight-decomp-cThsEp/scripts/gen_checks.py`

The snapshot has no ready-made local submersion (rectification) theorem. mathlib/Mathlib/Geometry/Manifold/Submersion.lean defines submersions by local normal forms and says that deriving them from a surjective derivative is future work. Implicit.lean only provides implicitToOpenPartialHomeomorph(OfComplemented) for strict derivatives with codomain F x ker f'. rg 'Submission\.' project matches only README text, so there are no Submission.* declarations.

All proof ingredients are present:
- ContDiffAt.toOpenPartialHomeomorph (InverseFunctionTheorem/ContDiff.lean l.31; hypothesis hn : n ≠ 0);
- OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean l.881);
- OpenPartialHomeomorph.hasFDerivAt_symm (FDeriv/OfCompLeft.lean l.214);
- ContinuousLinearEquiv.isOpen (Normed/Operator/BoundedLinearMaps.lean l.543);
- ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean l.916);
- OpenPartialHomeomorph.isOpen_inter_preimage_symm (OpenPartialHomeomorph/Basic.lean l.88);
- WithLp.prodContinuousLinearEquiv (ProdLp.lean l.556) and toLp_fst (l.145);
- LinearMap.range_comp_of_range_eq_top (Submodule/Range.lean l.421).
SimonGMT supplies IsSimonLocalRepresentation.exists_open_image_eq_inter (Simon 4.2, SubmanifoldTopology.lean). The contract does not import that module, so child 2 must import Poincare.SimonGMT.Chapter02.SubmanifoldTopology.

Verification in scratch /tmp/straight-decomp-cThsEp (pinned Lean v4.35.0-rc3, pinned mathlib/simongmt oleans, scratch olean of GMT.Ch02.Submission):
- Both statements pass validate_lean_statement unchanged and elaborate in the replayed contract scope (NodeChallenge_0/1 report only the expected sorry warning).
- Complete proofs ChildA.lean and ChildB.lean compile with #print axioms = [propext, Classical.choice, Quot.sound]. Sol0/Sol1 (`exact Submission.X` in the comparator scope) compile with the same axioms.
- Assembly2.lean proves the selected frozen type sorry-free from the real child proofs plus a sorried stand-in of the sibling coarea_jacobian_linear_algebra. Both types are string-identical to dag.json.

Neither proposed name is among the 30 lean_names in dag.json or occurs anywhere in the run directory. The c1_sard level_set_chart and chart_composition nodes have different types, so nothing is reused.
