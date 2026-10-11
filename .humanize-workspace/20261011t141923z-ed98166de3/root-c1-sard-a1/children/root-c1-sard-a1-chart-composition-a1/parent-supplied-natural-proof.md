# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_sard-a1`
- Child DAG node: `root.c1_sard-a1.chart_composition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof of root.c1_sard-a1, PART II step 7 (choice of W₃ by Simon 4.2), step 8 (image), step 9 (injectivity and injective derivative) and step 10 (properness, the ψ-part), stated for an arbitrary subset S of M and an arbitrary C¹ Simon local representation l of ψ⁻¹(S) inside V. Here a C¹ Simon local representation (Simon 4.1, SimonGMT IsSimonLocalRepresentation 1 X V W φ) means: V and W open, φ C¹ on V, φ injective on V, φ(V) = W ∩ X, φ proper relative to (V, W) (V ∩ φ⁻¹(Q) compact for every compact Q ⊆ W), and Dφ(x) injective for every x ∈ V.

1. (Choice of W₁, Simon 4.2.) V₁ is open (it is the target chart of the representation (D, V₁, l)) and V₁ ⊆ V. By Simon (4.2) for the local representation (V, W, ψ) of M (SimonGMT IsSimonLocalRepresentation.exists_open_image_eq_inter: by relative properness, ψ is a homeomorphism of V onto W ∩ M, so images of open subsets of V are relatively open in M) there is an open W₁ ⊆ W with ψ(V₁) = W₁ ∩ M.
2. (l maps D into V₁.) l(D) = V₁ ∩ ψ⁻¹(S) ⊆ V₁ ⊆ V.
3. (C¹.) ψ is C¹ on V, l is C¹ on D, and l maps D into V (step 2); hence ψ ∘ l is C¹ on D.
4. (Injective.) l is injective on D, l(D) ⊆ V and ψ is injective on V; hence ψ ∘ l is injective on D.
5. (Image.) (ψ ∘ l)(D) = ψ(l(D)) = ψ(V₁ ∩ ψ⁻¹(S)) = ψ(V₁) ∩ S = (W₁ ∩ M) ∩ S = W₁ ∩ S, using ψ(A ∩ ψ⁻¹B) = ψ(A) ∩ B, step 1 and S ⊆ M.
6. (Properness relative to (D, W₁).) Let Q ⊆ W₁ be compact. (a) Q ⊆ W₁ ⊆ W, so K := V ∩ ψ⁻¹(Q) is compact by the relative properness of ψ. (b) K ⊆ V₁: if x ∈ K then ψ(x) ∈ Q ⊆ W₁ and ψ(x) ∈ ψ(V) = W ∩ M ⊆ M, so ψ(x) ∈ W₁ ∩ M = ψ(V₁), i.e. ψ(x) = ψ(x') with x' ∈ V₁ ⊆ V; injectivity of ψ on V gives x = x' ∈ V₁. (c) D ∩ (ψ ∘ l)⁻¹(Q) = D ∩ l⁻¹(K): for z ∈ D, l(z) ∈ V (step 2), so ψ(l(z)) ∈ Q ⟺ l(z) ∈ V ∩ ψ⁻¹(Q) = K. (d) K is compact and K ⊆ V₁, so D ∩ l⁻¹(K) is compact by the relative properness of l with respect to (D, V₁).
7. (Injective derivative.) Let z ∈ D. Then l(z) ∈ V, V is open and ψ is C¹ on V, so ψ is differentiable at l(z); D is open and l is C¹ on D, so l is differentiable at z. By the chain rule D(ψ ∘ l)(z) = Dψ(l(z)) ∘ Dl(z), a composition of injective linear maps (Dψ is injective on V, Dl is injective on D); hence it is injective.
8. Steps 1 and 3-7 show W₁ ⊆ W, ψ '' V₁ = W₁ ∩ M and IsSimonLocalRepresentation 1 S D W₁ (ψ ∘ l) (D open by hypothesis, W₁ open by step 1). ∎

Formalization reference (machine-checked by the decomposer: extra import `Poincare.SimonGMT.Chapter02.SubmanifoldTopology`; inside `namespace GMT.Ch02` with the contract's opens; axioms propext, Classical.choice, Quot.sound only). Library: IsSimonLocalRepresentation.exists_open_image_eq_inter / isProperOnInto / injOn / image_eq / contDiffOn / isOpen_source / injective_fderiv (SimonGMT), ContDiffOn.comp, Set.InjOn.comp, Set.image_comp, Set.image_inter_preimage, fderiv_comp; ContDiffOn.differentiableOn takes `one_ne_zero` in this Mathlib.

```lean
theorem c1_sard_local_representation_comp : ∀ (n k N : ℕ) (M S : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N) (D : Set (Rn k)) (V₁ : Set (Rn n)) (l : Rn k → Rn n), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → S ⊆ M → V₁ ⊆ V → Chapter02.IsSimonLocalRepresentation 1 (ψ ⁻¹' S) D V₁ l → ∃ W₁ : Set (Rn N), W₁ ⊆ W ∧ ψ '' V₁ = W₁ ∩ M ∧ Chapter02.IsSimonLocalRepresentation 1 S D W₁ (ψ ∘ l) := by
  intro n k N M S V W ψ D V₁ l hψ hSM hV₁V hl
  obtain ⟨hD, hV₁, hlC, hlinj, hlimg, hlprop, hlder⟩ := hl
  obtain ⟨W₁, hW₁, hW₁W, hW₁img⟩ := hψ.exists_open_image_eq_inter hV₁ hV₁V
  have hlD : MapsTo l D V₁ := fun z hz => by
    have : l z ∈ l '' D := ⟨z, hz, rfl⟩
    rw [hlimg] at this; exact this.1
  refine ⟨W₁, hW₁W, hW₁img, hD, hW₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact hψ.contDiffOn.comp hlC (hlD.mono_right hV₁V)
  · exact hψ.injOn.comp hlinj (hlD.mono_right hV₁V)
  · rw [image_comp, hlimg, image_inter_preimage, hW₁img, inter_assoc, inter_eq_right.mpr hSM]
  · intro Q hQ hQW₁
    have hK := hψ.isProperOnInto Q hQ (hQW₁.trans hW₁W)
    have hKV₁ : V ∩ ψ ⁻¹' Q ⊆ V₁ := by
      rintro x ⟨hxV, hxQ⟩
      have hxM : ψ x ∈ W ∩ M := by rw [← hψ.image_eq]; exact ⟨x, hxV, rfl⟩
      have : ψ x ∈ ψ '' V₁ := by rw [hW₁img]; exact ⟨hQW₁ hxQ, hxM.2⟩
      obtain ⟨x', hx'V₁, hx'⟩ := this
      rw [← hψ.injOn (hV₁V hx'V₁) hxV hx']
      exact hx'V₁
    have heq : D ∩ (ψ ∘ l) ⁻¹' Q = D ∩ l ⁻¹' (V ∩ ψ ⁻¹' Q) := by
      ext z
      constructor
      · rintro ⟨hz, hzQ⟩; exact ⟨hz, hV₁V (hlD hz), hzQ⟩
      · rintro ⟨hz, _, hzQ⟩; exact ⟨hz, hzQ⟩
    rw [heq]
    exact hlprop _ hK hKV₁
  · intro z hz
    have hlz : l z ∈ V := hV₁V (hlD hz)
    have hdψ : DifferentiableAt ℝ ψ (l z) :=
      (hψ.contDiffOn.differentiableOn one_ne_zero).differentiableAt (hψ.isOpen_source.mem_nhds hlz)
    have hdl : DifferentiableAt ℝ l z :=
      (hlC.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hz)
    rw [fderiv_comp z hdψ hdl, ContinuousLinearMap.coe_comp]
    exact (hψ.injective_fderiv hlz).comp (hlder z hz)
```

## Key steps

1. Simon 4.2 gives an open W₁ ⊆ W with ψ(V₁) = W₁ ∩ M.
2. ψ ∘ l is C¹ and injective on D because l(D) ⊆ V₁ ⊆ V.
3. (ψ ∘ l)(D) = ψ(V₁ ∩ ψ⁻¹S) = ψ(V₁) ∩ S = W₁ ∩ S.
4. Properness: V ∩ ψ⁻¹Q is compact and lies in V₁ (injectivity of ψ), and D ∩ (ψ ∘ l)⁻¹Q = D ∩ l⁻¹(V ∩ ψ⁻¹Q).
5. D(ψ ∘ l)(z) = Dψ(l z) ∘ Dl(z) is injective.

## Reference use

### local-project

Queries:
- `rg -n "^def C1Sard|^def CoareaFormula|^def coareaJacobian|^def tangentSpace|^def tangentProjection" project/GMT/Ch02/Contract.lean`
- `rg -n "C1Sard|6.4" project/GMT/Ch02/README.md`
- `rg -n "theorem toOpenPartialHomeomorph|def toOpenPartialHomeomorph|theorem mem_toOpenPartialHomeomorph_source" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `rg -n "theorem OpenPartialHomeomorph.contDiffAt_symm" mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean; rg -n "theorem OpenPartialHomeomorph.hasFDerivAt_symm" mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `rg -n "protected theorem ContinuousLinearEquiv.isOpen" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean; rg -n "protected def restrOpen|theorem coe_restrOpen" mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `rg -n "theorem _root_.Submodule.adjoint_subtypeL|theorem adjoint_comp|theorem _root_.ContinuousLinearMap.adjoint_toLinearMap" mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean; rg -n "^def starProjection|theorem orthogonalProjectionOnto_mem_subspace_eq_self" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "theorem ContinuousOn.clm_comp" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean; rg -n "theorem ContDiffOn.continuousOn_fderiv_of_isOpen" mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean; rg -n "theorem continuousOn_iff_isClosed|theorem ContinuousOn.isOpen_inter_preimage" mathlib/Mathlib/Topology/ContinuousOn.lean`
- `rg -n "theorem lintegral_eq_zero_iff'|theorem lintegral_indicator_one" mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean`
- `rg -n "theorem finrank_range_add_finrank_ker|theorem injective_iff_surjective_of_finrank_eq_finrank" mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean; rg -n "lemma ball_prod_same" mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean; rg -n "theorem fderiv_comp " mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean; rg -n "theorem finrank_euclideanSpace_fin" mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n "def implicitToOpenPartialHomeomorph|def implicitFunction|theorem map_implicitFunction_eq" mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `rg -il "sard" mathlib/Mathlib; rg -n "Submission\." project --glob '*.lean'; rg -il "sard|regular value|implicit" lake-packages-25730c7c/simongmt/Poincare/SimonGMT/`
- `full reads of simongmt Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldTopology,SubmanifoldCalculus,CoareaLinearAlgebra,CoareaProjection}.lean; git rev-parse HEAD of the simongmt and mathlib package checkouts`
- `python3 -I gen_checks.py / gen_solutions.py (replay verifier gmt-compare.py contract_scope + child_modules for the six lean_statements); lean NodeChallenge/NodeSolution modules against scratch oleans of GMT.Ch02.Submission`
- `lean Assembly.lean, GCheck.lean, Combined.lean with #print axioms (six child proofs + parent assembly, uncle types as stand-ins)`
- `read dag.json lean_name list for collisions with the six proposed names`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/c1sard-decomp-Z3BOJI/Combined.lean`

Frozen contract: Contract.lean:349-374 fixes CoareaFormula and C1Sard. Conjunct (2) uses μHE[k] and volume on Rn m, and conjunct (3b) uses IsSimonSubmanifold (E := Rn k) 1. coareaJacobian (line 123) is defined with ContinuousLinearMap.adjoint and the det of L ∘L L†. README row 16 and line 103 confirm the relatively-closed reading and the rank conjunct.

Snapshot Mathlib supplies everything the six children use:
- the C¹ inverse function theorem, ContDiffAt.toOpenPartialHomeomorph (InverseFunctionTheorem/ContDiff.lean:31);
- OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881) and OpenPartialHomeomorph.hasFDerivAt_symm (FDeriv/OfCompLeft.lean:214);
- ContinuousLinearEquiv.isOpen (BoundedLinearMaps.lean:543) and restrOpen (OpenPartialHomeomorph/IsImage.lean:216; its coercions are rfl);
- Submodule.adjoint_subtypeL (Adjoint.lean:177), adjoint_comp (Adjoint.lean:136) and starProjection (Projection/Basic.lean:131);
- ContinuousOn.clm_comp (BoundedLinearMaps.lean:453), ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916) and continuousOn_iff_isClosed (Topology/ContinuousOn.lean:149);
- lintegral_eq_zero_iff' and lintegral_indicator_one (Lebesgue/Basic.lean:322, 572);
- rank-nullity (FiniteDimensional/Lemmas.lean:173, 204), ball_prod_same, fderiv_comp and finrank_euclideanSpace_fin.

No existing result proves C1Sard or any child. Implicit.lean offers an alternative implicit-function route. The 'Sard' matches (MeasureTheory/Function/Jacobian.lean) are the equal-dimension critical-value lemma, not the coarea-based C¹ Sard theorem. The SimonGMT 'implicit' matches are unrelated comments.

Pinned SimonGMT is at rev 2b3663083f3f, which matches the lakefile, and its oleans are built. It provides:
- coareaLinearJacobian_eq_sqrt_det and coareaLinearJacobian_eq_zero_iff (CoareaLinearAlgebra.lean:35-48);
- IsSimonLocalRepresentation.exists_open_image_eq_inter (SubmanifoldTopology.lean:100, Simon 4.2).
All of these depend only on propext, Classical.choice and Quot.sound.

The project snapshot has no Submission.* declarations, and dag.json has no c1_sard_* children, so the six names are free.

Verifier replay results:
- all six statements elaborate after import GMT.Ch02.Submission in the contract scope;
- the assembly proves C1Sard from the children and the two uncle types;
- complete Lean proofs of all six children compile, and the verifier-generated NodeSolution modules check against them using standard axioms only.
