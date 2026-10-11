# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_sard-a1`
- Child DAG node: `root.c1_sard-a1.regular_fiber-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof of root.c1_sard-a1, PART II steps 6, 7 and 11 (Simon, Ch. 2 §6, p. 66-67: "since J*f(x) ≠ 0 precisely when df_x has rank m, the implicit function theorem implies that either f⁻¹(y) \ C is empty or else it is a k-dimensional C¹ submanifold"). The construction is delegated to the sibling lemmas jacobian_rank (c1_sard_coarea_jacobian_eq_zero_iff), level_set_chart (c1_sard_submersion_level_set_chart) and chart_composition (c1_sard_local_representation_comp). Hypothesis (i) (tangent space = range of the chart derivative) and hypothesis (ii) (continuity of J*f on M) are supplied in the parent by the sibling nodes submanifold_tangent and jacobian_continuity.

Fix y ∈ ℝᵐ and write Z := {x : J*f(x) = 0}, Σ := (M ∩ f⁻¹{y}) \ Z. By definition IsSimonSubmanifold (E := ℝᵏ) 1 Σ means: 1 ≤ 1 (true), and every p ∈ Σ has (D, W₁, φ) with p ∈ W₁ and IsSimonLocalRepresentation 1 Σ D W₁ φ, φ : ℝᵏ → ℝᴺ. (If Σ = ∅ the second clause is vacuous.) Fix p ∈ Σ, so p ∈ M, f(p) = y and J*f(p) ≠ 0.

1. (Chart of M at p.) M is an (m+k)-dimensional C¹ Simon submanifold and p ∈ M, so there are V ⊆ ℝ^{m+k}, W ⊆ ℝᴺ and ψ with p ∈ W and IsSimonLocalRepresentation 1 M V W ψ. Since p ∈ W ∩ M = ψ(V), p = ψ(x_p) for some x_p ∈ V. Also ψ(V) = W ∩ M ⊆ M ⊆ U.
2. (Regular region of the chart.) V' := {x ∈ V : J*f(ψ(x)) ≠ 0}. J*f ∘ ψ is continuous on V (ψ is continuous on V and maps V into M, and J*f is continuous on M by (ii)) and V is open, so V' = V ∩ (J*f ∘ ψ)⁻¹(ℝ \ {0}) is open. x_p ∈ V' because J*f(p) ≠ 0.
3. (G := f ∘ ψ is C¹ on V'.) f is C¹ on U, ψ is C¹ on V ⊇ V', and ψ(V') ⊆ M ⊆ U; hence G is C¹ on V'.
4. (DG(x_p) is surjective.) Let T := tangentSpace M p and L := Df(p) ∘ ι_T. By jacobian_rank, J*f(p) = 0 ⟺ finrank(range L) < m; as J*f(p) ≠ 0, finrank(range L) ≥ m, and since range L ⊆ ℝᵐ with dim ℝᵐ = m, range L = ℝᵐ. So for w ∈ ℝᵐ there is t ∈ T with Df(p) t = w. By (i), T = range Dψ(x_p), so t = Dψ(x_p) v for some v ∈ ℝ^{m+k}. f is differentiable at p (p ∈ U open, f C¹ on U) and ψ is differentiable at x_p (x_p ∈ V open, ψ C¹ on V); by the chain rule DG(x_p) = Df(p) ∘ Dψ(x_p), so DG(x_p) v = Df(p) t = w. Hence DG(x_p) is surjective.
5. (Slice chart in the parameter space.) level_set_chart applied to m, k, the open set V', G and x₀ := x_p (x_p ∈ V', G C¹ on V', DG(x_p) onto) gives D ⊆ ℝᵏ, V₁ with x_p ∈ V₁ ⊆ V', and l : ℝᵏ → ℝ^{m+k} with IsSimonLocalRepresentation 1 (G⁻¹{G(x_p)}) D V₁ l. Here G(x_p) = f(p) = y.
6. (Change of represented set.) V₁ ∩ G⁻¹{y} = V₁ ∩ ψ⁻¹(Σ): for x ∈ V₁ ⊆ V' ⊆ V we have ψ(x) ∈ M and J*f(ψ(x)) ≠ 0, hence ψ(x) ∈ Σ ⟺ f(ψ(x)) = y ⟺ G(x) = y. Since IsSimonLocalRepresentation 1 X D V₁ l depends on X only through its image clause l(D) = V₁ ∩ X, also IsSimonLocalRepresentation 1 (ψ⁻¹(Σ)) D V₁ l.
7. (Composition.) chart_composition applied to n := m + k, k, N, M, S := Σ (Σ ⊆ M), the representation (V, W, ψ) of M, V₁ ⊆ V (V₁ ⊆ V' ⊆ V) and the representation (D, V₁, l) of ψ⁻¹(Σ) gives W₁ ⊆ W with ψ(V₁) = W₁ ∩ M and IsSimonLocalRepresentation 1 Σ D W₁ (ψ ∘ l).
8. (p ∈ W₁.) p = ψ(x_p) with x_p ∈ V₁, so p ∈ ψ(V₁) = W₁ ∩ M; hence p ∈ W₁.
9. Steps 1-8 give, for each p ∈ Σ, a C¹ Simon local representation (D, W₁, ψ ∘ l) of Σ with parameter space ℝᵏ and p ∈ W₁; with 1 ≤ 1 this is IsSimonSubmanifold (E := ℝᵏ) 1 Σ. As y was arbitrary, the statement holds. ∎

Formalization reference (machine-checked by the decomposer with only `import GMT.Ch02.Submission`, inside `namespace GMT.Ch02` with the contract's opens, against the exact frozen sibling statements; in the implementation the three sibling names are `Submission.c1_sard_coarea_jacobian_eq_zero_iff`, `Submission.c1_sard_submersion_level_set_chart`, `Submission.c1_sard_local_representation_comp`). Library: ContinuousOn.comp, ContinuousOn.isOpen_inter_preimage, isOpen_compl_singleton, ContDiffOn.comp, ContDiffOn.differentiableOn one_ne_zero, Submodule.finrank_le, Submodule.eq_top_of_finrank_eq, finrank_euclideanSpace_fin, fderiv_comp.

```lean
theorem c1_sard_regular_fiber_submanifold : ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → ContinuousOn (coareaJacobian M f) M → ∀ y : Rn m, Chapter02.IsSimonSubmanifold (E := Rn k) 1 ((M ∩ f ⁻¹' {y}) \ {x | coareaJacobian M f x = 0}) := by
  intro N m k M U f hM hU hMU hf htan hJ y
  refine ⟨le_rfl, ?_⟩
  intro p hp
  obtain ⟨⟨hpM, hpy⟩, hpZ⟩ := hp
  have hpy' : f p = y := hpy
  have hpZ' : coareaJacobian M f p ≠ 0 := hpZ
  obtain ⟨V, W, ψ, hpW, hψ⟩ := hM.2 p hpM
  have hpimg : p ∈ ψ '' V := by rw [hψ.image_eq]; exact ⟨hpW, hpM⟩
  obtain ⟨xp, hxpV, rfl⟩ := hpimg
  subst hpy'
  have hψM : MapsTo ψ V M := fun x hx => by
    have : ψ x ∈ ψ '' V := ⟨x, hx, rfl⟩
    rw [hψ.image_eq] at this; exact this.2
  set V' : Set (Rn (m + k)) := V ∩ (coareaJacobian M f ∘ ψ) ⁻¹' {0}ᶜ with hV'def
  have hV'open : IsOpen V' :=
    (hJ.comp hψ.contDiffOn.continuousOn hψM).isOpen_inter_preimage hψ.isOpen_source isOpen_compl_singleton
  have hV'V : V' ⊆ V := inter_subset_left
  have hxpV' : xp ∈ V' := ⟨hxpV, hpZ'⟩
  have hG : ContDiffOn ℝ 1 (f ∘ ψ) V' :=
    hf.comp (hψ.contDiffOn.mono hV'V) (fun x hx => hMU (hψM (hV'V hx)))
  have hdf : DifferentiableAt ℝ f (ψ xp) :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hMU hpM))
  have hdψ : DifferentiableAt ℝ ψ xp :=
    (hψ.contDiffOn.differentiableOn one_ne_zero).differentiableAt (hψ.isOpen_source.mem_nhds hxpV)
  have hsurjL : LinearMap.range ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype) = ⊤ := by
    have h1 := (c1_sard_coarea_jacobian_eq_zero_iff N m M f (ψ xp)).not.mp hpZ'
    apply Submodule.eq_top_of_finrank_eq
    have h2 := Submodule.finrank_le (LinearMap.range ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype))
    rw [finrank_euclideanSpace_fin] at h2 ⊢
    omega
  have hsurjG : Function.Surjective (fderiv ℝ (f ∘ ψ) xp) := by
    intro w
    have hw : w ∈ LinearMap.range ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype) := by
      rw [hsurjL]; trivial
    obtain ⟨t, ht⟩ := hw
    have htmem : (t : Rn N) ∈ LinearMap.range (fderiv ℝ ψ xp).toLinearMap := by
      rw [← htan V W ψ hψ xp hxpV]; exact t.2
    obtain ⟨v, hv⟩ := htmem
    refine ⟨v, ?_⟩
    rw [fderiv_comp xp hdf hdψ]
    have hv' : fderiv ℝ ψ xp v = t := hv
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hv']
    simpa using ht
  obtain ⟨D, V₁, l, hxpV₁, hV₁V', hl⟩ :=
    c1_sard_submersion_level_set_chart m k V' (f ∘ ψ) xp hV'open hxpV' hG hsurjG
  set S : Set (Rn N) := (M ∩ f ⁻¹' {f (ψ xp)}) \ {x | coareaJacobian M f x = 0} with hSdef
  have hset : V₁ ∩ (f ∘ ψ) ⁻¹' {(f ∘ ψ) xp} = V₁ ∩ ψ ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxV' := hV₁V' hx1
      exact ⟨hx1, ⟨hψM hxV'.1, hx2⟩, hxV'.2⟩
    · rintro ⟨hx1, ⟨_, hx2⟩, _⟩
      exact ⟨hx1, hx2⟩
  have hl' : Chapter02.IsSimonLocalRepresentation 1 (ψ ⁻¹' S) D V₁ l := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hl
    exact ⟨h1, h2, h3, h4, h5.trans hset, h6, h7⟩
  have hSM : S ⊆ M := fun x hx => hx.1.1
  obtain ⟨W₁, hW₁W, hW₁img, hrep⟩ :=
    c1_sard_local_representation_comp (m + k) k N M S V W ψ D V₁ l hψ hSM (hV₁V'.trans hV'V) hl'
  have hpW₁ : ψ xp ∈ W₁ := by
    have : ψ xp ∈ ψ '' V₁ := ⟨xp, hxpV₁, rfl⟩
    rw [hW₁img] at this; exact this.1
  exact ⟨D, W₁, ψ ∘ l, hpW₁, hrep⟩
```

## Key steps

1. Take a chart (V, W, ψ) of M at p = ψ(x_p); V' := {x ∈ V : J*f(ψ x) ≠ 0} is open and contains x_p.
2. G := f ∘ ψ is C¹ on V', and DG(x_p) = Df(p) ∘ Dψ(x_p) is surjective by jacobian_rank and T_pM = range Dψ(x_p).
3. level_set_chart gives (D, V₁, l) for G⁻¹{y} with x_p ∈ V₁ ⊆ V'; on V₁, G⁻¹{y} = ψ⁻¹(Σ_y).
4. chart_composition gives W₁ with ψ(V₁) = W₁ ∩ M and (D, W₁, ψ ∘ l) a Simon chart of Σ_y with p ∈ W₁.

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
