# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.piece_tangent_field-a1`
- Child DAG node: `root.tangent_structure-a1.piece_tangent_field-a1.projection_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof (node root.tangent_structure-a1.piece_tangent_field-a1), steps 1–2 (the formula Π(A) = A(A*A)⁻¹A* and the continuity of Φ at injective maps), specialized. The invertibility step and the final congruence step are written out. The adjoint is realized by the Riesz construction, because Mathlib.Analysis.InnerProductSpace.Adjoint (home of ContinuousLinearMap.adjoint) is not imported by the frozen contract and a leaf candidate may not add imports. No errata apply.

Conventions. X := ℝⁿ = EuclideanSpace ℝ (Fin n) and E := Ambient n ℓ = ℝ^{n+ℓ}; both are finite-dimensional real inner product spaces, hence complete. L(V, W) := V →L[ℝ] W with the operator-norm topology; L(X, X) is a complete normed ring whose multiplication is composition. For A ∈ L(X, E), range A := LinearMap.range A.toLinearMap is a finite-dimensional, hence complete, subspace of E, so Π(A) := (range A).starProjection ∈ L(E, E), the orthogonal projection onto range A, is defined. S := {A ∈ L(X, E) : A injective}. Ring.inverse on L(X, X) sends a unit to its two-sided inverse (and non-units to 0).

Proof.
1. The adjoint A ↦ A*. Let A ∈ L(X, E) and y ∈ E. The map x ↦ ⟪y, Ax⟫ is a continuous linear functional on X, so by the Riesz representation theorem (InnerProductSpace.toDual ℝ X : X ≃ StrongDual ℝ X, an isometric equivalence) there is a unique A*y ∈ X with ⟪A*y, x⟫ = ⟪y, Ax⟫ for all x ∈ X. By uniqueness, y ↦ A*y is linear; since ‖A*y‖ = sup_{‖x‖≤1} ⟪y, Ax⟫ ≤ ‖A‖‖y‖, we get A* ∈ L(E, X). Likewise A ↦ A* is linear with ‖A*‖ ≤ ‖A‖, so it is a continuous linear map L(X, E) → L(E, X). Concretely, A*y = (InnerProductSpace.toDual ℝ X).symm (ContinuousLinearMap.toSesqForm A y). The whole map A ↦ A* is the bundled composite (ContinuousLinearMap.compSL … ((toDual ℝ X).symm)).comp ContinuousLinearMap.toSesqForm, which is Mathlib's adjointAux rebuilt from pieces available under the frozen imports; it is continuous because it is a bundled continuous (semi)linear map. The identity ⟪A*y, x⟫ = ⟪y, Ax⟫ follows from InnerProductSpace.toDual_symm_apply and ContinuousLinearMap.toSesqForm_apply_coe.
2. Invertibility of the Gram operator. Let A ∈ S and T := A* ∘ A ∈ L(X, X). If Tv = 0, then |Av|² = ⟪Av, Av⟫ = ⟪A*(Av), v⟫ = ⟪Tv, v⟫ = 0 by step 1, so Av = 0, and v = 0 because A is injective; by linearity T is injective. Since X is finite-dimensional, an injective linear endomorphism of X is surjective (LinearMap.injective_iff_surjective), so T is bijective. A bijective continuous linear endomorphism of the Banach space X is a unit of L(X, X) (ContinuousLinearMap.isUnit_iff_bijective). Consequently T ∘ Ring.inverse(T) = id_X (Ring.mul_inverse_cancel).
3. The projection formula. For A ∈ L(X, E) put Φ(A) := A ∘ Ring.inverse(A* ∘ A) ∘ A* ∈ L(E, E). Let A ∈ S, T := A* ∘ A and B := Ring.inverse(T), so T ∘ B = id_X by step 2. Fix z ∈ E and set y := Φ(A)z = A(B(A*z)); then y ∈ range A. Every element of range A has the form Av with v ∈ X, and by step 1, ⟪z − y, Av⟫ = ⟪A*(z − y), v⟫ = ⟪A*z − T(B(A*z)), v⟫ = ⟪A*z − A*z, v⟫ = 0. Thus y ∈ range A and z − y is orthogonal to range A. By the characterization of the orthogonal projection (Submodule.eq_starProjection_of_mem_of_inner_eq_zero), Π(A)z = y = Φ(A)z. As z ∈ E was arbitrary, Π(A) = Φ(A) for every A ∈ S.
4. Continuity of Φ at points of S. Let A₀ ∈ S. The map A ↦ A* is continuous (step 1). Composition of continuous linear maps is jointly continuous for the operator norm (Continuous.clm_comp, ContinuousAt.clm_comp), so A ↦ A* ∘ A is continuous. By step 2, A₀* ∘ A₀ is a unit of the complete normed ring L(X, X), and Ring.inverse is continuous at every unit of such a ring (NormedRing.inverse_continuousAt). Composing, A ↦ Ring.inverse(A* ∘ A) is continuous at A₀. Applying ContinuousAt.clm_comp twice (to A ↦ A, A ↦ Ring.inverse(A* ∘ A) and A ↦ A*), A ↦ A ∘ Ring.inverse(A* ∘ A) ∘ A* = Φ(A) is continuous at A₀.
5. Conclusion. Let A₀ ∈ S. By step 4, Φ is continuous at A₀, hence continuous within S at A₀. By step 3, Π(A) = Φ(A) for every A ∈ S, and in particular Π(A₀) = Φ(A₀). A function that agrees with Φ on S and at A₀ is also continuous within S at A₀ (ContinuousWithinAt.congr), so Π is continuous within S at A₀. Since A₀ ∈ S was arbitrary, Π is continuous on S; that is, A ↦ (LinearMap.range A.toLinearMap).starProjection is ContinuousOn {A | Function.Injective A}. The case n = 0 needs no separate treatment: L(X, X) is then the zero ring, every element is a unit, and steps 1–5 apply verbatim. ∎

Implementation note (not part of the argument). Every cited result is available under the frozen imports, checked with #check in the frozen scope: InnerProductSpace.toDual, toDual_symm_apply, ContinuousLinearMap.toSesqForm, toSesqForm_apply_coe, ContinuousLinearMap.compSL, ContinuousLinearMap.isUnit_iff_bijective, LinearMap.injective_iff_surjective, Ring.mul_inverse_cancel, NormedRing.inverse_continuousAt, ContinuousAt.clm_comp, Submodule.eq_starProjection_of_mem_of_inner_eq_zero and ContinuousWithinAt.congr. ContinuousLinearMap.adjoint and LinearMap.adjoint are unknown constants there. No import change is needed, and none is allowed.

Appendix (implementation aid, not part of the argument). The following Lean proof of exactly the frozen type was checked to compile, with axioms propext, Classical.choice and Quot.sound only, when inserted as a single theorem before `main_theorem` in an otherwise unchanged copy of the frozen GMT/Ch04/Submission.lean (no import added; the controller's leaf delta check accepts it):

theorem Submission.ts_starProjection_range_continuousOn_injective : (∀ (n ℓ : ℕ), ContinuousOn (fun (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) ↦ (LinearMap.range A.toLinearMap).starProjection) {A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ | Function.Injective A}) := by
  intro n ℓ
  -- Riesz construction of the adjoint `A ↦ A*` (Mathlib's `adjointAux`, rebuilt from
  -- `toDual` and `toSesqForm`, which the frozen imports provide).
  set adj : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) →L⋆[ℝ]
      (Ambient n ℓ →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (ContinuousLinearMap.compSL _ _ _ _ _
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm :
        StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L⋆[ℝ] EuclideanSpace ℝ (Fin n))).comp
      (ContinuousLinearMap.toSesqForm :
        (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) →L[ℝ]
          Ambient n ℓ →L⋆[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n))) with hadj
  have hadj_inner : ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (y : Ambient n ℓ)
      (x : EuclideanSpace ℝ (Fin n)), inner ℝ (adj A y) x = inner ℝ y (A x) := by
    intro A y x
    change inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (ContinuousLinearMap.toSesqForm A y)) x = _
    rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.toSesqForm_apply_coe]
    rfl
  -- Φ(A) = A ∘ (A*A)⁻¹ ∘ A*
  set Φ : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → (Ambient n ℓ →L[ℝ] Ambient n ℓ) :=
    fun A ↦ A ∘L (Ring.inverse (adj A ∘L A) ∘L adj A) with hΦ
  -- A*A is a unit for injective A
  have hunit : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      IsUnit (adj A ∘L A) := by
    intro A hA
    have hinj : Function.Injective (adj A ∘L A) := by
      intro v w hvw
      have h0 : (adj A ∘L A) (v - w) = 0 := by
        rw [map_sub, hvw, sub_self]
      have h1 : ‖A (v - w)‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, ← hadj_inner]
        simp only [ContinuousLinearMap.comp_apply] at h0
        rw [h0, inner_zero_left]
      have h2 : A (v - w) = 0 := by
        simpa using h1
      have h3 : v - w = 0 := hA (by rw [h2, map_zero])
      exact sub_eq_zero.mp h3
    refine ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective (f := (adj A ∘L A).toLinearMap)).mp hinj
  -- the projection formula
  have hformula : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      (LinearMap.range A.toLinearMap).starProjection = Φ A := by
    intro A hA
    ext1 z
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨_, rfl⟩
    · rintro _ ⟨v, rfl⟩
      rw [ContinuousLinearMap.coe_coe, ← hadj_inner, map_sub]
      have hcancel : adj A (Φ A z) = adj A z := by
        have := Ring.mul_inverse_cancel _ (hunit A hA)
        calc adj A (Φ A z)
            = ((adj A ∘L A) * Ring.inverse (adj A ∘L A)) (adj A z) := by
              simp only [hΦ, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]
          _ = adj A z := by rw [this, one_apply_eq_self]
      rw [hcancel, sub_self, inner_zero_left]
  -- continuity of Φ at injective maps
  have hcont : ∀ A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A₀ →
      ContinuousAt Φ A₀ := by
    intro A₀ hA₀
    have hadjc : Continuous fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦ adj A :=
      adj.continuous
    have hgram : Continuous fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        adj A ∘L A := hadjc.clm_comp continuous_id
    have hinv : ContinuousAt (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        Ring.inverse (adj A ∘L A)) A₀ := by
      have := NormedRing.inverse_continuousAt (hunit A₀ hA₀).unit
      exact ContinuousAt.comp (f := fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        adj A ∘L A) (by simpa using this) hgram.continuousAt
    exact continuousAt_id.clm_comp (hinv.clm_comp hadjc.continuousAt)
  intro A₀ hA₀
  exact ((hcont A₀ hA₀).continuousWithinAt).congr (fun A hA ↦ hformula A hA) (hformula A₀ hA₀)

## Key steps

1. Riesz construction of the adjoint: A*y := (toDual ℝ ℝⁿ)⁻¹(x ↦ ⟪y, Ax⟫), a continuous linear map A ↦ A* with ⟪A*y, x⟫ = ⟪y, Ax⟫ (no extra import)
2. For injective A the Gram operator A*A on ℝⁿ is injective (⟨A*Av, v⟩ = |Av|²), hence bijective in finite dimension and a unit of L(ℝⁿ, ℝⁿ)
3. Π(A) = Φ(A) := A ∘ Ring.inverse(A*A) ∘ A* for injective A, by the orthogonality characterization of the projection
4. Φ is continuous at every injective A₀: A ↦ A* is continuous, Ring.inverse is continuous at units, and composition is continuous
5. Π agrees with Φ on the injective set, so ContinuousWithinAt.congr makes Π continuous on that set

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `git diff ff75f52 2cce809724fc09db16dc21873e5f9cd1ee6e2dfa -- GMT/ lakefile.toml lake-manifest.json GMT.lean`
- `rg -n "theorem inverse_continuousAt|theorem eq_starProjection_of_mem_of_inner_eq_zero|theorem continuousOn_iff'|theorem _root_.Measurable.stronglyMeasurable|theorem Measurable.find|theorem measurable_find |theorem ContinuousOn.measurable_piecewise|theorem adjoint_inner_left|def adjoint " <snapshot>/mathlib/Mathlib`
- `rg -n "isOpen_setOf_injective|isOpen_injective|starProjection.*[Cc]ontinu|[Cc]ontinu.*starProjection" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem .*isUnit_iff|isUnit_toLinearMap|injective_iff_surjective|theorem mul_inverse_cancel|clm_comp|instMeasurableSpace|instBorelSpace|invFunOn_mem|invFunOn_eq|leftInvOn_invFunOn|of_dist_le_mul|FiniteDimensional.proper" <snapshot>/mathlib/Mathlib`
- `rg -n "starProjection|orthogonalProjection" .lake/packages/simongmt/Poincare/SimonGMT | rg -i "contin|measurab"; rg -n "Measurable.find|measurable_piecewise|Nat.find" .lake/packages/simongmt/Poincare/SimonGMT`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-ptf-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-ptf-decomp/olean lean /tmp/ch04-ptf-decomp/Avail.lean Avail2.lean Avail3.lean (#check under the frozen imports only)`
- `python3 -I /tmp/ch04-ptf-decomp/scripts/gen.py children.json gen (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean gen/Challenge_*.lean`
- `lean /tmp/ch04-ptf-decomp/Synth_frozen.lean /tmp/ch04-ptf-decomp/Synth_imports.lean (#synth instance comparison)`
- `lean /tmp/ch04-ptf-decomp/Assembly.lean (parent frozen type from sorry'd children)`
- `lean /tmp/ch04-ptf-decomp/Frozen1.lean; lean /tmp/ch04-ptf-decomp/Frozen23.lean (complete proofs, frozen imports only, #print axioms)`
- `python3 -I /tmp/ch04-ptf-decomp/scripts/sim.py (controller leaf_verification.check_source_delta on each single-theorem insertion)`
- `lean GMT/Ch04/Submission.lean -o /tmp/ch04-ptf-decomp/sim2-olean/GMT/Ch04/Submission.olean (cwd simroot2); lean /tmp/ch04-ptf-decomp/gen-sim/SolAx_*.lean (comparator-style NodeSolution + #print axioms)`
- `grep -c <name> dag.json; grep -rl <name> nodes/; git grep -l <names> over every ref from git for-each-ref`
- `git show <ref>:GMT/Ch04/Submission.lean | grep '^import' over every ref (import-change scan)`
- `python3 survey of nodes/*/decomposition-v*.json should_split decisions; grep decomposition nodes/*/rlcr-plan-v1.md`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-lusin-exhaustion-a1/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-lusin-exhaustion-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/tmp/ch04-ptf-decomp/Assembly.lean`
- `/tmp/ch04-ptf-decomp/Frozen1.lean`
- `/tmp/ch04-ptf-decomp/Frozen23.lean`
- `/tmp/ch04-ptf-decomp/simroot2/GMT/Ch04/Submission.lean`
- `/tmp/ch04-ptf-decomp/scripts/sim.py`
- `/tmp/ch04-ptf-decomp/scripts/gen.py`

Contract and proof base:
- The snapshot Contract.lean and the workspace Contract.lean and Submission.lean all have sha256 6e58e5dd…0f4770b.
- The node's proof base 2cce8097 changes no Lean or Lake input (empty diff from ff75f52).

Pinned Mathlib 25730c7c — present and used (snapshot path:line):
- NormedRing.inverse_continuousAt (Analysis/Normed/Ring/Units.lean:183)
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Analysis/InnerProductSpace/Projection/Basic.lean:180)
- ContinuousLinearMap.isUnit_iff_bijective (Analysis/Normed/Operator/Banach.lean:459)
- LinearMap.injective_iff_surjective (LinearAlgebra/FiniteDimensional/Basic.lean:308)
- Ring.mul_inverse_cancel (Algebra/GroupWithZero/Units/Basic.lean:99)
- Continuous/ContinuousAt.clm_comp (Analysis/Normed/Operator/BoundedLinearMaps.lean:448–459)
- continuousOn_iff' (Topology/ContinuousOn.lean:124; cite as _root_.continuousOn_iff' under open Metric)
- ContinuousOn.measurable_piecewise (MeasureTheory/Constructions/BorelSpace/Basic.lean:523)
- Measurable.find (MeasureTheory/MeasurableSpace/Constructions.lean:515)
- Measurable.stronglyMeasurable (MeasureTheory/Function/StronglyMeasurable/Basic.lean:691)
- ContinuousLinearMap.instMeasurableSpace / instBorelSpace (MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean:47,50)
- Function.invFunOn_mem / invFunOn_eq and Set.InjOn.leftInvOn_invFunOn (Data/Set/Function.lean:963,966,987)
- LipschitzOnWith.of_dist_le_mul (Topology/MetricSpace/Lipschitz.lean:57)
- InnerProductSpace.toDual with toDual_symm_apply, and ContinuousLinearMap.toSesqForm with toSesqForm_apply_coe, plus ContinuousLinearMap.compSL.
All of these resolve under the frozen imports (#check under import GMT.Ch04.Submission alone).

Unavailable under the frozen imports:
- ContinuousLinearMap.adjoint and LinearMap.adjoint (Analysis/InnerProductSpace/Adjoint.lean:112) are unknown constants.
- The controller's leaf_verification.check_source_delta rejects any added import, so a leaf cannot bring them in.
- Hence child 1 rebuilds Mathlib's adjointAux from toDual and toSesqForm.

No-match results:
- No Mathlib or SimonGMT lemma gives continuity of A ↦ (range A).starProjection. ContinuousLinearMap.isOpen_injective (FiniteDimension.lean:263) exists but is not needed.
- No ready-made countable pasting lemma for relatively continuous fields exists beyond the Measurable.find and measurable_piecewise ingredients.
- SimonGMT offers only an a.e.-measurability transfer (Chapter03.aemeasurable_starProjection_of_approximateTangentField, Rectifiable.lean:260), which does not apply here.

Elaboration and proof checks:
- The three child types pass validate_lean_statement and elaborate as comparator NodeChallenge files in contract scope.
- The parent's frozen type follows from them (Assembly.lean).
- Complete frozen-import proofs of all three children and the parent assembly pass check_source_delta as single-theorem insertions and compile in a copy of Submission.lean. The comparator-style solutions use axioms propext, Classical.choice and Quot.sound only.
- Instance resolution is unchanged by extra imports.
- The proposed names are unused in dag.json, nodes/ and all git refs.
