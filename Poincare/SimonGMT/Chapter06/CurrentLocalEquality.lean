module

public import Poincare.SimonGMT.Chapter06.Currents

@[expose] public section

/-!
# Simon GMT, Chapter 6, §2.16: equality of currents on an open subset

This file implements the book's local-equality terminology by restricting
domain currents along an inclusion of open sets.
-/

open Filter Set
open scoped Topology

namespace Poincare.SimonGMT.Chapter06

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Regard a test form supported in `W` as a test form on a larger domain
`U`. -/
def testFormOnInclusion {W U : Set E} (hWU : W ⊆ U) (n : ℕ) :
    TestFormOn (E := E) W n →ₗ[ℝ] TestFormOn (E := E) U n where
  toFun omega := ⟨omega, omega.property.1, omega.property.2.trans hWU⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem testFormOnInclusion_coe {W U : Set E} (hWU : W ⊆ U)
    (n : ℕ) (omega : TestFormOn (E := E) W n) :
    ((testFormOnInclusion hWU n omega : TestFormOn (E := E) U n) :
      DifferentialForm E n) = omega :=
  rfl

/-- Restriction of a current from `U` to an included domain `W`. -/
def GeometricCurrentOn.restrictDomain {W U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U n) (hWU : W ⊆ U) :
    GeometricCurrentOn (E := E) W n where
  toCurrent := T.toCurrent.comp (testFormOnInclusion hWU n)
  continuous' omegaSeq hconv := by
    apply T.continuous'
    rcases hconv with ⟨K, hK, hKW, hseq, homega, hderiv⟩
    exact ⟨K, hK, hKW.trans hWU, hseq, homega, hderiv⟩

@[simp] theorem GeometricCurrentOn.restrictDomain_apply
    {W U : Set E} {n : ℕ} (T : GeometricCurrentOn (E := E) U n)
    (hWU : W ⊆ U) (omega : TestFormOn (E := E) W n) :
    T.restrictDomain hWU omega = T (testFormOnInclusion hWU n omega) :=
  rfl

/-- Simon (6.2.16): currents on possibly different domains are equal in an
open common subdomain when their restrictions to that subdomain agree. -/
def CurrentsAgreeOn {U₁ U₂ : Set E} {n : ℕ}
    (S : GeometricCurrentOn (E := E) U₁ n)
    (T : GeometricCurrentOn (E := E) U₂ n)
    (W : Set E) (hW₁ : W ⊆ U₁) (hW₂ : W ⊆ U₂) : Prop :=
  S.restrictDomain hW₁ = T.restrictDomain hW₂

theorem currentsAgreeOn_iff {U₁ U₂ : Set E} {n : ℕ}
    (S : GeometricCurrentOn (E := E) U₁ n)
    (T : GeometricCurrentOn (E := E) U₂ n)
    (W : Set E) (hW₁ : W ⊆ U₁) (hW₂ : W ⊆ U₂) :
    CurrentsAgreeOn S T W hW₁ hW₂ ↔
      ∀ omega : TestFormOn (E := E) W n,
        S (testFormOnInclusion hW₁ n omega) =
          T (testFormOnInclusion hW₂ n omega) := by
  rw [CurrentsAgreeOn]
  exact GeometricCurrentOn.ext_iff

theorem currentsAgreeOn_refl {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U n) (W : Set E) (hWU : W ⊆ U) :
    CurrentsAgreeOn T T W hWU hWU :=
  rfl

theorem currentsAgreeOn_symm {U₁ U₂ : Set E} {n : ℕ}
    {S : GeometricCurrentOn (E := E) U₁ n}
    {T : GeometricCurrentOn (E := E) U₂ n}
    {W : Set E} {hW₁ : W ⊆ U₁} {hW₂ : W ⊆ U₂}
    (h : CurrentsAgreeOn S T W hW₁ hW₂) :
    CurrentsAgreeOn T S W hW₂ hW₁ :=
  h.symm

theorem currentsAgreeOn_trans {U₁ U₂ U₃ : Set E} {n : ℕ}
    {R : GeometricCurrentOn (E := E) U₁ n}
    {S : GeometricCurrentOn (E := E) U₂ n}
    {T : GeometricCurrentOn (E := E) U₃ n}
    {W : Set E} {hW₁ : W ⊆ U₁} {hW₂ : W ⊆ U₂} {hW₃ : W ⊆ U₃}
    (hRS : CurrentsAgreeOn R S W hW₁ hW₂)
    (hST : CurrentsAgreeOn S T W hW₂ hW₃) :
    CurrentsAgreeOn R T W hW₁ hW₃ :=
  hRS.trans hST

/-! ## Support in a domain -/

/-- A domain current vanishes on `W` when it kills every domain test form
whose support lies in `W`. -/
def GeometricCurrentOn.VanishesOn {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U n) (W : Set E) : Prop :=
  ∀ omega : TestFormOn (E := E) U n,
    tsupport (omega : DifferentialForm E n) ⊆ W → T omega = 0

/-- The union of the relatively compact open subsets of `U` on which a
domain current vanishes. -/
def GeometricCurrentOn.zeroRegion {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U n) : Set E :=
  ⋃₀ {W : Set E |
    IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}

/-- Simon (6.2.11): the support of a current in `U` is the relative
complement in `U` of its open zero region. -/
def GeometricCurrentOn.support {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U n) : Set E :=
  U \ T.zeroRegion

theorem GeometricCurrentOn.isOpen_zeroRegion {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U n) : IsOpen T.zeroRegion := by
  apply isOpen_sUnion
  intro W hW
  exact hW.1

theorem GeometricCurrentOn.support_subset_domain {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U n) : T.support ⊆ U :=
  sdiff_subset

/-- The support is relatively closed in the current domain. -/
theorem GeometricCurrentOn.isClosed_supportInDomain {U : Set E} {n : ℕ}
    (T : GeometricCurrentOn (E := E) U n) :
    IsClosed {x : U | (x : E) ∈ T.support} := by
  have heq : {x : U | (x : E) ∈ T.support} =
      (Subtype.val : U → E) ⁻¹' (T.zeroRegion)ᶜ := by
    ext x
    simp [GeometricCurrentOn.support]
  rw [heq]
  exact T.isOpen_zeroRegion.isClosed_compl.preimage continuous_subtype_val

end

end Poincare.SimonGMT.Chapter06
