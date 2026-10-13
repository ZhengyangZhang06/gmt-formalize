# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.graph_cutoff_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 1, 5 and 6 of the parent proof (φ := (η∘Q)·P^#ψ is a test form supported in C, and it agrees with P^#ψ near the graph: η∘Q ≡ 1 near Φ(v) for v ∈ spt ψ, and both forms vanish near Φ(v) for v ∉ spt ψ), stated for an arbitrary smooth compactly supported ψ with spt ψ ⊆ B_s(0). The spanning property of (ι, ι') is a hypothesis here; the parent supplies it from Submission.dgcr_orthogonal_coordinates. Sibling lemma used (as the frozen declaration): Submission.dgcr_bwd_normal_cutoff.
Notation: ℝ^p means Euclid p = EuclideanSpace ℝ (Fin p); e_l := EuclideanSpace.single l (1 : ℝ) is the l-th standard basis vector; for an (m+1)-tuple w, removeNth i w := Fin.removeNth i w is the m-tuple with entry i deleted, so (removeNth i w)(l) = w(i.succAbove l) (Fin.removeNth_apply); Covector E m = E [⋀^Fin m]→L[ℝ] ℝ (continuous alternating m-linear forms); DifferentialForm E m = E → Covector E m; exteriorDerivative = Mathlib's extDeriv (Poincare.SimonGMT.Chapter06.exteriorDerivative is an abbrev), with the alternating-sum formula dω(x)(w₀,…,w_m) = Σᵢ (−1)^i • D[y ↦ ω(y)(removeNth i w)](x)(wᵢ) for ω differentiable at x (exteriorDerivative_apply); IsSmoothForm ψ := ContDiff ℝ ∞ ψ where ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞) (in the frozen contract scope `∞` denotes ENNReal's ∞ because of `open scoped ENNReal`, so write the order as (⊤ : ℕ∞)). Also L' := ι'* = ContinuousLinearMap.adjoint ι'.toContinuousLinearMap, Pr(x) := L(x − z), Q(x) := L'(x − z), Φ(v) := z + ιv + ι'u(v), and TestFormOn U m consists of the smooth compactly supported m-forms φ with tsupport φ ⊆ U.
1. Adjoint identities: L(ιv) = v, L(ι'w) = 0, L'(ιv) = 0 and L'(ι'w) = w for all v ∈ ℝ^{m+1}, w ∈ ℝ^k. Each is proved by pairing with an arbitrary y and using ext_inner_right: ⟨L(ιv), y⟩ = ⟨ιv, ιy⟩ = ⟨v, y⟩ and ⟨L'(ι'w), y⟩ = ⟨ι'w, ι'y⟩ = ⟨w, y⟩ (ContinuousLinearMap.adjoint_inner_left, LinearIsometry.inner_map_map); ⟨L(ι'w), y⟩ = ⟨ι'w, ιy⟩ = ⟨ιy, ι'w⟩ = 0 (real_inner_comm and orthogonality) and ⟨L'(ιv), y⟩ = ⟨ιv, ι'y⟩ = 0 (orthogonality), with ⟨0, y⟩ = 0 (inner_zero_left).
2. Decomposition: z + ι(Pr x) + ι'(Q x) = x for every x. Indeed, by the spanning hypothesis x − z = ιv₀ + ι'w₀ for some v₀, w₀; by step 1, Pr x = L(ιv₀ + ι'w₀) = v₀ and Q x = w₀; hence z + ιv₀ + ι'w₀ = z + (x − z) = x (add_assoc applied with explicit first argument z, then add_sub_cancel; note that an unqualified `rw [add_assoc]` would try to rewrite the type index m + 1 + k).
3. Cutoff. K := tsupport ψ is compact (HasCompactSupport ψ) and K ⊆ B_s(0). As u is continuous on B_s(0) ⊇ K, u(K) is compact (IsCompact.image_of_continuousOn with ContinuousOn.mono), and u(K) ⊆ B_h(0) by the hypothesis u(B_s(0)) ⊆ B_h(0). The sibling Submission.dgcr_bwd_normal_cutoff (applied to k, u(K), h and 0 < h) gives η : ℝ^k → ℝ, C^∞, with compact support, tsupport η ⊆ B_h(0), and such that every point of u(K) has a neighbourhood on which η ≡ 1.
4. The test form. Since −Lz + Lx = L(x − z) (map_sub, neg_add_eq_sub), (P^#ψ)(x) = ψ(Pr x).compContinuousLinearMap L. Define φ(x) := η(Q x) • (P^#ψ)(x). The map x ↦ Q x = L'(x − z) is affine, hence C^∞, so x ↦ η(Q x) is C^∞ (ContDiff.comp); P^#ψ is smooth (Poincare.SimonGMT.Chapter06.affinePullbackForm_isSmoothForm); hence φ is smooth (ContDiff.smul). (Write the smoothness order as (⊤ : ℕ∞), not ∞, in the contract scope.)
5. Support. S := {x : Pr x ∈ K ∧ Q x ∈ tsupport η} is closed (preimages of the closed sets K and tsupport η under the continuous maps Pr and Q, intersected). If x ∉ S then φ(x) = 0: if Pr x ∉ K then ψ(Pr x) = 0 (image_eq_zero_of_notMem_tsupport), so (P^#ψ)(x) = 0 (ext; simp) and φ(x) = η(Q x) • 0 = 0; if Q x ∉ tsupport η then η(Q x) = 0 and φ(x) = 0 • (P^#ψ)(x) = 0. Thus support φ ⊆ S, and since S is closed, tsupport φ ⊆ S (closure_minimal). Let F(v, w) := z + ιv + ι'w, a continuous map ℝ^{m+1} × ℝ^k → ℝ^{m+1+k}. By step 2, each x ∈ S equals F(Pr x, Q x) with (Pr x, Q x) ∈ K × tsupport η, so S ⊆ F(K × tsupport η). The set K × tsupport η is compact (IsCompact.prod), so F(K × tsupport η) is compact (IsCompact.image), and F(K × tsupport η) ⊆ C because K ⊆ B_s(0) and tsupport η ⊆ B_h(0). Therefore tsupport φ ⊆ F(K × tsupport η) ⊆ C ⊆ U, and φ has compact support (IsCompact.of_isClosed_subset with isClosed_tsupport). Hence φ, packaged with these facts, is an element of TestFormOn U m (smooth, compactly supported, tsupport ⊆ U), and tsupport φ ⊆ C is the first conclusion.
6. Germ property. Fix v ∈ B_s(0) and x₀ := Φ(v) = z + ιv + ι'u(v). By step 1, Q x₀ = L'(ιv + ι'u(v)) = u(v) and Pr x₀ = v (rewrite x₀ − z = ιv + ι'u(v) by add_assoc z and add_sub_cancel_left, then map_add and step 1).
 (i) If v ∈ K: u(v) ∈ u(K), so by step 3 η ≡ 1 on a neighbourhood of u(v). The map Q is continuous with Q x₀ = u(v), so Q tends to u(v) along 𝓝 x₀ and η(Q x) = 1 for all x near x₀ (Filter.Tendsto.eventually). For such x, φ(x) = 1 • (P^#ψ)(x) = (P^#ψ)(x) (one_smul).
 (ii) If v ∉ K: O := {x : Pr x ∉ K} is open (the complement of the closed set K pulled back by the continuous map Pr) and x₀ ∈ O since Pr x₀ = v ∉ K. For x ∈ O, ψ(Pr x) = 0, so (P^#ψ)(x) = 0 and φ(x) = η(Q x) • 0 = 0 = (P^#ψ)(x) (smul_zero).
 In both cases φ =ᶠ[𝓝 x₀] P^#ψ (filter_upwards), which is the second conclusion. ∎
Formalization note: this child is a machine leaf (one theorem `Submission.dgcr_bwd_graph_cutoff_lift` appended inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean; no helper declarations, no set_option). The following tactic proof was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context under default maxHeartbeats, passes the workflow's leaf source-delta check, and depends only on propext, Classical.choice, Quot.sound (and the sibling declaration named above); it may be used verbatim:
theorem Submission.dgcr_bwd_graph_cutoff_lift : ∀ (m k : ℕ) (U : Set (Euclid (m + 1 + k))) (ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid (m + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + 1 + k)) (u : Euclid (m + 1) → Euclid k) (z : Euclid (m + 1 + k)) (s h : ℝ) (ψ : DifferentialForm (Euclid (m + 1)) m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ x : Euclid (m + 1 + k), ∃ v : Euclid (m + 1), ∃ w : Euclid k, x = ι v + ι' w) → 0 < h → ContinuousOn u (ball 0 s) → (∀ v ∈ ball (0 : Euclid (m + 1)) s, u v ∈ ball (0 : Euclid k) h) → {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ⊆ U → IsSmoothForm ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid (m + 1)) s → ∃ φ : TestFormOn U m, tsupport (φ : DifferentialForm (Euclid (m + 1 + k)) m) ⊆ {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ∧ ∀ v ∈ ball (0 : Euclid (m + 1)) s, (φ : DifferentialForm (Euclid (m + 1 + k)) m) =ᶠ[𝓝 (z + ι v + ι' (u v))] affinePullbackForm (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) (-(ContinuousLinearMap.adjoint ι.toContinuousLinearMap z)) ψ := by
  intro m k U ι ι' u z s h ψ hperp hspan hh hu hmaps hCU hψs hψc hψsupp
  set L := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hL
  set L' := ContinuousLinearMap.adjoint ι'.toContinuousLinearMap with hL'
  have hLι : ∀ v', L (ι v') = v' := by
    intro v'
    apply ext_inner_right ℝ
    intro y
    rw [hL, ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map v' y
  have hLι' : ∀ w, L (ι' w) = 0 := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [hL, ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact hperp y w
  have hL'ι : ∀ v', L' (ι v') = 0 := by
    intro v'
    apply ext_inner_right ℝ
    intro y
    rw [hL', ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    exact hperp v' y
  have hL'ι' : ∀ w, L' (ι' w) = w := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [hL', ContinuousLinearMap.adjoint_inner_left]
    exact ι'.inner_map_map w y
  have hdec : ∀ x, z + ι (L (x - z)) + ι' (L' (x - z)) = x := by
    intro x
    obtain ⟨v₀, w₀, hx⟩ := hspan (x - z)
    have h1 : L (x - z) = v₀ := by rw [hx, map_add, hLι, hLι', add_zero]
    have h2 : L' (x - z) = w₀ := by rw [hx, map_add, hL'ι, hL'ι', zero_add]
    rw [h1, h2]
    calc z + ι v₀ + ι' w₀ = z + (ι v₀ + ι' w₀) := add_assoc _ _ _
      _ = z + (x - z) := by rw [hx]
      _ = x := add_sub_cancel z x
  have hK : IsCompact (tsupport ψ) := hψc
  obtain ⟨η, hηs, hηc, hηsupp, hη1⟩ := Submission.dgcr_bwd_normal_cutoff k (u '' tsupport ψ) h hh
    (hK.image_of_continuousOn (hu.mono hψsupp))
    (by rintro _ ⟨v, hv, rfl⟩; exact hmaps v (hψsupp hv))
  have hPr : Continuous (fun x : Euclid (m + 1 + k) => L (x - z)) :=
    L.continuous.comp (continuous_id.sub continuous_const)
  have hQ : Continuous (fun x : Euclid (m + 1 + k) => L' (x - z)) :=
    L'.continuous.comp (continuous_id.sub continuous_const)
  have hPapply : ∀ x, affinePullbackForm L (-(L z)) ψ x = (ψ (L (x - z))).compContinuousLinearMap L := by
    intro x
    simp only [affinePullbackForm, map_sub, neg_add_eq_sub]
  let φ : DifferentialForm (Euclid (m + 1 + k)) m :=
    fun x => η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x
  have hφs : IsSmoothForm φ := by
    have hηQ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid (m + 1 + k) => η (L' (x - z))) :=
      hηs.comp (L'.contDiff.comp (contDiff_id.sub contDiff_const))
    exact hηQ.smul (affinePullbackForm_isSmoothForm L (-(L z)) hψs)
  let F : Euclid (m + 1) × Euclid k → Euclid (m + 1 + k) := fun p => z + ι p.1 + ι' p.2
  have hF : Continuous F := by
    have h1 : Continuous (fun p : Euclid (m + 1) × Euclid k => ι p.1) := ι.continuous.comp continuous_fst
    have h2 : Continuous (fun p : Euclid (m + 1) × Euclid k => ι' p.2) := ι'.continuous.comp continuous_snd
    exact (continuous_const.add h1).add h2
  have hS : IsClosed {x : Euclid (m + 1 + k) | L (x - z) ∈ tsupport ψ ∧ L' (x - z) ∈ tsupport η} :=
    ((isClosed_tsupport ψ).preimage hPr).inter ((isClosed_tsupport η).preimage hQ)
  have hsuppS : support φ ⊆ {x | L (x - z) ∈ tsupport ψ ∧ L' (x - z) ∈ tsupport η} := by
    intro x hx
    by_contra hcon
    apply hx
    rcases not_and_or.mp hcon with h1 | h1
    · have h0 : ψ (L (x - z)) = 0 := image_eq_zero_of_notMem_tsupport h1
      have hP0 : affinePullbackForm L (-(L z)) ψ x = 0 := by
        rw [hPapply, h0]
        ext w
        simp
      show η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x = 0
      rw [hP0, smul_zero]
    · have h0 : η (L' (x - z)) = 0 := image_eq_zero_of_notMem_tsupport h1
      show η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x = 0
      rw [h0, zero_smul]
  have hsupp : tsupport φ ⊆ F '' (tsupport ψ ×ˢ tsupport η) := by
    refine (closure_minimal hsuppS hS).trans ?_
    rintro x ⟨hx1, hx2⟩
    exact ⟨(L (x - z), L' (x - z)), ⟨hx1, hx2⟩, hdec x⟩
  have hFC : F '' (tsupport ψ ×ˢ tsupport η) ⊆
      {x | ∃ v ∈ ball (0 : Euclid (m + 1)) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} := by
    rintro _ ⟨⟨v, w⟩, ⟨hv, hw⟩, rfl⟩
    exact ⟨v, hψsupp hv, w, hηsupp hw, rfl⟩
  have hcomp : IsCompact (F '' (tsupport ψ ×ˢ tsupport η)) := (hK.prod hηc).image hF
  refine ⟨⟨φ, ⟨hφs, hcomp.of_isClosed_subset (isClosed_tsupport _) hsupp⟩,
    (hsupp.trans hFC).trans hCU⟩, hsupp.trans hFC, ?_⟩
  intro v hv
  have hQv : L' (z + ι v + ι' (u v) - z) = u v := by
    rw [add_assoc z, add_sub_cancel_left, map_add, hL'ι, hL'ι', zero_add]
  have hPv : L (z + ι v + ι' (u v) - z) = v := by
    rw [add_assoc z, add_sub_cancel_left, map_add, hLι, hLι', add_zero]
  by_cases hvK : v ∈ tsupport ψ
  · have hev : ∀ᶠ y in 𝓝 (u v), η y = 1 := hη1 (u v) ⟨v, hvK, rfl⟩
    have hT := hQ.tendsto (z + ι v + ι' (u v))
    rw [hQv] at hT
    filter_upwards [hT.eventually hev] with x hx
    show η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x = affinePullbackForm L (-(L z)) ψ x
    rw [hx, one_smul]
  · have hopen : IsOpen {x : Euclid (m + 1 + k) | L (x - z) ∉ tsupport ψ} :=
      (isClosed_tsupport ψ).isOpen_compl.preimage hPr
    filter_upwards [hopen.mem_nhds (show L (z + ι v + ι' (u v) - z) ∉ tsupport ψ by rw [hPv]; exact hvK)] with x hx
    have h0 : ψ (L (x - z)) = 0 := image_eq_zero_of_notMem_tsupport hx
    have hP0 : affinePullbackForm L (-(L z)) ψ x = 0 := by
      rw [hPapply, h0]
      ext w
      simp
    show η (L' (x - z)) • affinePullbackForm L (-(L z)) ψ x = affinePullbackForm L (-(L z)) ψ x
    rw [hP0, smul_zero]

## Key steps

1. Adjoint identities for L = ι*, L' = ι'*; spanning gives x = z + ι(L(x−z)) + ι'(L'(x−z)).
2. Apply Submission.dgcr_bwd_normal_cutoff to the compact set u(spt ψ) ⊆ B_h(0) to get η.
3. φ(x) := η(L'(x−z)) • (P^#ψ)(x) is smooth.
4. support φ ⊆ {Pr ∈ spt ψ, Q ∈ spt η} (closed) ⊆ F(spt ψ × spt η), compact and ⊆ C ⊆ U; so φ ∈ TestFormOn U m with tsupport φ ⊆ C.
5. Near Φ(v): if v ∈ spt ψ then η∘Q ≡ 1 (continuity of Q, Q Φ(v) = u(v)); otherwise P^#ψ ≡ 0 near Φ(v); hence φ =ᶠ P^#ψ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (byte-identical); manifest.json project_commit b4d606d, mathlib_commit 25730c7c; simongmt package at 2b36630`
- `rg -n 'extDeriv_eq|theorem extDeriv_apply|theorem extDeriv_pullback' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `rg -n 'theorem curryLeft_apply_apply|def curryLeft' mathlib/Mathlib/Analysis/Normed/Module/Alternating/*.lean`
- `rg -n 'cons_removeNth_eq_comp_cycleRange_symm|sign_cycleRange' mathlib/Mathlib`
- `rg -n 'theorem det_self|theorem det_apply' mathlib/Mathlib/LinearAlgebra/Determinant.lean; rg -n 'Continuous.matrix_det|continuous_matrix' mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `rg -n 'map_perm|map_eq_zero_of_eq' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean; rg -n 'adjoint_inner_left' mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `rg -n 'theorem exists_lt_subset_ball' mathlib/Mathlib; rg -n 'one_of_mem_closedBall|tsupport_eq|hasCompactSupport|contDiff' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `rg -n 'continuous_of_finiteDimensional' mathlib/Mathlib (only LinearMap.continuous_of_finiteDimensional; no MultilinearMap variant)`
- `rg -n 'fderiv_mul_const|DifferentiableAt.smul_const|tsupport_smul_subset_left|image_eq_zero_of_notMem_tsupport|setIntegral_congr_fun' mathlib/Mathlib`
- `rg -n 'exteriorDerivative_apply|exteriorDerivative_affinePullbackForm|affinePullbackForm_isSmoothForm|def affinePullbackForm|tsupport_exteriorDerivative_subset|GeometricCurrentOn.boundary_apply|def exteriorDerivativeTestOn|def IsSmoothForm|abbrev TestFormOn' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,AffineCurrentPushforward}.lean`
- `lake env lean /tmp/bwd-split-work/Names.lean and Names2.lean: #check of all cited names after import GMT.Ch07.Submission`
- `python3 lean_contract.validate_lean_statement on the 6 child types; gmt-compare.contract_scope replay; lake env lean /tmp/bwd-split-work/Elab.lean (types elaborate in the comparator scope)`
- `lake env lean /tmp/bwd-split-work/Full.lean: six child proofs as GMT.Ch07.Submission.* theorems, the exact parent type proved from them plus dgcr_orthogonal_coordinates as a hypothesis, comparator-style `exact Submission.X` checks, #print axioms`
- `lake env lean /tmp/bwd-split-work/SimSubmission.lean: frozen Submission.lean with all six children inserted before `end GMT.Ch07`; leaf_verification.check_source_delta simulated for each insertion`
- `grep 'dgcr_bwd_' over dag.json, nodes/*, and all 1159 git refs (git grep): no match`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-5d86c28dbf/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-07a3972eec1d/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/bwd-split-work/Elab.lean`
- `/tmp/bwd-split-work/Full.lean`
- `/tmp/bwd-split-work/SimSubmission.lean`

The snapshot is project b4d606d with Mathlib 25730c7c, and its Contract.lean is byte-identical to the workspace Submission.lean. Every cited lemma is in the import closure of GMT.Ch07.Submission.
Mathlib lemmas used: Filter.EventuallyEq.extDeriv_eq, extDeriv_apply, ContinuousAlternatingMap.curryLeft_apply_apply, Fin.cons_removeNth_eq_comp_cycleRange_symm, Fin.sign_cycleRange, Module.Basis.det_apply/det_self, Continuous.matrix_det, continuous_matrix, AlternatingMap.map_perm/map_eq_zero_of_eq, ContinuousLinearMap.adjoint_inner_left, exists_lt_subset_ball, the ContDiffBump API, fderiv_mul_const and setIntegral_congr_fun.
simongmt lemmas used: exteriorDerivative_apply, affinePullbackForm with affinePullbackForm_isSmoothForm and exteriorDerivative_affinePullbackForm, tsupport_exteriorDerivative_subset, exteriorDerivativeTestOn and GeometricCurrentOn.boundary_apply.
MultilinearMap.continuous_of_finiteDimensional has no match, so the determinant covector proves its continuity explicitly.
Lean checks:
- All 6 child types pass validate_lean_statement and elaborate in the comparator contract scope.
- Each child compiles as a single theorem under default heartbeats and passes the leaf source-delta check.
- The exact parent type follows from children coordinate_form, graph_pullback_extderiv and graph_cutoff_lift plus dgcr_orthogonal_coordinates, with axioms only propext, Classical.choice and Quot.sound.
- No dgcr_bwd_ name collision exists in the DAG, node records or git refs.
