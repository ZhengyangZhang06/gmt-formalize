# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.coeff_minor_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (the splitting into D₁(j) + D₂(j), with (a) the uniform-continuity estimate and (b) the Claim of step 3), for an arbitrary minor M_{a,b} and an arbitrary continuous compactly supported scalar coefficient g; in the parent, g = α_γ = (y ↦ euclideanCovectorCoordinate (α y) γ), r = k, a = γ and b = id. This is the estimate “∫ψ(ω_γ∘u_j)M_γ(Du_j) − ∫ψ(ω_γ∘u)M_γ(Du) = ∫ψ(ω_γ∘u_j − ω_γ∘u)M_γ(Du_j) + ∫ψ(ω_γ∘u)(M_γ(Du_j) − M_γ(Du)) → 0” quoted in the parent proof.

Notation. λ = Lebesgue measure; ∫_Ω = integral over Ω with respect to λ; M_j := M_{a,b}(u_j), M_0 := M_{a,b}(u₀); B := r!·C^r.

1. (Bounds and measurability.) For u ∈ {u_j, u₀} and w ∈ Ω: ‖fderiv ℝ u w‖ ≤ C (norm_fderiv_le_of_lipschitzOn, since Ω ∈ 𝓝 w), so every entry of the minor has absolute value ≤ C (PiLp.norm_apply_le, ‖EuclideanSpace.single i 1‖ = 1) and |M_{a,b}(u)(w)| ≤ B (Leibniz formula and triangle inequality, from Matrix.det_apply). M_{a,b}(u) is Borel measurable (measurable_fderiv_apply_const; the determinant is continuous in the entries). g is continuous with compact support, so |g| ≤ G for a constant G (Continuous.bounded_above_of_compact_support) and g is uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). u is continuous on Ω (LipschitzOnWith.continuousOn), so g∘u is continuous on Ω and a.e.-strongly measurable for λ restricted to the open, hence measurable, set Ω (ContinuousOn.aestronglyMeasurable).

2. (Integrability.) Put η := ψ·(g∘u₀). Since ψ is integrable on Ω and g∘u₀ is a.e.-strongly measurable on Ω and bounded by G, η is integrable on Ω (Integrable.mul_bdd). Likewise ψ·(g∘u_j − g∘u₀) is integrable on Ω (bounded by 2G|ψ|), and multiplying a function integrable on Ω by M_j or M_0 (measurable and bounded by B on Ω) keeps it integrable on Ω. In particular ψ·(g∘u_j)·M_j = ψ·(g∘u_j − g∘u₀)·M_j + η·M_j with both summands integrable on Ω.

3. (Splitting.) Hence ∫_Ω ψ·(g∘u_j)·M_j = D₁(j) + ∫_Ω η·M_j with D₁(j) := ∫_Ω ψ·(g∘u_j − g∘u₀)·M_j, while ∫_Ω ψ·(g∘u₀)·M_0 = 0 + ∫_Ω η·M_0.

4. (D₁(j) → 0.) Since g is uniformly continuous and u_j → u₀ uniformly on Ω, g∘u_j → g∘u₀ uniformly on Ω (UniformContinuous.comp_tendstoUniformlyOn). Let ε > 0, I := ∫_Ω |ψ| and δ := ε/(2(BI + 1)) > 0. There is N with |g(u_j(w)) − g(u₀(w))| < δ for all j ≥ N and w ∈ Ω (Metric.tendstoUniformlyOn_iff). For such j, |ψ(w)·(g(u_j(w)) − g(u₀(w)))·M_j(w)| ≤ δB|ψ(w)| for w ∈ Ω, so |D₁(j)| ≤ δBI < ε (norm_integral_le_of_norm_le). Thus D₁(j) → 0.

5. (Weak-* convergence.) The sibling minor_weak_star, applied to v := u (so v_j = u_j), v₀ := u₀, the same r, a, b and the function η, which is integrable on Ω by Step 2, gives ∫_Ω η·M_j → ∫_Ω η·M_0.

6. (Conclusion.) By Steps 3–5, ∫_Ω ψ·(g∘u_j)·M_j = D₁(j) + ∫_Ω η·M_j → 0 + ∫_Ω η·M_0 = ∫_Ω ψ·(g∘u₀)·M_0. ∎

Reference implementation (compiled). The following single theorem, whose hypothesis hE is the frozen type of the sibling minor_weak_star (instantiate hE := Submission.deformation_ipl_mwc_minor_weak_star), was compiled with `lake env lean` against the frozen `import GMT.Ch06.Submission` in the exact comparator scope. It needs no new import, is fully proved, and #print axioms gives propext, Classical.choice, Quot.sound. It follows Steps 1–6 above; the prose proof governs.

theorem _root_.TestMWC4.coeff_ref (hE : ∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : ℕ → Eucl k → Eucl Q) (v₀ : Eucl k → Eucl Q), IsOpen Ω → (∀ j, LipschitzOnWith C (v j) Ω) → LipschitzOnWith C v₀ Ω → TendstoUniformlyOn v v₀ atTop Ω → ∀ (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k) (η : Eucl k → ℝ), IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ (v j) w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ v₀ w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))))) : (∀ (k Q : ℕ) (Ω : Set (Eucl k)) (ψ : Eucl k → ℝ) (g : Eucl Q → ℝ) (C : ℝ≥0) (u : ℕ → Eucl k → Eucl Q) (u₀ : Eucl k → Eucl Q) (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k), IsOpen Ω → IntegrableOn ψ Ω (volume : Measure (Eucl k)) → Continuous g → HasCompactSupport g → (∀ j, LipschitzOnWith C (u j) Ω) → LipschitzOnWith C u₀ Ω → TendstoUniformlyOn u u₀ atTop Ω → Tendsto (fun j => ∫ w in Ω, ψ w * g (u j w) * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ (u j) w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, ψ w * g (u₀ w) * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ u₀ w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))))) := by
  intro k Q Ω ψ g C u u₀ r a b hΩ hψ hg hgc hu hu₀ hconv
  -- |det A| ≤ n! c^n for entries bounded by c (Matrix.det_le is not imported)
  have abs_det_le : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ),
      (∀ i j, |A i j| ≤ c) → |A.det| ≤ (Nat.factorial n : ℝ) * c ^ n := by
    intro n A c hA
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), c ^ n := by
          gcongr with σ
          have h1 : |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [h1, Finset.abs_prod]
          calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, c := by
                gcongr with i
                exact hA _ _
            _ = c ^ n := by simp
      _ = (Nat.factorial n : ℝ) * c ^ n := by simp [Fintype.card_perm]
  -- bound and measurability of the minors of a map Lipschitz on Ω
  have minor_facts : ∀ {n : ℕ} (a : Fin n → Fin Q) (b : Fin n → Fin k) (u : Eucl k → Eucl Q),
      LipschitzOnWith C u Ω →
      (∀ w ∈ Ω, |Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))| ≤ (Nat.factorial n : ℝ) * (C : ℝ) ^ n) ∧
      Measurable (fun w => Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))) := by
    intro n a b u hu
    constructor
    · intro w hw
      apply abs_det_le
      intro t s
      have h1 : ‖fderiv ℝ u w‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hu
      calc |EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1))|
          = ‖(fderiv ℝ u w (EuclideanSpace.single (b s) 1)) (a t)‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ u w (EuclideanSpace.single (b s) 1)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖fderiv ℝ u w‖ * ‖EuclideanSpace.single (b s) (1 : ℝ)‖ := (fderiv ℝ u w).le_opNorm _
        _ ≤ C := by simpa using h1
    · have hdetc : Continuous fun A : Fin n → Fin n → ℝ => (Matrix.of A).det :=
        Continuous.matrix_det continuous_id
      have : ∀ t s : Fin n, Measurable fun w =>
          EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)) := fun t s =>
        (EuclideanSpace.proj (a t)).continuous.measurable.comp (measurable_fderiv_apply_const ℝ u _)
      exact hdetc.measurable.comp (measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => this t s)
  let M : (Eucl k → Eucl Q) → Eucl k → ℝ := fun v w => Matrix.det (Matrix.of fun t s : Fin r =>
    EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1)))
  set B : ℝ := (Nat.factorial r : ℝ) * (C : ℝ) ^ r with hB
  have hB0 : 0 ≤ B := by positivity
  have hMb : ∀ v, LipschitzOnWith C v Ω → ∀ w ∈ Ω, |M v w| ≤ B := fun v hv =>
    (minor_facts a b v hv).1
  have hMm : ∀ v, LipschitzOnWith C v Ω → Measurable (M v) := fun v hv =>
    (minor_facts a b v hv).2
  obtain ⟨G, hG⟩ := hg.bounded_above_of_compact_support hgc
  have hgm : ∀ v, LipschitzOnWith C v Ω →
      AEStronglyMeasurable (fun w => g (v w)) ((volume : Measure (Eucl k)).restrict Ω) :=
    fun v hv => (hg.comp_continuousOn hv.continuousOn).aestronglyMeasurable hΩ.measurableSet
  let η : Eucl k → ℝ := fun w => ψ w * g (u₀ w)
  have hη : IntegrableOn η Ω (volume : Measure (Eucl k)) :=
    Integrable.mul_bdd hψ (hgm u₀ hu₀) (ae_of_all _ fun w => hG _)
  have hint1 : ∀ j, IntegrableOn (fun w => ψ w * (g (u j w) - g (u₀ w)) * M (u j) w) Ω
      (volume : Measure (Eucl k)) := by
    intro j
    refine Integrable.mul_bdd (c := B) ?_ (hMm _ (hu j)).aestronglyMeasurable
      ((ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => by
        simpa [Real.norm_eq_abs] using hMb _ (hu j) w hw))
    exact Integrable.mul_bdd (c := G + G) hψ ((hgm _ (hu j)).sub (hgm _ hu₀))
      (ae_of_all _ fun w => (norm_sub_le _ _).trans (add_le_add (hG _) (hG _)))
  have hint2 : ∀ j, IntegrableOn (fun w => η w * M (u j) w) Ω (volume : Measure (Eucl k)) := by
    intro j
    exact Integrable.mul_bdd (c := B) hη (hMm _ (hu j)).aestronglyMeasurable
      ((ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => by
        simpa [Real.norm_eq_abs] using hMb _ (hu j) w hw))
  have hsplit : ∀ j, ∫ w in Ω, ψ w * g (u j w) * M (u j) w ∂(volume : Measure (Eucl k)) =
      (∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w ∂(volume : Measure (Eucl k))) +
        ∫ w in Ω, η w * M (u j) w ∂(volume : Measure (Eucl k)) := by
    intro j
    rw [← integral_add (hint1 j) (hint2 j)]
    congr 1; funext w; simp only [η]; ring
  have hlim0 : ∫ w in Ω, ψ w * g (u₀ w) * M u₀ w ∂(volume : Measure (Eucl k)) =
      0 + ∫ w in Ω, η w * M u₀ w ∂(volume : Measure (Eucl k)) := by
    rw [zero_add]
  have h2 := hE k Q Ω C u u₀ hΩ hu hu₀ hconv r a b η hη
  -- the first term tends to zero
  have hunif : TendstoUniformlyOn (fun j w => g (u j w)) (fun w => g (u₀ w)) atTop Ω :=
    (hgc.uniformContinuous_of_continuous hg).comp_tendstoUniformlyOn hconv
  have h1 : Tendsto (fun j => ∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w
      ∂(volume : Measure (Eucl k))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set I := ∫ w in Ω, |ψ w| ∂(volume : Measure (Eucl k)) with hI
    have hI0 : 0 ≤ I := integral_nonneg fun w => abs_nonneg _
    set δ := ε / (2 * (B * I + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif δ hδ0)
    refine ⟨N, fun j hj => ?_⟩
    rw [dist_zero_right]
    have hbound : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict Ω),
        ‖ψ w * (g (u j w) - g (u₀ w)) * M (u j) w‖ ≤ δ * B * |ψ w| := by
      refine (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => ?_)
      have e1 : |g (u j w) - g (u₀ w)| ≤ δ := by
        have := (hN j hj w hw).le
        rw [Real.dist_eq, abs_sub_comm] at this
        exact this
      have e2 := hMb _ (hu j) w hw
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |ψ w| * |g (u j w) - g (u₀ w)| * |M (u j) w| ≤ |ψ w| * δ * B := by gcongr
        _ = δ * B * |ψ w| := by ring
    calc ‖∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w ∂(volume : Measure (Eucl k))‖
        ≤ ∫ w in Ω, δ * B * |ψ w| ∂(volume : Measure (Eucl k)) :=
          norm_integral_le_of_norm_le (hψ.abs.const_mul _) hbound
      _ = δ * (B * I) := by rw [integral_const_mul, hI]; ring
      _ < ε := by
          rw [hδ]
          have : 0 < B * I + 1 := by positivity
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  rw [hlim0]
  exact (h1.add h2).congr fun j => (hsplit j).symm

## Key steps

1. Bounds: |M_{a,b}(u)| ≤ r!C^r on Ω, |g| ≤ G; all integrands are integrable on Ω.
2. Split ψ(g∘u_j)M_j = ψ(g∘u_j − g∘u₀)M_j + ηM_j with η = ψ(g∘u₀) ∈ L¹(Ω).
3. Uniform continuity of g and uniform convergence give |∫_Ω ψ(g∘u_j − g∘u₀)M_j| ≤ sup_Ω|g∘u_j − g∘u₀|·r!C^r·∫_Ω|ψ| → 0.
4. The sibling minor_weak_star tested against η gives ∫_Ω ηM_j → ∫_Ω ηM_0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = git HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: this node (depth 3, status decomposing, attempt 1, depends_on root.compactness_mass_bounds-a1.covector_expansion-a1) and the parent's decomposition-v3.json (format of reused children)`
- `python3 -I regex over dag.json titles/statements/lean statements: mollif|Piola|dense in|density of|C_c|integration by parts|weak-*|weak star|cofactor|convolution|minors|smooth approximation|ContDiffBump`
- `python3 -I over dag.json: status, candidate_commit, title/statement/lean_statement equality with the handoff for constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close, cmb_covector_eq_sum_coord_smul_wedge (all accepted, equal); lean_name collisions for deformation_ipl_mwc_* (none)`
- `grep -rn deformation_ipl_mwc over GMT/, the snapshot project, simongmt/Poincare and the snapshot Mathlib (no match)`
- `rg -n 'abbrev Covector|SimonMultiIndex|def wedgeCovectors|theorem wedgeCovectors_apply_det|def euclideanCovectorCoordinate' simongmt/Poincare/SimonGMT`
- `rg -n 'theorem norm_fderiv_le_of_lipschitzOn|LipschitzOnWith.extend_real|extend_finite_dimension|lipschitzExtensionConstant' snapshot Mathlib`
- `rg -n '^theorem' Mathlib/Analysis/Calculus/Rademacher.lean and Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean; sed ContinuousMapDense.lean 135-240, LineDeriv/IntegrationByParts.lean 215-245, ContDiff/Convolution.lean 50-100 and 415-435, Matrix/AbsoluteValue.lean det_le, ContDiff/RCLike.lean lipschitzWith_of_hasCompactSupport, FDeriv/Mul.lean finsetProd`
- `git log --all -G'^import' -- GMT/Ch06/Submission.lean; git show cdfc95dc (leaf gate rejects added imports); git show 2219dd32 (accepted ae-mollifier proof uses IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub)`
- `lake env lean /tmp/mwc_decomp/build/Avail.lean, build_v2/Avail2.lean, build_v2/Avail3.lean, build_v2/Small2.lean (#check availability under import GMT.Ch06.Submission)`
- `python3 -I /tmp/mwc_decomp/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare child_modules, contract mode) and lake env lean on the eleven /tmp/mwc_decomp/build_final/*_challenge.lean (all exit 0, sorry warnings only)`
- `lake env lean /tmp/mwc_decomp/build/Assembly.lean, build_v2/F_from_E.lean, build_v2/E_from_AD.lean, build_v2/RefImpl.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `grep 'Your solution is okay' in comparator-v1.log and isolated-comparator-result.json (passed: true) of the four reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/speculative-prompt-v4.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-covector-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-fderiv-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-close-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/mwc_decomp/build_final`
- `/tmp/mwc_decomp/build/Assembly.lean`
- `/tmp/mwc_decomp/build_v2/F_from_E.lean`
- `/tmp/mwc_decomp/build_v2/E_from_AD.lean`
- `/tmp/mwc_decomp/build_v2/RefImpl.lean`
- `/tmp/mwc_decomp/build/Avail.lean`
- `/tmp/mwc_decomp/build_v2/Avail2.lean`
- `/tmp/mwc_decomp/build_v2/Avail3.lean`

Pinned revisions are confirmed (HEAD = project_commit), and Contract = Submission = the snapshot Contract byte-for-byte.
No existing proof: neither Mathlib, SimonGMT nor any accepted DAG node proves weak continuity of Jacobian minors, the Piola identity or L¹-density by smooth functions. (The r = 1 analogue slicing_im_ll_gradient_weak_star and the density node slicing_im_ll_gws_smooth_dense are not accepted.) Hence seven new children; their names deformation_ipl_mwc_* collide with nothing.
Reused, with byte-identical types and comparator-passed: cmb_covector_eq_sum_coord_smul_wedge, constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close.
Import closure: the leaf gate forbids new imports (commit cdfc95dc).
- Available in the frozen closure: SimonGMT wedgeCovectors_apply_det; Mathlib norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.extend_real, extend_finite_dimension, LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.integral_lineDeriv_mul_eq, HasCompactSupport.contDiff_convolution_left/right, ContDiffAt.isSymmSndFDerivAt, HasFDerivAt.finsetProd, Matrix.det_succ_row_zero, Matrix.det_apply, measurable_fderiv(_apply_const), tendsto_integral_filter_of_dominated_convergence, IsCompact.exists_cthickening_subset_open, ContDiff.lipschitzWith_of_hasCompactSupport.
- Not available: ContDiffBump.normed and BumpFunction/Convolution, ContinuousMapDense, LineDeriv/IntegrationByParts, Matrix.det_le. The children replace them by the reused siblings or by short arguments.
Lean checks:
- All eleven statements validate and elaborate in the exact comparator scope.
- Three links compile with only propext, Classical.choice and Quot.sound: parent ⇐ coeff_minor_continuity + covector expansion; coeff_minor_continuity ⇐ minor_weak_star; minor_weak_star ⇐ test_density + minor_ibp_lipschitz.
