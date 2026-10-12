# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_iff_variational-a1`
- Child DAG node: `root.stationary_iff_variational-a1.first_variation_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E = Ambient n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)), d := n + ℓ = dim E, μ := V.weight, and p_x := (V.tangentSpace x).starProjection (the orthogonal projection onto T_xV). For A ∈ L(E, E) put T(A) := trace(A). By definition, div_M Z(x) := V.tangentialDiv Z x = trace(DZ(x)∘p_x) = T(DZ(x)∘p_x); this holds by unfolding, since the trace of the composite of the underlying linear maps is T of the composite continuous linear map. Hypotheses: μ is finite on compact sets; x ↦ p_x is μ-a.e. strongly measurable; K is compact; X and every Y_k are C¹ with tsupport inside K; and DY_k → DX uniformly on E. The finrank condition on T_xV is not needed.

1. (Trace bound.) For A, P ∈ L(E, E) with ‖P‖ ≤ 1 we have |T(A∘P)| ≤ d‖A‖. Indeed, for the standard orthonormal basis e_1, …, e_d of E, T(A∘P) = Σ_i ⟨e_i, A P e_i⟩. By Cauchy–Schwarz, |⟨e_i, A P e_i⟩| ≤ ‖e_i‖ ‖A P e_i‖ ≤ ‖A∘P‖ ‖e_i‖² = ‖A∘P‖ ≤ ‖A‖‖P‖ ≤ ‖A‖. Summing over the d indices gives the bound. Every orthogonal projection satisfies ‖p_x‖ ≤ 1, so |T(A∘p_x)| ≤ d‖A‖ for all x and all A.

2. (Measurability.) T is a linear functional on the finite-dimensional space L(E, E), hence continuous. Composition (A, P) ↦ A∘P is a continuous bilinear map. So (A, P) ↦ T(A∘P) is continuous. For a C¹ map Z, x ↦ DZ(x) is continuous, hence strongly measurable. With the hypothesis on x ↦ p_x, the pair x ↦ (DZ(x), p_x) is μ-a.e. strongly measurable. Composing with the continuous map (A, P) ↦ T(A∘P) shows that div_M Z is μ-a.e. strongly measurable.

3. (Vanishing off K.) Let tsupport Z ⊆ K and x ∉ K. Then x lies in the open set E ∖ tsupport Z, on which Z ≡ 0, so DZ(x) = 0 and div_M Z(x) = T(0) = 0.

4. (Integrability.) Let Z be C¹ with tsupport Z ⊆ K. Z has compact support (tsupport Z is a closed subset of the compact set K). So DZ is continuous with compact support, hence bounded by some B. By steps 1 and 3, |div_M Z| ≤ dB·1_K everywhere. Since μ(K) < ∞, the function dB·1_K is μ-integrable, and together with step 2 this shows div_M Z is μ-integrable. This applies to X and to every Y_k.

5. (Pointwise difference.) T and A ↦ A∘p_x are linear, so div_M Y_k(x) − div_M X(x) = T((DY_k(x) − DX(x))∘p_x). By step 1, |div_M Y_k(x) − div_M X(x)| ≤ d‖DY_k(x) − DX(x)‖ for all x, and by step 3 the difference vanishes for x ∉ K.

6. (Convergence.) Let m := μ(K) ∈ [0, ∞) and η > 0, and put η' := η/(2(dm + 1)) > 0. By uniform convergence there is N with ‖DY_k(x) − DX(x)‖ < η' for all k ≥ N and all x ∈ E. For k ≥ N, step 4 (integral of a difference of integrable functions) and step 5 give
 |∫ div_M Y_k dμ − ∫ div_M X dμ| = |∫ (div_M Y_k − div_M X) dμ| ≤ ∫ 1_K·dη' dμ = dη'm = η·dm/(2(dm + 1)) < η.
Hence Tendsto (fun k ↦ ∫ x, V.tangentialDiv (Y k) x ∂V.weight) atTop (𝓝 (∫ x, V.tangentialDiv X x ∂V.weight)). ∎

Implementation notes (pinned Mathlib 25730c7c, verified by compilation):
- step 1: LinearMap.trace_eq_sum_inner with EuclideanSpace.basisFun (Fin (n+ℓ)) ℝ, Finset.abs_sum_le_sum_abs, abs_real_inner_le_norm, ContinuousLinearMap.le_opNorm, ContinuousLinearMap.opNorm_comp_le, Submodule.starProjection_norm_le. Keep the bound as a local have rather than a new top-level helper, to avoid name clashes when Submission.lean is merged.
- step 2: T := (LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ) with LinearMap.continuous_of_finiteDimensional; tangentialDiv Z x = T ((fderiv ℝ Z x).comp p_x) holds by rfl; isBoundedBilinearMap_comp.continuous; Continuous.comp_aestronglyMeasurable; AEStronglyMeasurable.prodMk.
- step 3: fderiv_of_notMem_tsupport ℝ.
- step 4: IsCompact.measure_lt_top (state it as < ⊤, since in this scope ∞ is ambiguous between ℕ∞ω and ℝ≥0∞), integrableOn_const (C := …), IntegrableOn.integrable_indicator, Integrable.mono'.
- step 6: Metric.tendsto_atTop, Metric.tendstoUniformly_iff, integral_sub, norm_integral_le_of_norm_le, integral_indicator, setIntegral_const.
Extra import: Mathlib.Analysis.InnerProductSpace.Trace.

Verified Lean realization. Scope used for the scratch compilation (identical to the comparator's child scope): `import GMT.Ch04.Submission` plus the extra imports listed, then `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, and the declaration placed in `namespace Submission`. It was compiled with Lean v4.35.0-rc3 / Mathlib 25730c7c, and `#print axioms` reported only propext, Classical.choice and Quot.sound. It is an optional implementation aid; the numbered argument above is the proof.

```lean
theorem tendsto_integral_tangentialDiv_of_tendstoUniformly_fderiv : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (K : Set (Ambient n ℓ)) (X : Ambient n ℓ → Ambient n ℓ) (Y : ℕ → Ambient n ℓ → Ambient n ℓ), IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsCompact K → ContDiff ℝ 1 X → tsupport X ⊆ K → (∀ k, ContDiff ℝ 1 (Y k) ∧ tsupport (Y k) ⊆ K) → TendstoUniformly (fun k ↦ fderiv ℝ (Y k)) (fderiv ℝ X) atTop → Tendsto (fun k ↦ ∫ x, V.tangentialDiv (Y k) x ∂V.weight) atTop (𝓝 (∫ x, V.tangentialDiv X x ∂V.weight)) := by
  intro n ℓ V K X Y hfin hP hK hX hXK hY hconv
  set d : ℝ := ((n + ℓ : ℕ) : ℝ)
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have htrace : ∀ A P : Ambient n ℓ →L[ℝ] Ambient n ℓ, ‖P‖ ≤ 1 →
      |LinearMap.trace ℝ (Ambient n ℓ) (A.comp P).toLinearMap| ≤ d * ‖A‖ := by
    intro A P hP
    set b := EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ
    rw [LinearMap.trace_eq_sum_inner _ b]
    calc |∑ i, inner ℝ (b i) ((A.comp P).toLinearMap (b i))|
        ≤ ∑ i, |inner ℝ (b i) ((A.comp P).toLinearMap (b i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (n + ℓ), ‖A‖ := by
          gcongr with i
          have hb : ‖b i‖ = 1 := b.orthonormal.1 i
          calc |inner ℝ (b i) ((A.comp P).toLinearMap (b i))|
              ≤ ‖b i‖ * ‖(A.comp P) (b i)‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖b i‖ * (‖A.comp P‖ * ‖b i‖) := by gcongr; exact (A.comp P).le_opNorm (b i)
            _ = ‖A.comp P‖ := by rw [hb]; ring
            _ ≤ ‖A‖ * ‖P‖ := A.opNorm_comp_le P
            _ ≤ ‖A‖ * 1 := by gcongr
            _ = ‖A‖ := mul_one _
      _ = d * ‖A‖ := by simp [d]
  set T : (Ambient n ℓ →L[ℝ] Ambient n ℓ) →ₗ[ℝ] ℝ :=
    (LinearMap.trace ℝ (Ambient n ℓ)).comp (ContinuousLinearMap.coeLM ℝ) with hT
  have hTc : Continuous T := T.continuous_of_finiteDimensional
  have hdiv : ∀ Z x, V.tangentialDiv Z x =
      T ((fderiv ℝ Z x).comp (V.tangentSpace x).starProjection) := fun Z x ↦ rfl
  have hcomp : Continuous (fun q : (Ambient n ℓ →L[ℝ] Ambient n ℓ) × (Ambient n ℓ →L[ℝ] Ambient n ℓ) ↦
      q.1.comp q.2) := isBoundedBilinearMap_comp.continuous
  have hmeas : ∀ Z : Ambient n ℓ → Ambient n ℓ, ContDiff ℝ 1 Z →
      AEStronglyMeasurable (fun x ↦ V.tangentialDiv Z x) V.weight := by
    intro Z hZ
    have h1 : Continuous (fun x ↦ fderiv ℝ Z x) := hZ.continuous_fderiv one_ne_zero
    exact (hTc.comp hcomp).comp_aestronglyMeasurable (h1.aestronglyMeasurable.prodMk hP)
  have hbound : ∀ (A : Ambient n ℓ →L[ℝ] Ambient n ℓ) x,
      |T (A.comp (V.tangentSpace x).starProjection)| ≤ d * ‖A‖ := fun A x ↦
    htrace A _ (Submodule.starProjection_norm_le _)
  have hvan : ∀ Z : Ambient n ℓ → Ambient n ℓ, tsupport Z ⊆ K → ∀ x ∉ K,
      V.tangentialDiv Z x = 0 := by
    intro Z hZK x hx
    rw [hdiv, fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hZK h))]
    simp
  have hμK : V.weight K < ⊤ := hK.measure_lt_top
  have hint : ∀ Z : Ambient n ℓ → Ambient n ℓ, ContDiff ℝ 1 Z → tsupport Z ⊆ K →
      Integrable (fun x ↦ V.tangentialDiv Z x) V.weight := by
    intro Z hZ hZK
    have hZc : HasCompactSupport Z := hK.of_isClosed_subset (isClosed_tsupport Z) hZK
    obtain ⟨B, hB⟩ := (hZc.fderiv ℝ).exists_bound_of_continuous (hZ.continuous_fderiv one_ne_zero)
    refine Integrable.mono' ((integrableOn_const (C := d * B) hμK.ne).integrable_indicator
      hK.isClosed.measurableSet) (hmeas Z hZ) (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.norm_eq_abs, hdiv]
      exact (hbound _ x).trans (by gcongr; exact hB x)
    · rw [indicator_of_notMem hx, hvan Z hZK x hx, norm_zero]
  have hIX := hint X hX hXK
  rw [Metric.tendsto_atTop]
  intro η hη
  set m : ℝ := V.weight.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformly_iff.mp hconv (η / (2 * (d * m + 1)))
    (by positivity)).exists_forall_of_atTop
  refine ⟨N, fun k hk ↦ ?_⟩
  have hIY := hint (Y k) (hY k).1 (hY k).2
  rw [Real.dist_eq, ← integral_sub hIY hIX]
  calc |∫ x, V.tangentialDiv (Y k) x - V.tangentialDiv X x ∂V.weight|
      ≤ ∫ x, K.indicator (fun _ ↦ d * (η / (2 * (d * m + 1)))) x ∂V.weight := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le
          ((integrableOn_const (C := d * (η / (2 * (d * m + 1)))) hμK.ne).integrable_indicator
          hK.isClosed.measurableSet)
          (Eventually.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ K
        · rw [indicator_of_mem hx, Real.norm_eq_abs, hdiv, hdiv, ← map_sub,
            ← ContinuousLinearMap.sub_comp]
          refine (hbound _ x).trans ?_
          gcongr
          rw [← dist_eq_norm, dist_comm]
          exact (hN k hk x).le
        · rw [indicator_of_notMem hx, hvan _ (hY k).2 x hx, hvan X hXK x hx, sub_zero, norm_zero]
    _ = d * (η / (2 * (d * m + 1))) * m := by
        rw [integral_indicator hK.isClosed.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
    _ < η := by
        have h1 : 0 < d * m + 1 := by positivity
        have he : d * (η / (2 * (d * m + 1))) * m = η * (d * m) / (2 * (d * m + 1)) := by ring
        rw [he, div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hd0 hm0]
```

## Key steps

1. |trace(A∘P)| ≤ (n+ℓ)‖A‖ for ‖P‖ ≤ 1 (orthonormal-basis expansion), and ‖p_x‖ ≤ 1
2. div_M Z is μ-a.e. strongly measurable: a continuous function of (DZ(x), p_x)
3. div_M Z = 0 off K, and |div_M Z| ≤ (n+ℓ) sup‖DZ‖ 1_K is integrable since μ(K) < ∞
4. |div_M Y_k − div_M X| ≤ (n+ℓ)‖DY_k − DX‖_∞ 1_K by linearity of trace and composition
5. |∫ div_M Y_k − ∫ div_M X| ≤ (n+ℓ)‖DY_k − DX‖_∞ μ(K) → 0

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'theorem contDiff_symm|theorem Homeomorph.contDiff_symm|def toHomeomorph|theorem surjective|theorem toHomeomorph' Mathlib/Analysis/Calculus/InverseFunctionTheorem/ Mathlib/Analysis/Calculus/ContDiff/`
- `rg -n 'theorem (HasCompactSupport\.)?(contDiff_convolution_left|contDiff_convolution_right|hasFDerivAt_convolution_right|hasFDerivAt_convolution_left)|theorem dist_normed_convolution_le|theorem support_convolution_subset|theorem support_normed_eq|theorem tsupport_normed_eq|theorem hasCompactSupport_normed' Mathlib/Analysis/Convolution.lean Mathlib/Analysis/Calculus/BumpFunction/*.lean`
- `rg -n 'contDiff_convolution_left|hasFDerivAt_convolution_right|fderiv_convolution' Mathlib/`
- `cat Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `rg -n 'theorem trace_eq_sum_inner|theorem starProjection_norm_le|theorem (support_fderiv_subset|fderiv_of_notMem_tsupport|HasCompactSupport.fderiv)|lipschitzWith_of_hasCompactSupport' Mathlib/`
- `rg -n 'exists_cthickening_subset_open|IsCompact.cthickening|uniformContinuous_of_continuous|image_eq_zero_of_notMem_tsupport|lipschitzWith_of_nnnorm_fderiv_le|def Units.oneSub|def unitsEquiv|theorem invFun_eq |exists_bound_of_continuous|theorem integrableOn_const|LinearMap.continuous_of_finiteDimensional|def coeLM' Mathlib/`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-siv-audit/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-siv-audit/olean lean /tmp/ch04-siv-audit/src/ChildTypes.lean (comparator child-scope replay of the four statements)`
- `LEAN_PATH=... lean /tmp/ch04-siv-audit/src/Assembly.lean (parent from sorry'd children; exact frozen target via exact Submission.stationary_iff_variational_of_first_variation)`
- `LEAN_PATH=... lean /tmp/ch04-siv-audit/src/FeasA.lean, FeasB.lean, FeasC.lean, FeasD.lean, Full2.lean (#print axioms)`
- `python3 -I validate.py verifier/lean_contract.py stmts.json (validate_lean_statement)`
- `python3 dag.json listing of reserved lean_name values`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Logic/Function/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-iff-variational-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ch04-siv-audit/src/ChildTypes.lean`
- `/tmp/ch04-siv-audit/src/Assembly.lean`
- `/tmp/ch04-siv-audit/src/Full2.lean`

Contract identity: the snapshot contract, the workspace Contract.lean and Submission.lean are byte-identical (sha256 6e58e5dd…0f4770b), and the lake mathlib package is at the manifest revision 25730c7c. No ready-made lemma exists for any of the four children: the snapshot Mathlib has no IsCompactVariation-style statement and no C¹-uniform mollification lemma. SmoothApprox.lean only gives C⁰ approximation (UniformContinuous.exists_contDiff_dist_le). All the building blocks are present, though:
- ApproximatesLinearOn.surjective and .toHomeomorph, and Homeomorph.contDiff_symm (inverse function theorem for homeomorphisms).
- Units.oneSub and ContinuousLinearEquiv.unitsEquiv.
- ContDiffBump.normed with hasCompactSupport_normed, support_normed_eq and dist_normed_convolution_le.
- HasCompactSupport.contDiff_convolution_left and .hasFDerivAt_convolution_right, and support_convolution_subset.
- IsCompact.exists_cthickening_subset_open and IsCompact.cthickening.
- HasMulCompactSupport/HasCompactSupport.uniformContinuous_of_continuous and exists_bound_of_continuous.
- LinearMap.trace_eq_sum_inner, Submodule.starProjection_norm_le, fderiv_of_notMem_tsupport, ContDiffOn.fderiv_of_isOpen and lipschitzWith_of_nnnorm_fderiv_le.
Required instances hold on Ambient n ℓ: HasContDiffBump, IsAddHaarMeasure volume and IsNegInvariant volume. With GMT.Ch04.Submission compiled to an olean, the four child types elaborate in the exact comparator scope, and the parent assembles from them with exactly the frozen type. Complete proofs of all four children compile in Full2.lean, and every declaration depends only on propext, Classical.choice and Quot.sound. The convolution notation needs `open scoped Convolution`. Extra Mathlib imports the children need: InverseFunctionTheorem.ApproximatesLinearOn, BumpFunction.Convolution, BumpFunction.FiniteDimension, ContDiff.Convolution and InnerProductSpace.Trace.
