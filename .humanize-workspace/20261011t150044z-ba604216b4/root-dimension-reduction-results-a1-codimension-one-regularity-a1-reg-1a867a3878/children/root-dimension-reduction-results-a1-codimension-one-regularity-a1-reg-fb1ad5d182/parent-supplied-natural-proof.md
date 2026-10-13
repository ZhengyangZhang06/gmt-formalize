# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.test_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 3–6 and 8 of the supplied proof of chart_perimeter: the test forms of Simon Ch. 6, 2.35 (book/chapter-06.txt lines 606–632; ω = Σ_j (−1)^{j−1} a_j dx^1 ∧ … ∧ \hat{dx^j} ∧ … ∧ dx^n with dω = div a dx^1 ∧ … ∧ dx^n, lines 625–626, where the printed sign (−1)^j is a misprint for (−1)^{j−1}, cf. lines 594–595), transported to the graph chart G; with 0-based indices the sign is (−1)^j, as in the field of chart_divergence. Departures, all inessential: (a) the form is written ω(w) := Λ(ζ(w)φ(π(w))), which equals ζ(w)·Λ(φ(π(w))) of the supplied proof by linearity of Λ; (b) instead of a compact K ⊆ D with tsupport φ ⊆ K the hypothesis is "φ has compact support and tsupport φ ⊆ D" (the supplied proof's K may be taken to be tsupport φ); (c) u is only assumed differentiable on D; (d) conclusion (ii) is recorded separately for the mass estimate of the parent. Siblings used: chart_geometry, det_covector, coeff_bound, det_laplace.

Notation. π(w) := A(w − x) and p^⊥(w) := w − x − ιπ(w) for w ∈ ℝ^P.

Proof.
1. (Chart identities.) By chart_geometry (u is differentiable on D and ⟨ιw, u(v)⟩ = 0 for v ∈ D): ‖A‖ ≤ 1, and for every v ∈ D, π(G(v)) = v, p^⊥(G(v)) = u(v) and A(DG(v)y) = y for all y. The maps π and p^⊥ are affine (continuous linear maps composed with w ↦ w − x), hence C^∞. Since w − x = ιπ(w) + p^⊥(w) and |ιπ(w)| = |π(w)| (ι is an isometry), |w − x| ≤ |π(w)| + |p^⊥(w)| for every w.
2. (Λ.) By det_covector applied to A there is a continuous linear map Λ : ℝ^{n+1} → Λ^n(ℝ^P) with Λ(q)(a_0, …, a_{n−1}) = det[q, Aa_0, …, Aa_{n−1}] (column 0 equal to q, column k+1 equal to Aa_k) for all q and a.
3. (Cut-off.) Put a := (δ₂/2)² and b := (3δ₂/4)²; since δ₂ > 0, b − a = 5δ₂²/16 > 0. Let ζ(w) := smoothTransition((b − |p^⊥(w)|²)/(b − a)), where Real.smoothTransition is C^∞ (Real.smoothTransition.contDiff), takes values in [0, 1], vanishes on (−∞, 0] and equals 1 on [1, ∞). ζ is C^∞, being smoothTransition composed with the C^∞ map w ↦ (b − |p^⊥(w)|²)/(b − a) (contDiff_norm_sq), and 0 ≤ ζ ≤ 1.
  (3a) If ζ(w) ≠ 0, then (b − |p^⊥(w)|²)/(b − a) > 0 (otherwise ζ(w) = 0), so |p^⊥(w)|² < b and |p^⊥(w)| < 3δ₂/4.
  (3b) If |p^⊥(w)| < δ₂/2, then |p^⊥(w)|² < a, so (b − |p^⊥(w)|²)/(b − a) ≥ 1 and ζ(w) = 1.
4. (The form.) Define ω(w) := Λ(ζ(w)·φ(π(w))) for w ∈ ℝ^P. Then ω is C^∞: Λ is continuous linear, and w ↦ ζ(w)φ(π(w)) is C^∞ because ζ, φ and π are.
5. (Support.) Let S := {w : π(w) ∈ tsupport φ and |p^⊥(w)| ≤ 3δ₂/4}. S is closed, as an intersection of preimages of closed sets under the continuous maps π and |p^⊥|. If ω(w) ≠ 0 then ζ(w)φ(π(w)) ≠ 0 (because Λ(0) = 0), so ζ(w) ≠ 0 and φ(π(w)) ≠ 0; hence π(w) ∈ support φ ⊆ tsupport φ and, by (3a), |p^⊥(w)| < 3δ₂/4, i.e. w ∈ S. As S is closed, tsupport ω ⊆ S.
  (5a) (Compact support.) tsupport φ is compact, hence bounded: tsupport φ ⊆ closedBall(0, R) for some R. For w ∈ S, |w − x| ≤ |π(w)| + |p^⊥(w)| ≤ R + 3δ₂/4 by step 1. Thus tsupport ω is a closed subset of the compact ball closedBall(x, R + 3δ₂/4), so it is compact: ω has compact support.
  (5b) (S ⊆ Z.) For w ∈ S, π(w) ∈ tsupport φ ⊆ D, so |π(w)| < δ₁; and |p^⊥(w)| ≤ 3δ₂/4 < δ₂.
  (5c) (Z ⊆ closedBall(x, δ₁ + δ₂).) For w ∈ Z, |w − x| ≤ |π(w)| + |p^⊥(w)| < δ₁ + δ₂ by step 1.
  Hence tsupport ω ⊆ S ⊆ Z ⊆ closedBall(x, δ₁ + δ₂) ⊆ U. By step 4 and (5a), ω is a test form (C^∞ with compact support) with tsupport ω ⊆ U, i.e. ω ∈ 𝒟^n(U); and (i), (ii) hold.
6. ((iii) Coefficient bound.) Fix w ∈ ℝ^P and put q := ζ(w)φ(π(w)). Then |q| = ζ(w)·|φ(π(w))| ≤ 1·1 = 1, ω(w) = Λ(q), and Λ(q)(a) = det[q, Aa_0, …, Aa_{n−1}] for all a by step 2. By coeff_bound (with ‖A‖ ≤ 1 from step 1), covectorEuclideanNorm(ω(w)) ≤ (n+1)!·√(P^n).
7. ((iv) on D.) Let v ∈ D. By step 1, π(G(v)) = v and p^⊥(G(v)) = u(v) with |u(v)| < δ₂/2, so ζ(G(v)) = 1 by (3b) and ω(G(v)) = Λ(φ(v)). Fix j ∈ {0, …, n} and put a_k := DG(v)e_{j.succAbove k} (k = 0, …, n−1). By step 1, Aa_k = e_{j.succAbove k}. Hence, by step 2 and det_laplace, ω(G(v))(a_0, …, a_{n−1}) = det[φ(v), e_{j.succAbove 0}, …, e_{j.succAbove(n−1)}] = (−1)^j φ_j(v), where φ_j(v) is the j-th coordinate of φ(v). Therefore the j-th summand of (iv) is ((−1)^j·(−1)^j φ_j(v)) e_j = φ_j(v) e_j (as (−1)^{2j} = 1), and Σ_j φ_j(v) e_j = φ(v) (expansion of a vector of ℝ^{n+1} in the standard basis). So the right side of (iv) equals φ(v) at every v ∈ D.
8. ((iv) off D.) If v ∉ D, the right side of (iv) is 0 (indicator of D), and v ∉ tsupport φ because tsupport φ ⊆ D, so φ(v) = 0 (image_eq_zero_of_notMem_tsupport).
9. (Conclusion.) Steps 7–8 prove (iv) at every point, hence as an equality of functions (funext). Together with steps 5–6, ω has all the asserted properties. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the contract). The declaration below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b366308 when placed after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the frozen contract's `open` commands (both inside and outside a `noncomputable section`), and `#print axioms` reports only propext, Classical.choice and Quot.sound together with the four sibling declarations.

```lean
theorem Submission.codim1_lur_chart_test_form_exists : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ) (φ : Euclid (n + 1) → Euclid (n + 1)), 0 < δ₂ → closedBall x (δ₁ + δ₂) ⊆ U → DifferentiableOn ℝ u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ‖u v‖ < δ₂ / 2) → ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 δ₁ → (∀ y, ‖φ y‖ ≤ 1) → ∃ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ closedBall x (δ₁ + δ₂) ∧ (∀ w, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) w) ≤ ((n + 1).factorial : ℝ) * Real.sqrt ((P : ℝ) ^ n)) ∧ φ = (ball (0 : Euclid (n + 1)) δ₁).indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * (ω : DifferentialForm (Euclid P) n) (x + ι v + u v) (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ)) := by
  intro P n U x ι u δ₁ δ₂ φ hδ₂ hball hu horth hsmall hφ hφc hφD hφ1
  obtain ⟨hA, -, hG⟩ := Submission.codim1_lur_graph_chart_adjoint_identities P n x ι u δ₁ hu horth
  set A := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hAdef
  obtain ⟨Λ, hΛ⟩ := Submission.codim1_lur_det_covector_clm P n A
  -- the chart projections π(w) = ι*(w - x) and p⊥(w) = w - x - ι π(w)
  set π : Euclid P → Euclid (n + 1) := fun w => A (w - x) with hπdef
  set q : Euclid P → Euclid P := fun w => w - x - ι (A (w - x)) with hqdef
  have hπc : ContDiff ℝ (⊤ : ℕ∞) π := A.contDiff.comp (contDiff_id.sub contDiff_const)
  have hqc : ContDiff ℝ (⊤ : ℕ∞) q :=
    (contDiff_id.sub contDiff_const).sub (ι.toContinuousLinearMap.contDiff.comp hπc)
  have hdecomp : ∀ w, ‖w - x‖ ≤ ‖π w‖ + ‖q w‖ := by
    intro w
    have : w - x = ι (π w) + q w := by simp only [hπdef, hqdef]; abel
    rw [this]
    exact (norm_add_le _ _).trans (by rw [ι.norm_map])
  -- the cut-off ζ(w) = χ(|p⊥(w)|²), χ = 1 on [0, (δ₂/2)²], χ = 0 on [(3δ₂/4)², ∞)
  set a : ℝ := (δ₂ / 2) ^ 2 with ha
  set b : ℝ := (3 * δ₂ / 4) ^ 2 with hb
  have hab : 0 < b - a := by rw [ha, hb]; nlinarith
  set ζ : Euclid P → ℝ := fun w => Real.smoothTransition ((b - ‖q w‖ ^ 2) / (b - a)) with hζdef
  have hζc : ContDiff ℝ (⊤ : ℕ∞) ζ :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub ((contDiff_norm_sq ℝ).comp hqc)).div_const _)
  have hζ0 : ∀ w, 0 ≤ ζ w := fun w => Real.smoothTransition.nonneg _
  have hζ1 : ∀ w, ζ w ≤ 1 := fun w => Real.smoothTransition.le_one _
  have hζsupp : ∀ w, ζ w ≠ 0 → ‖q w‖ < 3 * δ₂ / 4 := by
    intro w hw
    by_contra hcon
    push Not at hcon
    apply hw
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hab.le
    have : (3 * δ₂ / 4) ^ 2 ≤ ‖q w‖ ^ 2 := pow_le_pow_left₀ (by positivity) hcon 2
    rw [hb]; linarith
  -- the test form ω(w) = Λ(ζ(w) φ(π(w))) = ζ(w) det[φ(π(w)), ι*·, …, ι*·]
  set ω₀ : DifferentialForm (Euclid P) n := fun w => Λ (ζ w • φ (π w)) with hω₀def
  have hω₀c : ContDiff ℝ (⊤ : ℕ∞) ω₀ := Λ.contDiff.comp (hζc.smul (hφ.comp hπc))
  -- support
  set S : Set (Euclid P) := {w | π w ∈ tsupport φ ∧ ‖q w‖ ≤ 3 * δ₂ / 4} with hSdef
  have hSclosed : IsClosed S :=
    ((isClosed_tsupport φ).preimage hπc.continuous).inter
      (isClosed_le (continuous_norm.comp hqc.continuous) continuous_const)
  have hsuppS : support ω₀ ⊆ S := by
    intro w hw
    have hne : ζ w • φ (π w) ≠ 0 := by
      intro h0; apply hw; simp only [hω₀def, h0, map_zero]
    refine ⟨subset_tsupport _ (right_ne_zero_of_smul hne), (hζsupp w (left_ne_zero_of_smul hne)).le⟩
  have htsS : tsupport ω₀ ⊆ S := closure_minimal hsuppS hSclosed
  obtain ⟨R, hR⟩ := hφc.isBounded.subset_closedBall 0
  have hSball : S ⊆ closedBall x (R + 3 * δ₂ / 4) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    have h1 : ‖π w‖ ≤ R := by simpa using hR hw.1
    linarith [hdecomp w, hw.2]
  have hcpt : HasCompactSupport ω₀ :=
    (isCompact_closedBall x _).of_isClosed_subset (isClosed_tsupport _) (htsS.trans hSball)
  have hSZ : S ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧
      ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} := by
    intro w hw
    refine ⟨?_, ?_⟩
    · have h1 := hφD hw.1
      rw [mem_ball_zero_iff] at h1
      exact h1
    · have := hw.2; show ‖q w‖ < δ₂; linarith
  have hZB : {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧
      ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ⊆
      closedBall x (δ₁ + δ₂) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    have h1 : ‖π w‖ < δ₁ := hw.1
    have h2 : ‖q w‖ < δ₂ := hw.2
    linarith [hdecomp w]
  let ω : TestFormOn U n := ⟨ω₀, ⟨⟨hω₀c, hcpt⟩, (htsS.trans hSZ).trans (hZB.trans hball)⟩⟩
  refine ⟨ω, htsS.trans hSZ, (htsS.trans hSZ).trans hZB, ?_, ?_⟩
  · -- coefficient bound
    intro w
    apply Submission.codim1_lur_det_covector_norm_le P n A (ζ w • φ (π w)) _ hA _ (hΛ _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζ0 w)]
    calc ζ w * ‖φ (π w)‖ ≤ 1 * 1 := mul_le_mul (hζ1 w) (hφ1 _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · -- the pull-back field is φ
    funext v
    by_cases hv : v ∈ ball (0 : Euclid (n + 1)) δ₁
    · rw [Set.indicator_of_mem hv]
      obtain ⟨hπv, hqv, hdv⟩ := hG v hv
      have hζv : ζ (x + ι v + u v) = 1 := by
        apply Real.smoothTransition.one_of_one_le
        rw [le_div_iff₀ hab, one_mul]
        have hq' : q (x + ι v + u v) = u v := hqv
        rw [hq']
        have h0 := hsmall v hv
        have : ‖u v‖ ^ 2 < (δ₂ / 2) ^ 2 := pow_lt_pow_left₀ h0 (norm_nonneg _) two_ne_zero
        rw [ha]; linarith
      have hterm : ∀ j : Fin (n + 1),
          (ω : DifferentialForm (Euclid P) n) (x + ι v + u v)
            (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1)) =
          (-1 : ℝ) ^ (j : ℕ) * φ v j := by
        intro j
        show Λ (ζ (x + ι v + u v) • φ (π (x + ι v + u v))) _ = _
        have hπ' : π (x + ι v + u v) = v := hπv
        rw [hζv, one_smul, hπ', hΛ]
        simp only [hdv]
        exact Submission.codim1_lur_det_laplace_first_column n (φ v) j
      simp only [hterm]
      have hsq : ∀ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * ((-1 : ℝ) ^ (j : ℕ) * φ v j) = φ v j := by
        intro j
        rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
      simp only [hsq]
      ext i
      simp [Pi.single_apply]
    · rw [Set.indicator_of_notMem hv]
      exact image_eq_zero_of_notMem_tsupport fun h => hv (hφD h)
```

## Key steps

1. chart_geometry: ‖ι*‖ ≤ 1, π∘G = id, p^⊥∘G = u and ι*∘DG = id on D; |w − x| ≤ |π(w)| + |p^⊥(w)|.
2. ω(w) := Λ(ζ(w)φ(π(w))) with Λ from det_covector and the smoothTransition cut-off ζ = χ(|p^⊥|²) is C^∞.
3. tsupport ω ⊆ {π ∈ tsupport φ, |p^⊥| ≤ 3δ₂/4}, a compact subset of Z ⊆ closedBall(x, δ₁ + δ₂) ⊆ U, so ω ∈ 𝒟^n(U).
4. coeff_bound with |ζφ∘π| ≤ 1 gives covectorEuclideanNorm(ω(w)) ≤ (n+1)!·√(P^n).
5. On D, ζ∘G = 1 and ι*DG(v)e_{j.succAbove k} = e_{j.succAbove k}, so det_laplace gives the j-th coefficient (−1)^j(−1)^jφ_j(v) = φ_j(v); off D both sides vanish.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C lake-packages-25730c7c/{mathlib,simongmt} rev-parse HEAD; python3 read of snapshot project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem det_succ_column_zero|theorem det_le |smoothTransition' <snapshot>/mathlib/Mathlib`
- `rg -n 'def curryLeft|def mkContinuous|compContinuousLinearMapCLM|continuous_of_finiteDimensional|toContinuousAlternatingMap' <snapshot>/mathlib/Mathlib/{Topology/Algebra/Module/Alternating,Analysis/Normed/Module/Alternating,LinearAlgebra/Alternating}`
- `rg -n 'volumeForm_robust|abs_volumeForm_apply_le' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean; rg -n 'adjoint_inner_left|norm_adjoint' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean; rg -n 'ContinuousOn.measurable_piecewise' <snapshot>/mathlib/Mathlib`
- `#check in the GMT.Ch07.Submission import closure: Matrix.det_le (unknown constant), Module.Basis.det, Matrix.det_apply, Fintype.card_perm, ContinuousAlternatingMap.curryLeft_apply_apply, Orientation.abs_volumeForm_apply_le, Orientation.volumeForm_robust', ContinuousOn.measurable_piecewise, Real.smoothTransition.contDiff, PiLp.norm_apply_le, MultilinearMap.continuous_of_finiteDimensional (unknown constant)`
- `grep -n '^theorem|^def|^abbrev|^structure' simongmt Chapter06/{Forms,Currents,Mass}.lean`
- `python3 scans of dag.json (902 then 983 nodes): frozen types of codim1_lur_chart_divergence_formula, dor_ims_massOn_le_measure and the selected node; accepted statements containing covectorEuclideanNorm, massOn with IsIntegerMultiplicity, R.measure … ≠ ∞, succAbove, Matrix.det; lean_name lookup of the five new names (no hits)`
- `grep -rl -E '<five new names>' runs/.../nodes runs/.../dag.json (no match); git for-each-ref | xargs -n 100 sh -c 'git grep -l -E "<five new names>" "$@" -- GMT/*.lean' (0 of 1695 ref tips; control cmr_abs_apply_le_massOn: 3 tips)`
- `git show {7a706164,702e7082,fae4fd1e}:GMT/Ch07/Submission.lean > Cand_*.lean; diff against GMT/Ch07/Contract.lean (additions only); '#print axioms' for cmr_abs_apply_le_massOn, rsd_imrep_compact_measure_ne_top, dor_ims_massOn_le_measure`
- `lean -DautoImplicit=false (LEAN_PATH from 'lake env printenv LEAN_PATH') /tmp/cpsplit/final/{Types,Inst,Assembly,FullChain,FullChainNoSection}.lean, /tmp/cpsplit/proto/{Laplace,DetCov,Coeff,Chart,TestForm}.lean, /tmp/cpsplit/out/Appendices.lean`
- `sed -n 560,640p book/chapter-06.txt (Simon 6.2.34–2.35); grep -n '( 1)j aj dx|!j  D ( 1)j 1' book/chapter-06.txt`
- `read nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-{1a867a3878,5d8d9c70c5}/ (handoff, supplied proof, decomposition-v1.json) and the handoffs/accepted-candidate.json of the two reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1a867a3878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1a867a3878/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cpsplit/final/Types.lean`
- `/tmp/cpsplit/final/Inst.lean`
- `/tmp/cpsplit/final/Assembly.lean`
- `/tmp/cpsplit/final/FullChain.lean`
- `/tmp/cpsplit/final/FullChainNoSection.lean`
- `/tmp/cpsplit/out/Appendices.lean`
- `/tmp/cpsplit/reuse/Cand_cmr_abs_apply_le_massOn.lean`
- `/tmp/cpsplit/reuse/Cand_rsd_imrep_compact_measure_ne_top.lean`
- `/tmp/cpsplit/reuse/Cand_dor_ims_massOn_le_measure.lean`

Pins match.
- Snapshot manifest: project b4d606db, Mathlib 25730c7c; both equal workspace HEAD and the lake package checkout (lake-packages-25730c7c/mathlib).
- simongmt is 2b366308 in both the snapshot lake-manifest and the package checkout.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library (what exists).
- In the import closure: Matrix.det_succ_column_zero; Matrix.det_apply with Fintype.card_perm (Leibniz); Module.Basis.det.
- Also present: Orientation.volumeForm_robust' and Orientation.abs_volumeForm_apply_le (Hadamard).
- Alternating-map API: AlternatingMap.mkContinuous, ContinuousAlternatingMap.curryLeft and compContinuousLinearMapCLM.
- Analysis: Real.smoothTransition (ContDiff of every order, values in [0, 1]); ContinuousLinearMap.adjoint_inner_left; ContinuousOn.measurable_piecewise.
- SimonGMT Chapter06 supplies Covector, DifferentialForm, TestFormOn, covectorEuclideanNorm, massAdmissibleOn and GeometricCurrentOn.le_massOn.

Library (what is missing).
- Matrix.det_le (Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean) and MultilinearMap.continuous_of_finiteDimensional are not in the import closure; Lean reports unknown constant.
- coeff_bound therefore proves the entrywise bound from the Leibniz formula, and det_covector obtains continuity from Hadamard's inequality.

DAG.
- Accepted declarations reused with byte-identical types:
  - rsd_imrep_compact_measure_ne_top (candidate 702e7082);
  - cmr_abs_apply_le_massOn (candidate 7a706164).
- Each candidate file only adds to Contract.lean. A fresh compile of each prints only propext, Classical.choice and Quot.sound, as it does for dor_ims_massOn_le_measure (fae4fd1e).
- The five new names occur in no dag.json node (983 nodes), no nodes/ file, and no GMT/*.lean at any of the 1695 ref tips.

Lean.
- Types.lean elaborates all 7 child types after import GMT.Ch07.Submission with the contract opens.
- Inst.lean confirms the matrix-column, coordinate, indicator, adjoint and smoothness-order conventions by rfl.
- Assembly.lean proves the frozen selected type from test_form and the two reused declarations, with chart_divergence and mass_upper_bound as axioms; no sorryAx occurs.
- FullChain.lean proves all five new children and then the selected theorem. Each new child depends only on the standard axioms; the selected theorem adds exactly its two resolved dependencies and the two reused declarations. The same holds with no enclosing noncomputable section.
- An independent review subagent re-ran these files and accepted the split.
