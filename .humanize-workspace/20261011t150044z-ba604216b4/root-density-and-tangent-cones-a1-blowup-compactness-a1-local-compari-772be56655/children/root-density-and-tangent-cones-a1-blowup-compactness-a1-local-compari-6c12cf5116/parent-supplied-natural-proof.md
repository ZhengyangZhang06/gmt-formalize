# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.slice_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (Simon Ch. 6, Lemma 4.1: "the last part of the lemma is just a restatement of the appropriate version of the co-area formula"; Ch. 3, 2.10(2): the slices are countably rectifiable "from the decomposition M = ⋃_j M_j"), with approximate tangent planes transferred by the locality theorem im_calculus (a) (TL).
Notation: μ := Hⁿ; S_t := M ∩ f⁻¹(t); S_{j,t} := A_j ∩ f⁻¹(t); B̄_k := closedBall(0, k); Φ_t(x) :⟺ G(x) ≠ 0 ∧ HasApproximateTangentSpaceAt n S_t x (T(x) ⊓ (ℝ∙G(x))ᗮ).

1. (Slices are locally finite for a.e. t.) Fix k ∈ ℕ and let g_k := the indicator function of B̄_k (value 1 on B̄_k, 0 elsewhere), which is Borel. For every t, ∫_{S_t} g_k dμ = (μ⌞S_t)(B̄_k) = μ(B̄_k ∩ S_t) (lintegral_indicator_one, Measure.restrict_apply; B̄_k is closed). By (i) and |G| ≤ L,
 ∫_ℝ μ(S_t ∩ B̄_k) dt = ∫_M ofReal|G|·g_k dH^{n+1} ≤ ∫_M L·g_k dH^{n+1} = L·H^{n+1}(M ∩ B̄_k) < ∞,
 the last because B̄_k is compact. The integrand t ↦ μ(S_t ∩ B̄_k) is a.e.-measurable by (i), so it is finite for a.e. t (ae_lt_top'). Intersecting over the countably many k (ae_all_iff): for a.e. t, μ(S_t ∩ B̄_k) < ∞ for every k. For such t and any compact K ⊆ ℝ^P, K is bounded, so K ⊆ B̄_k for some k ∈ ℕ and μ(S_t ∩ K) ≤ μ(S_t ∩ B̄_k) < ∞.
2. (Good t.) Call t good if (α) μ(S_t ∩ K) < ∞ for every compact K, (β) μ(M₀ ∩ f⁻¹(t)) = 0, and (γ) for every j the conclusion of (iii) holds at t. (α) holds a.e. by step 1, (β) by (ii), and (γ) by (iii) and ae_all_iff (countably many j). Hence a.e. t is good. Fix a good t.
3. (Rectifiability.) Every point of M lies in M₀ or in some A_j, so S_t ⊆ (M₀ ∩ f⁻¹(t)) ∪ ⋃_j S_{j,t}. The set M₀ ∩ f⁻¹(t) is μ-null by (β), hence countably n-rectifiable (countablyRectifiable_of_measure_zero); each S_{j,t} is countably n-rectifiable by (γ). With E_0 := M₀ ∩ f⁻¹(t) and E_{j+1} := S_{j,t}, the union ⋃_i E_i is countably n-rectifiable (countablyRectifiable_iUnion), and so is its subset S_t (CountablyRectifiable.mono).
4. (Tangent planes on each piece.) S_t is Borel (M and f Borel), μ(S_t ∩ K) < ∞ for every compact K by (α), and S_{j,t} ⊆ S_t is Borel. By im_calculus part (a) in dimension n, with U := ℝ^P and the pair S_{j,t} ⊆ S_t: for μ-a.e. x ∈ S_{j,t} and every linear subspace Q, S_{j,t} has approximate tangent space Q at x iff S_t does. Combining this with (γ) (for μ-a.e. x ∈ S_{j,t}: G(x) ≠ 0 and S_{j,t} has approximate tangent space T(x) ⊓ (ℝ∙G(x))ᗮ at x) gives Φ_t(x) for μ⌞S_{j,t}-a.e. x.
5. (All of S_t.) S_t ⊆ (S_t ∖ ⋃_j S_{j,t}) ∪ ⋃_j S_{j,t}, and S_t ∖ ⋃_j S_{j,t} ⊆ M₀ ∩ f⁻¹(t) is μ-null, so Φ_t holds μ⌞(S_t ∖ ⋃_j S_{j,t})-a.e. trivially. With step 4, ae_restrict_iUnion_iff and ae_restrict_union_iff, Φ_t holds μ⌞((S_t ∖ ⋃_j S_{j,t}) ∪ ⋃_j S_{j,t})-a.e., hence μ⌞S_t-a.e. (ae_restrict_of_ae_restrict_of_subset).
6. Steps 3 and 5 hold for every good t, hence for a.e. t. ∎

Lean realization note. The verified code below follows steps 1–6. CountablyRectifiable is never unfolded (step 3 applies countablyRectifiable_iUnion to the family i ↦ (i = 0 ? M₀ ∩ f⁻¹(t) : A_{i−1} ∩ f⁻¹(t)), then CountablyRectifiable.mono), and step 5 covers S_t by (M₀ ∩ f⁻¹(t)) ∪ ⋃_j S_{j,t} directly.

Appendix (verified Lean realization of the proof above). The code below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b36630 when placed after `import GMT.Ch07.Submission` in the frozen contract scope (inside `namespace GMT.Ch07` with the contract's `open` commands, after the contract's `noncomputable section … end`), i.e. where accepted `theorem Submission.…` declarations live in GMT/Ch07/Submission.lean. It refers to the sibling declarations Submission.cmc_imRep_locality_restrict_sub (each with its exact frozen type, introduced by `have h_<key> : <type> := Submission.<name>` at the start of the proof). It was checked twice: (i) with the exact frozen sibling types as hypotheses, giving no errors and no warnings and `#print axioms` = [propext, Classical.choice, Quot.sound]; (ii) end to end, in one file containing all eight new children of dtc_bc_lc_sl_coarea in dependency order, the parent theorem proved from them, and `sorry` placeholders only for the reused accepted declarations and the parent's resolved dependencies (no warning from any child declaration). `Submission.dtc_bc_lc_sl_co_slice_glue` has exactly the frozen type of this child.

```lean
theorem Submission.dtc_bc_lc_sl_co_slice_glue : ∀ (P n : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P) (T : Euclid P → Submodule ℝ (Euclid P)) (A : ℕ → Set (Euclid P)) (L : NNReal), MeasurableSet M → Measurable f → (∀ K : Set (Euclid P), IsCompact K → μHE[n + 1] (M ∩ K) ≠ ∞) → (∀ x, ‖G x‖ ≤ L) → (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) → (∀ j, MeasurableSet (A j)) → (∀ j, A j ⊆ M) → (∀ᵐ t, μHE[n] ((M \ ⋃ j, A j) ∩ f ⁻¹' {t}) = 0) → (∀ j, ∀ᵐ t, CountablyRectifiable n (A j ∩ f ⁻¹' {t}) ∧ ∀ᵐ x ∂(μHE[n].restrict (A j ∩ f ⁻¹' {t})), G x ≠ 0 ∧ HasApproximateTangentSpaceAt n (A j ∩ f ⁻¹' {t}) x (T x ⊓ (ℝ ∙ G x)ᗮ)) → ∀ᵐ t, CountablyRectifiable n (M ∩ f ⁻¹' {t}) ∧ ∀ᵐ x ∂(μHE[n].restrict (M ∩ f ⁻¹' {t})), G x ≠ 0 ∧ HasApproximateTangentSpaceAt n (M ∩ f ⁻¹' {t}) x (T x ⊓ (ℝ ∙ G x)ᗮ) := by
  have h_im_calculus : ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) := Submission.cmc_imRep_locality_restrict_sub
  intro P n M f G T A L hM hf hMK hGL hco hA hAM hslice hAj
  obtain ⟨hTL, -, -, -⟩ := h_im_calculus
  have hfib : ∀ t : ℝ, MeasurableSet (f ⁻¹' {t}) := fun t => hf (measurableSet_singleton t)
  have hSt : ∀ t : ℝ, MeasurableSet (M ∩ f ⁻¹' {t}) := fun t => hM.inter (hfib t)
  have hSj : ∀ t : ℝ, ∀ j, MeasurableSet (A j ∩ f ⁻¹' {t}) := fun t j => (hA j).inter (hfib t)
  -- Step 1: for a.e. `t` the slice has finite measure in every closed ball `closedBall 0 k`
  have hfin : ∀ k : ℕ, ∀ᵐ t, μHE[n] (M ∩ f ⁻¹' {t} ∩ closedBall (0 : Euclid P) (k : ℝ)) < ∞ := by
    intro k
    have hB : MeasurableSet (closedBall (0 : Euclid P) (k : ℝ)) := measurableSet_closedBall
    have hg : Measurable ((closedBall (0 : Euclid P) (k : ℝ)).indicator (1 : Euclid P → ℝ≥0∞)) :=
      measurable_one.indicator hB
    obtain ⟨hgm, hgeq⟩ := hco _ hg
    have hint : ∀ t : ℝ, ∫⁻ x in M ∩ f ⁻¹' {t},
        (closedBall (0 : Euclid P) (k : ℝ)).indicator (1 : Euclid P → ℝ≥0∞) x ∂μHE[n]
        = μHE[n] (M ∩ f ⁻¹' {t} ∩ closedBall (0 : Euclid P) (k : ℝ)) := by
      intro t
      rw [lintegral_indicator_one hB, Measure.restrict_apply hB,
        inter_comm (closedBall (0 : Euclid P) (k : ℝ))]
    have hbound : ∫⁻ t, ∫⁻ x in M ∩ f ⁻¹' {t},
        (closedBall (0 : Euclid P) (k : ℝ)).indicator (1 : Euclid P → ℝ≥0∞) x ∂μHE[n] ≠ ∞ := by
      rw [hgeq]
      have hfin' : (L : ℝ≥0∞) * μHE[n + 1] (M ∩ closedBall (0 : Euclid P) (k : ℝ)) ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top (hMK _ (isCompact_closedBall 0 (k : ℝ)))
      refine ne_top_of_le_ne_top hfin' ?_
      calc ∫⁻ x in M, ENNReal.ofReal ‖G x‖
              * (closedBall (0 : Euclid P) (k : ℝ)).indicator (1 : Euclid P → ℝ≥0∞) x ∂μHE[n + 1]
          ≤ ∫⁻ x in M, (L : ℝ≥0∞)
              * (closedBall (0 : Euclid P) (k : ℝ)).indicator (1 : Euclid P → ℝ≥0∞) x ∂μHE[n + 1] := by
            refine lintegral_mono fun x => ?_
            gcongr
            rw [← ENNReal.ofReal_coe_nnreal]
            exact ENNReal.ofReal_le_ofReal (hGL x)
        _ = (L : ℝ≥0∞) * μHE[n + 1] (M ∩ closedBall (0 : Euclid P) (k : ℝ)) := by
            rw [lintegral_const_mul _ hg, lintegral_indicator_one hB, Measure.restrict_apply hB,
              inter_comm (closedBall (0 : Euclid P) (k : ℝ))]
    filter_upwards [ae_lt_top' hgm hbound] with t ht
    rwa [hint t] at ht
  -- Step 2: good `t`
  filter_upwards [ae_all_iff.2 hfin, hslice, ae_all_iff.2 hAj] with t h1 h2 h3
  have hcover : M ∩ f ⁻¹' {t} ⊆ ((M \ ⋃ j, A j) ∩ f ⁻¹' {t}) ∪ ⋃ j, A j ∩ f ⁻¹' {t} := by
    rintro y ⟨hyM, hyf⟩
    by_cases hy : y ∈ ⋃ j, A j
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hy
      exact Or.inr (mem_iUnion.2 ⟨j, hj, hyf⟩)
    · exact Or.inl ⟨⟨hyM, hy⟩, hyf⟩
  refine ⟨?_, ?_⟩
  · -- Step 3: rectifiability (only the public API of `CountablyRectifiable` is used)
    have hE : ∀ i : ℕ, CountablyRectifiable n
        (if i = 0 then (M \ ⋃ j, A j) ∩ f ⁻¹' {t} else A (i - 1) ∩ f ⁻¹' {t}) := by
      intro i
      split_ifs
      · exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero h2
      · exact (h3 (i - 1)).1
    have hsub : M ∩ f ⁻¹' {t} ⊆ ⋃ i : ℕ,
        (if i = 0 then (M \ ⋃ j, A j) ∩ f ⁻¹' {t} else A (i - 1) ∩ f ⁻¹' {t}) := by
      intro y hy
      rcases hcover hy with hy0 | hy1
      · exact mem_iUnion.2 ⟨0, by simpa using hy0⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.1 hy1
        exact mem_iUnion.2 ⟨j + 1, by simpa using hj⟩
    exact (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ hE).mono hsub
  · -- Steps 4-5: approximate tangent planes
    have hlocfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
        μHE[n] (M ∩ f ⁻¹' {t} ∩ K) ≠ ∞ := by
      intro K hK _
      obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Euclid P)
      obtain ⟨k, hk⟩ := exists_nat_ge r
      exact ne_top_of_le_ne_top (h1 k).ne
        (measure_mono (inter_subset_inter_right _ (hr.trans (closedBall_subset_closedBall hk))))
    refine ae_restrict_of_ae_restrict_of_subset hcover ?_
    rw [ae_restrict_union_iff, ae_restrict_iUnion_iff]
    refine ⟨?_, fun j => ?_⟩
    · rw [Measure.restrict_eq_zero.2 h2]
      simp
    · have hloc := hTL P n univ (A j ∩ f ⁻¹' {t}) (M ∩ f ⁻¹' {t}) isOpen_univ (hSj t j) (hSt t)
        (inter_subset_inter_left _ (hAM j)) (subset_univ _) hlocfin
      filter_upwards [hloc, (h3 j).2] with x hx1 hx2
      exact ⟨hx2.1, (hx1 _).1 hx2.2⟩
```

## Key steps

1. Co-area with g = 1_{closedBall(0,k)} and |G| ≤ L: ∫ Hⁿ(M ∩ f⁻¹(t) ∩ B̄_k) dt ≤ L·H^{n+1}(M ∩ B̄_k) < ∞, so a.e. slice is locally Hⁿ-finite.
2. For a.e. t (countably many conditions): the slice of M₀ is null and every piece has the slice property.
3. M ∩ f⁻¹(t) ⊆ (null set) ∪ ⋃_j A_j ∩ f⁻¹(t) is countably n-rectifiable.
4. im_calculus (a) transfers the approximate tangent plane T(x) ⊓ (ℝ G(x))ᗮ from A_j ∩ f⁻¹(t) to M ∩ f⁻¹(t) at a.e. point; the null part is negligible.
5. Verified Lean realization supplied in the appendix (compiles warning-free; standard axioms only).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat .lake/packages manifest (simongmt 2b36630)`
- `python3 -I scans of dag.json (1523 nodes): slicing-a1 subtree and statuses; frozen types of chart_pieces, chart_coarea, eilenberg, im_calculus; nodes matching bi-Lipschitz|immersion|density point|Lebesgue density|blowUpMap|tangential gradient|co-area|Injective (fderiv; the dor_lmb...slicing-a1.slice_family-a1 subtree (lipschitz_chart_pieces, density_directions, piece_coarea, piece_slice_tangent, tangential_gradient)`
- `git show <commit>:GMT/Ch07/Submission.lean and whitespace-normalised type comparison for cmc_imRep_locality_restrict_sub (2af75d6), codim1_rdo_c1cov_local_lower_lipschitz (12e74ed), rsd_tendsto_closedBall_density_of_approxTangent (dbef2c1), dor_lmb_approx_tangent_locality (53d4678): all MATCH; nodes/*/accepted-candidate.json comparator_passed = true`
- `grep -c dtc_bc_lc_sl_co_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_co_' over 6410 refs (no match); survey of 400 accepted candidate commits: added declarations are theorem Submission.*`
- `grep in the snapshot Mathlib: Besicovitch.ae_tendsto_measure_inter_div, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_smul, Measure.addHaar_closedBall, measure_inter_add_sdiff, lintegral_iUnion, lintegral_tsum, ENNReal.Tendsto.sub, ContinuousOn.measurable_piecewise, Measurable.find, ContinuousOn.preimage_isClosed_of_isClosed, InjOn.leftInvOn_invFunOn, ae_restrict_iUnion_iff, ae_restrict_union_iff, ae_restrict_iff', ae_lt_top', NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint_inner_left, toDual_symm_apply, IsCompact.exists_bound_of_continuousOn, LinearMap.isUnit_iff_ker_eq_bot`
- `grep in SimonGMT: Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, .unique, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono); Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn); Chapter04/TangentDensity.lean; no nonlinear co-area, tangential gradient or slicing declarations`
- `sed book/chapter-03.txt lines 300-460 (Remark 1.8, 2.1-2.10) and book/chapter-06.txt lines 1140-1200 (Lemma 4.1)`
- `Lean checks through a persistent LSP worker: #check availability file under import GMT.Ch07.Submission; /tmp/coarea_split/v2/ch/Challenge_<key>.lean (11 modules from gmt-compare.py child_modules, contract mode); /tmp/coarea_split/asm/Assembly3.lean; /tmp/coarea_split/agents/{A,B,C,D,E} hypothesis-form proofs; /tmp/coarea_split/e2e2/E2E_from_json.lean and E2E_solution.lean (end to end, comparator form)`
- `sed /runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py (_decompose depth gate, _dependency_problem, _existing_lean_name_problem) and prompts.py (DECOMPOSITION_AUDIT, RLCR_LEAN_TASK, LEAN_AUDIT, SPECULATIVE_PARENT_TASK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-772be56655/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ec0e4b9204/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/prompts.py`
- `/tmp/coarea_split/v2/ch`
- `/tmp/coarea_split/asm/Assembly3.lean`
- `/tmp/coarea_split/e2e2/E2E_from_json.lean`
- `/tmp/coarea_split/e2e2/E2E_solution.lean`

Neither the pinned SimonGMT library nor Mathlib has a nonlinear co-area formula, a tangential gradient of Lipschitz functions on rectifiable sets, or slicing. They do supply every tool cited in the child proofs: the Lebesgue density theorem, Lusin–Souslin, the Lipschitz image bound, the mean value inequality, Haar scaling, adjoints, continuity of Ring.inverse, and the countable-rectifiability lemmas. Three comparator-accepted DAG declarations are reused with identical types: cmc_imRep_locality_restrict_sub, codim1_rdo_c1cov_local_lower_lipschitz and rsd_tendsto_closedBall_density_of_approxTangent. dor_lmbsf_density_directions (accepted) overlaps one step of density_gradient_bound but is not needed. The eight new names are unreserved. All 11 types elaborate in the exact comparator challenge modules. Every new child is proved in Lean exactly as typed, both in hypothesis form and end to end. The exact frozen parent type is proved from the children and its resolved dependencies, using only propext, Classical.choice and Quot.sound.
