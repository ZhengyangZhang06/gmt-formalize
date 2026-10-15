# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.limit_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 7 (agreement on expanding balls); cf. Simon Ch. 6, 2.13 (chapter-06.txt lines 308–313: weak convergence is convergence on each test form, and ∂ is continuous for it).
Notation: B_r := ball(0, r); 𝒟^k := TestFormOn ℝ^P k.

1. (Supports lie eventually inside the balls.) Every α ∈ 𝒟^k (any k) has compact, hence bounded, tsupport, so tsupport α ⊆ B_r for some r ∈ ℝ (Bornology.IsBounded.subset_ball). As ρ_j → ∞, ρ_j ≥ r for all large j, and then tsupport α ⊆ B_r ⊆ B_{ρ_j}.

2. (S_j ⇀ C.) Let ω ∈ 𝒟^{m+1}. By step 1 and the agreement hypothesis, currentEval(S_j, ω) = Ŝ_j(ω) for all large j. Since Ŝ_j(ω) → C(ω) (WeaklyConvergesOn), the sequence (currentEval(S_j, ω))_j, which eventually coincides with it, converges to C(ω) as well (Tendsto.congr'). This is ConvergesWeakly (j ↦ S_j) C.

3. (∂C = 0.) Let β ∈ 𝒟^m. By definition of the boundary, ∂Ŝ_j(β) = Ŝ_j(dβ) and ∂C(β) = C(dβ), with dβ ∈ 𝒟^{m+1} (exteriorDerivativeTestOn); hence ∂Ŝ_j(β) → ∂C(β) (WeaklyConvergesOn.boundary). By step 1 and the vanishing hypothesis, ∂Ŝ_j(β) = 0 for all large j, so the same sequence also converges to 0. Limits in ℝ are unique, so ∂C(β) = 0. As β is arbitrary, C.boundary = 0 (GeometricCurrentOn.ext). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). Compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308 after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open` commands (after its `noncomputable section ... end`). No extra import and no sibling declaration is needed; `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dimred_mbl_tc_limit_of_agreement : ∀ (P m : ℕ) (Us : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : ℕ → ℝ), Tendsto ρ atTop atTop → WeaklyConvergesOn Ŝ C → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 (ρ j) → Ŝ j ω = currentEval (Ss j) (ω : DifferentialForm (Euclid P) (m + 1))) → (∀ (j : ℕ) (β : TestFormOn (univ : Set (Euclid P)) m), tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 (ρ j) → (Ŝ j).boundary β = 0) → C.boundary = 0 ∧ ConvergesWeakly Ss C := by
  intro P m Us Ss Ŝ C ρ hρ hconv hagree hbd
  -- every test form on ℝ^P has tsupport in some ball, eventually inside `ball 0 (ρ j)`
  have hev : ∀ {k : ℕ} (ω : TestFormOn (univ : Set (Euclid P)) k), ∀ᶠ j in atTop,
      tsupport (ω : DifferentialForm (Euclid P) k) ⊆ ball 0 (ρ j) := by
    intro k ω
    obtain ⟨r, hr⟩ := ω.property.1.2.isCompact.isBounded.subset_ball (0 : Euclid P)
    filter_upwards [hρ.eventually_ge_atTop r] with j hj
    exact hr.trans (ball_subset_ball hj)
  constructor
  · apply GeometricCurrentOn.ext
    intro β
    have h1 : Tendsto (fun j => (Ŝ j).boundary β) atTop (𝓝 (C.boundary β)) :=
      hconv.boundary β
    have h2 : Tendsto (fun j => (Ŝ j).boundary β) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev β] with j hj
      exact (hbd j β hj).symm
    rw [tendsto_nhds_unique h1 h2]
    rfl
  · intro ω
    refine (hconv ω).congr' ?_
    filter_upwards [hev ω] with j hj
    exact hagree j ω hj
```

## Key steps

1. Every test form has tsupport in some ball, hence in ball(0, ρ_j) for all large j.
2. Eventually currentEval(S_j, ω) = Ŝ_j(ω) → C(ω): ConvergesWeakly.
3. ∂Ŝ_j(β) → ∂C(β) and ∂Ŝ_j(β) = 0 eventually, so ∂C(β) = 0.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of RUN/dag.json: selected node, parent root.dimension_reduction_results-a1.moving_blowups-a1 and its children, dependency types (dor_imrep_massOn_eq_measure_and_support, dimred_mbl_current_foundations, dimred_mbl_slice_mass_bounds, dimred_mbl_closure_and_boundary_rectifiability), accepted declarations mentioning massOn/IMRep/compact/diagonal/separab, collisions for dimred_mbl_tc_*`
- `rg -n 'Banach|Alaoglu|SecondCountableTopology|IsSeparable|diagonal|extraction' lake-packages/simongmt/Poincare/SimonGMT/Chapter06 (no match); rg -n 'WeaklyConvergesOn|Banach' SNAPSHOT/project --glob '*.lean'`
- `rg -n 'instSecondCountableTopology|theorem extraction_forall_of_eventually|IsSeparable.exists_countable_dense_subset|Filter.EventuallyEq.extDeriv_eq' SNAPSHOT/mathlib/Mathlib; grep of setLIntegral_congr_fun, lipschitzWith_one_norm, ContDiffBump API, tsupport_sub, norm_iteratedFDeriv_zero`
- `sed -n on book/chapter-06.txt lines 284–333 (2.9, 2.13–2.15), 755–767 (3.2), 875–895 (3.11), 1330–1380 (4.6–4.10)`
- `grep -n _existing_lean_name_problem _overlay_accepted_children _accepted_checkpoint ensure in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and store.py; contract_scope in verifier/gmt-compare.py`
- `lake env lean on Types/Final.lean (7 child types), Assembly.lean (conditional parent), LT.lean, TR.lean, WC.lean (child proofs from sibling types), SubForm.lean and SubParent.lean (Submission-form compile), all with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-truncated-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-cov-64249b6f60/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-imrep-1bd5f15878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/tc-decomp-x7k2/lean/Assembly.lean`
- `/tmp/tc-decomp-x7k2/lean/TR.lean`
- `/tmp/tc-decomp-x7k2/lean/WC.lean`
- `/tmp/tc-decomp-x7k2/lean/LT.lean`

Pins match: HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308, and Submission.lean is byte-identical to Contract.lean. Neither the pinned libraries nor any accepted DAG node proves weak compactness of currents. SimonGMT Chapter06 has no match. The project snapshot states Simon 2.15 only as the unproved Ch06 contract conjunct CompactnessUnderMassBounds (GMT/Ch06/Contract.lean:194–205), a different problem. So weak_compactness is a new child. Its Lean route exists in Mathlib: ContinuousMap.instSecondCountableTopology (separate import), IsSeparable.exists_countable_dense_subset, IsCompact.tendsto_subseq on a countable product, and norm_iteratedFDeriv_zero. The cut-off uses ContDiffBump and Filter.EventuallyEq.extDeriv_eq. Step 1 uses Filter.extraction_forall_of_eventually. Four accepted declarations are reused with identical frozen types: cmr_abs_apply_le_massOn, cmr_covector_euclidean_equiv, cmc_imRep_locality_restrict_sub and lcmp_imRep_measure_restrict. The new names dimred_mbl_tc_* collide with nothing. All child types elaborate. The conditional assembly proves the exact parent type, and each new child is proved in Lean from its sibling types. All of these depend only on propext, Classical.choice and Quot.sound.
