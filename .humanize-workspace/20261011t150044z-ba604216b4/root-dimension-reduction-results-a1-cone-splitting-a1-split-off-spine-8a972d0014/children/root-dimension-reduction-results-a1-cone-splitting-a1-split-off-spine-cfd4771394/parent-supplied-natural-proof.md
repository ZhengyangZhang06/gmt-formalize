# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.box_cancellation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 9 and 10 of the selected proof (comparison off K₀ and the arithmetic in [0, ∞]), with a := ofReal((2r + 2)^k), b := ofReal((2r)^k), e := M(E′) and B := ball(0, ρ) generalized; the selected node supplies the hypothesis a·μ₀(B) ≤ (a − b)·μ₀(B) + b·μ₀′(B) + e from (MIN) and steps 7–8. The selected proof is the project's argument for Simon, Lemma 7.3.5 (book/chapter-07.txt, lines 407–417), whose proof Simon leaves to the reader.
Inherited results cited by exact Lean name:
 (MC) Submission.dimred_cs_sos_mt_measure_comparison: if S₁, S₂ ∈ 𝒟_j(ℝ^P) are represented by R₁, R₂ and W₀ ⊆ B are open with spt(S₁ − S₂) ⊆ W₀, then R₁.measure(B) + R₂.measure(W₀) = R₂.measure(B) + R₁.measure(W₀).
 (F1) Submission.imrep_represents_massOn_eq_measure: M_W(T) = R.measure(W) for T represented by R in an open U and every open W ⊆ U.
Notation. μ₀ := R₀.measure, μ₀′ := R₀′.measure, M₀ := R₀.carrier, θ₀ := R₀.mult; x := μ₀(B), y := μ₀′(B), u := μ₀(W₀), v := μ₀′(W₀). Subtraction in [0, ∞] is truncated.

1. (Measure comparison.) (MC) with S₁ := S₀′, S₂ := S₀, R₁ := R₀′, R₂ := R₀ and the open sets W₀ ⊆ B (spt(S₀′ − S₀) ⊆ W₀) gives y + u = x + v.
2. (Masses on W₀.) By (F1) with U := ℝ^P and the open W₀: M_{W₀}(S₀) = u and M_{W₀}(S₀′) = v. So it suffices to prove b·u ≤ b·v + e.
3. (x < ∞.) B is bounded and ℝ^P is proper, so closure B is compact (Bornology.IsBounded.isCompact_closure) and Borel (closed). By the definition of R₀.measure, withDensity_apply and Measure.restrict_restrict, μ₀(closure B) = ∫_{closure B} θ₀ d(H^m⌞M₀) = ∫_{M₀ ∩ closure B} θ₀ dH^m, which is finite by R₀.locallyIntegrable_mult (closure B is compact and ⊆ ℝ^P). Hence x ≤ μ₀(closure B) < ∞, and a·x < ∞ because a < ∞ (ENNReal.mul_ne_top).
4. (Arithmetic.) Add b·u to both sides of the hypothesis, then use distributivity, step 1 and (a − b) + b = a (valid since b ≤ a; tsub_add_cancel_of_le):
 a·x + b·u ≤ (a − b)·x + b·y + e + b·u = (a − b)·x + b·(y + u) + e = (a − b)·x + b·(x + v) + e = ((a − b) + b)·x + (b·v + e) = a·x + (b·v + e).
5. (Cancellation.) Since a·x ≠ ∞, ENNReal.le_of_add_le_add_left gives b·u ≤ b·v + e, which by step 2 is b·M_{W₀}(S₀) ≤ b·M_{W₀}(S₀′) + e. ∎

Formalization sketch (context, not part of the numbered proof). The following Lean proof of exactly the frozen type compiled during decomposition (Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract opens), with every cited Submission.* dependency present as a stub of its exact frozen type:
theorem Submission.dimred_cs_sos_mt_cm_box_cancellation : ∀ (P m : ℕ) (S₀ S₀' : GeometricCurrentOn (univ : Set (Euclid P)) m) (R₀ R₀' : IMRep (univ : Set (Euclid P)) m) (W₀ B : Set (Euclid P)) (a b e : ℝ≥0∞), R₀.Represents S₀ → R₀'.Represents S₀' → IsOpen W₀ → IsOpen B → Bornology.IsBounded B → (S₀' - S₀).support ⊆ W₀ → W₀ ⊆ B → b ≤ a → a ≠ ∞ → a * R₀.measure B ≤ (a - b) * R₀.measure B + b * R₀'.measure B + e → b * S₀.massOn W₀ ≤ b * S₀'.massOn W₀ + e := by
  intro P m S₀ S₀' R₀ R₀' W₀ B a b e hR₀ hR₀' hW₀ hB hBb hsupp hWB hba ha hineq
  -- measure comparison: y + u = x + v
  have hcmp := Submission.dimred_cs_sos_mt_measure_comparison P m S₀' S₀ R₀' R₀ W₀ B hR₀' hR₀ hW₀ hB
    hsupp hWB
  -- masses on W₀ are measures (F1)
  rw [Submission.imrep_represents_massOn_eq_measure P m univ W₀ S₀ R₀ isOpen_univ hR₀ hW₀ (subset_univ _),
    Submission.imrep_represents_massOn_eq_measure P m univ W₀ S₀' R₀' isOpen_univ hR₀' hW₀ (subset_univ _)]
  -- x = μ₀(B) is finite
  have hfin : R₀.measure B ≠ ∞ := by
    have hK : IsCompact (closure B) := hBb.isCompact_closure
    have h1 : R₀.measure (closure B) = ∫⁻ x in R₀.carrier ∩ closure B, (R₀.mult x : ℝ≥0∞) ∂μHE[m] := by
      unfold IMRep.measure
      rw [withDensity_apply _ isClosed_closure.measurableSet,
        Measure.restrict_restrict isClosed_closure.measurableSet, inter_comm]
    have h2 := R₀.locallyIntegrable_mult (closure B) hK (subset_univ _)
    rw [← h1] at h2
    exact ne_top_of_le_ne_top h2 (measure_mono subset_closure)
  have hax : a * R₀.measure B ≠ ∞ := ENNReal.mul_ne_top ha hfin
  apply ENNReal.le_of_add_le_add_left hax
  calc a * R₀.measure B + b * R₀.measure W₀
      ≤ (a - b) * R₀.measure B + b * R₀'.measure B + e + b * R₀.measure W₀ := by gcongr
    _ = (a - b) * R₀.measure B + b * (R₀'.measure B + R₀.measure W₀) + e := by ring
    _ = (a - b) * R₀.measure B + b * (R₀.measure B + R₀'.measure W₀) + e := by rw [hcmp]
    _ = ((a - b) + b) * R₀.measure B + (b * R₀'.measure W₀ + e) := by ring
    _ = a * R₀.measure B + (b * R₀'.measure W₀ + e) := by rw [tsub_add_cancel_of_le hba]

## Key steps

1. Submission.dimred_cs_sos_mt_measure_comparison (S₁ := S₀′, S₂ := S₀) gives μ₀′(B) + μ₀(W₀) = μ₀(B) + μ₀′(W₀).
2. Submission.imrep_represents_massOn_eq_measure identifies M_{W₀}(S₀) = μ₀(W₀) and M_{W₀}(S₀′) = μ₀′(W₀).
3. B bounded ⇒ closure B compact ⇒ μ₀(B) ≤ ∫_{M₀ ∩ closure B} θ₀ dH^m < ∞ (locallyIntegrable_mult), so a·μ₀(B) < ∞.
4. a·x + b·u ≤ (a − b)x + b(y + u) + e = (a − b)x + b(x + v) + e = a·x + (b·v + e); cancel the finite a·x.

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1 = workspace HEAD, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean and Submission.lean with the workspace copies (identical)`
- `python3 over dag.json: the selected node, its ancestors' depends_on and statuses, the exact lean_statement of all 14 dependency/reuse declarations, accepted nodes whose lean_statement mentions '.support', 'ᶜ = 0', 'cycle', 'competitor' (found dimred_mbl_lc_rc_cycle_competitor, dtc_bc_lc_rc_cycle_competitor, cbrld_ns_support_sub_subset, dimred_mbl_pf_imrep_carrier_mass_support, rsd_imrep_compact_measure_ne_top), and grep -c of the five new dimred_cs_sos_mt_cm_* names (0 hits)`
- `git show 35e359955ef6bac37033306b3f33a12c284b7174:GMT/Ch07/Submission.lean: Submission.dimred_mbl_lc_rc_cycle_competitor present with a type byte-identical to dag.json; its import lines equal the contract's`
- `grep -n over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean: GeometricCurrentOn, boundary(_apply), zero_apply, ext, massOn, mass, massOn_mono, massAdmissibleOn, VanishesOn, zeroRegion, support, testFormOnInclusion, restrictDomain, IsTestForm`
- `grep -rn over the snapshot mathlib: setIntegral_sdiff, integral_sub, measure_sdiff (measure_diff deprecated), ENNReal.le_of_add_le_add_left, withDensity_absolutelyContinuous, withDensity_apply, Measure.restrict_apply', Measure.restrict_restrict, starProjection_add_starProjection_orthogonal, inner_starProjection_left_eq_right, starProjection_apply_mem, starProjection_eq_self_iff, Submodule.isClosed_orthogonal, Submodule.closed_of_finiteDimensional, Submodule.mem_span_range_iff_exists_fun, Orthonormal.inner_right_fintype, isBounded_iff_subset_ball, isBounded_iff_subset_closedBall, Bornology.IsBounded.isCompact_closure`
- `grep -n '3.5\|left to the reader' book/chapter-07.txt; sed -n 405,420p (Lemma 3.5, proof left to the reader)`
- `lake env lean /tmp/cm-decomp/{T0,Assembly,A,B,D,E,F,Final}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-8a972d0014/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-4725781174/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`

Pins match. The manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c, and the snapshot Contract.lean and Submission.lean are byte-identical to the workspace files. Simon leaves Lemma 7.3.5 to the reader, so the children are extracted from the supplied project proof. Neither SimonGMT nor the snapshot mathlib contains the five new statements, and their names are unused in dag.json and the snapshot. One accepted declaration fits exactly: Submission.dimred_mbl_lc_rc_cycle_competitor (accepted; candidate 35e35995; type byte-identical; contract imports). It is reused as the Step 4 child. Other accepted lemmas found (cbrld_ns_support_sub_subset, dimred_mbl_pf_imrep_carrier_mass_support, rsd_imrep_compact_measure_ne_top) are not ancestor dependencies. Their content is covered in a few lines inside carried_transfer and box_cancellation, so they are not added. The snapshot mathlib supplies every library fact the child proofs use, under the names cited, including setIntegral_sdiff, measure_sdiff, ENNReal.le_of_add_le_add_left, starProjection_add_starProjection_orthogonal, inner_starProjection_left_eq_right, Submodule.mem_span_range_iff_exists_fun, Orthonormal.inner_right_fintype and Bornology.IsBounded.isCompact_closure. Lean check (Final.lean): the 5 new children are proved from stubs of exactly their cited dependencies, and the frozen parent type is proved from the child and dependency stubs. It compiles with no errors; sorry occurs only in the 14 stubs.
