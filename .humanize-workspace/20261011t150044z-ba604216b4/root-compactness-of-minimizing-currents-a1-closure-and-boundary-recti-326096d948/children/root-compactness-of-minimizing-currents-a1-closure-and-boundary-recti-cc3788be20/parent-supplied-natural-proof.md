# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.isp_of_im-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.isp_of_im-a1.restrict_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–5 of the supplied proof of cbr_cc_slice_property_of_im (the proofs that A_t and B_t are integer multiplicity), isolated for an arbitrary integer multiplicity X ∈ 𝒟_q(U), an arbitrary admissible representation (μ, ξ) of X and an arbitrary Borel set E. The parent applies it twice with U := ℝ^P and E := {f < t}: with (q, X, μ, ξ, A) := (d + 1, X, μ, ξ, A_t) and with (q, X, μ, ξ, A) := (d, ∂X, μ', ξ', B_t). Step 3 of the supplied proof is provided by the reused siblings imrep_data (cmc_fcl_imrep_integral_data) and imrep_restrict (cmc_fcl_imrep_restrict_formula).
Notation: |α| := covectorEuclideanNorm α; for a field ζ and a form ω, ζ(ω) denotes the function x ↦ ζ(x)(ω(x)); H^q := μHE[q].
1. (Representation of X.) Since X is integer multiplicity, there is an IMRep R_X = (M, θ, ζ) in U of degree q with R_X.Represents X. Put ν := R_X.measure = (H^q⌞M).withDensity θ.
2. (Restricted IMRep.) U is open and E is Borel, so (IMC)(b) applied to R_X and E gives a current A' ∈ 𝒟_q(U) and an IMRep R' in U with R'.Represents A', R'.carrier = M ∩ E, R'.mult = θ and R'.orient = ζ.
3. (Admissibility of (ν, ζ).) The sibling imrep_data applied to the current X and its representation R_X gives: (a) ν(K) < ∞ for every compact K ⊆ U; (b) ζ is ν-a.e. strongly measurable; (c) if |ζ(x)(α)| ≤ |α| for all α for H^q⌞M-a.e. x, then the same holds for ν-a.e. x; (d) X(ω) = ∫ ζ(ω) dν for every ω ∈ 𝒟^q(U). The hypothesis of (c) is exactly (IMC)(d) for R_X, so |ζ(x)(α)| ≤ |α| for all α holds for ν-a.e. x.
4. (Applying (RU).) Apply (RU) with k := q, the open set U, (μ₁, ξ₁) := (μ, ξ), (μ₂, ξ₂) := (ν, ζ) and (μ₃, ξ₃) := (0, 0), the zero measure with the zero field x ↦ 0. Its hypotheses hold. Finiteness on compact subsets of U: for μ by assumption, for ν by 3(a), and trivially for the zero measure. A.e. strong measurability: for ξ by assumption, for ζ by 3(b), and for the constant field 0 because constant functions are strongly measurable (aestronglyMeasurable_const). Unit bounds: for ξ by assumption, for ζ by step 3, and for the zero measure because every property holds a.e. for it (its a.e. filter is ⊥). The identity: for every ω ∈ 𝒟^q(U), ∫ ξ(ω) dμ = X(ω) = ∫ ζ(ω) dν = ∫ ζ(ω) dν + ∫ 0 d0, by the representation hypothesis on (μ, ξ), by 3(d), and because every integral against the zero measure is 0 (integral_zero_measure). The conclusion of (RU) with the Borel set B := E gives, for every ω ∈ 𝒟^q(U), ∫_E ξ(ω) dμ = ∫_E ζ(ω) dν + ∫_E 0 d0 = ∫_E ζ(ω) dν, because the restriction of the zero measure is the zero measure (Measure.restrict_zero) and its integral vanishes.
5. (Applying imrep_restrict.) The sibling imrep_restrict applied to R := R_X, R', A' and E (E Borel, R' represents A', carrier(R') = M ∩ E, mult(R') = θ, orient(R') = ζ) gives A'(ω) = ∫_E ζ(ω) dν for every ω ∈ 𝒟^q(U).
6. (Conclusion.) For every ω ∈ 𝒟^q(U), A(ω) = ∫_E ξ(ω) dμ (hypothesis on A) = ∫_E ζ(ω) dν (step 4) = A'(ω) (step 5) = R'.action(ω) (R' represents A'). Hence R'.Represents A, so A is integer multiplicity (IsIntegerMultiplicity A is witnessed by R'). ∎
Appendix (verified Lean). This tactic proof of exactly the frozen statement compiled after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens, with Submission.cmc_fcl_imrep_integral_data and Submission.cmc_fcl_imrep_restrict_formula available at their frozen types. #print axioms: propext, Classical.choice, Quot.sound.
  intro hIMCb hIMCd hRU P q U X A μ ξ E hU hX hμ hξm hξb hXrep hE hArep
  obtain ⟨RX, hRX⟩ := hX
  obtain ⟨A', R', hR'A', hcar, hmult, hor⟩ := hIMCb P q U RX E hU hE
  obtain ⟨hfinK, hmeas, hbnd, hint⟩ := Submission.cmc_fcl_imrep_integral_data P q U X RX hRX
  have hRU' := hRU P q U μ RX.measure 0 ξ RX.orient (fun _ => 0) hU hμ hfinK
    (fun K _ _ => by simp) hξm hmeas aestronglyMeasurable_const hξb (hbnd (hIMCd P q U RX))
    (by simp) (fun ω => by rw [← hXrep ω, ← hint ω]; simp)
  obtain ⟨-, hA'⟩ := Submission.cmc_fcl_imrep_restrict_formula P q U RX R' A' E hE hR'A' hcar hmult hor
  refine ⟨R', fun ω => ?_⟩
  rw [hArep ω, hRU' E ω hE, ← hA' ω, hR'A' ω]
  simp

## Key steps

1. Choose an IMRep R_X of X; (IMC)(b) with the Borel set E gives a current A' and an IMRep R' representing A' with carrier R_X.carrier ∩ E and the multiplicity and orientation of R_X.
2. imrep_data for (X, R_X), with (IMC)(d): R_X.measure is finite on compact subsets of U, R_X.orient is R_X.measure-a.e. strongly measurable and unit bounded, and X(ω) = ∫ R_X.orient(ω) dR_X.measure.
3. (RU) with (μ, ξ), (R_X.measure, R_X.orient), (0, 0) and B := E gives ∫_E ξ(ω) dμ = ∫_E R_X.orient(ω) dR_X.measure.
4. imrep_restrict gives A'(ω) = ∫_E R_X.orient(ω) dR_X.measure, so A(ω) = A'(ω) = R'.action(ω) and R' represents A.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp of snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (all identical)`
- `python3 -I over dag.json: frozen type of the selected node (split into IMC(a-d), SL, MM, RU) and of the sibling cbr_cc_current_algebra; accepted declarations whose type mentions IMRep and .measure (cmc_fcl_imrep_integral_data, cmc_fcl_imrep_restrict_formula, cmc_fcl_massOn_le_measure_inter, cmc_fcl_massOn_le_add, cbr_imRep_measure_basic, lcmp_imRep_measure_restrict, dor_lmb_imrep_restrict_current, rsd_imrep_compact_measure_ne_top, cmc_massOn_eq_imRep_measure); status/candidate_commit of the three reused nodes (all accepted; candidate commits cc7e5b19, 7868c22b and 1041782e); lean_name collision check for cbr_ccisp_restrict_isIntegerMultiplicity and cbr_ccisp_ae_massOn_lt_top (absent among 1310 DAG names)`
- `rg -n 'cbr_ccisp|cmc_fcl_|cbr_cc_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project --glob '*.lean' (no match)`
- `rg -n -F in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib: 'theorem ae_lt_top ', "theorem ae_restrict_iff' ", 'theorem ae_all_iff ', 'theorem _root_.Bornology.IsBounded.subset_ball', 'isCompact_closedBall' (ProperSpace export), 'theorem ball_subset_closedBall', 'theorem mul_lt_top ', 'theorem integral_zero_measure', 'theorem aestronglyMeasurable_const', 'theorem measurableSet_lt ', 'theorem exists_nat_gt', 'theorem limsup_const' (liminf_const via to_dual), 'theorem integral_withDensity_eq_integral_smul', 'theorem restrict_withDensity ', 'theorem enorm_integral_le_lintegral_enorm', 'theorem withDensity_absolutelyContinuous', 'theorem lintegral_indicator_one '`
- `grep -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Mass,Currents}.lean: massAdmissibleOn, GeometricCurrentOn.massOn, GeometricCurrentOn.massOn_mono, GeometricCurrentOn.le_massOn, GeometricCurrentOn.ext, GeometricCurrentOn.boundary_apply`
- `sed -n on /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, existing_by_name child-id mapping) and store.py ensure (existing nodes are returned unchanged)`
- `git show cc7e5b19a93e9f857a433ce9746013fcfc7ba856:GMT/Ch07/Submission.lean (accepted declarations are written theorem Submission.X inside namespace GMT.Ch07)`
- `lake env lean /tmp/isp-im-decomp/lean/{Types,Assembly,Restrict,AeFinite,Full,Final}.lean with #print axioms (all compile; axioms propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-326096d948/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-326096d948/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-2bdc65f87f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-a5cfc87778/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-be968f7b5a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/tmp/isp-im-decomp/lean/Full.lean`
- `/tmp/isp-im-decomp/lean/Final.lean`

Findings:
- The snapshot (project b4d606d, Mathlib 25730c7c) has a Contract.lean byte-identical to the workspace Contract.lean and Submission.lean.
- Neither the snapshot project nor SimonGMT contains the restriction-IM or a.e.-finite-slice-mass lemmas: rg finds no cbr_ccisp_/cmc_fcl_/cbr_cc_ match, and SimonGMT Chapter06 supplies only massOn, massOn_mono, le_massOn and GeometricCurrentOn.ext. Two new children are therefore needed.
- Three accepted DAG declarations match steps 3 and 6(i) of the supplied proof exactly: cmc_fcl_imrep_integral_data, cmc_fcl_imrep_restrict_formula and cmc_fcl_massOn_le_measure_inter. Each has status accepted with a candidate commit. They are reused by Lean name with types copied byte-for-byte, which runtime.py _existing_lean_name_problem permits.
- The new names cbr_ccisp_restrict_isIntegerMultiplicity and cbr_ccisp_ae_massOn_lt_top collide with nothing.
- Every Mathlib lemma used by the new proofs is in the pinned snapshot: ae_lt_top, ae_restrict_iff', ae_all_iff, Bornology.IsBounded.subset_ball, isCompact_closedBall, liminf_const, ENNReal.mul_lt_top, integral_zero_measure, aestronglyMeasurable_const, measurableSet_lt and exists_nat_gt.
Lean checks (lake env lean in the workspace):
- All five child types elaborate in the replayed contract scope.
- The exact frozen node type compiles from the children plus cbr_cc_current_algebra.
- Both new children compile, and the reused proofs recompile verbatim.
- Axioms are only propext, Classical.choice and Quot.sound.
