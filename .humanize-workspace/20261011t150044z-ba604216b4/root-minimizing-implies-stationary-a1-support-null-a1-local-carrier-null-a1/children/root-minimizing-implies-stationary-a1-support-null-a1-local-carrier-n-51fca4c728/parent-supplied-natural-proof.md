# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.support_null-a1.local_carrier_null-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.support_null-a1.local_carrier_null-a1.orient_component_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 4–6 of the parent proof for one fixed covector α, followed by the passage from H^n⌞(M ∩ closure W) to H^n⌞(M ∩ W).
This proof uses the sibling component_integrable: for every compact K ⊆ U and every α ∈ Λ^n, x ↦ θ(x)·ξ(x)(α) is integrable on M ∩ K with respect to H^n.
Notation.
- M := R.carrier, θ := R.mult, ξ := R.orient, H^n := μHE[n], C := closure W.
- ν := H^n⌞(M ∩ C) = μHE[n].restrict (M ∩ C) and ν' := H^n⌞(M ∩ W) = μHE[n].restrict (M ∩ W).
- Fix α ∈ Covector (Euclid P) n and put f(x) := θ(x)·ξ(x)(α).
Fields of R used: measurableSet_carrier, mult_pos.
Representation: T(ω) = R.action(ω) = ∫_M θ(x)·ξ(x)(ω(x)) dH^n(x) for every ω ∈ TestFormOn U n. Openness of U is not needed.
1. Measurability. M is measurable (measurableSet_carrier), C is closed and W is open, so M ∩ C and M ∩ W are measurable.
2. Local integrability. C is compact and C ⊆ U, so component_integrable with K = C makes f ν-integrable. Hence f is locally integrable with respect to ν (Integrable.locallyIntegrable), and in particular locally integrable on W with respect to ν (LocallyIntegrable.locallyIntegrableOn).
3. Testing T. Let g : ℝ^P → ℝ be C^∞ (ContDiff ℝ ∞) with compact support and tsupport g ⊆ W. Define the n-form ω(x) := g(x)·α.
- ω is C^∞, being the product of the smooth g with the constant α (ContDiff.smul with contDiff_const).
- ω has compact support (HasCompactSupport.smul_right).
- tsupport ω ⊆ tsupport g ⊆ W ⊆ C ⊆ U (tsupport_smul_subset_left, subset_closure, and the hypothesis closure W ⊆ U).
Hence ω ∈ TestFormOn U n with tsupport ω ⊆ W, so T(ω) = 0 because T vanishes on W. By the representation,
0 = T(ω) = ∫_M θ(x)·ξ(x)(g(x)·α) dH^n(x).
If x ∈ M ∖ (M ∩ C), then x ∉ C ⊇ W ⊇ tsupport g, so g(x) = 0 (image_eq_zero_of_notMem_tsupport). The integrand at x is then θ(x)·ξ(x)(0) = 0. Since M is measurable and M ∩ C ⊆ M, the integral over M equals the integral over M ∩ C (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, which needs no integrability assumption). By linearity of ξ(x), θ(x)·ξ(x)(g(x)·α) = g(x)·(θ(x)·ξ(x)(α)) = g(x)·f(x). Therefore
∫ g(x)·f(x) dν(x) = ∫_{M∩C} θ(x)·ξ(x)(g(x)·α) dH^n(x) = ∫_M θ(x)·ξ(x)(g(x)·α) dH^n(x) = 0.
4. Fundamental lemma. ℝ^P is a finite-dimensional real normed space with its Borel σ-algebra, ℝ is complete, and W is open.
- By step 2, f is locally integrable on W for ν.
- By step 3, ∫ g·f dν = 0 for every C^∞ g with compact support and tsupport g ⊆ W.
Mathlib's IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero then gives: for ν-a.e. x, x ∈ W ⇒ f(x) = 0.
5. Passage to ν'. Since W ⊆ closure W = C, M ∩ W ⊆ M ∩ C, so ν' ≤ ν (Measure.restrict_mono). By ae_mono, for ν'-a.e. x, x ∈ W ⇒ f(x) = 0. Also, by step 1, ν'-a.e. x lies in M ∩ W (ae_restrict_mem).
6. Cancelling θ. Take x in both full-measure sets of step 5.
- x ∈ W, so θ(x)·ξ(x)(α) = f(x) = 0.
- x ∈ M, so θ(x) > 0 (mult_pos), i.e. (θ(x) : ℝ) ≠ 0.
Hence ξ(x)(α) = 0. This holds for ν'-a.e. x, which is exactly ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x α = 0.

## Key steps

1. component_integrable with K = closure W makes f = θ·ξ(α) integrable, hence locally integrable on W, for ν = H^n⌞(M ∩ closure W).
2. For g ∈ C_c^∞ with tsupport g ⊆ W, ω = g·α is a test form in U supported in W, so 0 = T(ω) = ∫_M θ ξ(gα) dH^n = ∫ g f dν (g = 0 off W; setIntegral_eq_of_subset_of_forall_sdiff_eq_zero).
3. IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero on the open W gives, for ν-a.e. x, x ∈ W ⇒ f(x) = 0.
4. Restrict to ν' = H^n⌞(M ∩ W) ≤ ν (restrict_mono, ae_mono); ν'-a.e. x lies in M ∩ W (ae_restrict_mem).
5. θ > 0 on M cancels the factor θ, giving ξ(x)(α) = 0 for ν'-a.e. x.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `cat GMT/Ch07/Submission.lean (IMRep fields, IMRep.action, IMRep.Represents, MultiVector, IsUnitOrientationOf)`
- `sed -n 1,70p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean; sed -n 95,200p .../Chapter06/Currents.lean; grep -n 'VanishesOn|zeroRegion|def support' -A6 .../Chapter06/*.lean`
- `python3 -I scan of dag.json: nodes under root.minimizing_implies_stationary-a1.support_null-a1 and root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1; lean_name/status/lean_statement of imsupp_unit_orientation_ne_zero_norm_le_one, imsupp_covector_finiteDimensional, imsupp_orient_apply_ae_eq_zero_of_vanishesOn, regcomp_rim_action_integrable, rsd_cmr_ic_action_integrable`
- `git diff b4d606d 2e5d20d49a4a41f79e81db1a65e850fb919b38ba -- GMT/ (accepted proof of imsupp_unit_orientation_ne_zero_norm_le_one)`
- `python3 -I read of nodes/root-minimizing-implies-stationary-a1-support-null-a1/decomposition-v1.json (reused child entry and parent rationale)`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib; sed -n 196,215p mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `rg in local-references/123e8435b4a2469b/mathlib/Mathlib: Module.Basis.ext_alternating, toAlternatingMap_injective, of_injective, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, integrable_toReal_of_lintegral_ne_top, Integrable.mono', measurable_from_nat, image_eq_one_of_notMem_mulTSupport, tsupport_smul_subset_left, HasCompactSupport.smul_right, ae_iff, ae_all_iff, restrict_apply_univ, ae_restrict_mem, Basis.ext`
- `rg -n 'FiniteDimensional' mathlib/Mathlib/Topology/Algebra/Module/Alternating/*.lean mathlib/Mathlib/Analysis/Normed/Module/Alternating/*.lean (no match); example (P n : ℕ) : FiniteDimensional ℝ (Covector (Euclid P) n) := by infer_instance (failed to synthesize)`
- `rg -n 'FiniteDimensional|lintegral_ne_top|IntegrableOn|ae_eq_zero_of_integral' local-references/123e8435b4a2469b/project -g '*.lean' (only unrelated Ch02/Ch05/Ch06 contract lines)`
- `rg -n 'FiniteDimensional ℝ \(Covector|instance.*FiniteDimensional' lake-packages-25730c7c/simongmt/Poincare -g '*.lean' (no match)`
- `sed -n 290,310p and 755,775p book/chapter-06.txt (Simon 6.2.11, 6.3.2(3))`
- `python3 verifier/lean_contract.py validate_lean_statement on all four child types (all OK, unchanged)`
- `dag.json lean_name scan and git grep -E 'lcn_covector_finiteDimensional|lcn_mult_mul_orient_apply_integrableOn|lcn_orient_apply_ae_eq_zero_of_vanishesOn' over all 566 refs -- GMT (no match)`
- `sed -n 1380,1420p, 1790,1900p, 6490,6545p /runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/runtime.py and ensure() in store.py (depth gate, cross-branch reuse only for accepted identical types, existing node returned unchanged)`
- `lake env lean /tmp/lcn-decomp/All.lean (full proofs of the 3 new children, accepted child, parent glue; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/lcn-decomp/Check.lean (exact parent type from sorry-stubs of all four children)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1-local-carrier-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1-local-carrier-null-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/store.py`
- `/tmp/lcn-decomp/All.lean`
- `/tmp/lcn-decomp/Check.lean`
- `/tmp/lcn-decomp/Probe.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) matches the frozen Ch07 contract.

What the contract provides:
- IMRep fields used here: measurableSet_carrier, measurable_mult, mult_pos, locallyIntegrable_mult, aestronglyMeasurable_orient, orients.
- IMRep.action and IMRep.Represents.
- From SimonGMT Chapter06: Covector = E [⋀^Fin n]→L[ℝ] ℝ, IsTestForm, TestFormOn (tsupport ⊆ U) and VanishesOn.

What no local source provides:
- The snapshot project and the SimonGMT package contain no FiniteDimensional instance or lemma for Covector. infer_instance fails, and rg finds no match.
- They also contain no lemma on local integrability or a.e. vanishing of IMRep components.
These obligations therefore become new children.

Every Mathlib lemma cited in the child proofs exists at 25730c7c with the signature used:
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean:205; needs LocallyIntegrableOn on the open set and ContDiff ℝ ∞ test functions);
- Module.Basis.ext_alternating, ContinuousAlternatingMap.toAlternatingMap_injective, FiniteDimensional.of_injective;
- setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (no integrability hypothesis), integrable_toReal_of_lintegral_ne_top, Integrable.mono', measurable_from_nat;
- tsupport_smul_subset_left, HasCompactSupport.smul_right, image_eq_zero_of_notMem_tsupport;
- ae_iff, ae_all_iff, ae_restrict_mem, Measure.restrict_apply_univ, Basis.ext.

Reuse and naming (from dag.json):
- imsupp_unit_orientation_ne_zero_norm_le_one is accepted (2e5d20d) with a byte-identical type, so it is reused.
- imsupp_covector_finiteDimensional, imsupp_orient_apply_ae_eq_zero_of_vanishesOn, regcomp_rim_action_integrable and rsd_cmr_ic_action_integrable are unaccepted and owned by other parents. The runtime forbids sharing them.
- The three new lcn_* names are globally unique across the DAG and all git refs.

Kernel checks with lake env lean:
- Full proofs of all children plus the glue use only propext, Classical.choice and Quot.sound.
- The exact parent type compiles from sorry-stubs of the children.

Textual sources are Simon 6.2.11 (book/chapter-06.txt about lines 296–303) and 6.3.2(3) (about lines 763–768). Simon uses without proof that an integer multiplicity current carries no mass where it vanishes.
