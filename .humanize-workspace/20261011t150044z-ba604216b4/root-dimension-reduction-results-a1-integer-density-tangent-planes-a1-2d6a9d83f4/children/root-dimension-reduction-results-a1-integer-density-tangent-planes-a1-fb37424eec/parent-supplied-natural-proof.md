# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.sector_open_smooth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ⟨·,·⟩ is the inner product of ℝ^P = Euclid P; π := Q.starProjection is the orthogonal projection onto Q, a continuous linear map (Q is finite-dimensional, hence closed). Ω := {x : 0 < ⟨x,a⟩}; q(x) := ⟨x,e⟩/⟨x,a⟩ (real division, t/0 = 0); f := arctan ∘ q; F̃ := (|·|, f) : ℝ^P → ℝ × ℝ; Z_s := {x : 0 < ⟨x,a⟩ ∧ ||x| − 1| < s ∧ |f(x)| < s ∧ |x − πx| < s|x|}. No hypothesis on Q, a, e, s is needed.
1. (Ω is open.) Ω is the set where the continuous function x ↦ ⟨x,a⟩ is strictly greater than the constant 0, hence open (`isOpen_lt continuous_const (continuous_id.inner continuous_const)`).
2. (Points of Ω.) Every x ∈ Ω satisfies ⟨x,a⟩ ≠ 0, and x ≠ 0 because ⟨0,a⟩ = 0.
3. (f is C¹ on Ω.) Fix x ∈ Ω. The maps y ↦ ⟨y,e⟩ and y ↦ ⟨y,a⟩ are continuous linear, hence C^∞ (`ContDiff.inner ℝ contDiff_id contDiff_const`). Their quotient q is C^∞ at x because the denominator ⟨x,a⟩ is nonzero (step 2; `ContDiffAt.div`). Real.arctan is C^∞ on ℝ (`Real.contDiff_arctan`), so f = arctan ∘ q is C^∞, in particular C¹, at x, hence C¹ within Ω at x. Since x ∈ Ω was arbitrary, f is ContDiffOn ℝ 1 on Ω; in particular f is continuous on Ω.
4. (F̃ is C¹ on Ω.) Fix x ∈ Ω. The norm of a real inner product space is C^∞ at every nonzero point (`contDiffAt_norm ℝ`), and x ≠ 0 by step 2, so |·| is C¹ at x and hence within Ω at x. Together with step 3, the pair F̃ = (|·|, f) is C¹ within Ω at x (`ContDiffWithinAt.prodMk`). Hence ContDiffOn ℝ 1 F̃ Ω, which is the second conjunct.
5. (Z_s is open.) Let B := Ω ∩ {x : |f(x)| < s}. The function x ↦ |f(x)| is continuous on Ω (step 3), Ω is open (step 1) and (−∞, s) is open, so B = Ω ∩ (|f|)⁻¹((−∞, s)) is open (`ContinuousOn.isOpen_inter_preimage`). The sets A₁ := {x : ||x| − 1| < s} and A₃ := {x : |x − πx| < s|x|} are open, each being the set where one continuous function on ℝ^P is strictly smaller than another (`isOpen_lt`; |·| and π are continuous). Unfolding the definitions, x ∈ Z_s iff (0 < ⟨x,a⟩ and |f(x)| < s) and ||x| − 1| < s and |x − πx| < s|x|, i.e. Z_s = B ∩ A₁ ∩ A₃. A finite intersection of open sets is open, so Z_s is open (if s ≤ 0 it is empty, which is consistent). This is the first conjunct. ∎

## Key steps

1. Ω = {⟨x,a⟩ > 0} is open and its points are nonzero with ⟨x,a⟩ ≠ 0.
2. arctan(⟨x,e⟩/⟨x,a⟩) is C¹ (hence continuous) on Ω: quotient of linear maps with nonvanishing denominator composed with the smooth arctan.
3. |·| is C^∞ away from 0, so F̃ = (|·|, f) is ContDiffOn ℝ 1 on Ω.
4. Z_s = (Ω ∩ |f|⁻¹(−∞,s)) ∩ {||x|−1| < s} ∩ {|x−πx| < s|x|} is a finite intersection of open sets (ContinuousOn.isOpen_inter_preimage, isOpen_lt).

## Reference use

### local-project

Queries:
- `python3 over dag.json nodes (lean_name/lean_statement/status): idtp_cse_fibre_area_identities and its siblings; idtp_carrier_area_formula (speculative-ready); accepted imrep_approxTangent_starProjection_aesm, dorag_aa_ae_finrank_approxTangentPlane, cbr_imRep_measure_basic, dpf_det_gram_stdOrthonormalBasis_eq, dpf_aestronglyMeasurable_gramJacobian; cousin idtp_cse_rc_angle_fderiv; statements containing 'finrank ℝ (approxTangentPlane', 'stdOrthonormalBasis', '!₂[' or ℝ × ℝ with fderiv`
- `grep -c idtp_cse_fa_ dag.json (0); rg -l idtp_cse_fa_ nodes/ dag.json local-references/123e8435b4a2469b/project (no match); for f in .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean: grep -l idtp_cse_fa_ (no match)`
- `git show db9124843c:GMT/Ch07/Submission.lean | grep dorag_aa_ae_finrank_approxTangentPlane (accepted lemmas are delivered as `theorem Submission.X` in namespace GMT.Ch07)`
- `grep -n 'HasApproximateTangentSpaceAt.finrank_eq|HasApproximateTangentSpaceAt.unique|def CountablyRectifiable|def HasApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn '!₂\[|volume_preserving_toLp|volume_preserving_ofLp|volume_preserving_finTwoArrow' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg 'setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable|restrict_withDensity|lintegral_withDensity_eq_lintegral_mul_non_measurable|apply_continuousLinearMap|ContinuousOn.isOpen_inter_preimage|contDiffAt_norm|hasStrictFDerivAt_norm_sq|HasFDerivAt.sqrt|HasFDerivAt.arctan|HasFDerivAt.prodMk|comp_fderiv|lintegral_comp_emb|aemeasurable_comp_iff|det_fin_two|det_reindex_self|sum_inner_mul_inner|sum_repr|starProjection_eq_self_iff|HasFDerivAt.div' .lake/packages/mathlib/Mathlib (same rev 25730c7c as the snapshot; no fderiv-form real quotient rule exists at this pin)`
- `lake env lean /tmp/fa-decomp-7c1e/check/{Stmts,Parent,C1,C3,Deriv}.lean and /tmp/fa-decomp-7c1e/verify/C2.lean (+ #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2d6a9d83f4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2d6a9d83f4/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-18ac87081c/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/tmp/fa-decomp-7c1e/check/Stmts.lean`
- `/tmp/fa-decomp-7c1e/check/Parent.lean`
- `/tmp/fa-decomp-7c1e/check/C1.lean`
- `/tmp/fa-decomp-7c1e/check/C3.lean`
- `/tmp/fa-decomp-7c1e/check/Deriv.lean`
- `/tmp/fa-decomp-7c1e/verify/C2.lean`
- `/tmp/fa-decomp-7c1e/scripts/jac_check.py`

The pins match. The workspace Submission.lean (GMT.Ch07 namespace, frozen opens) is the compiler authority; mathlib is 25730c7c, equal to the snapshot's mathlib_commit, and SimonGMT is 2b36630.

Reusable results already in the DAG:
- Accepted: dorag_aa_ae_finrank_approxTangentPlane (R.measure-a.e. finrank T_x = n), cbr_imRep_measure_basic (μHE⌞carrier ≪ R.measure) and imrep_approxTangent_starProjection_aesm. These replace the parent's direct use of the orients field and HasApproximateTangentSpaceAt.finrank_eq.
- Pending: idtp_carrier_area_formula (speculative-ready), which child 3 uses.
- Not reusable: dpf_det_gram_stdOrthonormalBasis_eq applies only to L : Euclid P →L Euclid P. No existing node gives the area formula into ℝ × ℝ or the polar-map Jacobian. The cousin idtp_cse_rc_angle_fderiv is still pending.

All Mathlib names cited in the child proofs exist at the pin. The proofs avoid the missing fderiv-form quotient rule by using the inverse and product rules.

The proposed idtp_cse_fa_* names are unreserved. All four types elaborate. The parent is kernel-checked from the three child types plus the accepted-lemma types, with standard axioms only. Children 1 and 2 are fully proved, and child 3 is proved relative to the carrier-area-formula type.
