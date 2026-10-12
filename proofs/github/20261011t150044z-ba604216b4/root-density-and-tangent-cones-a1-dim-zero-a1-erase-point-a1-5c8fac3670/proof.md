# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.dim_zero-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.dim_zero-a1.erase_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof ("R_S := (M ∖ {p}, θ, ξ) is an IMRep in U representing S: M ∖ {p} is Borel, ⊆ U and countably 0-rectifiable (subset of M); measurability, positivity and local integrability are inherited from R; orientation: …; representation: S(ω) = ∫_M θξ(ω) dH⁰ − θ(p)ξ(p)(ω(p))·H⁰({p}) = ∫_{M∖{p}} θξ(ω) dH⁰"), together with the measure computation μ_R = μ_{R_S} + θ(p)H⁰⌞{p} used in steps 4 and 8, with the details supplied.

Uses the siblings carrier_finite (Submission.dtc_dim_zero_carrier_finite) and tangent_delete_point (Submission.dtc_approxTangent_sdiff_singleton).

Notation: M := R.carrier, θ := R.mult, ξ := R.orient, M' := M ∖ {p}, H⁰ := μHE[0]. Recall that H⁰{y} = 1 for every y: μHE[0] = μH[0] (Mathlib Measure.euclideanHausdorffMeasure_zero) and μH[0]{y} = 1 (Measure.hausdorffMeasure_zero_singleton).

1. Construction of R'. Let R' have carrier M', mult θ and orient ξ. We verify the fields of IMRep U 0.
   (a) measurableSet_carrier: M' = M ∖ {p} is Borel, because M is Borel and {p} is closed.
   (b) carrier_subset: M' ⊆ M ⊆ U.
   (c) rectifiable: CountablyRectifiable 0 M' follows from CountablyRectifiable 0 M (a field of R) and M' ⊆ M, by CountablyRectifiable.mono.
   (d) measurable_mult: θ is measurable (a field of R).
   (e) mult_pos: if x ∈ M' then x ∈ M, so 0 < θ(x).
   (f) locallyIntegrable_mult: for compact K ⊆ U we have M' ∩ K ⊆ M ∩ K. So ∫⁻_{M'∩K} θ dH⁰ ≤ ∫⁻_{M∩K} θ dH⁰ < ∞ by monotonicity of the lower integral in the domain (lintegral_mono_set).
   (g) aestronglyMeasurable_orient: H⁰⌞M' ≤ H⁰⌞M (Measure.restrict_mono). So a.e.-strong measurability of ξ for H⁰⌞M (a field of R) gives it for H⁰⌞M'.
   (h) orients:
       - The field orients of R says: for H⁰⌞M-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt 0 M x Q and IsUnitOrientationOf (ξ x) Q.
       - Since M' ⊆ M, the same property holds for H⁰⌞M'-a.e. x (ae_restrict_of_ae_restrict_of_subset).
       - Since M' is measurable, H⁰⌞M'-a.e. x lies in M' (ae_restrict_mem).
       - Take x satisfying both. Then x ≠ p. Apply tangent_delete_point with n = 0, the Borel set M, base point x and deleted point p. It turns HasApproximateTangentSpaceAt 0 M x Q into HasApproximateTangentSpaceAt 0 M' x Q.
       - IsUnitOrientationOf (ξ x) Q is unchanged. Hence R' satisfies orients.
   By construction R'.carrier = M ∖ {p}, R'.mult = θ and R'.orient = ξ.
2. Measure identity.
   - Since p ∈ M, we have M = M' ∪ {p}, the two pieces are disjoint, and {p} is measurable. So H⁰⌞M = H⁰⌞M' + H⁰⌞{p} (Measure.restrict_union).
   - H⁰⌞{p} = H⁰{p}·δ_p = δ_p, by Measure.restrict_singleton and H⁰{p} = 1.
   - The density construction is additive in the measure (withDensity_add_measure). Also δ_p.withDensity θ = θ(p)·δ_p, because singletons are measurable (dirac_withDensity).
   - Therefore R.measure = (H⁰⌞M).withDensity θ = (H⁰⌞M').withDensity θ + θ(p)·δ_p = R'.measure + θ(p)·δ_p.
3. Action identity. Fix ω ∈ 𝒟⁰(U) (ω : TestFormOn U 0) and set g(x) := θ(x)·ξ(x)(ω(x)) ∈ ℝ. Then R.action ω = ∫_M g dH⁰ and R'.action ω = ∫_{M'} g dH⁰.
   (a) K := tsupport ω is compact, because ω has compact support, and K ⊆ U, because ω is a test form on U. By carrier_finite, M ∩ K is finite.
   (b) For every y, g is integrable on {y} with respect to H⁰, because H⁰{y} = 1 < ∞ and g(y) is a real number (integrableOn_singleton).
   (c) M ∩ K = ⋃_{y ∈ M∩K} {y} is a finite union, so g is integrable on M ∩ K (integrableOn_finite_biUnion together with (a) and (b)).
   (d) Let x ∈ M ∖ (M ∩ K). Then x ∉ tsupport ω, so ω(x) = 0, ξ(x)(0) = 0 by linearity, and g(x) = 0. Since M is measurable and g vanishes on M ∖ (M ∩ K), g is integrable on M (IntegrableOn.of_forall_sdiff_eq_zero), hence also on M' ⊆ M.
   (e) M = M' ∪ {p} disjointly, {p} is measurable, and g is integrable on M' and on {p}.
       - So ∫_M g dH⁰ = ∫_{M'} g dH⁰ + ∫_{{p}} g dH⁰ (setIntegral_union).
       - ∫_{{p}} g dH⁰ = H⁰{p}·g(p) = g(p) (integral_singleton).
       - Hence R.action ω = R'.action ω + θ(p)·ξ(p)(ω(p)).
   Together with steps 1 and 2, this proves the claim.

## Key steps

1. R' := (M ∖ {p}, θ, ξ) satisfies every IMRep field. The orients field uses tangent_delete_point at the a.e. points x ∈ M ∖ {p}, all of which differ from p.
2. H⁰⌞M = H⁰⌞(M ∖ {p}) + δ_p because H⁰{p} = 1, so μ_R = μ_{R'} + θ(p)δ_p by additivity of withDensity and dirac_withDensity.
3. g = θ·ξ(ω) is integrable on M, because M ∩ tsupport ω is finite (carrier_finite) and g vanishes off tsupport ω.
4. Splitting the integral over M = (M ∖ {p}) ∪ {p} gives τ_R(ω) = τ_{R'}(ω) + θ(p)ξ(p)(ω(p)).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (both identical; snapshot project b4d606d, mathlib 25730c7c)`
- `rg -n 'structure GeometricCurrentOn|GeometricCurrentOn.ext|instance .*Zero|zero_apply|TestFormOnConverges|abbrev TestFormOn' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `rg -n 'GeometricCurrentOn.VanishesOn|GeometricCurrentOn.zeroRegion|GeometricCurrentOn.support|restrictDomain' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `rg -n 'massAdmissibleOn|GeometricCurrentOn.massOn|le_massOn|covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `rg -n 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `rg -n 'pointCurrent|Dirac' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `rg -n 'def CountablyRectifiable|CountablyRectifiable.mono|def blowUpMap|def HasApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'euclideanHausdorffMeasure_zero' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n 'hausdorffMeasure_zero_singleton' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'sum_measure_singleton|Infinite.exists_subset_card_eq|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|IntegrableOn.of_forall_sdiff_eq_zero|integrableOn_singleton_iff|integrableOn_finite_biUnion|theorem setIntegral_union|theorem integral_singleton|theorem restrict_singleton|theorem restrict_union|dirac_withDensity|withDensity_add_measure|iteratedFDeriv_zero_eq_comp|TendstoUniformlyOn.tendsto_at|set_biUnion_coe' mathlib/Mathlib`
- `lean_name inventory: rg over runs/20261011T150044Z-ba604216b4 (dag.json, all node JSON/markdown), GMT/Ch07/Submission.lean and git log --all -S for dtc_dim_zero_carrier_finite, dtc_approxTangent_sdiff_singleton, dtc_dim_zero_erase_point, dtc_point_current (no match)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the four child types`
- `lake build GMT.Ch07.Submission in /tmp/dz-decomp-7f3a/proj; lake env lean Check/Assembly.lean, Check/ChildA.lean, Check/ChildB.lean, Check/ChildC.lean, Check/ChildD.lean, Check/All.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-zero-dim-minimizing-trivial-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-finite-of-dim-zero-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Dirac/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dz-decomp-7f3a/proj/Check/Assembly.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/ChildA.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/ChildB.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/ChildC.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/ChildD.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/All.lean`
- `/tmp/dz-decomp-7f3a/scripts/stmts.py`

The snapshot contract and submission (project b4d606d, mathlib 25730c7c) are byte-identical to the workspace copies.

The frozen objects the children use come from SimonGMT:
- GeometricCurrentOn, its ext and Zero instance, and TestFormOnConverges (Chapter06/Currents.lean).
- VanishesOn, zeroRegion and support (Chapter06/CurrentLocalEquality.lean).
- massAdmissibleOn and massOn (Chapter06/Mass.lean).
- CountablyRectifiable.mono, blowUpMap and HasApproximateTangentSpaceAt (Chapter03/Rectifiable.lean).

The library's only point current is the algebraic whole-space degree-0 `pointCurrent` in Chapter06/Product.lean. It has no domain, continuity or support lemma, so the child dtc_point_current is needed.

The library has no lemma on deleting a point from a carrier, on 0-dimensional local finiteness, or on locality of approximate tangent spaces under point deletion. These are the remaining three children.

Mathlib supplies the required facts: μHE[0] = μH[0] with μH[0]{x} = 1, sum_measure_singleton, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, IntegrableOn.of_forall_sdiff_eq_zero, integrableOn_singleton(_iff), integrableOn_finite_biUnion, setIntegral_union, integral_singleton, Measure.restrict_union, Measure.restrict_singleton, withDensity_add_measure, dirac_withDensity, and iteratedFDeriv_zero_eq_comp. Set.diff_subset is deprecated in favour of sdiff_subset.

Verification results:
- All four child types elaborate in the comparator scope and pass validate_lean_statement.
- All four children were proved in the scratch project using only propext, Classical.choice and Quot.sound.
- The parent's frozen type is proved from the exact child strings plus the stubbed resolved sibling dtc_mass_eq_measure.
- None of the four names occurs anywhere else in the run or in the repository.
