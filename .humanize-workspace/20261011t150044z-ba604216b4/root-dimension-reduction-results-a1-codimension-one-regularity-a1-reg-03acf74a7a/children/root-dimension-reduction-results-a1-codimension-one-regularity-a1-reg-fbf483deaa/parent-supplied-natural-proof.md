# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1.density_trichotomy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. These are steps 5 (density points) and 6 (conclusion) of the parent-supplied proof of `codim1_rdo_dg_halfspace_rigidity`. They make rigorous Simon's “hence (9)” in Ch. 3, 4.3 (chapter-03.txt lines 664–690), with the parent's erratum: for the inward normal the limit set is {⟨z, v⟩ > c}, not {⟨z, v⟩ < c}. The hypothesis is exactly what the parent produces in its step 4; no unit-length assumption on v is needed.

Notation.
- E := ℝⁿ, L := Lⁿ; B̄_r(x) is the closed ball.
- θ_r(x) := L(F ∩ B̄_r(x)) / L(B̄_r(x)) ∈ [0, ∞], with division in [0, ∞].
- “r ↓ 0” is the filter 𝓝[>] 0 on ℝ, which is nontrivial.
- A₁ := {x : θ_r(x) → 1 as r ↓ 0} and A₀ := {x : θ_r(x) → 0 as r ↓ 0}.

1. Density points are ordered: if z₁ ∈ A₁ and z₀ ∈ A₀, then ⟨z₀, v⟩ < ⟨z₁, v⟩.
   (a) Suppose instead ⟨z₀, v⟩ ≥ ⟨z₁, v⟩ and put a := z₀ − z₁. Then ⟨a, v⟩ ≥ 0, so by hypothesis N_a := {z : z ∈ F and z + a ∉ F} is L-null.
   (b) For every r ∈ ℝ and z: ‖z − z₁‖ ≤ r ⟺ ‖(z + a) − z₀‖ ≤ r, since (z + a) − z₀ = z − z₁. Hence
       B̄_r(z₁) = (· + a)⁻¹(B̄_r(z₀)) and {z : z + a ∈ F} ∩ B̄_r(z₁) = (· + a)⁻¹(F ∩ B̄_r(z₀)).
       Lebesgue measure is translation invariant for arbitrary sets (Mathlib `measure_preimage_add_right`), so L(B̄_r(z₁)) = L(B̄_r(z₀)) and L({z : z + a ∈ F} ∩ B̄_r(z₁)) = L(F ∩ B̄_r(z₀)).
   (c) F ∩ B̄_r(z₁) ⊆ ({z : z + a ∈ F} ∩ B̄_r(z₁)) ∪ N_a. By monotonicity and subadditivity,
       L(F ∩ B̄_r(z₁)) ≤ L(F ∩ B̄_r(z₀)) + L(N_a) = L(F ∩ B̄_r(z₀)).
   (d) Divide by the common denominator L(B̄_r(z₁)) = L(B̄_r(z₀)). Division in [0, ∞] is monotone in the numerator (Mathlib `ENNReal.div_le_div_right`), so θ_r(z₁) ≤ θ_r(z₀) for every r ∈ ℝ.
   (e) Let r ↓ 0 and use the two limits (Mathlib `le_of_tendsto_of_tendsto'`). This yields 1 ≤ 0 in [0, ∞], a contradiction. So ⟨z₀, v⟩ < ⟨z₁, v⟩.

2. Lebesgue density theorem.
   - F is Borel and L is locally finite on ℝⁿ. By Mathlib `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`, θ_r(x) → 1_F(x) as r ↓ 0 for every x outside an L-null set N.
   - If x ∈ F and x ∉ N, the limit is 1, so x ∈ A₁.
   - If x ∉ F and x ∉ N, the limit is 0, so x ∈ A₀.
   - Thus F ∖ A₁ ⊆ N and (ℝⁿ ∖ F) ∖ A₀ ⊆ N.

3. Trivial cases.
   - If A₁ = ∅, then F ⊆ N, so L(F) = 0 (first alternative).
   - If A₀ = ∅, then ℝⁿ ∖ F ⊆ N, so L(ℝⁿ ∖ F) = 0 (second alternative).

4. The threshold c. Assume A₁ ≠ ∅ and A₀ ≠ ∅, and fix z₁* ∈ A₁ and z₀* ∈ A₀.
   - By step 1, ⟨z₀*, v⟩ < ⟨z₁*, v⟩; in particular v ≠ 0 (otherwise both sides are 0).
   - The set S := {⟨z₀, v⟩ : z₀ ∈ A₀} ⊆ ℝ is nonempty and, by step 1, bounded above by ⟨z₁*, v⟩. So c := sup S is a real number.
   - For every z₀ ∈ A₀, ⟨z₀, v⟩ ≤ c (Mathlib `le_csSup`).
   - For every z₁ ∈ A₁, ⟨z₁, v⟩ is an upper bound of S by step 1, hence c ≤ ⟨z₁, v⟩ (Mathlib `csSup_le`).

5. The symmetric difference. Let H := {z : c < ⟨z, v⟩} and P := {z : ⟨z, v⟩ = c}.
   (a) F ∖ H ⊆ N ∪ P. Let z ∈ F with ⟨z, v⟩ ≤ c and z ∉ N. By step 2, z ∈ A₁, so c ≤ ⟨z, v⟩ by step 4. Hence ⟨z, v⟩ = c and z ∈ P.
   (b) H ∖ F ⊆ N. Let z ∉ F with c < ⟨z, v⟩. If z ∉ N, then step 2 gives z ∈ A₀ and step 4 gives ⟨z, v⟩ ≤ c, a contradiction. Hence z ∈ N.
   Therefore F Δ H = (F ∖ H) ∪ (H ∖ F) ⊆ N ∪ P.

6. The hyperplane is null.
   - Since v ≠ 0, P = p + ker⟨·, v⟩ with p := (c/‖v‖²) v (so ⟨p, v⟩ = c) is an affine subspace of ℝⁿ (Mathlib `AffineSubspace.mk' p (ker ⟨·, v⟩)`, membership by `AffineSubspace.mem_mk'`).
   - P ≠ ℝⁿ, because p + v ∉ P: ⟨p + v, v⟩ = c + ‖v‖² ≠ c.
   - A proper affine subspace of ℝⁿ is null for the add-Haar measure L (Mathlib `MeasureTheory.Measure.addHaar_affineSubspace`), so L(P) = 0.

7. Conclusion. L(F Δ H) ≤ L(N) + L(P) = 0, which is the third alternative with this c. Together with step 3, one of the three alternatives always holds. ∎

## Key steps

1. Ordering: if z₁ has F-density 1 and z₀ has F-density 0, then ⟨z₀,v⟩ < ⟨z₁,v⟩; otherwise translating by a = z₀ − z₁ gives θ_r(z₁) ≤ θ_r(z₀) for all r, hence 1 ≤ 0.
2. Lebesgue density theorem: F ∖ A₁ and Fᶜ ∖ A₀ lie in one null set N.
3. A₁ = ∅ ⇒ L(F) = 0; A₀ = ∅ ⇒ L(Fᶜ) = 0.
4. Otherwise c := sup{⟨z₀,v⟩ : z₀ ∈ A₀} is finite, ⟨z₀,v⟩ ≤ c ≤ ⟨z₁,v⟩ for z₀ ∈ A₀, z₁ ∈ A₁, and v ≠ 0.
5. F Δ {⟨z,v⟩ > c} ⊆ N ∪ {⟨z,v⟩ = c}, and that proper hyperplane is Lebesgue-null.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sha256sum of snapshot vs .lake/packages/mathlib for AEEqOfIntegralContDiff.lean, AEEqOfIntegral.lean, Besicovitch.lean, EqHaar.lean, PartitionOfUnity.lean, Integral/Prod.lean, FDeriv/Const.lean (all SAME)`
- `rg -n "theorem ae_eq_of_integral_contDiff_smul_eq|theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem ae_nonneg_of_forall_setIntegral_nonneg|theorem ae_le_of_forall_setIntegral_le|theorem ae_nonneg_of_forall_setIntegral_nonneg_of|theorem ae_eq_zero_of_forall_setIntegral_isCompact|isCompact.*nonneg|theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg" mathlib/Mathlib`
- `sed -n 60,215p mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean; sed -n 120,215p and 340,430p mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `rg -n --glob '*.lean' "theorem .*(halfspace|half_space|halfSpace)" project mathlib/Mathlib/Analysis mathlib/Mathlib/MeasureTheory`
- `rg -n --glob '*.lean' "theorem .*(ae_nonneg_of_integral|integral_contDiff.*nonneg|nonneg_of_integral_contDiff|ae_translate|translate_invariant|ae_add_right_invariant)" project mathlib/Mathlib (no match)`
- `rg -n --glob '*.lean' "theorem .*(halfspace|half_space|translat|ae_nonneg|density_point|lebesgue_density|integral_contDiff)" lake-packages-25730c7c/simongmt (no match)`
- `rg -n "theorem ae_tendsto_measure_inter_div_of_measurableSet|theorem addHaar_affineSubspace|intervalIntegral_integral_swap|theorem exists_contMDiff_support_eq_eq_one_iff|theorem support_fderiv_subset" mathlib/Mathlib`
- `python3 scans of dag.json: status counts (1010 nodes), lean_name hits for the five codim1_rdo_dg_hr_* names (none), identical frozen types (none), similar statements (fderiv+HasCompactSupport+∀ᵐ, symmDiff, 0 ≤ ∫+ContDiff); scan of 925 nodes/*/decomposition-v*.json and decomposition-review-retry.json for the names (only this node's never-activated decomposition-v1.json)`
- `cat nodes/<this node>/{decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json,decomposition-scope-v1.json,parent-child-handoff.json}`
- `sed -n 1000,1100p, 1388,1640p, 1800,1990p, 2760,2900p, 6532,6590p runtime.py (_decompose, _solve_children node bound, _install_speculative_assumptions, _existing_lean_name_problem); grep 'Unknown identifier .Euclid' nodes/*/speculative-process-v*.log`
- `sed -n 655,692p book/chapter-03.txt (Simon Ch. 3, 4.3 (7)-(9))`
- `lake env lean -DautoImplicit=false /tmp/hr-split-v2/Types.lean (5 child types + parent frozen type proved from them; #print axioms)`
- `lake env lean /tmp/hr-split-v2/Stub.lean and /tmp/hr-split-v2/StubAssembly.lean (replica of controller speculative stub; parent proved against stub axioms)`
- `lake env lean /tmp/hr-split-v2/{Parse,Avail,Avail2,Avail3,Inst}.lean (rfl parse checks; availability of every cited lemma; ContDiffBump.normed and ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable unknown; instances for general n)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-03acf74a7a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-03acf74a7a/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-03acf74a7a/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/speculative-process-v1.log`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt`
- `/tmp/hr-split-v2/Types.lean`
- `/tmp/hr-split-v2/Stub.lean`
- `/tmp/hr-split-v2/StubAssembly.lean`
- `/tmp/hr-split-v2/Parse.lean`
- `/tmp/hr-split-v2/Avail.lean`
- `/tmp/hr-split-v2/Avail2.lean`
- `/tmp/hr-split-v2/Avail3.lean`
- `/tmp/hr-split-v2/Inst.lean`

Pins and identity checks:
- Snapshot manifest: project b4d606db, Mathlib 25730c7c. Both match the workspace HEAD and .lake/packages/mathlib. SimonGMT is pinned at 2b366308.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
- Every cited Mathlib file in the snapshot is byte-identical to the workspace package.

Library results used by the children:
- Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet (Besicovitch.lean:1089)
- Measure.addHaar_affineSubspace (EqHaar.lean:199)
- exists_contMDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:755)
- intervalIntegral_integral_swap (Integral/Prod.lean:483)
- support_fderiv_subset (FDeriv/Const.lean:379)
- ae_eq_of_integral_contDiff_smul_eq (AEEqOfIntegralContDiff.lean:195)
- MeasurableSet.exists_lt_isCompact_of_ne_top, integral_pos_iff_support_of_nonneg, measure_preimage_add_right, integral_add_right_eq_self

What is missing:
- There is no nonnegative-test version of the fundamental lemma. AEEqOfIntegral.lean:130 requires global integrability.
- No translation identity, half-space rigidity or density-trichotomy lemma exists in Mathlib, the project or SimonGMT (rg found no match).
- ContDiffBump.normed and the mollifier convergence lemma are not in the import closure of GMT.Ch07.Submission.

Lean checks:
- All 5 child types elaborate after `import GMT.Ch07.Submission`, both in GMT.Ch07 scope and in the replicated speculative stub (root namespace Submission, regex-selected opens).
- Children use EuclideanSpace ℝ (Fin n) because speculative logs show `Euclid` failing in the stub.
- The parent's exact frozen type is proved from the children, with step 4 formalized. #print axioms gives propext, sorryAx, Classical.choice, Quot.sound; against stub axioms it gives only those three plus the three consumer-child axioms.

Names and reuse:
- The five codim1_rdo_dg_hr_* names occur in no DAG node (1010 nodes). The only file containing them is this node's never-activated decomposition-v1.json, which carries the identical audited split.
- No accepted node has an identical frozen type, so nothing is reused.

Source: the printed Simon Ch. 3, 4.3 (8)–(9) text is confirmed at chapter-03.txt lines 664–690.
