# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.image_tangent-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.image_tangent-a1.c1_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the standard cut-off step that lets the reused sibling codim1_rdo_c1_piece_approxTangent, which assumes a globally C¹ map, be applied to the map χ of the selected node. That map is only C¹ on the open set V. In the supplied proof (steps 2 and 4) only the values of χ on a small ball B_δ(y) ⊆ int C ⊆ V are used.
Notation: B_ρ(y) and B̄_ρ(y) are the open and closed balls; tsupport φ is the closure of {φ ≠ 0}.

1. (A ball inside W.) W is open and y ∈ W, so choose ρ > 0 with B_ρ(y) ⊆ W.

2. (Bump function.) ℝ^k = EuclideanSpace ℝ (Fin k) is a finite-dimensional inner product space, so smooth bump functions exist (Mathlib ContDiffBump, instance hasContDiffBump_of_innerProductSpace). Let φ : ℝ^k → ℝ be the bump function centred at y with inner radius ρ/4 and outer radius ρ/2; note 0 < ρ/4 < ρ/2.
- φ is C^∞ (ContDiffBump.contDiff).
- φ(x) = 1 for every x ∈ B̄_{ρ/4}(y) (ContDiffBump.one_of_mem_closedBall).
- tsupport φ = B̄_{ρ/2}(y) (ContDiffBump.tsupport_eq), which lies in B_ρ(y) ⊆ W.

3. (Definition of g and ε.) Put g(x) := φ(x)·χ(x) for x ∈ ℝ^k and ε := ρ/4 > 0.
- B_ε(y) ⊆ B_ρ(y) ⊆ W.
- For x ∈ B_ε(y) ⊆ B̄_{ρ/4}(y), φ(x) = 1, so g(x) = χ(x).
Thus g = χ on B_ε(y).

4. (g is C¹ at points of W.) Let x ∈ W. W is open, so it is a neighbourhood of x on which χ is C¹; hence χ is C¹ at x (ContDiffOn.contDiffAt). φ is C^∞, in particular C¹, at x. A product of a C¹ scalar function and a C¹ vector-valued function is C¹ (ContDiffAt.smul), so g is C¹ at x.

5. (g is C¹ at points outside W.) Let x ∉ W.
- x ∉ tsupport φ, because tsupport φ ⊆ W by step 2.
- The complement of the closed set tsupport φ is an open neighbourhood of x on which φ = 0 (image_eq_zero_of_notMem_tsupport). So g = 0·χ = 0 on that neighbourhood.
- The constant map 0 is C¹, and being C¹ at a point depends only on the germ there (ContDiffAt.congr_of_eventuallyEq). Hence g is C¹ at x.

6. (Conclusion.) By steps 4 and 5, g is C¹ at every point of ℝ^k, hence C¹ on ℝ^k (contDiff_iff_contDiffAt). Together with step 3, g and ε have all the required properties. (The argument is uniform in k, including k = 0.) ∎

## Key steps

1. Choose ρ > 0 with B_ρ(y) ⊆ W.
2. Take a smooth bump φ centred at y that equals 1 on B̄_{ρ/4}(y) and has tsupport φ = B̄_{ρ/2}(y) ⊆ W.
3. Set g := φ·χ and ε := ρ/4. Then B_ε(y) ⊆ W and g = χ on B_ε(y).
4. On W, g is a product of a C^∞ and a C¹ function, so it is C¹. Off W, g vanishes near the point, so it is C¹ there too. Hence g is C¹ on ℝ^k.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I scans of dag.json: accepted nodes whose lean_statement mentions HasApproximateTangentSpaceAt (once or twice), blowUpMap, areaJacobianAt, fderiv/ContDiff, '‖a - b‖ ≤ ‖', EqOn, Antilipschitz; status/candidate_commit of codim1_rdo_c1_piece_approxTangent, codim1_rdo_c1cov_local_lower_lipschitz, codim1_ac_sat_c1_local_extension (decomposing, not reusable), dtc_bc_lc_sl_c1_tangent (decomposing); nodes whose children lie outside their own subtree (65 accepted parents)`
- `python3 -I exact-type and collision check: DAG lean_statement == proposed lean_statement for the two reused names (True, accepted, candidate present); dor_lmbsf_cit_c1_local_extension and dor_lmbsf_cit_approxTangent_of_subset: 0 DAG matches`
- `git show 9ff76906722dcb8bcc007644718f45ab2b7ad407:GMT/Ch07/Submission.lean; git show 12e74edc2f87670883f4d67e2d52fc0830d265e7:GMT/Ch07/Submission.lean (accepted proofs, contract imports only); git log --all --oneline -S dor_lmbsf_cit (no match)`
- `rg -n 'theorem one_of_mem_closedBall|theorem tsupport_eq|protected theorem contDiff ' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n ContDiffBump mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `rg -n 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean; rg -n 'theorem Filter.EventuallyEq.fderiv_eq' mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean; rg -n 'theorem subset_image_sdiff' mathlib/Mathlib/Data/Set/Image.lean`
- `rg -n 'injective_iff_antilipschitz|theorem HasStrictFDerivAt.approximates_deriv_on_nhds|theorem approximates_deriv_on_nhds|theorem contDiff_iff_contDiffAt|theorem ContDiffAt.congr_of_eventuallyEq|image_eq_one_of_notMem_mulTSupport' mathlib/Mathlib`
- `rg -n 'theorem euclideanHausdorffMeasure_zero|theorem hausdorffMeasure_zero_singleton|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib`
- `rg -n 'HasApproximateTangentSpaceAt|blowUpMap' project/GMT/Ch07/Contract.lean; rg -n 'dor_lmbsf_cit|c1_local_extension|approxTangent_of_subset' project mathlib (no match)`
- `grep -n 'def HasApproximateTangentSpaceAt|def blowUpMap' simongmt Chapter03/Rectifiable.lean; grep -n 'integral_area_formula_of_injective_derivative' simongmt Chapter02/WeightedArea.lean; grep -n 'def areaJacobianAt' simongmt Chapter02/Area.lean`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|An accepted theorem may be reused|max_depth' /runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/runtime.py`
- `python3 -I gmt-compare.contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') (replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end); lean_contract.validate_lean_statement on the four child types`
- `lake env lean -DautoImplicit=false /tmp/dor-cit-decomp/Types.lean; /tmp/dor-cit-decomp/Assembly.lean (#print axioms DorCit.parent_from_children, ext_proof, loc_proof); /tmp/dor-cit-decomp/Combined.lean (#print axioms Submission.dor_lmbsf_c1_image_approxTangent)`
- `sed -n 95,128p book/chapter-03.txt; grep -n '1.6 Theorem|Proof of 1.6|C 1 submanifold' book/chapter-03.txt; grep -n 'Area Formula|3.1 |3.2 |3.5 ' book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-a0846a5122/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-18e8208cd7/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ec0e4b9204/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f448992aee/decomposition-v1.json`
- `/runtime/flows/gmt-claude-15bd82d86f30/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/dor-cit-decomp/Types.lean`
- `/tmp/dor-cit-decomp/Assembly.lean`
- `/tmp/dor-cit-decomp/Combined.lean`

Pins: the snapshot (project b4d606db, Mathlib 25730c7c) matches the workspace. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical.

Definitions: SimonGMT Chapter03.HasApproximateTangentSpaceAt is finrank P = n plus convergence of ∫_{blowUpMap x r '' M} f dμHE[n] along 𝓝[>] 0 for every C_c test function. The area formula is SimonGMT Chapter02.integral_area_formula_of_injective_derivative.

Reusable accepted declarations (status accepted, candidate commit present, DAG lean_statement byte-identical to the proposed one):
- codim1_rdo_c1_piece_approxTangent (9ff76906): approximate tangent space of g(B_r(c)) for a globally C¹ g with a lower Lipschitz bound. This covers supplied steps 0–2 and 4–6.
- codim1_rdo_c1cov_local_lower_lipschitz (12e74edc): supplied step 2.
Both proofs use only the contract imports.

Not reusable:
- codim1_ac_sat_c1_local_extension has the same shape as the cutoff lemma but is still decomposing.
- The accepted locality lemmas (dtc_approxTangent_of_null_diff, rsd_cmr_ir_approxTangent_of_local_null, hasApproximateTangentSpaceAt_iff_of_null_sdiff) go in the other direction or are global, so the pointwise subset/closure lemma is new.

No snapshot file contains dor_lmbsf_cit, c1_local_extension or approxTangent_of_subset.

Mathlib supplies everything the new children need:
- ContDiffBump (one_of_mem_closedBall, tsupport_eq, contDiff, hasContDiffBump_of_innerProductSpace);
- contDiff_iff_contDiffAt, ContDiffAt.congr_of_eventuallyEq, image_eq_zero_of_notMem_tsupport;
- setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, Filter.EventuallyEq.fderiv_eq, subset_image_sdiff;
- euclideanHausdorffMeasure_zero and hausdorffMeasure_zero_singleton for n = 0.

Lean checks:
- All four child types elaborate in the exact comparator scope.
- The parent type follows from them using only propext, Classical.choice and Quot.sound.
- With the real accepted proofs and the prototype proofs of the two new lemmas, Submission.dor_lmbsf_c1_image_approxTangent compiles end to end with only the standard axioms.
